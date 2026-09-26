#!/bin/bash
# Set up an isolated self-hosted GitHub Actions runner for the heavy Lean build (.github/workflows/lean.yml).
#
# What it does (run once, as your normal admin user, from the repo root; it asks for sudo):
#   1. creates a hidden, NON-admin macOS user `bgrunner` whose primary group is its own group `bgrunner`
#      (not `staff`), so it cannot read your home directory, which is drwxr-x--- group staff;
#   2. checks that isolation: `bgrunner` must be unable to list your home directory, or the script stops;
#   3. installs elan (the Lean toolchain manager) and the GitHub Actions runner inside /Users/bgrunner;
#   4. registers the runner with the repository, with the label `bg-lean`
#      (fetches a one-hour registration token with `gh`, which must be logged in as the repo owner);
#   5. installs a LaunchDaemon that runs the runner as `bgrunner` at boot, at reduced CPU priority;
#   6. optionally (--seed-lake DIR) copies an already-built .lake into the runner's checkout, so the first
#      CI run does not rebuild everything (APFS clone copy: fast, no extra disk until files diverge);
#   7. optionally (--block-loopback) adds a pf firewall anchor that blocks `bgrunner` from connecting to
#      localhost services, so CI jobs cannot reach anything listening on this machine.
#
# Safety model: lean.yml only triggers on pushes to main and manual dispatch, never on pull requests, so code
# from forks never runs here.  Keep "Settings > Actions > General > Fork pull request workflows" set to
# require approval, and do not add a pull_request trigger to any job with `runs-on: self-hosted`.
#
# Undo: sudo launchctl bootout system/com.drmurphyisin.bg-runner; sudo rm /Library/LaunchDaemons/com.drmurphyisin.bg-runner.plist;
#       remove the runner in GitHub settings; sudo sysadminctl -deleteUser bgrunner; sudo dseditgroup -o delete bgrunner;
#       and, if used, remove the `bgrunner` anchor lines from /etc/pf.conf and `sudo pfctl -f /etc/pf.conf`.

set -euo pipefail

REPO="DrMurphyIsIn/brualdi-goldwasser"
RUNNER_USER="bgrunner"
RUNNER_HOME="/Users/$RUNNER_USER"
LABEL="com.drmurphyisin.bg-runner"
SEED_LAKE=""
BLOCK_LOOPBACK=0

while [ $# -gt 0 ]; do
  case "$1" in
    --seed-lake) SEED_LAKE="$2"; shift 2 ;;
    --block-loopback) BLOCK_LOOPBACK=1; shift ;;
    *) echo "unknown option $1"; exit 2 ;;
  esac
done

ME="$(id -un)"
MYHOME="$(eval echo "~$ME")"
[ "$ME" != "root" ] || { echo "run as your normal user, not root (the script calls sudo itself)"; exit 1; }
command -v gh >/dev/null || { echo "needs the GitHub CLI (gh), logged in as the repository owner"; exit 1; }

echo "== 1. user and group"
if ! dscl . -read "/Groups/$RUNNER_USER" >/dev/null 2>&1; then
  sudo dseditgroup -o create -r "BG CI runner" "$RUNNER_USER"
fi
GID="$(dscl . -read "/Groups/$RUNNER_USER" PrimaryGroupID | awk '{print $2}')"
if ! id "$RUNNER_USER" >/dev/null 2>&1; then
  PW="$(openssl rand -base64 30)"          # never used interactively; the account is hidden
  sudo sysadminctl -addUser "$RUNNER_USER" -fullName "BG CI runner" -password "$PW" -home "$RUNNER_HOME" >/dev/null
  unset PW
fi
sudo dscl . -create "/Users/$RUNNER_USER" PrimaryGroupID "$GID"
sudo dscl . -create "/Users/$RUNNER_USER" IsHidden 1
sudo dscl . -create "/Users/$RUNNER_USER" UserShell /bin/bash
sudo dseditgroup -o edit -d "$RUNNER_USER" -t user staff 2>/dev/null || true
sudo dseditgroup -o edit -d "$RUNNER_USER" -t user admin 2>/dev/null || true
sudo mkdir -p "$RUNNER_HOME"
sudo chown -R "$RUNNER_USER:$RUNNER_USER" "$RUNNER_HOME"
sudo chmod 700 "$RUNNER_HOME"

echo "== 2. isolation check"
if sudo -u "$RUNNER_USER" ls "$MYHOME" >/dev/null 2>&1; then
  echo "STOP: $RUNNER_USER can list $MYHOME.  Fix permissions (e.g. chmod 750 or 700 on it) and rerun."
  exit 1
fi
if dsmemberutil checkmembership -U "$RUNNER_USER" -G admin | grep -q "is a member"; then
  echo "STOP: $RUNNER_USER is an admin"; exit 1
fi
echo "ok: $RUNNER_USER cannot read $MYHOME and is not an admin"

echo "== 3. elan and the runner"
sudo -u "$RUNNER_USER" -H bash -c 'cd ~ && [ -x ~/.elan/bin/elan ] || (curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none)'
VER="$(gh api repos/actions/runner/releases/latest --jq .tag_name | sed 's/^v//')"
TARBALL="actions-runner-osx-arm64-$VER.tar.gz"
sudo -u "$RUNNER_USER" -H bash -c "mkdir -p ~/actions-runner && cd ~/actions-runner && \
  { [ -x ./run.sh ] || { curl -sSfL -o $TARBALL https://github.com/actions/runner/releases/download/v$VER/$TARBALL && tar xzf $TARBALL && rm $TARBALL; }; }"

echo "== 4. register with $REPO"
if ! sudo test -f "$RUNNER_HOME/actions-runner/.runner"; then
  TOKEN="$(gh api -X POST "repos/$REPO/actions/runners/registration-token" --jq .token)"
  sudo -u "$RUNNER_USER" -H bash -c "cd ~/actions-runner && ./config.sh --unattended --url https://github.com/$REPO \
    --token '$TOKEN' --name \"$(scutil --get LocalHostName)-bg-lean\" --labels bg-lean --work _work --replace"
  unset TOKEN
fi

echo "== 5. LaunchDaemon"
PLIST="/Library/LaunchDaemons/$LABEL.plist"
sudo tee "$PLIST" >/dev/null <<PL
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
  <key>Label</key><string>$LABEL</string>
  <key>UserName</key><string>$RUNNER_USER</string>
  <key>GroupName</key><string>$RUNNER_USER</string>
  <key>WorkingDirectory</key><string>$RUNNER_HOME/actions-runner</string>
  <key>ProgramArguments</key><array><string>$RUNNER_HOME/actions-runner/run.sh</string></array>
  <key>EnvironmentVariables</key><dict>
    <key>HOME</key><string>$RUNNER_HOME</string>
    <key>PATH</key><string>$RUNNER_HOME/.elan/bin:/usr/bin:/bin:/usr/sbin:/sbin</string>
  </dict>
  <key>RunAtLoad</key><true/>
  <key>KeepAlive</key><true/>
  <key>Nice</key><integer>10</integer>
  <key>StandardOutPath</key><string>$RUNNER_HOME/actions-runner/launchd.log</string>
  <key>StandardErrorPath</key><string>$RUNNER_HOME/actions-runner/launchd.log</string>
</dict></plist>
PL
sudo chown root:wheel "$PLIST"; sudo chmod 644 "$PLIST"
sudo launchctl bootout "system/$LABEL" 2>/dev/null || true
sudo launchctl bootstrap system "$PLIST"

if [ -n "$SEED_LAKE" ]; then
  echo "== 6. seed .lake from $SEED_LAKE"
  DEST="$RUNNER_HOME/actions-runner/_work/brualdi-goldwasser/brualdi-goldwasser/formalization"
  sudo mkdir -p "$DEST"
  sudo cp -cR "$SEED_LAKE" "$DEST/.lake"
  sudo chown -R "$RUNNER_USER:$RUNNER_USER" "$RUNNER_HOME/actions-runner/_work"
  echo "seeded (lake still rehashes sources and rebuilds anything that differs)"
fi

if [ "$BLOCK_LOOPBACK" = 1 ]; then
  echo "== 7. pf: block $RUNNER_USER from localhost"
  sudo tee /etc/pf.anchors/bgrunner >/dev/null <<PF
block drop out quick on lo0 proto { tcp, udp } from any to any user $RUNNER_USER
PF
  if ! grep -q 'anchor "bgrunner"' /etc/pf.conf; then
    sudo cp /etc/pf.conf "/etc/pf.conf.bak.$(date +%Y%m%d%H%M%S)"
    printf 'anchor "bgrunner"\nload anchor "bgrunner" from "/etc/pf.anchors/bgrunner"\n' | sudo tee -a /etc/pf.conf >/dev/null
  fi
  sudo pfctl -nf /etc/pf.conf && sudo pfctl -f /etc/pf.conf 2>/dev/null && sudo pfctl -E 2>/dev/null || true
fi

echo
echo "done.  Check: gh api repos/$REPO/actions/runners --jq '.runners[] | {name,status,labels:[.labels[].name]}'"
echo "Then trigger a build: gh workflow run lean -R $REPO"
