# Independent check with Comparator

[Comparator](https://github.com/leanprover/comparator) is the Lean FRO's tool for checking a proof
against a separately written statement. Here:

- `BGChallenge.lean` states the Brualdi-Goldwasser theorem in Mathlib's vocabulary, with `sorry`, and
  imports only the definitions of the answer (`R3Cert.BGAnswer`), not the proof.
- `BGSolution.lean` states the same two theorems and proves them.
- `bg.comparator.json` asks Comparator to confirm that the solution proves exactly the challenge's
  statements, that the proofs use only `propext`, `Quot.sound` and `Classical.choice`, and that the
  exported proof is accepted both by Lean's kernel and by
  [nanoda](https://github.com/ammkrn/nanoda_lib), an independent implementation of the Lean kernel in
  Rust. A soundness bug would have to fool two independently written kernels.

## Run it

```bash
# build the tools once (tag = this project's Lean version)
git clone --depth 1 --branch v4.32.0 https://github.com/leanprover/comparator.git
(cd comparator && lake build lean4export comparator)
git clone --depth 1 https://github.com/ammkrn/nanoda_lib.git && (cd nanoda_lib && cargo build --release)

# then, from formalization/ (after ./build.sh)
export COMPARATOR_LEAN4EXPORT=$PWD/../comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
export COMPARATOR_NANODA=$PWD/../nanoda_lib/target/release/nanoda_bin
export COMPARATOR_LANDRUN=/path/to/landrun   # a sandbox; on macOS a pass-through shim works
lake env comparator comparator/bg.comparator.json
```

## Result

On 27 September 2026 the check passed at commit `295d0ac` (the Lean sources have not changed since):
Comparator reported "Nanoda kernel accepts the solution", "Lean default kernel accepts the solution" and
"Your solution is okay!". The run took 5.1 hours and peaked at 63 GB of memory on an Apple-silicon Mac,
with the pass-through shim described below in place of the landrun sandbox. It has not yet been run in CI.

## The sandbox

Comparator runs its children inside [landrun](https://github.com/Zouuup/landrun), a Linux sandbox.
Since the solution here is our own, a pass-through shim that preserves the `--` separator is enough
(the kernel replay, not the sandbox, is the guarantee); use a real sandbox for untrusted solutions.

## Uniqueness of the maximizer

- `BGUniqueChallenge.lean` states uniqueness using Mathlib alone (it imports nothing else): for n ≥ 4,
  n ≠ 21, any two trees on n vertices that maximize per (lapMatrix) / ∏ deg among all trees on n vertices
  are isomorphic (`unique`); for n = 21 there are two maximizing trees that are not isomorphic, and every
  maximizing tree is isomorphic to one of them (`two_at_21`).
- `BGUniqueSolution.lean` proves both from `BGUnique/Mathlib.lean`.
- `unique.comparator.json` runs the check. Three negative controls must be rejected:
  `neg_unique_at21` (uniqueness claimed at n = 21 as well), `neg_unique_oneclass21` (a single isomorphism
  class at n = 21) and `neg_unique_everytree` (every tree is a maximizer). All three are false: their
  negations are proved in `BGUnique/Controls.lean`.

Run it like the main check, after `lake build BGUnique`:

```bash
lake env comparator comparator/unique.comparator.json
```

The three negative controls were run on 2 October 2026: Comparator rejected each one with "Challenge and
solution theorem statement do not match", on the theorem the control alters. On `unique.comparator.json`,
Comparator's statement, definition and axiom comparison passes (it reaches the kernel-replay phase); the
kernel replays themselves (Lean's kernel and nanoda) were not completed (a run was stopped after 6.4 hours),
so no Comparator kernel verdict is recorded for the uniqueness challenge. The theorems are checked by Lean's
kernel in the ordinary build (`lake build BGUnique`), and their axioms are listed in `BGUnique/AxiomGuard.lean`.
The challenge states uniqueness (and the two classes at n = 21); which tree attains the maximum is
`bg_maximizers_mathlib`, and the maximum value is the main challenge `BGChallenge.lean`.
