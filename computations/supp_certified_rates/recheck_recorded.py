"""Re-verify the 28 RECORDED certificates of thm:lam-cert (the witnesses listed in tab:lam-cert).

certify_plain.py and certify_leafx.py obtain their witness h from a floating-point linear program, which is
untrusted input: a different LP solver or version can return a different h (sometimes one that just fails
to certify, see README.md). This wrapper skips the LP and feeds the witness recorded in
certificates/cert_*.json (rational nodes, node values as exact formal numbers c + sum a_p log p) to the
unchanged checking routine certify() of the two programs. It then compares the number of nodes, the tail
parameter M (resp. N) and the number of verified cells with the recorded values.
Usage: python3 recheck_recorded.py            (all 28)
       python3 recheck_recorded.py plain_5_2  (one; name of the json without cert_ and .json)"""
import os, sys, json, glob, re
os.environ["OMP_NUM_THREADS"] = "1"
from fractions import Fraction as Fr
from formal import FL
import certify_plain, certify_leafx

HERE = os.path.dirname(os.path.abspath(__file__))


def parse_fl(s):
    m = re.fullmatch(r"FL\((.*?) \+ (.*)\)", s)
    c, rest = m.group(1), m.group(2).strip()
    a = {}
    if rest:
        for term in rest.split(" + "):
            v, p = term.split("*log")
            a[int(p)] = Fr(v)
    return FL(Fr(c), a)


def recorded(path):
    d = json.load(open(path))
    nodes = [Fr(y) for y, _ in d["nodes"]]
    vals = [parse_fl(v) for _, v in d["nodes"]]
    return d, nodes, vals


def run(path):
    name = os.path.basename(path)[5:-5]
    d, nodes, vals = recorded(path)
    lam = Fr(d["lam"])
    fake = lambda *args, **kw: (list(nodes), list(vals), None)
    if name.startswith("plain"):
        certify_plain.build_h = fake
        info = certify_plain.certify(lam, verbose=False)
        keys = ("nnodes", "M", "certificates", "exact_zero_endpoints")
    else:
        certify_leafx.build_h = fake
        info = certify_leafx.certify(lam, verbose=False)
        keys = ("nnodes", "N", "certificates", "exact_zero_endpoints")
    same = all(info[k] == d[k] for k in keys)
    print("%-16s lam=%-8s CERTIFIED  %s  %s" % (name, d["lam"], "  ".join("%s=%s" % (k, info[k]) for k in keys),
          "matches record" if same else "DIFFERS from record " + str({k: d[k] for k in keys})))
    return same


if __name__ == "__main__":
    files = sorted(glob.glob(os.path.join(HERE, "certificates", "cert_*.json")))
    if len(sys.argv) > 1:
        files = [os.path.join(HERE, "certificates", "cert_%s.json" % sys.argv[1])]
    ok = [run(f) for f in files]
    print("%d recorded certificates re-verified; %d match the recorded counts" % (len(ok), sum(ok)))
