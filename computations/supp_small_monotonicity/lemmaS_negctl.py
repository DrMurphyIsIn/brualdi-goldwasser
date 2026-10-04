"""Negative controls for lemmaS_certify.py.  Expected: the baseline PASSES; every broken variant FAILS in BOTH columns:
 OWN   = the variant generates its own witness and verifies it;
 TRUST = the variant's verification step is run against the BASELINE witness (class bounds from the unmodified code on the same box).
 (1) r_3' lowered by 0.001 consistently, with A3 evaluated by the recursion (no identity): A3 then has l' = +0.007.
 (2) DELTA = 0 (the slack is what absorbs the box width).  DELTA enters ONLY witness generation, so its TRUST column is the
     baseline check and is expected to PASS; it is a control on witness generation, not on the verifier.
 (3) A box beyond the true threshold, [0.1986, 0.1990], where S5 = A4 has l' > 0 (Lemma S is false there).
 (4) A3's value raised by 0.002."""
import sys
src = open('lemmaS_certify.py').read().split('\nif __name__')[0]
def module(reps=()):
    s = src
    for a, b in reps:
        assert a in s, a[:50]; s = s.replace(a, b)
    ns = {}; sys.argv = ['x']; exec(s, ns); return ns
BASEMOD = module()
def verdict(ns, box, W):
    try:
        w, ex = ns['check_box'](*box, W=W)
        viol = max(w[0], ex)
        return (viol < 0), f"{'PASSES' if viol < 0 else 'FAILS '} viol={viol:+.2e} ({'GEN ' + str(w[1]) if w[0] >= ex else 'exact type'})"
    except AssertionError as e: return False, f"FAILS  assertion: {str(e)[:60]}"
def run(label, box, reps=()):
    ns = module(reps)
    base_W = BASEMOD['g_iter']((box[0] + box[1])/2, -0.012)
    _, own = verdict(ns, box, None)
    _, tr = verdict(ns, box, base_W)
    print(f"{label:48s} | OWN: {own:55s} | TRUST: {tr}", flush=True)
B = (0.1, 0.102)
run("baseline [0.1, 0.102]", B)
run("(1) r3' - 0.001 consistently, A3 by recursion", B,
    [("rp = (D('1.5')/(1 + S/2) + (D('1.5')/((2 + S)*(2 + S)))/(1 + 3*S/(4*(2 + S))))/7",
      "rp = (D('1.5')/(1 + S/2) + (D('1.5')/((2 + S)*(2 + S)))/(1 + 3*S/(4*(2 + S))))/7 - D('0.001')"),
     ("            if t == A3: lp = D(0)\n", ""),
     ("lp=(iv.mpf(0) if tb['name'] == A3 else mv(tb['lp'], tm['lp']))", "lp=mv(tb['lp'], tm['lp'])")])
run("(2) DELTA = 0", B, [("N0, D1, DT, YH, DELTA, EPS = 7, 12, 300, 0.1, 0.003, 1e-9", "N0, D1, DT, YH, DELTA, EPS = 7, 12, 300, 0.1, 0.0, 1e-9")])
run("(3) box beyond threshold [0.1986, 0.1990]", (0.1986, 0.1990))
run("(4) A3 value raised by 0.002", B, [("lp=(iv.mpf(0) if tb['name'] == A3 else", "lp=(iv.mpf('0.002') if tb['name'] == A3 else")])
