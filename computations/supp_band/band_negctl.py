"""Negative controls for certify_band.py on the box [1.0, 1.01] (DELTA = 0.0003). Expected: baseline PASSES, every variant FAILS
(by a failed check, a diverged witness, or a violated structural assertion)."""
import sys, types
src = open('certify_band.py').read()
def run(label, patches=()):
    s = src
    for a, b in patches:
        assert a in s, (label, a[:50]); s = s.replace(a, b)
    m = types.ModuleType('cbx'); exec(s.split('if __name__')[0], m.__dict__)
    try:
        J, G, GT = m.witness(1.0, 1.01, 0.0003); w = m.check(1.0, 1.01, J, G, GT); ok = w[0] < 0; info = f"{w[0]:+.2e} at {w[1]}"
    except (RuntimeError, AssertionError) as e:
        ok, info = False, f"{type(e).__name__}: {str(e)[:60]}"
    # trusted check of the variant against the BASELINE witness (so a failure is the check's, not the iteration's)
    try:
        w2 = m.check(1.0, 1.01, *BASE); info2 = f"{w2[0]:+.2e} at {w2[1]}"; ok2 = w2[0] < 0
    except (RuntimeError, AssertionError) as e:
        ok2, info2 = False, f"{type(e).__name__}: {str(e)[:40]}"
    print(f"{label:52s}: own witness {'PASSES' if ok else 'FAILS'} ({info}); baseline witness {'PASSES' if ok2 else 'FAILS'} ({info2})", flush=True)
import certify_band as _cb
BASE = _cb.witness(1.0, 1.01, 0.0003)
run("baseline")
run("best arm treated as GEN (all-P2 exclusion removed)",
    [("s = (d-1)*c[o[0]] if o[0] != iP2 else (d-2)*c[o[0]] + c[o[1]]\n                best = min(", "s = (d-1)*c[o[0]]\n                best = min(")])
run("F* lowered consistently by 0.002", [("    return (J*iv.log(1 + L/2) + iv.log(2 + L*(1+q)) - iv.log(2 + L))/(2*J+1)",
                                         "    return (J*iv.log(1 + L/2) + iv.log(2 + L*(1+q)) - iv.log(2 + L))/(2*J+1) - iv.mpf('0.002')")])
run("PAD and slack removed (DELTA = 0 in check)", [("v = pb - G[(e, k)] + PAD", "v = pb - (G[(e, k)] - 0.0003) + PAD")])
run("tail: DMAX factor dropped ((d-1) h_t <= h_t)", [("        c = DMAX*h + coef*yhi", "        c = h + coef*yhi")])
