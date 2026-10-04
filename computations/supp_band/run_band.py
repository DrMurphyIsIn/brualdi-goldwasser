"""Adaptive driver for certify_band.py on [LAM0, LAM1]: try width w; on witness divergence or check failure halve it (min 1e-5);
after a pass grow w by 1.5 (cap WMAX).  Every accepted box prints PASS with its worst slack; the run ends CERTIFIED only if
the whole interval is covered contiguously."""
import os, sys, time
os.environ.setdefault('OMP_NUM_THREADS', '1')
import certify_band as cb
L0, L1, W0, WMAX, DELTA = map(float, sys.argv[1:6])
x, w, n, t0 = L0, W0, 0, time.time()
while x < L1 - 1e-15:
    y = min(x + w, L1)
    try:
        J, G, GT = cb.witness(x, y, DELTA); res = cb.check(x, y, J, G, GT); ok = res[0] < 0
    except (RuntimeError, AssertionError) as e:
        ok, res = False, (None, str(e))
    if ok:
        n += 1; print(f"PASS [{x!r}, {y!r}] J={J} maxG={max(v for v in G.values() if v > -1e300):+.5f} GT={GT:+.5f} worst={res[0]:+.2e} at {res[1]}", flush=True)
        x = y; w = min(w*1.5, WMAX)
    else:
        w /= 2
        if w < 1e-5: print(f"FAILED at {x}: {res}", flush=True); sys.exit(1)
print(f"BAND [{L0}, {L1}]: CERTIFIED; {n} boxes; DELTA={DELTA}; {time.time()-t0:.0f}s", flush=True)
