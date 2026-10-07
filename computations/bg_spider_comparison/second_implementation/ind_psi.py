# Psi_k = max_{y in [0,1]} (log(1+y) - k h_eta(y)), eta = eta_{k-1}, for k = 2..23.
# This driver was added when the folder was assembled for publication; it only calls fmax_upper of
# ind_common.py (with S = 0, j = k, Y = 1, which is exactly Psi_k), the rigorous concave-tangent
# upper bound used by ind_root.py.
from ind_common import *
for k in range(2, 24):
    ub = fmax_upper(Fr(0), k, k, ETA[k - 1], Fr(1))
    print(k, "Psi<=%.7f" % float(ub), flush=True)
