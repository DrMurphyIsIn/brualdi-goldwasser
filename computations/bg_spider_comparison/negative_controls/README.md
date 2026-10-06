# Negative control: spider comparison (lem:bg-compare(i))

`nc_spider_comparison.py` reruns the comparison V_k(n) - eta_{k-1}(n-1) < Lambda_sp(n) of the
spider-comparison lemma for k = 9 and 10 with the programs of the parent folder.

- Unperturbed: the comparison holds for every n in [108, 315] (expected PASS).
- Perturbed: at n = 107 = n-bar(k) - 1 it fails (expected FAIL), so the threshold n-bar(k) = 108 is sharp
  for the program and the check can fail.

Run from this folder: `python3 nc_spider_comparison.py` (about 11 minutes, single core, under 100 MB).
Expected output: `expected_output.txt`.
