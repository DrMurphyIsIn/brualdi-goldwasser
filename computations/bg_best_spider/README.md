# bg_best_spider: count exchanges and the exact comparisons for the best spider

**Paper items:**
- Lemma `lem:bgx-counts` (computer-verified: count exchanges), the table of twelve exchanges;
- the exact rational and integer comparisons in the proof of Theorem `thm:bg-bestspider` (the best spider:
  Pi_0, Theta, Pi_s, the roots D_s^* and the signs of q_s at the neighbouring integers);
- the exact integer comparisons in the proof of Corollary `cor:bgx-limits`
  (G_4^11 < G_5^9, G_6^11 < G_5^13, (G_4^6/G_6^4)^11 < G_5^2);
- also the identities of Lemma `lem:bgx-split` (splitting a long arm) and the margins quoted in
  Remark `rem:bgx-race`.

Role: part of the proof.

## Files and what each checks

| script | checks | runtime here |
|---|---|---|
| `tab.py` | For each row of the table of `lem:bgx-counts`: the exact ratio Xi (printed to 6 decimals), the exact decimal xi <= Xi (asserted), and the two quadratics Delta_xi(X, y_lo X), Delta_xi(X, y_hi X), normalized to coprime integer coefficients. The output is the LaTeX body of the table. | 0.3 s |
| `exch.py` | The same twelve exchanges (and the cherry absorptions P + A_j -> A_{j+1}): for both Xi and the decimal xi, the expanded Delta and the smallest integer D_0 from which it is positive (this gives the thresholds 15 and 16 of the last two rows, unchanged with Xi in place of xi). | 0.5 s |
| `shortproof.py` | Theorem `thm:bg-bestspider`: G_4, G_5, G_6, Theta = 18468/18515, Pi_0, Pi_1..Pi_10 exactly (Pi_4 > 1 > Pi_5 asserted); q_s(0) < 0 and the exact signs q_1(27) < 0 < q_1(28), q_2(38) < 0 < q_2(39), q_3(65) < 0 < q_3(66), q_4(210) < 0 < q_4(211); a cross-check of the race sign against a direct exact comparison of the two candidate spiders for every D < 3000 and every s; the relative margins at n = 722, 733, 2319, 2330; the absorption thresholds 24 and 34. | 46 s |
| `race.py` | The same races in sympy (roots D_s^* and switch sizes n = 11 D + 2 s + 1) and the deficits g(A_4), g(A_6). | 0.5 s |
| `split.py` | Lemma `lem:bgx-split`: the closed form of Xi(u), the polynomial identity for the scaled Delta, its value at Y = X/3, and the negative discriminants. | 0.6 s |
| `identities_check.py` | A second check, written separately: the balance, leaf-pair and absorption identities; every row of the `lem:bgx-counts` table re-derived and compared with the printed quadratics (`prop [True, True]`); the split lemma; the race (Pi_s, roots, signs); and the exact integer comparisons of `cor:bgx-limits` (`int compare True True True`). | 1.7 s |

## How to run

    python3 tab.py
    python3 exch.py
    python3 shortproof.py
    python3 race.py
    python3 split.py
    python3 identities_check.py

Requires Python 3 with `sympy` and `mpmath` (only `fractions` otherwise). Peak memory under 70 MB each.

## Expected output

`expected_output.txt` holds the six outputs in the order above, each headed by `===== python3 <script>`.

## Re-run status

PASS (2026-10-04): the twelve rows printed by `tab.py` coincide with the table of `lem:bgx-counts`
(xi, Xi to six decimals, and both quadratics); `exch.py` gives the thresholds D_0 >= 15 and >= 16 for the
last two rows with both xi and Xi; `shortproof.py` reproduces Pi_0, Theta, Pi_1..Pi_4, Pi_5 and the sign
pairs of the table in the proof of `thm:bg-bestspider`, and the margins 2.0e-5 (n = 722) and 3.6e-6
(n = 2319) of `rem:bgx-race`; `identities_check.py` prints `int compare True True True` for the three
integer comparisons of `cor:bgx-limits` and liminf = 1.1234943...

The direct sweep over balanced spiders mentioned in Appendix C, item C8, is archived, with its output, in
`../bg_hull_dp/spider_sweep/` (it was adapted in October 2026, as a single-process program, from the script
`certificates/checks/bg_spider_opt.py` of this repository).
