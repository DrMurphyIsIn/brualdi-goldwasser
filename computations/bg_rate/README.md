# bg_rate: the rate potential, the non-atom gap, Psi_k and the large-n thresholds

**Paper items (all certified by one program, `certify.py`):**
- Lemma `lem:bg-rate` (rate potential; computer-verified): for each cap 1 <= K <= 22 the rational eta_K of
  table `tab:bg-rate`, convexity of H = h - eta_K w, and the 253 one-variable inequalities
  Phi^H_c >= 0 on [0, c], 1 <= c <= K <= 22 (section D of the output);
- Proposition `prop:bg-gap` (non-atom gap; computer-verified), section B of the output; see also
  `../bg_nonatom_gap/`;
- the degree >= 24 constants of Proposition `prop:bg-high` (section C);
- the upper bounds Psi_k, 2 <= k <= 23, of table `tab:bg-rate` (section E), used in Lemma `lem:bg-compare`;
- Lemma `lem:bg-compare`(ii): the thresholds n0(k) <= 316 against the table spiders (n <= 491) and the
  benchmark spider A_5^a A_4^b (n >= 492) (section G).

Role: part of the proof.

## What is checked, and how

All arithmetic is `mpmath.iv` (outward rounding, 120 bits) on rational enclosures of the constants
(`core.log_encl`: atanh series with explicit remainder).
- B: for each child count c of a minimal non-atom: c = 1 via Phi_1(3/7); 2 <= c <= 9 via m_c + w_c(y_a) +
  delta(a) over a in {leaf, A_1, ..., A_30} and the tail A_{>30}; c = 10, 11, 12 by interval branch-and-bound
  of min Phi_c on [0, c]; c >= 13 via Q(13). The minimum is asserted >= 0.01426.
- D: the rates eta_K are proposed by an untrusted float bisection (`rate_explore.py`, numpy), rounded down to
  rationals, and then certified: convexity reduces to eta_K (621/14 - 3/2) <= gamma - s, and each
  Phi^H_c >= 0 on [0, c] is proved by interval branch-and-bound (`ivtools.bb_min_ge0`). At the two exact zeros
  (c, S) = (1, 1) and (5, 5/3) the boxes next to the zero are closed by one-sided derivative enclosures
  (derivative <= 0 on the left piece, >= 0 on the right piece).
- E: Psi_k = max_{y in [0,1]} (log(1+y) - k H(y)) by best-first interval branch-and-bound (upper bound).
- G: for 2 <= k <= 23 and every N up to 20000, Psi_k - eta_{k-1} N against the lower bound log pi - (n-1)F*
  of the table spider (exact pi, rational log enclosure) or, beyond the table, of the benchmark spider.

`certify.py` writes `certify_out.json` (the certified rates eta_K and thresholds); `../bg_spider_comparison/`
reads a copy of it.

## Second implementation

`second_implementation/ratecheck.py` (with its own `indep.py`; it imports nothing from this folder) was
written separately from the statements. It encloses 5/3 as an interval and uses one-sided derivatives on
each piece over supersets, re-proves all 253 inequalities (214,531 boxes, the count quoted in the paper),
checks convexity of H for all caps, and recomputes upper bounds for Psi_k, comparing each with the column
of table `tab:bg-rate` (`OK` = the paper's value is a valid upper bound). It writes `psi_indep.json`.

## How to run

    python3 certify.py                                   # writes certify_out.json
    cd second_implementation && python3 ratecheck.py     # writes psi_indep.json

Requires Python 3 with `mpmath` and `numpy`. `table_maximizers.tex` is the appendix table of the paper
(same file as `paper/table_maximizers.tex` of this repository).

## Expected output

`expected_output.txt` (output of `certify.py`), `certify_out.json`,
`second_implementation/expected_output.txt`, `second_implementation/psi_indep.json`.

## Runtimes measured here (one core)

| run | time | peak memory |
|---|---|---|
| `certify.py` | 231 s | 37 MB |
| `second_implementation/ratecheck.py` | 62 s | 18 MB |

## Re-run status

PASS (2026-10-04). `certify.py`: output and `certify_out.json` identical to the earlier run; the 22 rates
eta_K equal the column eta_{k-1} of table `tab:bg-rate` exactly (2791/2500000, ..., 613/2000000), all 22
caps print `verified=True`; delta_0 = 0.014273 >= 0.01426 with the inputs of `prop:bg-gap`
(Phi_1(3/7) >= 0.017444, min at c = 6, a = A_4: 0.014273, min Phi_c >= 0.017838 / 0.022008 / 0.025662 for
c = 10, 11, 12, Q(13) >= 0.018608); the benchmark floor 0.112186 > 0.11218 and the degree >= 24 ceiling
0.110157; the Psi_k bounds; thresholds n0(k) with maximum 316 at k = 23. The paper's Psi_k column is these
bounds rounded up (the program prints them rounded to nearest; the second implementation confirms every
paper value is a valid upper bound). The bound m_c + w_c(y(A_31)) >= 0.028 of `prop:bg-gap` is used only
inside the minimum (the `A>30` candidate) and is not printed separately.

`ratecheck.py`: 253 one-variable checks, 214,531 boxes, H convex for all caps, and `OK` for all 22 Psi_k
values of table `tab:bg-rate`. (Its comparison table was updated to the paper's current Psi_k column;
the computation is unchanged.)
