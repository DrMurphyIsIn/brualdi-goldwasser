# Which tree maximizes the Laplacian ratio?

In 1984 Richard Brualdi and John Goldwasser studied the permanent of the Laplacian matrix of a tree
and asked a deceptively simple question: among all trees on *n* vertices, which one makes the
**Laplacian ratio**

  π(T) = per(L(T)) / ∏ deg(v)

as large as possible? The ratio is also a weighted count of matchings, π(T) = Σ over matchings M of
∏ over edges uv of M of 1/(deg u · deg v), so the question asks which tree has the "heaviest" matchings
once every edge is discounted by the degrees of its endpoints.

A conjectured answer by Wu, Dong and Lai was refuted in 2026 by Pant, whose counterexamples were
caterpillars of hubs. The question remained open.

This repository answers it, for every *n*, with a machine-checked proof.

## The answer

For every n ≥ 4 the maximizer is a **spider of cherry arms**: one centre vertex, and hanging from it
only *arms*, where an arm is a vertex carrying some number of *cherries* (pendant paths of length two).
Almost every arm carries **five** cherries. The exact shape depends on n only through a small
correction:

- For **n ≥ 492**, let s = 6(n − 1) mod 11. Every arm carries 5 cherries, except
  - s = 1, 2, 3, 4: s arms carry 6 cherries (but for s = 3 with n ≤ 722, and s = 4 with n ≤ 2319,
    it is instead 11 − s arms that carry 4 cherries);
  - s = 5, …, 10: 11 − s arms carry 4 cherries.
- For **4 ≤ n ≤ 491** the maximizer is given by an explicit table
  (`formalization/R3Cert/BGSpiderTableData.lean`); for small n it may also carry a few cherries or
  a leaf directly at the centre, and for n = 21 two different trees tie.

For n ≤ 3 there is only one tree of each size.

Why five? An arm with five cherries is an 11-vertex block whose contribution to the ratio is exactly
621/64 = ρ¹¹, where ρ = (621/64)^(1/11) ≈ 1.2295 turns out to be the exact exponential growth rate of
the maximum: we prove (64/621)·ρⁿ ≤ max π ≤ 2·ρⁿ⁻¹. The five-cherry arm is the unique structure that
achieves this rate, and the maximizer uses as many of them as the arithmetic of n allows.

## What is proved, and how to check it

The main theorem, in Lean 4 with Mathlib:

```lean
theorem R3Cert.BGMaximizerAll.bg_maximizer_all (n : ℕ) (h4 : 4 ≤ n) :
    usize (bgMax n) = n ∧ ∀ t : UTree, usize t = n → Aobj t ≤ Aobj (bgMax n)
```

`bgMax n` is the explicit spider above, `UTree` ranges over all trees, and `Aobj` is the Laplacian
ratio. The companion theorem `bg_maximizer_all_perm` states the same inequality literally for
`permanent (lapl G) / ∏ degree` of the realized graphs. Every headline theorem depends only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`,
no added axioms.

```bash
cd formalization
lake exe cache get          # Mathlib build cache
./build.sh                  # the full development, in memory-safe batches (see "Resources")
lake env lean AxiomGuard.lean
```

The proof splits by size:

| n | argument |
|---|---|
| 4–6 | exact rational evaluation of every tree |
| 7–149 | an *envelope certificate*: a sharded, kernel-checked Bellman bound showing that any tree which is not a spider is strictly beaten |
| 150–491 | refined per-vertex *rate cells* show the maximizer is a spider; an exhaustive kernel sweep of the spider family finds the best one |
| ≥ 492 | the same reduction to spiders, then exchange arguments and 223 polynomial certificates identify the rule above |

## Certificates and Telperion

Large parts of the proof are *certificates*: tables of exact rational or integer data, plus Lean
checks that the kernel evaluates. They are produced by generators in `certificates/`, packaged with
[Telperion](telperion/), a certificate pipeline in which the generator is untrusted and the Lean kernel
is the only trusted component. A wrong certificate is simply a failed build.

Every certificate family regenerates from scratch, byte for byte:

```bash
certificates/verify.sh            # all families + exact re-checks (~15 min)
certificates/verify.sh --full     # also the independent all-tree search for n <= 491 (+16 min)
```

## Resources

The full Lean build is heavy: some certificate fragments need 15–35 GiB of memory each and the whole
development takes several CPU-hours. Build with limited parallelism on a machine with at least 64 GiB of
memory. Lake cannot limit its own parallelism, so use `./build.sh` in `formalization/`, which builds the
heavy certificate files a few at a time before the rest.

## Reading the proof

- **The paper**, [`paper/paper.pdf`](paper/paper.pdf), tells the whole argument: the matching sum, the sharp
  ceiling, the reduction to spiders, the spider optimization, and how the certificates are checked.
- **The project page**, <https://drmurphyisin.github.io/brualdi-goldwasser/>, lets you pick any n and see
  its maximizer drawn, with a table for every n up to 3000. Three labs let you try the proof's ideas by
  hand: a *tree lab* (build a tree; step through its matchings, watch the cavity recursion, see the
  subaction inequality's slack at every vertex), a *spider lab* (scramble a spider and let the balance
  lemma repair it) and *the races* (the 722 and 2319 switches, decided in exact arithmetic).
- **The Lean source** is big (about 57,000 lines, most of it generated certificate data), and it was carried
  over from a larger research repository. [`formalization/READING_GUIDE.md`](formalization/READING_GUIDE.md)
  says which files hold the definitions a reviewer needs, and which leftover comments and flags to ignore.

## Continuous integration

- `certificates` (GitHub-hosted, also on pull requests) regenerates every certificate family and compares
  it byte for byte.
- `lean` (self-hosted, pushes to `main` and manual runs only) builds the whole formalization and checks
  that all 17 headline theorems use only the standard axioms. It runs on the maintainer's machine because
  GitHub-hosted runners don't have enough memory for the heaviest files. Pull requests never trigger it.
- `pages` publishes `site/` and the paper.

## Status

This result has **not yet been independently reviewed.** The Lean kernel checks the proof, but the
statement, the definitions, and the correspondence between `Aobj` and the Laplacian ratio deserve human
scrutiny. We welcome review, questions and issues.

## Layout

```
formalization/   Lean 4 project: the import closure of bg_maximizer_all (+ the sharp rate ceiling)
certificates/    generators and frozen Telperion records for every certificate family
telperion/       vendored Telperion engine (BSL 1.1)
paper/           the paper (paper.tex, gen_table.py builds its appendix from the Lean table)
site/            the project page (build.py fills template.html from the Lean table)
scripts/         setup for the isolated self-hosted CI runner
```

## License

Mathematics, certificates and Lean code: Apache-2.0. Documents: CC-BY-4.0. The vendored Telperion
engine: Business Source License 1.1, free for research, teaching and peer review. See
[LICENSING.md](LICENSING.md) and [NOTICE.md](NOTICE.md).
