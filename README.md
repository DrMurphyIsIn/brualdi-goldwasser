# Which tree maximizes the Laplacian ratio?

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22983413.svg)](https://doi.org/10.5281/zenodo.22983413)

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
ratio.

The same result is also stated purely in Mathlib's vocabulary, in
[`formalization/Statement.lean`](formalization/Statement.lean): for every tree `G : SimpleGraph V` on
`n ≥ 4` vertices (Mathlib's `IsTree`), `(G.lapMatrix ℝ).permanent / ∏ v, G.degree v ≤ F (bgChildren n)`,
and some tree on `Fin n` attains it. There a reviewer needs to trust only Mathlib's graph and permanent
definitions plus the short closed form `F` and the list `bgChildren n`. The companion theorem `bg_maximizer_all_perm` states the same inequality literally for
`permanent (lapl G) / ∏ degree` of the realized graphs. Every headline theorem depends only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`,
no added axioms.

How to build and check all of this yourself is in [Getting started](#getting-started) below.

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
[Telperion](telperion/README.md), a certificate pipeline in which the generator is untrusted and the Lean kernel
is the only trusted component. A wrong certificate is simply a failed build.

Every certificate family regenerates from scratch, byte for byte:

```bash
certificates/verify.sh            # all families + exact re-checks (~15 min)
certificates/verify.sh --full     # also the independent all-tree search for n <= 491 (+16 min)
```

## Getting started

### What you need

| | needed for | version | notes |
|---|---|---|---|
| **git** | cloning | any | |
| **elan** (the Lean toolchain manager) | the Lean proof | any | installs the exact Lean version pinned in `formalization/lean-toolchain` (**Lean 4 v4.32.0**) automatically |
| **Mathlib** | the Lean proof | **v4.32.0** (pinned in `formalization/lake-manifest.json`) | fetched automatically, with a prebuilt cache |
| **RAM** | the Lean proof | **96 GB recommended** | the heaviest certificate file alone peaks at 63 GB (see [Resources](#resources)) |
| **disk** | the Lean proof | about **15 GB** | Mathlib and its cache about 12 GB, this project's build about 2 GB |
| **Python ≥ 3.11** + [`certificates/requirements.txt`](certificates/requirements.txt) | regenerating the certificates | sympy, numpy, mpmath, networkx | nothing else outside the standard library |
| **TeX Live** (or MacTeX) with pgfplots | building the paper (optional) | 2023 or later | see [`paper/README.md`](paper/README.md) |
| **Rust** (cargo) | the Comparator / nanoda check (optional) | stable | see [`formalization/comparator/README.md`](formalization/comparator/README.md) |

You don't need anything to *read* the result: [`paper/paper.pdf`](paper/paper.pdf) and the
[project page](https://drmurphyisin.github.io/brualdi-goldwasser/) are ready to go. The Lean proof has
been built and checked on macOS (Apple Silicon); the certificate checks also run on Ubuntu in CI.

### 1. Clone

```bash
git clone https://github.com/DrMurphyIsIn/brualdi-goldwasser.git
cd brualdi-goldwasser
```

The repository is small (about 30 MB). A specific release can be checked out with `git checkout v1.1.0`;
release `v1.0.0` is archived with DOI [10.5281/zenodo.22983413](https://doi.org/10.5281/zenodo.22983413).

### 2. Install Lean

If you don't already have elan:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
source ~/.elan/env        # or open a new terminal
```

(On Windows, see <https://lean-lang.org/install/>.) Inside `formalization/`, elan reads
`lean-toolchain` and installs Lean v4.32.0 the first time you run `lake`.

### 3. Fetch Mathlib and build

```bash
cd formalization
lake exe cache get        # download Mathlib's prebuilt files (a few minutes)
./build.sh                # build and kernel-check everything
```

`./build.sh` checks the heavy certificate files one at a time and then everything else. On a machine
with 96 GB or more, `./build.sh 2` does two at a time; that is how it was measured: **1 hour 14 minutes**
from scratch on an Apple M3 Ultra, peak **63 GB**. On an already-built tree it takes seconds.

### 4. Check the statement and the axioms

```bash
lake env lean Statement.lean     # the theorem in Mathlib's vocabulary
lake env lean AxiomGuard.lean    # the axioms of all 20 headline theorems
```

Every line printed should read `depends on axioms: [propext, Classical.choice, Quot.sound]`. A `sorry`
anywhere in a proof would show up here as `sorryAx`, and a `native_decide` as `Lean.ofReduceBool`.

### 5. Regenerate the certificates

```bash
cd ..                                   # back to the repository root
python3 -m venv .venv && source .venv/bin/activate
pip install -r certificates/requirements.txt
certificates/verify.sh                  # about 15 minutes
certificates/verify.sh --full           # also the independent all-tree search for n <= 491 (+16 min)
```

This regenerates every certificate family from scratch and compares it byte for byte with the files the
Lean kernel checked. It ends with `all certificate families reproduce exactly`.

### 6. Optional extras

- **An independent second kernel.** [`formalization/comparator/`](formalization/comparator/) holds a
  challenge/solution pair for the Lean FRO's [Comparator](https://github.com/leanprover/comparator), which
  replays the proof in Lean's kernel and in [nanoda](https://github.com/ammkrn/nanoda_lib), an independent
  implementation in Rust. Its README has the steps. It is slow: expect several hours.
- **The paper:** [`paper/README.md`](paper/README.md). **The project page:** [`site/README.md`](site/README.md).

### Troubleshooting

- **The build is killed, or the machine starts swapping.** A certificate file ran out of memory. Use
  `./build.sh` (one heavy file at a time) and close other large programs; `G149/Frag22` alone needs
  about 63 GB.
- **`lake exe cache get` fails, or Mathlib starts compiling from source.** Check that you are inside
  `formalization/` and that elan picked up v4.32.0 (`lean --version`). Compiling Mathlib from source also
  works, but takes hours longer.
- **`certificates/verify.sh` reports a difference.** Make sure you are on a clean checkout
  (`git status`) and on a supported Python (≥ 3.11). Anything else is worth an issue.

Found a problem, or have a question about the mathematics? See [CONTRIBUTING.md](CONTRIBUTING.md).

## Resources

The full Lean build is heavy because the Lean kernel keeps every intermediate term of a declaration in
memory while it checks it, and some certificates are large. Measured peaks: `G149/Frag22` alone
reaches 63 GB; the next heaviest certificate files need 40–50 GB; most files need far less. Lake cannot limit its
own parallelism, so `formalization/build.sh` builds the heavy certificate files a few at a time (one by
default) before everything else.

## Reading the proof

- **The paper**, [`paper/paper.pdf`](paper/paper.pdf), tells the whole argument: the matching sum, the sharp
  ceiling, the reduction to spiders, the spider optimization, and how the certificates are checked.
- **The project page**, <https://drmurphyisin.github.io/brualdi-goldwasser/>, lets you pick any n and see
  its maximizer drawn, with a table for every n up to 3000. Three labs let you try the proof's ideas by
  hand: a *tree lab* (build a tree; step through its matchings, watch the cavity recursion, see the
  subaction inequality's slack at every vertex), a *spider lab* (scramble a spider and let the balance
  lemma repair it) and *the races* (the 722 and 2319 switches, decided in exact arithmetic).
- **The Lean source** is big (about 44,000 lines, most of it generated certificate data), and it was carried
  over from a larger research repository. [`formalization/READING_GUIDE.md`](formalization/READING_GUIDE.md)
  says which files hold the definitions a reviewer needs, and which leftover comments and flags to ignore.

## Continuous integration

- `certificates` (GitHub-hosted, also on pull requests) regenerates every certificate family and compares
  it byte for byte.
- `lean` (self-hosted, pushes to `main` and manual runs only) builds the whole formalization and checks
  that all 20 headline theorems, and the statement in `Statement.lean`, use only the standard axioms. It runs on the maintainer's machine because
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
telperion/       vendored Telperion engine (BSL 1.1); telperion/README.md describes it on its own terms
paper/           the paper (paper.tex, gen_table.py builds its appendix from the Lean table)
site/            the project page (build.py fills template.html from the Lean table)
scripts/         setup for the isolated self-hosted CI runner
CONTRIBUTING.md  how to review the work and report problems
CITATION.cff     how to cite this work
```

## License

Mathematics, certificates and Lean code: Apache-2.0. Documents: CC-BY-4.0. The vendored Telperion
engine: Business Source License 1.1, free for research, teaching and peer review. See
[LICENSING.md](LICENSING.md) and [NOTICE.md](NOTICE.md).
