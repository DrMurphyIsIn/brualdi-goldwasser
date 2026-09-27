# Telperion

Telperion turns mathematical claims that are too numerous or too tedious to prove by hand into Lean 4
theorems that the Lean kernel checks. You describe a *family* of claims (an inequality with parameters,
a table of finite facts, an identity, an enclosure of a constant), Telperion finds a certificate for each
member in exact arithmetic, and it writes out Lean files whose proofs replay those certificates. Then Lean
checks them.

It was built for computer-assisted proofs, where the conceptual argument fits in a paper but rests on
hundreds or thousands of concrete inequalities that a referee cannot realistically check by hand.

## The trust model

The whole design follows from one rule: **the generator is untrusted, and the Lean kernel is the only
trusted component.**

Telperion is a large Python program, and large programs have bugs. So nothing it computes is taken on
faith. Every certificate becomes a Lean proof, and the kernel re-checks it from scratch. If the generator
is wrong, whether through a bug, a floating-point slip, or a claim that was never true, the result is a
Lean file that does not compile, not a false theorem. A wrong certificate is a failed build.

That means the Python checks inside Telperion are there to catch mistakes early and to explain them, not
to establish truth. It also means the part a human must still check is the *statement*: whether the
theorems Lean accepts say what you meant. Several of the tools below exist to make that check easier.

## How it works

```
family ──► certify ──► validate ──► emit ──► Lean files ──► Lean kernel
            │                        │
            └─ refuse + diagnose     └─ provenance hash, freeze, drift check
```

1. **Describe a family.** A family is a finite grid of instances. The basic kind is a claim `0 ≤ target`
   about rational functions of nonnegative real variables. Others are bilinear box claims (`before ≤
   after` on a rectangle), identities, finite decidable facts, and existential "one of these witnesses
   works" claims. A family can also declare *ties* (points where the claim must be exactly tight, so an
   overclaim with slack is refused), *anchors* (known values the pipeline must reproduce), and an
   *independent implementation* of the target, which is cross-checked at random rational points so that
   a bug in one engine is caught by the other.
2. **Certify.** For every instance Telperion looks for a certificate in exact arithmetic (sympy over
   rationals, never floats). For the basic kind this is a Pólya certificate: the claim's numerator has only
   nonnegative coefficients over a positive denominator, which makes nonnegativity evident. If an instance
   cannot be certified, Telperion refuses to go further and says why. The claim may be false (it then
   searches for an exact rational counterexample), true but not certifiable in this form (it suggests
   transformations), or set up wrongly.
3. **Validate.** An exact numeric layer of rational interval arithmetic and verified constants checks the
   family's side conditions. Emission is refused unless validation is green.
4. **Emit.** Deterministic templates turn each certificate into a Lean theorem, respecting your project's
   imports, namespace and prelude. Every file starts with a header carrying a SHA-256 hash of everything
   that determined it: the family, the grid, the expressions, the Lean profile and the templates.
   Timestamps are deliberately left out, so identical inputs produce byte-identical files.
5. **Freeze and compare.** `freeze` stores the emitted files with a manifest; `diff_frozen` regenerates a
   family and reports any drift. A certificate directory can therefore be audited by regenerating it,
   without reading thousands of lines of generated Lean.

## A small example

```python
import sympy as sp
from telperion.family import InequalityFamily, GridSpec
from telperion.certify import certify
from telperion.emit import DirectPolyaEmitter
from telperion.lean import LeanProfile
from telperion.workflow import emit, ValidationReport

x = sp.Symbol("x", nonnegative=True)
fam = InequalityFamily(
    name="demo",
    symbols=(x,),
    grid=GridSpec([("k", range(1, 4))]),
    lean_name=lambda pt: f"demo_nonneg_{pt['k']}",
    # the claim: 0 <= (x^2 + k x + 1) / (x + k) for all x >= 0, for k = 1, 2, 3
    target=lambda pt: (x**2 + pt["k"] * x + 1) / (x + pt["k"]),
)
result = emit(certify(fam), LeanProfile(namespace=("Demo",)), [DirectPolyaEmitter()],
              ValidationReport.from_asserts([("claim is well-posed", lambda: None)]))
print(list(result.files.values())[0])
```

This prints a Lean file with three theorems, one per value of `k`, such as

```lean
theorem demo_nonneg_2 (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ (1 + 2 * x + x ^ 2) / ((2 + x)) := by
  have hd1 : (2 + x : ℝ) ≠ 0 := by positivity
  ...
  positivity
```

and Lean with Mathlib accepts it. Change the target to the false claim `x - 1` and `certify` stops before
any Lean is written:

```
CertificationError: 1 instance(s) failed certification:
  {'k': 1}: numerator not all-nonneg-integer: [((0,), -1)]
```

(Both behaviours were checked for this README against Lean 4 v4.32.0 and Mathlib v4.32.0.)

## What it can certify

The engine has about 160 *emitters*, one per certificate shape. Each pairs an exact-arithmetic certificate
check with a Lean proof template. The main groups are:

- **Positivity of rational functions:** Pólya certificates, bilinear boxes reduced to their corners,
  Bernstein and Handelman forms, orthant and domain transformations.
- **Sums of squares and algebraic certificates:** rational SOS and Gram matrices, constrained SOS,
  Positivstellensatz-style multipliers, Nullstellensatz and real-Nullstellensatz refutations, Farkas and
  cone certificates, infeasibility.
- **Identities and telescopes:** rational-function identities on a ray, forward telescopes, recurrences.
- **Finite facts:** guarded universally quantified statements over explicit tables, proved by kernel
  evaluation (`decide +kernel`), with tables encoded as natural-number bitmasks and fixed-point integers
  so that the kernel can evaluate them efficiently.
- **Enclosures of transcendental quantities:** rigorous rational brackets for `exp` and `log` at rational
  points, threshold and Laurent-type bounds, and ball-arithmetic (Arb) enclosures for analytic
  quantities.
- **Complex analysis:** argument-principle and zero-counting certificates, zero-free regions, and bounds
  used in analytic number theory.

`ls src/telperion/emit_*.py` lists them all; each module's docstring states its claim shape, its
certificate, and what it refuses.

## Making the kernel do the work

Big certificates meet a practical obstacle: the Lean kernel is fast at some things and very slow at
others. The emitters follow a set of rules learned the hard way:

- **Arithmetic over ℚ is slow in the kernel**, because normalizing a rational number goes through a
  well-founded gcd, so large checks use ℕ and ℤ (and fixed point) and small ones use ℚ.
- **Well-founded recursion does not reduce well in the kernel**, so recursive checks use structural
  recursion with an explicit fuel argument.
- **The kernel does not share the evaluation of repeated subterms**, so emitted code passes literals and
  forces evaluation of shared values rather than re-computing them.
- **The kernel keeps every intermediate term of a declaration in memory**, so large checks are split into
  many small theorems, and many files, which a unifying file assembles.
- `native_decide` is never used, so Lean's compiler is never trusted.

## Guarding against proofs that prove nothing

A green build means Lean accepted every proof. It does not mean the theorems say anything. Telperion adds
checks for the ways a build can be green but empty:

- an **honesty lint** refuses `sorry`, `admit`, smuggled `axiom` declarations and decorative stubs such
  as `theorem foo : True := trivial`;
- a **non-vacuity gate** refuses emitted theorems that are reflexive tautologies (`X = X`, `0 ≤ 0`);
- **negative controls** demonstrate the trust model directly. They bypass the Python self-check, forge
  a certificate of a *false* instance, emit it with the same emitter, and confirm that the Lean kernel
  rejects it. They also check the positive half: a genuine certificate of a true instance is accepted;
- an **auditor** runs the same checks on Lean written by anyone else (a person, or an automated prover);
- a **bridge to [Comparator](https://github.com/leanprover/comparator)**, the Lean FRO's independent
  judge, produces challenge files. Comparator then confirms that a proof proves exactly a separately
  written statement, uses only allowed axioms, and passes a replay in Lean's kernel and in
  [nanoda](https://github.com/ammkrn/nanoda_lib), an independent kernel implementation.

## Other tools

- **`telperion` command line:** `certify`, `diagnose`, `verify` (elaborate against a pre-built Lean
  environment and report axioms), `audit`, `lint-lean`, `package`, `recheck`, `margins` and others; run
  `telperion --help`.
- **Diagnosis and coverage:** when certification fails, `diagnose` separates "false", "true but not in
  this form" and "set up wrongly"; `coverage` clusters refusals across a corpus to show which certificate
  shape is missing.
- **Maintenance:** a proof-repair pass for Mathlib renames (driven by Mathlib's own deprecation records),
  a content-addressed index of emitted statements that finds the same lemma proved twice, and a merger
  that combines emitted files while refusing name clashes between different statements.
- **Performance:** a content-addressed certification cache and parallel certification. The cache is a
  speed layer only; a stale entry would produce a file that fails to compile or to match its frozen copy.
- **A missions registry:** a graph of mathematical claims with statuses (draft, open, proved, refuted),
  in which only a verification gate may mark a claim proved, and the independent judge above can check
  proved claims against their registered statements.
- **An MCP server** (`telperion-mcp`, with the `mcp` extra) exposes the certify, validate and emit
  workflow as tools for AI agents. There is deliberately no tool that emits without certifying and
  validating first.
- **Experimental:** an evolutionary search for certificates, and bridges that mine candidate problems from
  public sources or submit to external proof platforms. These make network requests only when invoked,
  and everything they produce still goes through the same certify, emit and kernel gate.

## Installation

Python 3.11 or later. From this directory:

```bash
pip install -e .                 # the core engine: needs only sympy
pip install -e ".[dev]"          # with the test dependencies
pip install -e ".[flint]"        # ball-arithmetic enclosures (python-flint)
pip install -e ".[sdp]"          # semidefinite-programming search for SOS certificates (cvxpy)
pip install -e ".[mcp]"          # the MCP server
```

Emitted Lean needs a Lean 4 project with Mathlib. Telperion is tested against the Lean and Mathlib
versions pinned by the project it is used in; here, Lean 4 v4.32.0 and Mathlib v4.32.0.

## About this copy

This directory is a vendored snapshot (version 0.1.6) of the engine's source, taken from the separate
repository where Telperion is developed. It includes the source only, not that repository's test suite,
documentation or worked examples.

The subpackage `telperion.bg` is a research lab of probes specific to the Brualdi–Goldwasser problem. It is
not part of the engine: the engine never imports it, and the development repository enforces that
boundary with a test.

In this repository, the Brualdi–Goldwasser certificate generators are standalone scripts (in
`../certificates/`). They use Telperion's provenance layer (`EmitResult`, `freeze`, `diff_frozen`) to
record every certificate family and to check that it regenerates byte for byte.

## License

Business Source License 1.1: free for research, teaching and peer review; see [LICENSE](LICENSE).
Contributions require the contributor license agreement in [CLA.md](CLA.md). The mathematics and Lean
code elsewhere in this repository are Apache-2.0; see [../LICENSING.md](../LICENSING.md).
