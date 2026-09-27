# Reviewing and contributing

Thank you for taking a look. This result has not yet been refereed, and review is the most valuable
contribution anyone can make.

## What most needs checking

The Lean kernel checks every deduction, so the questions that remain are about **meaning**:

1. **Does the formal statement say what the paper claims?** Start with
   [`formalization/Statement.lean`](formalization/Statement.lean). On the graph side it uses only
   Mathlib's `SimpleGraph.IsTree`, `lapMatrix`, `Matrix.permanent` and `degree`. The only definitions of
   ours it depends on are `F` (in `formalization/R3Cert/BGSpiderOpt.lean`) and `bgChildren` (in
   `formalization/R3Cert/BGAnswer.lean`, reading the table in `BGSpiderTableData.lean` and the rule `W`
   in `BGSpiderRule.lean`).
2. **Does `F` really compute the Laplacian ratio of the spider it describes?** The paper derives it in
   Section 6; the theorem `brualdi_goldwasser_attained` also confirms, inside Lean, that the value is
   attained by an actual tree.
3. **Is anything in the paper overstated?** Section 11 lists what is not claimed (for example, uniqueness
   of the maximizer is established by computation, not in Lean).

[`formalization/READING_GUIDE.md`](formalization/READING_GUIDE.md) explains how the Lean source is
organized and which leftover names and comments can be ignored.

## How to send feedback

- Open an issue using the **Review comment** template for questions about the mathematics, the
  statement or the definitions, or the **Build or reproduction problem** template if something does not
  build or verify as documented.
- Or write to the author directly (see the paper).

Please be as specific as you can: a file and line, a theorem name, or a page and equation number.

## Pull requests

Corrections to the documentation, the paper and the scripts are welcome. For the Lean code, please keep
the invariant that every headline theorem depends only on `propext`, `Classical.choice` and `Quot.sound`
(`lake env lean AxiomGuard.lean` checks this), and that generated certificate files are only changed by
regenerating them (`certificates/verify.sh` checks this).

The vendored `telperion/` engine is under the Business Source License 1.1 and contributions to it require
a contributor license agreement (`telperion/CLA.md`). Everything else is Apache-2.0 (code) or CC-BY-4.0
(documents); see [LICENSING.md](LICENSING.md).

## How this work was made

The formalization, the certificate generators and much of the exploration were developed with extensive
assistance from an AI system (Claude, by Anthropic), under the author's direction. That is part of why
everything is machine-checked, and why human review of the statement matters.
