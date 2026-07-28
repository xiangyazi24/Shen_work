# Liang shifting-habitat project

This directory contains Liang Kong's CMBE 2026 proposal and the accompanying
formalization audit.

- `CMBE_2026.pdf`: source proposal.
- `FORMALIZATION_AUDIT.md`: corrected model, corrected theorem statements,
  proof status, and the bridge to ShenWork.
- `CORRECTED_THEOREMS.tex` / `CORRECTED_THEOREMS.pdf`: mathematical proof
  note with a clean mathematical main body, clearly labelled global
  conjectures, and an appendix auditing each defect in the original proposal.

The Lean development lives in:

- `ShenWork/Liang/ModelAudit.lean`
- `ShenWork/Liang/CorrectedModel.lean`
- `ShenWork/Liang/MovingCorridor.lean`
- `ShenWork/Liang/LinearDeterminacy.lean`
- `ShenWork/Liang/IDEComparison.lean`
- `ShenWork/Liang/StateSpace.lean`

The common raw convolution engine is
`ShenWork/Analysis/DispersalKernel.lean`.
