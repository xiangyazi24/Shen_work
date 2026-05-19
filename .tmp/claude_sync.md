# Claude-Codex Sync: Current Target Split

## Current State

BUILD OK, 0 sorry (but `Lemma_4_1_neg_holds` has an uncommitted sorry at the boundary case).

## Uncommitted Work (Claude)

`Lemma_4_1_neg_holds` at line ~4170: combines constant + exponential regions into
full `IsPaperFrozenSuperSolution` for `upperBarrier`. Has 1 sorry at the boundary
case `exp(-κx) = M`.

**Fix for boundary**: When `exp(-κx) = M`, `upperBarrier κ M x = M = exp(-κx)`.
Both the constant region formula AND the exponential region formula give the same
value at the boundary. The paperWaveOperator at this point can be evaluated using
either formula. The constant region proof `paperWaveOperator_upperBarrier_const_region_nonpos_neg`
requires strict `M < exp(-κx)`, but we can instead directly compute
`paperWaveOperator_const_eq` at x where `upperBarrier κ M x = M` (which is true
when `exp(-κx) ≥ M`, i.e., when `M ≤ exp(-κx)`). So use `le_of_eq heq` to get
`M ≤ exp(-κx)` and apply the constant region.

## Target Split

### Claude: Fix boundary case + commit Lemma_4_1_neg_holds

Fix the boundary sorry by using the non-strict constant region:
when `exp(-κx) = M`, we have `M ≤ exp(-κx)` so the constant region
formula applies. The key: `paperWaveOperator_const_nonpos_neg`
(the standalone theorem) works with `InWaveTrapSet κ M u` and any x.

### Codex: Prove the positive sensitivity constant region for Lemma 4.1

Add `Lemma_4_1_pos_holds` — the `0 ≤ χ < χ*` branch. The constant region
is already proved (`paperWaveOperator_upperBarrier_const_region_nonpos_pos`).
The exponential region for positive χ needs the paper's Case 2 estimate.
Start with the constant-only version.

### Neither should touch: Defs.lean, LeibnizRule.lean

## Files

- Claude: `ShenWork/Paper1/Statements.lean` near line 4170 only
- Codex: `ShenWork/Paper1/Statements.lean` after `Lemma_4_1_neg_holds`
