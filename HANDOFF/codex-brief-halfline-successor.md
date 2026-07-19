# Codex Brief — χ>0 buffered half-line successor (the last piece of P1 Thm 1.2)

Repo ~/Shen_work. Rules: 0 sorry, 0 axiom, NEW files only, verify each with
`lake build ShenWork.Paper1.<Module>`. Do NOT commit. Do NOT edit existing files
(you may append import lines to ShenWork.lean at the very end).

READ FIRST: HANDOFF/fable-halfline-successor-spec.md — it contains the full
mathematical design (R(δ) choice, moving cut, both weighted contact
inequalities with constants, buffer boundary supply, seed decomposition).
Follow it; if you find a genuine error in it, say so explicitly rather than
silently deviating.

## Committed pieces you must use (do not rebuild)

- `ChiPosHalfLineRectangle`, `ChiPosHalfLineRectangleStep`,
  `uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors`
  (Paper1/WholeLineChiPosHalfLineRectangle.lean) — the abstract layer and target.
- `frozenElliptic_upper_of_left_halfLine_ceiling`
  (Paper1/WholeLineHalfLineResolverUpperNatural.lean) and
  `frozenElliptic_lower_of_left_halfLine_floor`
  (Paper1/WholeLineWeightedRegularityHalfLineResolverLowerNatural.lean).
- `chiZeroKPPFloor` + `chiNegKPPFloorRate` (floor barrier family) and
  `chiPosTargetCeiling` (Paper1/WholeLineChiPosTargetCeilingNatural.lean).
- The generic half-line maximum principle
  `leftHalfLineSlabSup_le_of_scalar_pde`
  (Paper1/WholeLineWeightedRegularityHalfLineMaximumNatural.lean).
- The whole-line weighted comparison as a template for the b^m form:
  Paper1/WholeLineChiPosWeightedResolverComparisonNatural.lean.
- Buffer closeness: `eventually_coMovingPath_close_on_Icc_of_weightedL2_of_spatialModulus`
  and the χ>0 weighted convergence
  `wholeLineCauchyGlobal_coMovingWeightedL2Convergence_chi_pos_natural`.
- Range bound: `wholeLineCauchyGlobal_le_max_of_chi_pos`.

## Deliverables, in order

D1. `WholeLineChiPosHalfLineWeightedComparison.lean`
    The two WEIGHTED buffered comparisons on a left half-line, in the co-moving
    frame (the drift `c·u_z` is carried exactly as in the χ≤0 buffered file):
    - `leftHalfLine_ge_of_weighted_buffered_chiPos_floor`: hypotheses = slab
      bounds `[ℓ, M]` on `z ≤ cut + R`, global `[0, G]`, buffer floor at
      `[cut, cut+R]`, PDE, plus the scalar budget
      `b' ≤ b(1 − b^α) − χ·b^m·(M^γ − b^γ) − χ·b^m·τ·G^γ` (τ = exp(−R)/2);
      conclusion: the floor barrier stays below `u` on `z ≤ cut`.
    - `leftHalfLine_le_of_weighted_buffered_chiPos_ceiling`: the mirror with the
      resolver LOWER bound and the a^m-weighted budget
      `a' ≥ a(1 − a^α) + χ·a^m·(a^γ − L̂^γ) + χ·a^m·τ·L̂^γ`.
    IMPORTANT: keep the barrier-value factor (`b^m` / `a^m`). The committed
    constant-defect wrappers in WholeLineChiPosBufferedComparisonNatural.lean are
    NOT usable as the iterative engine (they are unsatisfiable from small floors
    when m = 1).

D2. `WholeLineChiPosHalfLineTargets.lean`
    Target selection: given the old rectangle with strict margins and δ > 0,
    produce `L̂ ∈ (ℓ, 1)` and `M̂ ∈ (1, M)` with
    `0 < chiPosFloorGap p M L̂ ≤ δ/2` and `0 < chiPosCeilingGap p L̂ M̂ ≤ δ/2`,
    plus the corresponding barrier rates positive. Use the committed
    monotonicity lemmas `chiPosFloorGap_strictAntiOn_Ioi` /
    `chiPosCeilingGap_strictMonoOn_Ioi` (WholeLineChiPosRectangleTargets.lean)
    and an intermediate-value argument.

D3. `WholeLineChiPosHalfLineSuccessor.lean`
    `exists_next_chiPosHalfLineRectangle` producing
    `Nonempty {new // ChiPosHalfLineRectangleStep p δ old new}` from D1+D2 plus
    the buffer machinery, following spec §1–§5 (choose R(δ), then the new cut,
    then the targets, then the barrier settling time for `new.start`).

D4. Report precisely which of the spec's steps needed adaptation and what, if
    anything, is still missing for the seed (spec §6) — do NOT attempt the seed
    producer in this task.

Each file must end with a `#print axioms` section covering its main results.
