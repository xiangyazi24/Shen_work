# Codex Brief — Prop 1.2(2) SUPERCRITICAL branch (α > m+γ−1)

Repo ~/Shen_work (HEAD f23fd2df). Rules: 0 sorry, 0 axiom, NEW files only,
`lake build ShenWork.Paper1.<Module>` green per file, append imports to
ShenWork.lean at the END (required — a module outside the root closure is not
verified). Do NOT commit. Do NOT edit other existing files.

## Goal

The committed `Proposition_1_2_positive_branch_critical`
(Proposition12PositiveBranchCritical.lean) covers only `α = m+γ−1`. The paper's
Proposition 1.2(2) (p.7) assumes `α ≥ m+γ−1`. Close the supercritical half.

## Why the crude ceiling fails (do not retry it)

The committed supercritical chain bounds `u` by
`wholeLineCauchyParameterCeiling = max 1 ((1+χ)^{1/(α−q)})`, `q := m+γ−1`.
That height is useless for a rectangle: at `m = 1` the floor margin is
`1 − χ M^γ`, which is NEGATIVE there whenever `α−q` is small (e.g. χ=0.4,
α−q=0.1, γ=1 gives M≈28.9). Verified numerically.

## The right height (scalar layer already committed)

`ShenWork/Paper1/WholeLineChiPosEquilibriumCeiling.lean` provides:
- `chiPosEquilibriumEq p M = M^α − χ M^q − 1`;
- `chiPosEquilibriumEq_one : chiPosEquilibriumEq p 1 = −χ` (≤ 0);
- `chiPosEquilibriumEq_pos_of_large` (≥ 0 once `1+χ ≤ M^{α−q}`);
- `chiPosCeilingGap_at_equilibrium` : at a root `M`, the ceiling margin is the
  EXACT product `χ · M^{m−1} · ℓ^γ` (hence > 0 for every ℓ > 0);
- `chiPos_equilibrium_rpow_alpha_lt_two` : `M^α < 2` when `χ < 1/2` — for `m = 1`
  this reads exactly `χ M^γ < 1`, which is what makes the floor margin positive
  for small ℓ.
Numerics: 256 parameter combinations (m,γ ∈ {1,1.5,2,3}, α−q ∈ {0.05,0.3,1,3},
χ ∈ {0.05,0.2,0.4,0.499}), both margins strictly positive at the root, 0 failures.

## Deliverables

E1. `WholeLineChiPosEquilibriumRoot.lean` — existence and basic properties:
    continuity of `chiPosEquilibriumEq p` on `[1, ∞)`, then IVT between `1` and
    the crude parameter ceiling to get
    `∃ M, 1 ≤ M ∧ chiPosEquilibriumEq p M = 0` (supercritical, `0 ≤ χ`).
    Define `chiPosEquilibriumCeiling p` by choice and export
    `_one_le`, `_eq_zero`, and `_le_parameterCeiling`.

E2. `WholeLineChiPosEquilibriumDescent.lean` — the ceiling-only descent.
    Mirror the committed supercritical ceiling chain
    (`WholeLineChiPosSupercriticalLongTimeBound.lean`) but based at
    `chiPosEquilibriumCeiling p` instead of the parameter ceiling. The
    supersolution obligation is now
      `χ·B^{m+γ} + reactionFun α B + λ(B − M*) ≤ 0` for `B ≥ M*`,
    which at `B = M*` is an EQUALITY by the root property; for `B > M*` use that
    `B ↦ B^α − χB^q` is strictly increasing on `[M*, ∞)` (α > q, B ≥ 1). Choose
    any positive rate `λ` for which the inequality holds — deriving an explicit
    admissible `λ` from the increasing gap is the only real work here. Only the
    resolver LOWER bound `V ≥ 0` is used, so no floor is needed.
    Land `wholeLineCauchyGlobal_uniformLimsupLe_equilibriumCeiling_of_chi_pos_supercritical`.

E3. `WholeLineChiPosSupercriticalRectangle.lean` — seed + rounds for the
    supercritical whole-line squeeze: reuse `chiPos_squeeze_gap_step_of_le`
    (committed, hypothesis `m+γ−1 ≤ α`) and the existing rectangle structure
    (`ChiPosWholeLineRectangle`). The seed's ceiling is `M* + r` from E2, its
    floor from the committed uniform-positivity burn-in; both margins from the
    scalar lemmas above (ceiling margin: continuity in the height around the
    exact product; floor margin: small ℓ, using `M^α < 2` when `m = 1`).

E4. `Proposition12PositiveBranchSupercritical.lean` — the capstone, mirroring
    `Proposition_1_2_positive_branch_critical` with `hcritical` replaced by
    `hsuper : p.m + p.γ - 1 < p.α`, and a combined theorem covering
    `p.m + p.γ - 1 ≤ p.α` (the paper's full hypothesis) by case split.

Report per-item build status and any place where the design above is wrong.
