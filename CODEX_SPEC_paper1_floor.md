# CODEX SPEC — Paper 1 Prop 1.2(1) floor campaign (χ ≤ 0 lower envelope)

## Goal
Prove the FLOOR mirror of the existing moving-ceiling architecture, driving to:
`wholeLineCauchyGlobal_uniformLiminfGe_one_of_chi_nonpos` — for the canonical global
solution with initial datum bounded below by `c ∈ (0,1]` (uniformly positive), the
uniform lower envelope `UniformLiminfGe u 1` holds when `p.χ ≤ 0`.
Then combine with the existing `wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos`
via `uniformConvergesToConstant_of_limsupLe_liminfGe` to produce the χ≤0 branch of
Proposition 1.2 for the canonical solution. NO sorry/admit/native_decide/custom axiom.

## The design (already machine-checked — do NOT re-derive, do NOT change)
Interface file: `ShenWork/Paper1/UniformTwoSidedConvergence.lean` (READ IT FIRST). It has:
- `UniformLiminfGe`, `uniformConvergesToConstant_of_limsupLe_liminfGe`
- `Psi_ge_const_general_of_nonneg_le`, `frozenElliptic_ge_of_rpow_ge` (resolver LOWER bounds)
- `wholeLineCauchyExpFloor c lam t = 1 + (c-1)·exp(-(lam·t))` with `_zero`, `_hasDerivAt`,
  `_deriv_eq_sub` (deriv = lam·(1−B)), `_le_one`, `_ge`, `_pos`, `_restart` (rate fixed,
  level restarted), `_tendsto_one`, `_eventually_ge`
- `expFloor_reaction_dominates : 1 ≤ α → 0 < lam → lam ≤ c → c ≤ B → B ≤ 1 →
   lam·(1−B) ≤ B·(1−B^α)` — THE key arithmetic. The rate `lam` is DECOUPLED from the
  level `c` (naive rate-1 mirror is FALSE at α=1). Standing hypotheses everywhere:
  `0 < lam`, `lam ≤ c`, `c ≤ 1`, and `1 ≤ p.α`.

Mathematical mechanism at a spatial almost-MINIMUM x₀ of u(t,·):
- drift term `u_x · V_x` ≈ 0 (approximate-min, same absorption as the ceiling's approx-max);
- nonlocal zeroth-order: `−χ·u^m·(V − u^γ)` with `χ ≤ 0` and `V ≥ (almost-inf u)^γ`
  (by `frozenElliptic_ge_of_rpow_ge` from the inductive pinch `u ≥ floor`) is ≥ 0, favorable;
- reaction `u(1−u^α) ≥ B(1−B^α) ≥ lam(1−B) = B'(t)` by `expFloor_reaction_dominates`.
So `w := wholeLineCauchyExpFloor C lam − u` satisfies the mirrored differential inequality
at its almost-maximum, and the SAME whole-line approximate-extremum machinery that proved
`wholeLineSlab_le_expCeiling_of_nonpositive_resolver_pde` applies (either mirror the proof,
or where possible apply the existing max-side helper lemmas to `w`).

## Template to mirror (line-by-line study, then mirror)
`ShenWork/Paper1/WholeLineCauchyLongTimeBound.lean`:
1. `wholeLineSlab_le_expCeiling_of_nonpositive_resolver_pde` (L75–388) →
   `wholeLineSlab_ge_expFloor_of_nonpositive_resolver_pde`. Hypotheses: same regularity/
   PDE/bounded package PLUS `hlam : 0 < lam`, `hlamC : lam ≤ C`, `hC1 : C ≤ 1`,
   `hα : 1 ≤ p.α`, `hinit : ∀ x, C ≤ u 0 x`. Conclusion:
   `∀ t ∈ Icc 0 T, ∀ x, wholeLineCauchyExpFloor C lam t ≤ u t x`.
   NOTE: you will likely also need `hnonneg` (kept) and the upper bound `hupper` (kept —
   integrability of the resolver kernel needs it).
2. `wholeLineCauchyBUCMildFixedPoint_exp_ceiling_Ico` (L392) and `_Icc` (L527) → floor
   versions on the canonical fixed-point construction.
3. `wholeLineCauchyStepExpCeiling` (L582–603) → `wholeLineCauchyStepExpFloor` (recursion
   with FIXED rate lam, level restarted via `wholeLineCauchyExpFloor_restart`).
4. `wholeLineCauchyGlobalDatum_segment_le_expCeiling` (L606) → `_segment_ge_expFloor`.
5. `wholeLineCauchyGlobal_le_expCeiling_of_chi_nonpos` (L679) → `_ge_expFloor_of_chi_nonpos`:
   for datum with `∀ x, c ≤ u₀ x` (and existing datum-side bounds), pick `lam := c`
   (satisfies lam ≤ c) — floor propagates globally.
6. `wholeLineCauchyGlobal_uniformLimsupLe_one_of_chi_nonpos` (L715) →
   `wholeLineCauchyGlobal_uniformLiminfGe_one_of_chi_nonpos` via
   `wholeLineCauchyExpFloor_eventually_ge`.
7. Final: combine 6 with the existing limsup theorem through
   `uniformConvergesToConstant_of_limsupLe_liminfGe` into
   `wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_nonpos`.

The fixed-point/gluing layers live in `ShenWork/Paper1/WholeLineCauchyGlobalGluing.lean`,
`WholeLineCauchySharpBound.lean` and their imports — grep for every helper the ceiling
proof uses and locate/build its mirror. Reuse existing approximate-extremum lemmas applied
to `−u` or `B − u` where signs permit instead of re-proving them.

## Constraints
- New file(s) only: `ShenWork/Paper1/WholeLineCauchyLongTimeFloor.lean` (split into
  `...FloorSlab.lean` + `...FloorGlobal.lean` if one file gets heavy). Do NOT edit any
  existing file. Do NOT edit `Statements.lean`.
- NO git commands (orchestrator commits). ≤100 cols. Reuse existing lemmas by exact name.
- This Mac cannot lake build. Verify remotely, EXACTLY:
  1. `rsync -a ~/repos/Shen_work/ShenWork/ uisai2:/dev/shm/lean/Shen_work-p1floor/ShenWork/`
  2. `ssh uisai2 'cd /dev/shm/lean/Shen_work-p1floor && env LAKE_NO_UPDATE=1 PATH=$HOME/.elan/bin:$PATH lake env lean ShenWork/Paper1/<File>.lean'`
  Never `lake update`, never full-tree build, never touch uisai2:~/repos/Shen_work.
- #print axioms every headline (expect [propext, Classical.choice, Quot.sound]); add the
  directive temporarily, run, then remove it.

## Report
Which of steps 1–7 closed; every new theorem's full name + #print axioms; if a step walls,
the exact goal state, file:line, and the specific missing fact. Do not fake, do not weaken.
