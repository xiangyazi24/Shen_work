# Tasks for Codex (GPT-5.5)

BUILD OK, 11 sorry remaining. Priority order:

## P0: coercive_exponential_barrier_estimate (ParabolicMaxPrinciple:681+686)
Two sorry in the barrier proof:
1. `hR_large : B < ε * (1 + R ^ 2)` — arithmetic with Real.sqrt
2. Main argument: compact domain max + interior derivative test + contradiction

All building blocks are proved. You need to:
- Show `by_contra` + on `[0,T]×[-R,R]` ψ achieves max (use `exists_max_on_Icc_prod`)
- Max can't be at t=0 (`spatialCoercivePerturbation_initial_neg`)
- Max can't be at x=±R (`spatialCoercivePerturbation_neg_on_large_spatial_boundary`)
- Interior max: `dt = 0` (IsLocalMax.hasDerivAt_eq_zero), `dxx ≤ 0` (second deriv test)
- Apply `spatialCoercivePerturbation_no_positive_max_with_derivative_signs`

Closing this unlocks ComparisonPrinciple:130 automatically.

## P1: MildSolution integrability (173, 175)
Need `AEStronglyMeasurable` for time-parametric integral `s ↦ ∫ y, heatKernel(t-s)(x-y) * F(s,y)`.
Approach: add continuity hypotheses, use `MeasureTheory.continuousOn_of_dominated` → `ContinuousOn.aestronglyMeasurable`.

## P2: MildSolution Banach fixed point (328)
Need to construct fixed point of Φ on function space. Use `BoundedContinuousFunction` or `ContractingWith.fixedPoint`.

## P3: heteroclinic_from_shooting (TravelingWaveODE:336)
Global ODE existence + convergence to E0.

## P4: Deep theorems
- Defs:456 — TW uniqueness (sliding method)
- Paper3/Defs:24,30 — persistence + global stability

## Key API discoveries
- `continuous_rpow_const.comp_aestronglyMeasurable` for rpow measurability
- `fderiv_pi` + `dsimp` for componentwise fderiv
- `(try ring) <;> linear_combination` for mixed ring/hypothesis goals
- `MeasureTheory.continuousOn_of_dominated` for parametric integral continuity
