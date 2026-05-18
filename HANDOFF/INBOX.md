# Tasks for Codex (GPT-5.5)

BUILD OK, 8 sorry remaining. Priority order:

## P0: coercive_exponential_barrier_estimate (ParabolicMaxPrinciple:995)
One sorry remains in the barrier proof:
1. Main argument: compact domain max + interior derivative test + contradiction

Done:
- Fixed the definition-level obstruction in the maximum-principle API:
  `IsClassicalSubSolution`, `IsClassicalSuperSolution`, and
  `IsClassicalLinearSubSolution` now include closed-rectangle `ContinuousOn`
  fields, and their derivative/PDE hypotheses use `Ioc 0 T` instead of `Ioo 0 T`.
  This rules out the old initial/terminal jump counterexamples and makes a
  compact-rectangle maximum proof mathematically honest.
- `hR_large : B < ε * (1 + R ^ 2)` closed by arithmetic with `Real.sqrt`.
- Added `exists_positive_interior_max_on_Icc_prod`: with `ContinuousOn`, a positive point
  and negative parabolic boundary produce a positive max at `t > 0`, `x ∈ (-R,R)`.
- Added `spatialCoercivePerturbation_exists_positive_interior_max_on_rect`, the coercive
  perturbation specialization of the previous lemma.
- Added `time_deriv_nonneg_at_Icc_max`: at a positive-time max on `[0,T]`,
  the time derivative is nonnegative.
- Added `space_deriv_eq_zero_at_Icc_interior_max`: at an interior spatial max,
  the first spatial derivative is zero.
- Added rectangle-max projection wrappers `time_deriv_nonneg_at_Icc_prod_max` and
  `space_deriv_eq_zero_at_Icc_prod_interior_max`.
- Added `second_space_deriv_nonpos_at_Icc_interior_max` plus the rectangle wrapper:
  at an interior spatial maximum, the second spatial derivative is nonpositive.
- Added `spatialCoercivePerturbation_no_positive_interior_rect_max`: a positive
  interior rectangle maximum contradicts the strict PDE inequality.
- Replaced the two Paper3 false positive theorem bodies with proved negation/counterexample
  theorems under the current toy solution definitions.
- Removed the unused false positive theorem `pde_bounded_by_rectangle_ode`; the file already proves
  the corresponding universal statement false under the current toy PDE definitions.

All building blocks are proved. You need to:
- Prove `ContinuousOn` for ψ on `[0,T]×[-R,R]` from the strengthened
  `hw.continuousOn_rect R` plus continuity of the exponential factor and polynomial
  coercive term.
- Use the `Ioc 0 T` fields at the positive rectangle maximum; the top edge is now
  included in the PDE-valid time interval, so the old terminal-time obstruction is gone.
- PDE references to consult for the exact statement: Protter-Weinberger,
  *Maximum Principles in Differential Equations*, chapter "Parabolic Equations";
  Evans, *Partial Differential Equations*, parabolic maximum principle section.

## P1: MildSolution integrability (173, 175)
Need `AEStronglyMeasurable` for time-parametric integral `s ↦ ∫ y, heatKernel(t-s)(x-y) * F(s,y)`.
Approach: add continuity hypotheses, use `MeasureTheory.continuousOn_of_dominated` → `ContinuousOn.aestronglyMeasurable`.

## P2: MildSolution Banach fixed point (328)
Need to construct fixed point of Φ on function space. Use `BoundedContinuousFunction` or `ContractingWith.fixedPoint`.

## P3: heteroclinic_from_shooting (TravelingWaveODE:336)
Global ODE existence + convergence to E0.

## P4: Deep theorems
- Defs:456 — TW uniqueness (sliding method)

## Key API discoveries
- `continuous_rpow_const.comp_aestronglyMeasurable` for rpow measurability
- `fderiv_pi` + `dsimp` for componentwise fderiv
- `(try ring) <;> linear_combination` for mixed ring/hypothesis goals
- `MeasureTheory.continuousOn_of_dominated` for parametric integral continuity
