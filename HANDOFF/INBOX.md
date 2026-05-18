# Tasks for Codex (GPT-5.5)

BUILD OK, 7 sorry remaining. Priority order:

## Done: Parabolic maximum principle

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
- Closed `coercive_exponential_barrier_estimate` by constructing a compact
  rectangle maximum for the coercive exponential perturbation, proving it cannot
  be positive, and then sending `ε → 0`.
- As a result, `weak_maximum_principle_linear`, `parabolic_maximum_principle`,
  `comparison_principle`, and `comparison_with_spatially_constant_super` are now
  proved without `sorry`.
- Replaced the two Paper3 false positive theorem bodies with proved negation/counterexample
  theorems under the current toy solution definitions.
- Removed the unused false positive theorem `pde_bounded_by_rectangle_ode`; the file already proves
  the corresponding universal statement false under the current toy PDE definitions.

## P0: MildSolution integrability (173, 175)
Need `AEStronglyMeasurable` for time-parametric integral `s ↦ ∫ y, heatKernel(t-s)(x-y) * F(s,y)`.
Approach: add continuity hypotheses, use `MeasureTheory.continuousOn_of_dominated` → `ContinuousOn.aestronglyMeasurable`.

## P1: MildSolution Banach fixed point (328)
Need to construct fixed point of Φ on function space. Use `BoundedContinuousFunction` or `ContractingWith.fixedPoint`.

## P2: heteroclinic_from_shooting (TravelingWaveODE:336)
Global ODE existence + convergence to E0.

## P3: Deep theorems
- Defs:456 — TW uniqueness (sliding method)

## Key API discoveries
- `continuous_rpow_const.comp_aestronglyMeasurable` for rpow measurability
- `fderiv_pi` + `dsimp` for componentwise fderiv
- `(try ring) <;> linear_combination` for mixed ring/hypothesis goals
- `MeasureTheory.continuousOn_of_dominated` for parametric integral continuity
