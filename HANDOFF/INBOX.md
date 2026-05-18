# Tasks for Codex (GPT-5.5)

BUILD OK, 1 sorry remaining. Priority order:

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
- Removed the false explicit logistic-profile traveling-wave construction:
  `TravelingWaveConstruction.lean` now states only true profile/barrier facts, and
  `TravelingWaves.lean` / `StabilityUniqueness.lean` no longer claim those profiles
  prove `IsTravelingWave`.
- Closed the two `MildSolution.lean` integrability `sorry`s by making the missing
  time-integrability hypotheses explicit in the Duhamel difference/Lipschitz estimate.
  The theorem now proves the algebraic integral identity from genuine
  `MeasureTheory.Integrable` assumptions instead of pretending spatial measurability
  implies time integrability.
- Added `abstract_mild_fixed_point`, a proved Banach fixed-point wrapper that converts
  a complete metric self-map, a contraction proof, and an eval/Φ commutation lemma
  into a raw mild fixed point.
- Added traveling-wave translation infrastructure in `Defs.lean`:
  `IsTravelingWave.shift`, `IsMonotoneTravelingWave.shift`, and
  `exp_bound_shift_right`. These are true phase-shift facts needed before any honest
  uniqueness proof can fix the wave phase using asymptotics/stability.
- Added `cStarStar_ge_two`, `two_lt_of_cStarStar_lt`, and
  `kappa_pos_of_cStarStar_lt`, extracting the speed facts needed from the
  stability/uniqueness threshold.
- Added `IsTravelingWave.shift_right_with_exp_bound` and
  `IsMonotoneTravelingWave.shift_right_with_exp_bound`, combining phase-shift
  invariance with preservation of the right exponential tail bound when shifting
  right.
- Removed the undernormalized `cm_tw_uniqueness` theorem and downstream
  `uniqueness_traveling_wave` wrapper. The old hypotheses used only a strict
  exponential upper bound, but right shifts preserve both the traveling-wave
  equations and that bound, so this statement should not be kept as a theorem
  without the paper's actual phase/asymptotic normalization and stability proof.
- Removed `heteroclinic_from_shooting_hypotheses` and `shooting_theorem` from
  `TravelingWaveODE.lean`. The file keeps the proved local shooting-segment
  lemmas and the honest `travelingWave_of_heteroclinic` projection, but no
  longer claims that a one-dimensional positive root gives a global heteroclinic.

## P0: MildSolution Banach fixed point (376)
Need to instantiate `abstract_mild_fixed_point` by constructing the actual complete
function space, self-map, self-map/integrability facts, and contraction proof for Φ.

## Key API discoveries
- `continuous_rpow_const.comp_aestronglyMeasurable` for rpow measurability
- `fderiv_pi` + `dsimp` for componentwise fderiv
- `(try ring) <;> linear_combination` for mixed ring/hypothesis goals
- `MeasureTheory.continuousOn_of_dominated` for parametric integral continuity
