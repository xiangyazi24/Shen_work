# Proof Integrity Gaps — 11-Point Audit (2026-05-19)

## Passing Points: 1, 2, 4, 9

- **Point 1 (0 sorry)**: PASS
- **Point 2 (0 custom axiom)**: PASS
- **Point 4 (0 trivially true)**: PASS — the previous
  `Preliminary.lean` placeholder theorems with `True` conclusion have been
  removed from Lean sources.
- **Point 9 (build passes)**: PASS

## Failing Points: 3, 5, 6, 7, 8

### Point 3: 假设结构体逃避

**Problem**: The main paper theorems are "proved" by projecting from assumption
structures that bundle the conclusions as fields.

| Structure | File | Fields that ARE the theorems being "proved" |
|-----------|------|---------------------------------------------|
| `Paper3Constants` | Paper3/Statements.lean | Multiple fields for stability/threshold comparisons |
| `StabilityNorms` | Paper3/Statements.lean | Norm continuity, compactness fields |
| `CompactnessData` | Paper3/Statements.lean | Time-translate compactness fields |
| `SemigroupEstimateData` | Paper2/Statements.lean | Semigroup L^p estimates |
| `BoundedDomainData` | Paper2/Statements.lean | Abstract domain/boundary/integral |
| `SpectralData` | Paper3/Statements.lean | Abstract Neumann spectrum |

`Paper1AnalyticData`, `Paper2AnalyticData`, and their package-field
`_conditional` projections have been removed from Lean sources.  Paper1 and
Paper2 still have many open statement targets, but those targets are no longer
inhabited by a single analytic-data projection package.

**Fix**: For each field, either:
(a) Prove it from lower-level lemmas and remove the field, or
(b) Keep it as an explicit axiom and mark the theorem as "conditional"

### Point 5: Prop 假设逃避

**Problem**: The former theorem-shaped package projections have been removed
from Lean sources, but theorem-scale assumptions still exist as fields of
`SemigroupEstimateData`, `StabilityNorms`, `CompactnessData`, and
`Paper3Constants`.  Those fields make the analytic work explicit but do not
prove it.  The remaining risk is to accidentally count a package field or an
accessor from an assumed theorem as a source proof.

**Fix**: Prove each theorem from raw mathematical objects (CMParams, functions,
etc.) without assumption structure parameters, or honestly label as conditional.

### Point 6: End-to-end 定理不存在

**Problem**: No full Paper1 main theorem (Theorem 1.1-1.3, Propositions
1.1-1.2) has been proved end-to-end from only raw math objects.  The former
`Paper1AnalyticData` projection route has been removed, so the remaining full
targets are open unless one of the listed raw branches/bridges applies.
Paper2's all-in-one analytic projection route has also been removed; the
remaining Paper2 full targets are open or represented by real branches and
formal obstruction theorems. Paper3 package fields still externalize the main
stability, compactness, persistence, and comparison arguments, but their
projection theorem wrappers have been removed.

**Genuinely end-to-end theorems** (no assumption packages):
- `Psi_elliptic_ode`: v'' - λv + μf = 0
- `frozenElliptic_ode`: V'' - V + u^γ = 0
- `frozenElliptic_continuous`, `frozenElliptic_differentiable`
- `frozenElliptic_tendsto_atTop/atBot_of_U_tendsto`
- `chemotaxis_resolvent_bound`: paper eq (4.4)
- `paperWaveOperator_const_nonpos_neg/pos`: Lemma 4.1 constant region
- `paperWaveOperator_exp_nonpos_of_chi_nonpos`: Lemma 4.1 exp region (χ≤0)
- `Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa`: frozen
  Lemma 4.1 away from the interface for χ≥0, from paper speed hypotheses
- `Lemma_4_1_neg_frozen_holds_away_from_interface_of_plateau_source_bound`:
  frozen Lemma 4.1 away from the interface for χ≤0, conditional on the
  explicit plateau comparison `frozenElliptic p u x ≤ (u x)^γ`
- `Lemma_4_1_strengthened_away_from_interface_proved`: the two frozen
  Lemma 4.1 away-from-interface branches assembled into one explicit,
  assumption-package-free strengthened statement
- `NegativeSensitivityWaveFixedPointConstruction.upperBarrier_superSolution_away_from_interface`
  and
  `PositiveSensitivityWaveFixedPointConstruction.upperBarrier_superSolution_away_from_interface`:
  non-projection fixed-point-construction bridge theorems replacing the former
  false `Lemma_4_1` package route; the negative branch keeps the necessary
  plateau comparison as an explicit hypothesis
- `NegativeSensitivityWaveFixedPointConstruction.exists_paper_constant_subsolution`:
  the negative-sensitivity fixed-point construction now produces an explicit
  constant paper-operator subsolution directly from the corrected
  `constant_subsolution_paperWaveOperator_nonneg_of_chi_nonpos` branch and the
  internally chosen `d`, without using the refuted original Lemma 4.2
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_paper_constant_subsolution`
  and
  `PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_paper_const_sub_chi_zero`:
  fixed-point construction bridges returning the fixed profile together with a
  verified constant paper-operator subsolution; the positive branch is the
  χ=0 slice where `MChi p = 1`
- `not_differentiableAt_upperBarrier_of_interface`: formal interface
  obstruction showing that `upperBarrier κ M` is not differentiable at
  `exp(-κ*x) = M` when `κ,M > 0`; the original everywhere-classical
  `IsFrozenSuperSolution` formulation therefore needs an interface treatment
  or a corrected weak/away-from-interface statement
- `not_Lemma_4_1`: a concrete negative-sensitivity counterexample to the
  current Lemma 4.1 statement.  The profile lies in `InWaveTrapSet (1/2) 1`,
  vanishes at a plateau point, but its elliptic resolvent is strictly positive
  there, contradicting the plateau comparison forced by the original frozen
  supersolution claim.
- `not_Lemma_4_2`: a concrete positive-sensitivity counterexample to the
  current Lemma 4.2 statement.  With `χ = 2/V0` for the same resolvent-positive
  trap-set profile, the constant frozen subsolution branch gives
  `frozenWaveOperator = -d*(1+d) < 0` at the point where `u = 0`, contradicting
  the claimed subsolution inequality.
- `not_Remark_4_2`: the same positive-sensitivity constant-branch obstruction
  lifted to the finite-time trap-set statement using the time-independent path
  `u(t,x) = lemma41CounterexampleProfile x`.
- `not_Remark_4_2_M_one`: the same finite-time positive-sensitivity
  obstruction specialized to the `M = 1` slice of Remark 4.2, so that slice is
  also a refuted original target rather than an unproved theorem.
- `Lemma_4_2_chi_zero_strengthened_proved`: χ=0 Lemma 4.2 raw-plus-constant
  subsolution construction with the needed `κtilde ≤ 2κ` hypothesis made
  explicit
- `Lemma_4_2_chi_zero_D_ge_one_strengthened_proved`: χ=0 Lemma 4.2
  raw-plus-constant subsolution construction with the needed large-`D`
  hypothesis `1 ≤ D` made explicit
- `Lemma_4_2_chi_zero_alpha_one_strengthened_proved`: χ=0, α=1 Lemma 4.2
  slice, where the paper range condition implies `κtilde ≤ 2κ`
- `Remark_4_2_M_one_chi_zero_strengthened_proved`: finite-time `M = 1`,
  χ=0 slice of Remark 4.2 under the explicit `κtilde ≤ 2κ` hypothesis
- `Remark_4_2_chi_zero_strengthened_proved`: general-`M`, finite-time χ=0
  slice of Remark 4.2, with the large-`D` condition absorbed into the
  existential threshold `D0`
- `constant_subsolution_frozenWaveOperator_nonneg_of_small_d_time_trap`:
  finite-time constant subsolution branch for general `M`, under the explicit
  frozen smallness condition
  `|χ| d^(m-1) M^γ ≤ 1 - d^α`
- `constant_subsolution_frozen_smallness_of_half_bound`,
  `constant_subsolution_frozenWaveOperator_nonneg_of_half_bound_trap`, and
  `constant_subsolution_frozenWaveOperator_nonneg_of_half_bound_time_trap`:
  ordinary and finite-time constant subsolution branches under the checkable
  sufficient conditions `|χ| M^γ ≤ 1/2` and `d ≤ 1/2`
- `Remark_4_2_M_one_chi_zero_D_ge_one_strengthened_proved`: finite-time
  `M = 1`, χ=0 slice of Remark 4.2 under the explicit `1 ≤ D` hypothesis
- `Remark_4_2_M_one_chi_zero_alpha_one_strengthened_proved`: finite-time
  `M = 1`, χ=0, α=1 slice of Remark 4.2
- `not_forall_InTimeWaveTrapSet_slice_inWaveTrapSet_general_M`: formal
  obstruction showing that finite-time trap-set slices with general `M` do not
  automatically lie in the ordinary `InWaveTrapSet κ M`; the upper barriers
  differ by the factor `M` in the exponential branch
- `Lemma_2_1_zero_output_branch` and `Lemma_2_1_zero_data`: real
  zero-output/all-zero-data branches of the Paper1 heat-semigroup estimate
  interface, closed under explicit nonnegativity of the input norm rather than
  by projecting from `Paper1AnalyticData`
- `heatKernel_integral_abs_eq_one`,
  `heatKernel_integral_abs_translated`, `heatKernel_hasDerivAt`,
  `deriv_heatKernel`, `integral_abs_mul_exp_neg_mul_sq`,
  `heatKernel_deriv_abs_integral`,
  `modifiedHeatKernel_deriv_abs_integrable`,
  `modifiedHeatKernel_deriv_abs_integral`,
  `heatKernel_deriv_abs_integral_translated`,
  `modifiedHeatKernel_deriv_abs_integral_translated`,
  `heatKernel_deriv_translated_integrable`,
  `modifiedHeatKernel_deriv_translated_integrable`,
  `heatKernel_deriv_mul_bounded_integrable`,
  `modifiedHeatKernel_deriv_abs_translated_integrable`,
  `modifiedHeatKernel_deriv_mul_bounded_integrable`,
  `heatKernel_deriv_mul_bounded_integral_abs_le`,
  `heatKernel_deriv_convolution_bounded_abs_le`,
  `heatKernel_deriv_convolution_diff_bounded_abs_le`,
  `modifiedHeatKernel_deriv_mul_bounded_integral_abs_le`,
  `modifiedHeatKernel_deriv_convolution_bounded_abs_le`,
  `modifiedHeatKernel_deriv_convolution_diff_bounded_abs_le`,
  `heatKernel_translated_hasDerivAt_left`,
  `heatKernel_translated_hasDerivAt_right`, `heatSemigroup_mono_bounded`,
  `modifiedSemigroup_mono_bounded`,
  `heatSemigroup_zero_fun`, `modifiedSemigroup_zero_fun`,
  `modifiedSemigroup_const`,
  `heatSemigroup_lower_bound`, `heatSemigroup_upper_bound_of_bound`,
  `heatSemigroup_interval_bound`, `modifiedSemigroup_lower_bound`,
  `modifiedSemigroup_upper_bound`, `modifiedSemigroup_interval_bound`,
  `heatSemigroup_abs_le_semigroup_abs`,
  `modifiedSemigroup_abs_le_semigroup_abs`,
  `heatSemigroup_abs_le_of_abs_le`,
  `modifiedSemigroup_abs_le_of_abs_le`,
  `heatSemigroup_abs_le_of_abs_le_bounded`,
  `modifiedSemigroup_abs_le_of_abs_le_bounded`,
  `modifiedSemigroup_Linfty_bound`, `modifiedSemigroup_Linfty_decay`,
  `heatSemigroup_add`, `modifiedSemigroup_add`, `heatSemigroup_neg`,
  `modifiedSemigroup_neg`, `heatSemigroup_const_mul`,
  `modifiedSemigroup_const_mul`, `heatSemigroup_add_bounded`,
  `modifiedSemigroup_add_bounded`, `modifiedSemigroup_sub`,
  `heatSemigroup_sub_bounded`, `modifiedSemigroup_sub_bounded`, and
  `heatSemigroup_contraction`, `modifiedSemigroup_contraction`: real
  whole-line heat-kernel estimates for the heat and modified semigroups.  They
  use heat-kernel positivity, translated kernel mass one, the explicit
  first-derivative formula, derivative-kernel integrability, bounded
  measurable input data, and Bochner integral linearity to prove monotonicity,
  pointwise lower-, upper-, and interval-bound preservation,
  modified-semigroup lower/upper/interval bounds, domination by a nonnegative
  majorant, heat/modified-semigroup linearity, `L∞` decay, and heat/modified
  pairwise `L∞` contraction.
- `Lemma_2_2_proved`, `Lemma_2_3_proved`, `Lemma_2_4_proved`
- `Lemma_2_5_pointwise_bound`, `Lemma_2_5_attained_at_inv`,
  `Lemma_2_5_sharp_bound`, `Lemma_2_5_sharp_constant_minimal`,
  `Lemma_2_5_sharp_constant_positive`, `Lemma_2_5_sharp_constant_iff`,
  `Lemma_2_5_full_statement`, `Lemma_2_5_full_range_statement`,
  `Lemma_2_5_pointwise_pos`, `Lemma_2_5_pointwise_bound_lt_exp_neg_one`,
  `Lemma_2_5_pointwise_mem_Ioo_zero_exp_neg_one`,
  `Lemma_2_5_pointwise_bound_le_larger_Psi_beta`, and
  `Lemma_2_5_pointwise_bound_lt_larger_Psi_beta` (Paper2): direct
  end-to-end bridges from the proved scalar Lemma 2.5 inequality to the
  concrete `Psi_beta` equality case, pointwise positivity/range,
  sharp-constant positivity/minimality, endpoint limits, and monotonicity
  results.
- `SupNormNonincreasingOn.of_forall_eq` (Paper2): an unconditional
  constant-time branch of the Lemma 3.1 conclusion, separate from the false
  arbitrary-API maximum-principle statement.
- `Lemma_2_5_zero_function_branch`, `Lemma_2_5.zero_function_witness`, plus
  the unit and L² unit-resolvent witness specializations: real zero-function
  branches of the weighted resolvent-gradient estimate, closing the
  integrability and integral inequality directly by `Psi_zero`.
- `Lemma_2_5_constant_function_branch` and
  `Lemma_2_5.constant_function_witness`, plus the unit and L² unit-resolvent
  witness specializations: real nonnegative constant-source branches of the
  weighted resolvent-gradient estimate.  They use `Psi_const_general` to
  identify `Psi (c^γ; l, μ)` as a constant, so the derivative term vanishes and
  the weighted inequality follows from positivity of the exponential weight.
- `Lemma_2_5_constant_source_branch` and
  `Lemma_2_5.constant_source_witness`, plus the unit and L² unit-resolvent
  witness specializations: real constant-source branches of the same estimate
  for any nonnegative profile satisfying `u^γ = a` pointwise.  They use
  `Psi_const_general` after rewriting the source, not an assumption package.
- `Remark_4_3.same_wave_branch` and
  `Remark_4_3.exists_same_wave_branch`: real same-wave branches of the
  Remark 4.3 weighted initial closeness conclusion, proved by reducing the
  weighted distance to the zero integrand rather than projecting from the
  former `Paper1AnalyticData.sharpTailCloseness` field
- `WeightedL2InitialCloseness.of_integrand_exp_bounds`,
  `WeightedL2InitialCloseness.of_left_exp_bound_eventual_right_exp_bound`,
  `weightedL2_integrand_norm_le_of_abs_sub_le`, and
  `weightedL2_integrand_norm_le_of_abs_sub_le_exp`: real integrability and
  weighted-integrand bridges for the distinct-wave Remark 4.3 route, including
  the case where the right-tail domination is only eventual
- `Remark43TailRateBound.exists_larger`,
  `HasRemark43TailAsymptotic.eventually_norm_normalized_error_le_one`,
  `HasRemark43TailAsymptotic.eventually_abs_sub_exp_le`,
  `HasRemark43TailAsymptotic.eventually_abs_sub_abs_le_two_exp`,
  `HasWaveUpperTailBound.abs_sub_le_two_MChi`,
  `Remark_4_3.distinct_wave_branch_of_aestronglyMeasurable`, and
  `Remark_4_3.distinct_wave_branch_of_continuous`: real tail-window,
  left/right domination, and strengthened distinct-wave weighted closeness
  bridges for Remark 4.3
- `Remark_4_3_regular_proved`: full corrected regular Remark 4.3 theorem,
  proved end-to-end from the explicit bridges above rather than from
  `Paper1AnalyticData`; the original `Remark_4_3` statement still lacks the
  measurability/continuity hypothesis needed for the `Integrable` conclusion
- `Lemma_5_1_signal_bound_for_frozenElliptic`: the uniform `V`/`V'`
  bound from Lemma 5.1 for the fixed-point case `V = frozenElliptic p U`,
  derived directly from the wave upper-tail bound and the `Psi` kernel
  estimates
- `Lemma_5_1_signal_bound_for_frozenElliptic_of_continuous`: the same
  fixed-point signal bound with `IsCUnifBdd U` derived from continuity plus the
  upper-tail bound
- `Lemma_5_1_exponential_signal_bound_for_frozenElliptic`: the exponential
  `V`/`V'` bound from Lemma 5.1 for the same fixed-point case, using the
  kernel exponential tail estimate and
  `gamma_mul_kappa_lt_one_of_gamma_add_inv_lt_speed`
- `Lemma_5_1_exponential_signal_bound_for_frozenElliptic_of_continuous`: the
  corresponding exponential signal bound with `IsCUnifBdd U` internalized from
  continuity plus the upper-tail bound
- `Lemma_5_1.fixed_point_signal_package`: the uniform and exponential
  fixed-point signal estimates packaged together in the same conjunctive shape
  as the first two conclusions of Lemma 5.1
- `Lemma_5_1.fixed_point_signal_package_of_continuous`: the same signal package
  with the boundedness/uniform-continuity input derived from continuity plus
  the upper-tail bound
- `Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds`: the full
  fixed-point Lemma 5.1 conclusion with the signal estimates proved from the
  `Psi` kernel and only the remaining `U'` estimates left as explicit
  derivative hypotheses
- `Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds_of_continuous`:
  the same fixed-point full-conclusion branch with `IsCUnifBdd U` internalized
  from continuity plus the upper-tail bound
- `Lemma_5_1_resolvent_identified_proved`: the same full Lemma 5.1 conclusion
  in the arbitrary-traveling-wave shape, once the missing identity
  `V = frozenElliptic p U`, continuity of `U`, and the remaining `U'`
  estimates are supplied explicitly; boundedness of `U` follows from
  `HasWaveUpperTailBound.isBddFun`
- `FrozenStationaryWaveProfile.fixed_point_signal_package_of_inWaveTrapSet` and
  `FrozenStationaryWaveProfile.fixed_point_conclusion_of_wave_derivative_bounds`:
  the same fixed-point Lemma 5.1 signal estimates and explicit-`U'` conclusion
  specialized to a frozen stationary profile in the wave trap, avoiding the
  arbitrary-`IsTravelingWave` projection route
- `Lemma_5_2_explicit.nonincreasing_branch`,
  `Lemma_5_2_explicit.monotoneTravelingWave_branch`,
  `Lemma_5_2.nonincreasing_branch`,
  `Lemma_5_2.monotoneTravelingWave_branch`,
  `Lemma_5_2_explicit_frozen_monotone_trap_proved`, and
  `Lemma_5_2_frozen_monotone_trap_proved`: real monotone-wave and frozen
  monotone-trap branches of Lemma 5.2.  The upper-tail bound gives
  `0 ≤ MChi p`, the explicit log-derivative constant is nonnegative under the
  Lemma 5.2 speed hypothesis, and `U' ≤ 0`, `U > 0` give `U'/U ≤ 0`.  In the
  frozen trap branch, `FrozenStationaryWaveProfile` supplies the traveling
  wave and `InMonotoneWaveTrapSet` supplies both the upper-tail bound and
  `U' ≤ 0`.
- `not_Remark52GammaSpeedAlgebra`,
  `not_remark5SpeedCondition_implies_Lemma_5_2_speed`, and
  `not_Remark52LogDerivativeAlgebra`: formal obstructions showing that the
  current Remark 5.2 speed condition is not strong enough to route the proof
  through explicit Lemma 5.2
- `remark51MPrime_nonneg_of_MChi_pos`,
  `remark52MTriplePrime_nonneg_of_MChi_pos`,
  `Remark_5_2.nonincreasing_branch`,
  `Remark_5_2.monotoneTravelingWave_branch`, and
  `Remark_5_2_frozen_monotone_trap_proved`: real monotone-wave and frozen
  monotone-trap branches of Remark 5.2.  The proof does not use the invalid
  speed-algebra route; it proves the displayed `M'''` denominator-normalized
  constant is nonnegative and then uses `U' ≤ 0` and `U > 0` to get
  `U'/U ≤ 0`.
- `Lemma_5_3_zero_difference_branch`, `Lemma_5_3_zero_source_branch`,
  `Lemma_5_3.self_difference_branch`, `Lemma_5_3.same_power_branch`, and the
  `Lemma_5_3.same_power_branch_*` CM/tail/stability specializations: the
  weighted elliptic perturbation estimate in zero-source cases, proved directly
  from `Psi_zero` and positivity of the right-hand side.  The zero-difference
  case uses `u1 = u2`; the stronger zero-source branch assumes only
  `u2^gamma = u1^gamma` pointwise; the same-power branch family exposes these
  results in the full Lemma 5.3 hypothesis shapes used later in Section 5.  The
  continuous tail/stable-tail/strict-tail/stability variants also discharge the
  previously exposed `IsCUnifBdd` inputs from the corresponding upper-tail
  bounds plus continuity.
- `Lemma_2_5_proved` (Paper2), together with the sharp `Psi_beta` package and
  normalized sharp `Theta_beta` form
- `remark16ChiStarWeak_scalar_properties` (Paper2): direct scalar algebra for
  the weak Remark 1.6 threshold `(1.30c)`, including positivity, the
  min-half/sqrt smallness implication used by the linear Theorem 1.2 branch,
  and comparison with `2β - 1`.
- `remark16StrongThreshold_sign_properties` (Paper2): direct sign algebra for
  the strong Remark 1.6 thresholds `(1.30a)` and `(1.30b)`, with strict
  positivity hypotheses for the first threshold and for the second threshold
  when the exposed constant `K` is positive.
- `Lemma_2_1_zero_output_branch`, `Lemma_2_2_zero_embedding_branch`,
  `Lemma_2_3_zero_divergence_branch`, and
  `Lemma_2_4_zero_fractional_divergence_branch` (Paper2): real
  zero-output/zero-embedding branches for the abstract semigroup estimates,
  closed under explicit nonnegativity hypotheses instead of projecting from
  `SemigroupEstimateData` fields.  The concrete
  `zeroSemigroupEstimateData` instance and `Lemma_2_1_zero_data`--
  `Lemma_2_4_zero_data` close all four targets for the all-zero interface
  without using package-field projections.
- `Lemma_A_2_zero_output_branch`, `Lemma_A_3_zero_embedding_branch`,
  `Lemma_A_4_zero_divergence_branch`, and
  `Lemma_A_5_zero_fractional_divergence_branch` (Paper3): the same real
  zero-output/zero-embedding branches exposed at the Appendix A.2--A.5 alias
  surface, reusing the proved Paper2 branch theorems rather than package
  projections.  `Lemma_A_2_zero_data`--`Lemma_A_5_zero_data` expose the same
  all-zero semigroup instance at the Appendix surface.
- `Theorem_2_2_linear_stability_chi_nonpos_branch_proved` (Paper3): the
  nonpositive-sensitivity linear-stability branch of Paper3 Theorem 2.2,
  derived directly from the Neumann spectral positivity lemmas for the
  positive and minimal equilibria.  This intentionally does not claim the
  local exponential stability part of Theorem 2.2.
- `Theorem_2_2_linear_threshold_branch_proved` (Paper3): the stable/unstable
  linear spectral-threshold branch of Paper3 Theorem 2.2, proved directly from
  the explicit nonzero-mode infimum `paperCriticalSensitivity` and the Neumann
  spectrum lemmas rather than from `Paper3Constants.linearStabilityInstability`.
  The analytic local exponential stability conclusions remain package-supplied.
- `Paper3ConstantsUsesCriticalSpectrum.positiveEquilibrium_linearlyStable`,
  `Paper3ConstantsUsesCriticalSpectrum.positiveEquilibrium_linearlyUnstable`,
  `Paper3ConstantsUsesCriticalSpectrum.minimalEquilibrium_linearlyStable`,
  `Paper3ConstantsUsesCriticalSpectrum.minimalEquilibrium_linearlyUnstable`,
  and `Theorem_2_2_linear_critical_spectrum_branch_proved` (Paper3): once
  the constants package's `chiCritical` field is identified with the concrete
  `paperCriticalSensitivity` infimum, the positive/minimal equilibrium linear
  stable and unstable branches follow directly from spectral lemmas, without
  assuming `Theorem_2_2` or `Paper3Constants.linearStabilityInstability`.
  This still leaves the analytic local exponential stability conclusions open.
- `Lemma_A_7.nonminimal_condition_linearlyStable_of_critical_spectrum`,
  `Lemma_A_7.chiStrong1_linearlyStable_of_critical_spectrum`--
  `Lemma_A_7.chiStrong4_linearlyStable_of_critical_spectrum`,
  `Lemma_A_8.minimal_condition_linearlyStable_of_critical_spectrum`, and
  `Lemma_A_8.chiMinimal1_linearlyStable_of_critical_spectrum`--
  `Lemma_A_8.chiMinimal2_linearlyStable_of_critical_spectrum` (Paper3): the
  A.7/A.8 threshold comparison hypotheses now give the linear-stability
  conclusions directly from `HasNeumannSpectrum`,
  `Paper3ConstantsUsesCriticalSpectrum`, and the explicit
  `paperCriticalSensitivity` spectral branch, without assuming
  `Theorem_2_2`.  This intentionally does not claim the local exponential
  stability part.
- `Theorem_2_4_linear_stability_branch_proved` and
  `Theorem_2_5_linear_stability_branch_proved` (Paper3): the linear-stability
  portions of the strong-logistic and minimal global-stability theorems now
  follow directly from the A.7/A.8 threshold comparisons plus the
  critical-spectrum bridge.  The global stability and exponential convergence
  conclusions remain explicit analytic package fields.
- `Theorem_2_2_xpSigma_local_exponential_branch_proved` (Paper3): the
  `X^σ_p` small-perturbation exponential-decay branch of Theorem 2.2 is proved
  from the concrete spectral critical-sensitivity bridge and Lemma A.1, rather
  than by assuming `Theorem_2_2` or
  `Paper3Constants.linearStabilityInstability`.  This branch intentionally
  assumes an existing global solution and `xpSigmaDistance` smallness; the
  sup-norm local well-posedness/continuity upgrade remains open.
- Paper3 recalled Proposition 1.1--1.4 bridge lemmas:
  `Proposition_1_1.paper2`,
  `Proposition_1_2_of_negativeSensitivityGlobalEventualBound`,
  `Proposition_1_3.of_paper2_theorem_1_3`, and
  `Proposition_1_4.of_paper2_theorem_1_2` keep the useful conditional
  routes from Paper2 targets or the smaller eventual-bound hypothesis.  The
  former theorem-shaped `_proved` wrapper Props for these bridges have been
  removed, so they are not counted as source proofs.
- `not_forall_Proposition_1_3` and `not_forall_Proposition_1_4` (Paper3):
  formal obstructions showing that the recalled Part-I global-existence
  propositions cannot be proved over arbitrary `BoundedDomainData`; the same
  no-regularity abstract domain used for Paper2 local existence supplies a
  positive initial datum but makes every required global classical solution
  impossible.
- `not_forall_Proposition_1_1` (Paper2): formal obstruction showing that
  Paper2 local existence cannot be proved for arbitrary `BoundedDomainData`;
  an abstract domain with `classicalRegularity := False` admits no classical
  solution even though initial data are admissible
- `not_forall_Proposition_2_1` (Paper2): formal obstruction showing that the
  Paper2 elliptic signal `L^p` estimate cannot be derived from the current
  abstract semigroup/norm API alone; a fake `lpNorm` can make the constant
  PDE solution `u = 1`, `v = 1/2` violate the estimate
- `not_forall_Corollary_2_1` (Paper2): formal obstruction showing that the
  cross-diffusion bootstrap cannot be derived from the current abstract
  integral/cross-diffusion-energy API alone; a fake two-point integral makes
  the `p₀ = 2` bound trivial while the `p = 3` integral blows up before `T = 1`
- `not_forall_Lemma_2_6` (Paper2): formal obstruction showing that the
  abstract `Lᵖ` bootstrap conclusion cannot be derived from the current
  fakeable bootstrap-energy interface alone; the energy inequality holds for
  all `p ≥ p₀ = 4`, but the conclusion asks for an unbounded `p = 3` norm
- `not_forall_Proposition_2_2` (Paper2): formal obstruction showing that the
  Paper2 weighted gradient estimate cannot be derived from the current
  abstract bounded-domain API alone; fake `integral`/`gradNorm` fields can make
  the same constant PDE solution violate the estimate
- `not_forall_Proposition_2_3` (Paper2): formal obstruction showing that the
  Paper2 weighted signal estimate cannot be derived from the current abstract
  bounded-domain API alone; fake `integral` fields can make the same constant
  PDE solution violate the estimate
- `not_forall_Proposition_2_4` (Paper2): formal obstruction showing that the
  Paper2 mass comparison cannot be derived from the current abstract API alone;
  fake `supNorm`/`integral` fields allow a mismatched initial trace and violate
  mass conservation
- `not_forall_Proposition_2_5` (Paper2): formal obstruction showing that the
  Paper2 boundedness criterion cannot be derived from the current abstract API
  alone; fake operators make an unbounded finite-time profile satisfy the PDE
  and all abstract `Lᵖ` bounds
- `not_forall_Lemma_2_7` (Paper2): formal obstruction showing that the
  damping differential inequality cannot be derived over an arbitrary fake
  integral; a fake integral can make the differential inequality hold while
  the target `Lᵖ` integral blows up before `T = 1`
- `not_Lemma_3_1_minimal_counter` and `not_forall_Lemma_3_1` (Paper2):
  formal obstructions showing that the negative-sensitivity upper-envelope
  monotonicity cannot be derived from the current abstract API alone; a fake
  time derivative makes an increasing profile satisfy the PDE while `supNorm`
  records the increase
- `not_Lemma_3_1_nonminimal_counter` (Paper2): concrete counterexample to the
  current abstract-domain Lemma 3.1 statement in the positive-logistic branch
- `not_forall_Lemma_3_1_nonminimal_branch` (Paper2): formal obstruction for
  the first `a,b > 0` branch itself.  The fake `timeDeriv` field is chosen to
  equal the logistic reaction of an increasing profile, so the abstract PDE is
  satisfied while the `SupNormNonincreasingOn` conclusion fails
- `not_forall_Lemma_4_1` (Paper2): formal obstruction showing that the
  mass-gradient interpolation estimate cannot be derived from the current
  abstract API alone; fake `integral` fields make the left `Lᵖ` term positive
  while the gradient and mass terms vanish
- `not_forall_Theorem_1_1`, `not_forall_Theorem_1_2`, and
  `not_forall_Theorem_1_3` (Paper2): formal obstructions showing that the three
  Paper2 main global-existence theorem targets cannot be derived for arbitrary
  `BoundedDomainData`; the same fake domain with `classicalRegularity := False`
  refutes the required solution-existence conclusions
- `not_paper2_theorem_1_1_implies_paper3_proposition_1_2` (Paper3):
  formal obstruction showing that Paper2 Theorem 1.1's finite-`Tmax`
  boundedness plus global-existence branch does not imply recalled Paper3
  Proposition 1.2's eventual-in-time boundedness under the current abstract
  bounded-domain API
- `not_forall_Theorem_2_1_part1`, `not_forall_Theorem_2_1_part2`,
  `not_forall_Theorem_2_1_part3`, and
  `not_exists_Paper3Constants_theorem21_part1_counterdomain`--
  `not_exists_Paper3Constants_theorem21_part4_counterdomain` (Paper3):
  formal obstructions showing that the uniform-persistence lower-bound
  conclusions cannot be derived from the current abstract `BoundedDomainData`
  API alone; positive constant solutions can satisfy the abstract PDE while a
  fake `infValue` functional is identically zero.  Lean also proves the sharper
  package-level fact that no corresponding `Paper3Constants` package can exist
  on the relevant fake lower-envelope APIs for any of parts (1)--(4).
- `not_exists_StabilityNorms_no_supNorm_convergence` (Paper3): a field-level
  obstruction for `StabilityNorms`.  The fake bounded-domain API admits the
  positive constant solution `u = v = 1`, but its `supNorm` is identically
  `1`; the `negativeSensitivityGlobalStability` field would force that
  constant `1` signal to converge to `0`, so no `StabilityNorms` package exists
  on this arbitrary `BoundedDomainData`.
- `not_InitialContinuityRaw_constant_xpSigmaDistance` (Paper3): a raw
  obstruction for the shape of `StabilityNorms.initialContinuity`.  On a fake
  one-point domain with `supNorm ≡ 0`, every initial perturbation and trace is
  arbitrarily small, while an exposed `xpSigmaDistance ≡ 1` cannot be forced
  below `ε = 1/2`.  Thus initial continuity needs a real link between the
  chosen `X^σ_p` metric and the sup-norm/PDE API.
- `not_SectorialLocalExponentialRaw_constant_c1Distance` (Paper3): a raw
  obstruction for the shape of `StabilityNorms.sectorialLocalExponential`.
  With `xpSigmaDistance ≡ 0` and `c1Distance ≡ 1`, the smallness hypothesis is
  automatic for the positive constant solution, but the conclusion would force
  the constant left-hand side `2` to be bounded by `C exp(-rate t)` for all
  `t ≥ 0`, impossible because the right-hand side tends to `0`.
- `not_ConvergenceToExponentialNonminimalRaw_constant_c1Distance` (Paper3): a
  raw obstruction for the nonminimal exponential-upgrade branch of
  `Paper3Constants.convergenceToExponential`.  Fake `supNorm ≡ 0` gives
  uniform convergence for the constant solution, but an unrelated
  `c1Distance ≡ 1` prevents any exponential `C¹` convergence estimate.
- `not_NonminimalGlobalStabilityRaw_constant_c1Distance` (Paper3): a raw
  obstruction for the nonminimal global-stability field.  The third
  strong-logistic alternative can be satisfied by concrete parameters, but an
  unrelated constant `c1Distance ≡ 1` still makes the claimed exponential
  convergence estimate impossible.
- `not_MinimalGlobalStabilityRaw_constant_c1Distance` (Paper3): a raw
  obstruction for the minimal global-stability field.  The mass-constrained
  minimal model can satisfy the first threshold branch with concrete
  parameters, but an unrelated constant `c1Distance ≡ 1` still makes the
  claimed exponential convergence estimate impossible.
- `not_LinearStabilityInstabilityNonminimalRaw_constant_c1Distance` (Paper3):
  a raw obstruction for the nonminimal local-stability part of
  `Paper3Constants.linearStabilityInstability`.  Fake sup-norm closeness makes
  the initial datum admissibly small, but an unrelated constant
  `c1Distance ≡ 1` prevents every asserted exponential convergence estimate.
- `not_UpperEnvelopeMonotonicityRaw_eval_increasing_solution` (Paper3): a raw
  obstruction for `CompactnessData.upperEnvelopeMonotonicity`.  With fake
  `timeDeriv` and `supNorm`, the abstract PDE admits the increasing profile
  `u(t)=t+1` as a positive global bounded solution, while the point-value upper
  envelope violates the asserted monotonicity.
- `not_TimeTranslateCompactnessRaw_false_locallyConverges` (Paper3): a raw
  obstruction for `CompactnessData.timeTranslateCompactness`.  If the exposed
  local-convergence predicate is identically false, no subsequential
  compactness conclusion can be derived, even for a positive constant solution.
- `not_NeumannResolventGradientBoundExistsRaw_false_bound` (Paper3): a raw
  obstruction for `CompactnessData.neumannResolventGradientBound_exists`.
  If the exposed resolvent-gradient predicate is identically false, no uniform
  bound witness can exist.
- `not_EventualMinimalUpperBoundRaw_zero_bound` (Paper3): a raw obstruction
  for `Paper3Constants.eventualMinimalUpperBound`.  If the exposed eventual
  upper-bound function is unrelated to the fake `supNorm`, the positive
  constant solution can violate the asserted eventual upper bound.
- `not_LemmaA7ThresholdComparisonsRaw_arbitrary_thresholds` (Paper3): a raw
  obstruction for Lemma A.7-style threshold comparison fields.  If the exposed
  strong thresholds are constantly `1` and the exposed critical threshold is
  constantly `0`, admissible concrete parameters force the impossible
  inequality `1 ≤ 0`.
- `not_LemmaA8ThresholdComparisonsRaw_arbitrary_thresholds` (Paper3): a raw
  obstruction for Lemma A.8-style minimal threshold comparison fields.  If the
  exposed minimal thresholds are constantly `1` and the exposed critical
  threshold is constantly `0`, admissible minimal-model parameters force the
  impossible inequality `1 ≤ 0`.
- `Proposition_1_1_constant_one_branch`,
  `Proposition_1_1_constant_one_negative_long_time_branch`,
  `Proposition_1_1_constant_one_positive_long_time_branch`, and
  `Proposition_1_2_constant_one_branch`, plus
  `Proposition_1_2_constant_one_long_time_branch`: real Paper1 Cauchy/stability
  branches for the equilibrium initial datum `u₀ ≡ 1`, using the constant
  global solution `u ≡ v ≡ 1`; the long-time branches expose the boundedness
  and limsup consequences directly.
- `constant_one_nonnegativeInitialDatum`, `constant_one_uniformlyPositive`,
  `Proposition_1_1_constant_one_negative_admissible_branch`,
  `Proposition_1_1_constant_one_positive_admissible_branch`,
  `Proposition_1_2_constant_one_negative_admissible_branch`, and
  `Proposition_1_2_constant_one_positive_admissible_branch`: the same
  equilibrium branches with the original initial-data admissibility hypotheses
  verified explicitly, still only for `u₀ ≡ 1`.
- `Proposition_1_1_constant_one_negative_branch`,
  `Proposition_1_1_constant_one_positive_branch`,
  `Proposition_1_2_constant_one_negative_branch`,
  `Proposition_1_2_constant_one_positive_branch`, and the two corresponding
  Proposition 1.2 long-time sign branches: the same equilibrium branch
  repackaged in the exact negative/positive branch shapes of Propositions 1.1
  and 1.2; the positive Proposition 1.1 branch uses
  `one_le_positive_branch_limsup_bound`.
- `Theorem_1_2_self_initial_data_branch`: exact Paper1 Theorem 1.2
  self-initial-data branch, using the moving traveling wave as the Cauchy
  solution and proving both moving-frame convergence errors are zero
- `Theorem_1_2_self_initial_data_admissible_branch`: the same branch with
  `NonnegativeInitialDatum`, `StrictlyPositiveAtLeft`, and reflexive
  `WeightedL2InitialCloseness` verified for the wave profile initial datum
- `HasStrictWaveUpperTailBound.nonnegativeInitialDatum_of_continuous` and
  `Theorem_1_2_self_initial_data_admissible_branch_of_strict_tail`: the
  self-initial-data stability branch with bounded continuous admissibility
  derived from the strict upper-tail hypothesis instead of supplied as a
  separate `IsCUnifBdd` input
- `FrozenStationaryWaveProfile.to_globalCauchySolutionFrom` and
  `Theorem_1_2_frozen_profile_self_initial_data_branch`: the same
  self-initial-data stability branch specialized to a frozen stationary
  profile, so the fixed-point route no longer has to expose a manual
  `IsTravelingWave` conversion before applying the zero-error moving-frame
  argument
- `Theorem_1_2_frozen_profile_self_initial_data_admissible_branch`: the frozen
  profile version with the same initial-data admissibility and reflexive
  weighted-closeness hypotheses discharged
- `Theorem_1_2_frozen_profile_self_initial_data_admissible_branch_of_strict_tail`:
  the frozen-profile version with `IsCUnifBdd` likewise derived from the strict
  upper-tail hypothesis plus continuity
- `Theorem_1_3_same_wave_branch`: reflexive Paper1 Theorem 1.3 same-wave
  uniqueness branch, independent of the uniqueness package
- `Theorem_1_3_profile_eq_of_uniform_movingFrame_and_resolvent`: a real
  uniqueness bridge showing that uniform moving-frame convergence of the
  second profile to the first profile, plus resolvent identification
  `Vᵢ = frozenElliptic p Uᵢ`, gives the two profile equalities required by
  Theorem 1.3 without projecting from `Paper1AnalyticData.travelingWaveUniqueness`
- `Theorem_1_3_profile_eq_of_stability_cauchy_unique_and_resolvent`: a sharper
  real uniqueness bridge that applies the weighted-stability conclusion to the
  second wave as initial datum, uses an explicit Cauchy-uniqueness/solution
  identification hypothesis to replace the produced Cauchy solution by the
  moving second wave, and then invokes the moving-frame/resolvent bridge above
- `Theorem_1_3_profile_eq_of_remark43_stability_cauchy_unique_and_resolvent`:
  the same uniqueness bridge with the weighted initial closeness supplied by
  the corrected regular Remark 4.3 tail theorem, so the bridge inputs are now
  sharp tail asymptotics, profile continuity, stability, Cauchy uniqueness,
  and resolvent identification
- `Theorem_1_3.uniqueness_bridge_from_stability_remark43_and_resolvent`:
  threshold-level bridge using the real `Theorem_1_2` stability package and
  `Remark_4_3_regular` tail-closeness theorem; the remaining assumptions are
  the admissible Remark 4.3 tail rate, Cauchy uniqueness/solution
  identification for the second wave, and elliptic resolvent identification
- `exists_remark43TailRateBound_with_weight_below` and
  `Theorem_1_3.uniqueness_bridge_from_stability_remark43_and_resolvent_of_kappa_cap`:
  the Remark 4.3 tail rate is now selected internally once
  `kappa c < 1/(1+|χ|^(1/6))` is supplied; the remaining Theorem 1.3 bridge
  assumptions are the kappa/cap gap, Cauchy uniqueness, and elliptic resolvent
  identification
- `kappa_lt_stability_weight_cap_of_stabilitySpeedBaseline_lt` and
  `Theorem_1_3.uniqueness_bridge_from_stability_remark43_and_resolvent_of_speed`:
  the stability speed lower bound itself supplies the kappa/cap gap, so the
  Theorem 1.3 bridge no longer exposes any manual Remark 4.3 rate or weight
  admissibility assumption; the remaining explicit analytic inputs are Cauchy
  uniqueness and elliptic resolvent identification
- `Theorem_1_3.frozen_profile_uniqueness_bridge_from_stability_remark43`:
  specializes the speed-level bridge to `FrozenStationaryWaveProfile`, where
  the elliptic resolvent identities are definitional; the remaining explicit
  analytic input is Cauchy uniqueness/solution identification, plus the stated
  tail/continuity hypotheses
- `Theorem_1_3.frozen_trap_profile_uniqueness_bridge_from_stability_remark43`:
  further specializes to frozen profiles in `InWaveTrapSet`, using the trap-set
  continuity field internally; the remaining explicit analytic input is Cauchy
  uniqueness/solution identification together with the strict upper-tail and
  Remark 4.3 tail-asymptotic hypotheses
- `Lemma_A_6_proved` (Paper3)
- `FrozenStationaryWaveProfile.mk_auto_limits`
- `Theorem_1_1.of_raw_frozen_stationary_branches`: raw fixed-point data
  bridge for Paper1 Theorem 1.1.  Positivity, boundedness, stationarity,
  endpoint limits, monotonicity/tail data, and upper barriers are assembled
  into `FrozenStationaryWaveProfile`s internally, then converted to the paper
  traveling-wave existence conclusion without projecting from
  `Paper1AnalyticData.travelingWaveExistence`.
- `InWaveTrapSet.tendsto_atTop_zero`,
  `InWaveTrapSet.frozenElliptic_tendsto_atTop_zero`,
  `InMonotoneWaveTrapSet.tendsto_atTop_zero`,
  `InMonotoneWaveTrapSet.frozenElliptic_tendsto_atTop_zero`,
  `HasWaveUpperTailBound.tendsto_atTop_zero`,
  `HasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero`,
  `HasStrictWaveUpperTailBound.tendsto_atTop_zero`,
  `HasStrictWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero`,
  `FrozenAuxiliaryLimitOutput.tendsto_atTop_zero_of_inWaveTrapSet`, and the
  corresponding `FrozenWaveMapConstruction.exists_fixed_*_with_atTop_limit`
  and `exists_fixed_*_with_atTop_limits` bridges, plus the specialized
  `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_atTop_limits`
  and
  `PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_atTop_limits`
  bridges: the right-end limits `U → 0` and `frozenElliptic p U → 0` are now
  derived from trap-set bounds plus the resolvent limit theorem instead of
  being carried only as external profile assumptions.
- `paperWaveOperator_eq_frozenWaveOperator_at_fixed_point`

**Fix**: Work toward proving assumption package fields from existing
infrastructure, converting projections into real proofs.

### Point 7: 接口最小化

**Problem**: Paper2/Paper3 packages and the lower-level abstract interfaces
still bundle theorem-scale analytic assumptions.  The former Paper1
all-in-one analytic package has been removed; the remaining Paper1 work is to
prove the open statement targets from the existing raw bridges rather than
reintroduce a package field.

**Fix**: Identify which fields follow from others and internalize the
derivations.

### Point 8: 反例检查

**Problem**: Not systematically done. Known false statements now include
the caught `expDecay_mem_InWaveTrapSet` attempt, original Paper1 `Lemma_4_1`,
original Paper1 `Lemma_4_2`, and original Paper1 `Remark_4_2`.

**Fix**: For each theorem that was difficult to prove, verify the
statement is not false before continuing.

## Priority Fix Order

1. **P0**: Keep Preliminary.lean free of trivially-true placeholders
2. **P1**: Prove Paper1 statement targets that already have infrastructure:
   - Original Lemma_4_1 — the current original statement is now formally
     refuted by `not_Lemma_4_1`, so the former `upperBarrierSuperSolution`
     field and `Lemma_4_1_conditional` projection have been removed together
     with the obsolete `Paper1AnalyticData` package. Frozen
     exponential/away-from-interface branches are
     proved for both signs of χ only under extra speed/dominance hypotheses;
     Lean also proves the current Lemma 4.1 hypotheses do **not** imply the
     needed `mκ ≤ 1` / `γκ < 1` bounds (`not_Lemma_4_1_*_force_*`). The
     corrected away-from-interface strengthened version is proved by
     `Lemma_4_1_strengthened_away_from_interface_proved`; downstream Paper1
     statements now also have non-projection fixed-point-construction bridges
     through
     `NegativeSensitivityWaveFixedPointConstruction.upperBarrier_superSolution_away_from_interface`
     and
     `PositiveSensitivityWaveFixedPointConstruction.upperBarrier_superSolution_away_from_interface`.
     They should use a corrected Lemma 4.1 target, not a package projection of
     the false original statement.
   - Original Lemma_4_2 — the current original statement is now formally
     refuted by `not_Lemma_4_2`, so the former `lowerBarrierSubSolution` field
     and `Lemma_4_2_conditional` projection have been removed. The constant
     subsolution branch is proved only
     under explicit frozen smallness hypotheses, and the χ=0 raw-plus-constant
     corrected slices are proved by `Lemma_4_2_chi_zero_strengthened_proved`,
     `Lemma_4_2_chi_zero_D_ge_one_strengthened_proved`, and
     `Lemma_4_2_chi_zero_alpha_one_strengthened_proved`. Downstream Paper1
     statements should use a corrected Lemma 4.2 target, not a package
     projection of the false original statement.
   - Original Remark_4_2 — the current original finite-time statement is now
     formally refuted by `not_Remark_4_2`, and its `M = 1` slice is refuted by
     `not_Remark_4_2_M_one`, so the former
     `finiteTimeTrapSubSolution` field and `Remark_4_2_conditional` projection
     have been removed. The χ=0 corrected finite-time
     slices remain proved; downstream uses should depend on those corrected
     statements or a new strengthened Remark 4.2.
3. **P2**: Replace the refuted Section 4 targets by corrected statements and
   route downstream uses through the proved strengthened slices
4. **P3**: Prove semigroup estimates (Lemma_2_1) from heat kernel
5. **P4**: Prove weighted gradient estimate (Lemma_2_5)
6. **P5**: Prove Section 5 estimates (Lemma_5_1-5.3) from wave ODE analysis
7. **P6**: Prove Schauder construction → Theorem_1_1
8. **P7**: Prove stability/uniqueness → Theorem_1_2, 1.3
9. **P8**: Instantiate bounded-domain API for Paper2/Paper3

## Structures Assessment (per Playbook §1 Point 3)

### Legitimate abstract interfaces (NOT escape hatches):
- `BoundedDomainData`: abstract smooth bounded domain API (Point, boundary, norms, Laplacian, etc.) — any smooth bounded domain satisfies these. Mathlib doesn't have this.
- `SpectralData` / `HasNeumannSpectrum`: Neumann eigenvalue API — any Neumann Laplacian provides this.
- `HeatSemigroupEstimateData`: abstract semigroup norm API — any analytic semigroup provides this.
- `Paper2Constants`: just a nonneg real constant K.

### Assumption packages that bundle unproved estimates:
- `SemigroupEstimateData`: L^p semigroup estimates as fields (should be proved from heat kernel)
- `StabilityNorms` / `CompactnessData`: norm continuity, compactness (should be proved from Sobolev)
- `Paper3Constants`: threshold formulas + persistence/boundedness estimates as fields

### Assessment:
The abstract interfaces are justified per standard mathematical practice.
The assumption packages represent genuine open formalization challenges requiring bounded-domain PDE infrastructure not yet in Mathlib.

Per Playbook §1 Point 11 (honest reporting):
- Paper1: "unconditionally proved" for Lemma 2.2-2.4, Lemma 4.1/4.2 strengthened, chemotaxis resolvent, Psi ODE
- Paper2/Paper3: "conditional on bounded-domain API instantiation" — the abstract domain interface is legitimate but the semigroup/stability estimate proofs require Mathlib infrastructure that doesn't exist

## Phase 4 Classification (v4 proposal)

### Paper3 `_proved` theorems — actual classification:

| Theorem | Uses abstract structure? | Correct classification |
|---------|--------------------------|------------------------|
| `Lemma_A_6_proved` | No | genuinely proved |
| `Lemma_3_1_proved` | `BoundedDomainData` | from_assumed_bounded_domain |
| `Theorem_2_2_linear_*_proved` | `BoundedDomainData` + `SpectralData` | from_assumed_bounded_domain |
| `Theorem_2_4_linear_stability_branch_proved` | `BoundedDomainData` + `Paper3Constants` | from_assumed_bounded_domain |
| `Theorem_2_5_linear_stability_branch_proved` | `BoundedDomainData` + `Paper3Constants` | from_assumed_bounded_domain |

### Paper2 `_proved` theorems:

| Theorem | Uses abstract structure? | Correct classification |
|---------|--------------------------|------------------------|
| `Lemma_2_5_proved` | No | genuinely proved |

### Paper1 `_proved` theorems:

| Theorem | Uses abstract structure? | Correct classification |
|---------|--------------------------|------------------------|
| `Lemma_2_2_proved` | No | genuinely proved |
| `Lemma_2_3_proved` | No | genuinely proved |
| `Lemma_2_4_proved` | No | genuinely proved |
| All `_strengthened_proved` | No | genuinely proved |
| All `not_*` counterexamples | No | genuinely proved |

### Not renaming existing `_proved` per v4 additive policy
Per v4 proposal "Do not refactor all of Paper2 first", existing
theorem names are kept. Classification is recorded here only.
