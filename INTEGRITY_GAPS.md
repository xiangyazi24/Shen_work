# Proof Integrity Gaps — 11-Point Audit (2026-05-19)

## Passing Points: 1, 2, 3, 4, 9

- **Point 1 (0 sorry)**: PASS
- **Point 2 (0 custom axiom)**: PASS
- **Point 3 (0 assumption-structure theorem projection)**: PASS — the former
  analytic-data structures whose fields were the paper theorem conclusions
  have been removed; remaining abstract structures only carry raw operations,
  predicates, threshold functions, or explicitly named spectrum facts.
- **Point 4 (0 trivially true)**: PASS — the previous
  `Preliminary.lean` placeholder theorems with `True` conclusion have been
  removed from Lean sources.
- **Point 9 (build passes)**: PASS

## Failing Points: 5, 6, 7, 8

### Point 3: 假设结构体逃避

**Current status**: The old theorem-shaped analytic-data structures have been
removed.  The remaining structures are now mostly raw interfaces:

| Structure | File | Current role |
|-----------|------|---------------------------------------------|
| `Paper3Constants` | Paper3/Statements.lean | Threshold functions plus `gaussianLowerConst_pos`; no stability theorem fields |
| `StabilityNorms` | Paper3/Statements.lean | Two distance functionals; no continuity/compactness theorem fields |
| `CompactnessData` | Paper3/Statements.lean | Abstract convergence/upper-envelope/resolvent-gradient relations, not theorem conclusions |
| `SemigroupEstimateData` | Paper2/Statements.lean | Norms and semigroup operations only; no semigroup-estimate theorem fields |
| `BoundedDomainData` | Paper2/Statements.lean | Abstract domain/PDE operators and admissibility/regularity predicates |
| `SpectralData` | Paper3/Statements.lean | Eigenvalue sequence and first nonzero value; spectrum facts live in explicit `HasNeumannSpectrum` hypotheses |

`Paper1AnalyticData`, `Paper2AnalyticData`, and their package-field
`_conditional` projections have been removed from Lean sources.  Paper1 and
Paper2 still have many open statement targets, but those targets are no longer
inhabited by a single analytic-data projection package.

**Residual risk**: Do not count a theorem that merely assumes one of the
abstract relation predicates as end-to-end.  Such theorems must be named
conditional or must expose the relevant hypothesis in the declaration name.

### Point 5: Prop 假设逃避

**Problem**: The former theorem-shaped package projections have been removed
from Lean sources, but theorem-scale assumptions still exist as explicit Prop
inputs such as `Lemma_A_1`, `Lemma_A_7`, `Lemma_A_8`, `Corollary_5_1`, and
sectorial/local-exponential stability hypotheses.  Those assumptions make the
analytic work explicit but do not prove it.  The remaining risk is to
accidentally count an accessor from an assumed theorem as a source proof.

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
- `Lemma_4_1_strengthened_away_from_interface_direct`: the two frozen
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
- `Lemma_4_2_chi_zero_strengthened_direct`: χ=0 Lemma 4.2 raw-plus-constant
  subsolution construction with the needed `κtilde ≤ 2κ` hypothesis made
  explicit
- `Lemma_4_2_chi_zero_D_ge_one_strengthened_direct`: χ=0 Lemma 4.2
  raw-plus-constant subsolution construction with the needed large-`D`
  hypothesis `1 ≤ D` made explicit
- `Lemma_4_2_chi_zero_alpha_one_strengthened_direct`: χ=0, α=1 Lemma 4.2
  slice, where the paper range condition implies `κtilde ≤ 2κ`
- `Remark_4_2_M_one_chi_zero_strengthened_direct`: finite-time `M = 1`,
  χ=0 slice of Remark 4.2 under the explicit `κtilde ≤ 2κ` hypothesis
- `Remark_4_2_chi_zero_strengthened_direct`: general-`M`, finite-time χ=0
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
- `Remark_4_2_M_one_chi_zero_D_ge_one_strengthened_direct`: finite-time
  `M = 1`, χ=0 slice of Remark 4.2 under the explicit `1 ≤ D` hypothesis
- `Remark_4_2_M_one_chi_zero_alpha_one_strengthened_direct`: finite-time
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
- `Lemma_2_2_direct`, `Lemma_2_3_direct`, `Lemma_2_4_direct`
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
- `Remark_4_3_regular_direct`: full corrected regular Remark 4.3 theorem,
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
- `Lemma_5_1.fixed_point_signal_statement`: the uniform and exponential
  fixed-point signal estimates recorded together in the same conjunctive shape
  as the first two conclusions of Lemma 5.1
- `Lemma_5_1.fixed_point_signal_statement_of_continuous`: the same signal statement
  with the boundedness/uniform-continuity input derived from continuity plus
  the upper-tail bound
- `Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds`: the full
  fixed-point Lemma 5.1 conclusion with the signal estimates proved from the
  `Psi` kernel and only the remaining `U'` estimates left as explicit
  derivative hypotheses
- `Lemma_5_1.fixed_point_conclusion_of_wave_derivative_bounds_of_continuous`:
  the same fixed-point full-conclusion branch with `IsCUnifBdd U` internalized
  from continuity plus the upper-tail bound
- `Lemma_5_1_resolvent_identified_direct`: the same full Lemma 5.1 conclusion
  in the arbitrary-traveling-wave shape, once the missing identity
  `V = frozenElliptic p U`, continuity of `U`, and the remaining `U'`
  estimates are supplied explicitly; boundedness of `U` follows from
  `HasWaveUpperTailBound.isBddFun`
- `FrozenStationaryWaveProfile.fixed_point_signal_statement_of_inWaveTrapSet` and
  `FrozenStationaryWaveProfile.fixed_point_conclusion_of_wave_derivative_bounds`:
  the same fixed-point Lemma 5.1 signal estimates and explicit-`U'` conclusion
  specialized to a frozen stationary profile in the wave trap, avoiding the
  arbitrary-`IsTravelingWave` projection route
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_statement`
  and
  `PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_statement`:
  construction-level bridges that take the Schauder fixed point/trap output
  plus the explicit sharp-upper-bound obligation needed for strict positivity,
  then derive Lemma 5.1's signal statement for the constructed fixed point from
  the `Psi` kernel estimates
- `Lemma_5_2_explicit.nonincreasing_profile_branch`,
  `Lemma_5_2_explicit.nonincreasing_branch`,
  `Lemma_5_2_explicit.monotoneTravelingWave_branch`,
  `Lemma_5_2.nonincreasing_profile_branch`,
  `Lemma_5_2.nonincreasing_branch`,
  `Lemma_5_2.monotoneTravelingWave_branch`,
  `Lemma_5_2_explicit_frozen_monotone_trap_direct`, and
  `Lemma_5_2_frozen_monotone_trap_direct`: real nonincreasing-profile,
  monotone-wave, and frozen monotone-trap branches of Lemma 5.2.  The minimal
  profile branch uses only `0 ≤ MChi p`, `U > 0`, and `U' ≤ 0`; the explicit
  log-derivative constant is nonnegative under the Lemma 5.2 speed hypothesis,
  so `U'/U ≤ 0` closes the bound.  The monotone-wave and frozen trap branches
  specialize this minimal profile result.
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_log_derivative_bound`
  and
  `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_log_derivative_B`:
  construction-level negative-sensitivity bridges that combine the constructed
  monotone fixed point, the explicit sharp-upper-bound obligation giving
  strict positivity, and the minimal nonincreasing-profile Lemma 5.2 branch to
  produce the log-derivative estimate without first packaging a full traveling
  wave.
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_log_derivative`
  and
  `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_log_derivative_B`:
  same-fixed-point bridges combining the Lemma 5.1 signal statement and the
  Lemma 5.2 log-derivative estimate for one constructed negative-sensitivity
  fixed point, avoiding later existential splicing between two separately
  chosen fixed points.
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_const_sub_signal_and_log_derivative`,
  `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_const_sub_signal_and_log_derivative_B`,
  and
  `PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_paper_const_sub_chi_zero`:
  same-fixed-point bridges carrying the corrected constant paper-subsolution
  branches together with the Section 5 signal estimates, and in the negative
  branch also the Lemma 5.2 log-derivative estimate.
- `not_Remark52GammaSpeedAlgebra`,
  `not_remark5SpeedCondition_implies_Lemma_5_2_speed`, and
  `not_Remark52LogDerivativeAlgebra`: formal obstructions showing that the
  current Remark 5.2 speed condition is not strong enough to route the proof
  through explicit Lemma 5.2
- `remark51MPrime_nonneg_of_MChi_pos`,
  `remark52MTriplePrime_nonneg_of_MChi_pos`,
  `Remark_5_2.nonincreasing_positive_profile_branch`,
  `Remark_5_2.nonincreasing_branch`,
  `Remark_5_2.monotoneTravelingWave_branch`, and
  `Remark_5_2_frozen_monotone_trap_direct`: real monotone-wave and frozen
  monotone-trap branches of Remark 5.2.  The proof does not use the invalid
  speed-algebra route; it proves the displayed `M'''` denominator-normalized
  constant is nonnegative and then uses `U' ≤ 0` and `U > 0` to get
  `U'/U ≤ 0`.
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_remark52_log_derivative`:
  applies the positive/nonincreasing profile branch to the constructed
  negative-sensitivity fixed point without first packaging a full traveling
  wave.
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_signal_and_remark52_log_derivative`
  and
  `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_const_sub_signal_and_remark52_log_derivative`:
  keep the Lemma 5.1 signal estimates, corrected constant subsolution, and
  Remark 5.2 log-derivative branch on the same constructed fixed point.
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
- `Lemma_2_5_full_statement` (Paper2), together with the sharp `Psi_beta` statements and
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
- `Theorem_2_2_linear_stability_chi_nonpos_branch_direct` (Paper3): the
  nonpositive-sensitivity linear-stability branch of Paper3 Theorem 2.2,
  derived directly from the Neumann spectral positivity lemmas for the
  positive and minimal equilibria.  This intentionally does not claim the
  local exponential stability part of Theorem 2.2.
- `Theorem_2_2_linear_threshold_branch_direct` (Paper3): the stable/unstable
  linear spectral-threshold branch of Paper3 Theorem 2.2, proved directly from
  the explicit nonzero-mode infimum `paperCriticalSensitivity` and the Neumann
  spectrum lemmas rather than from `Paper3Constants.linearStabilityInstability`.
  The analytic local exponential stability conclusions remain package-supplied.
- `Paper3ConstantsUsesCriticalSpectrum.positiveEquilibrium_linearlyStable`,
  `Paper3ConstantsUsesCriticalSpectrum.positiveEquilibrium_linearlyUnstable`,
  `Paper3ConstantsUsesCriticalSpectrum.minimalEquilibrium_linearlyStable`,
  `Paper3ConstantsUsesCriticalSpectrum.minimalEquilibrium_linearlyUnstable`,
  and `Theorem_2_2_linear_critical_spectrum_branch_direct` (Paper3): once
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
- `Theorem_2_4_linear_stability_branch_of_Lemma_A_7` and
  `Theorem_2_5_linear_stability_branch_of_Lemma_A_8` (Paper3): the linear-stability
  portions of the strong-logistic and minimal global-stability theorems now
  follow directly from the A.7/A.8 threshold comparisons plus the
  critical-spectrum bridge.  The global stability and exponential convergence
  conclusions remain explicit analytic package fields.
- `Theorem_2_2_xpSigma_local_exponential_branch_of_Lemma_A_1` (Paper3): the
  `X^σ_p` small-perturbation exponential-decay branch of Theorem 2.2 is proved
  from the concrete spectral critical-sensitivity bridge and Lemma A.1, rather
  than by assuming `Theorem_2_2` or
  `Paper3Constants.linearStabilityInstability`.  This branch intentionally
  assumes an existing global solution and `xpSigmaDistance` smallness; the
  sup-norm local well-posedness/continuity upgrade remains open.
- Paper3 recalled Proposition 1.1--1.4 bridge status:
  the former Paper2-theorem bridge lemmas (`Proposition_1_1.paper2`,
  `Proposition_1_3.of_paper2_theorem_1_3`, and
  `Proposition_1_4.of_paper2_theorem_1_2`) are no longer present in Lean
  sources.  The remaining positive bridge
  `Proposition_1_2_of_negativeSensitivityGlobalEventualBound` is explicitly
  conditional on the smaller eventual-bound hypothesis, so it is not counted
  as a source proof of Paper3 Proposition 1.2.
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
- The former namespace-style Theorem 1.2/1.3 bridge names
  `Theorem_1_2.stability_from_*`, `Theorem_1_3.uniqueness_bridge_*`,
  `Theorem_1_3.frozen_profile_uniqueness_bridge_*`, and
  `Theorem_1_3.frozen_trap_profile_uniqueness_bridge_*` are no longer present
  in Lean sources.  The current theorem list uses the flat branch names below;
  this audit should track those names directly.
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
- `Theorem_1_3_profile_eq_of_stability_second_tail_continuous`:
  the same bridge with the second-profile `IsCUnifBdd` input derived internally
  from the upper-tail bound and continuity
- `Theorem_1_3_profile_eq_of_remark43_stability_cauchy_unique_and_resolvent`:
  the same uniqueness bridge with the weighted initial closeness supplied by
  the corrected regular Remark 4.3 tail theorem, so the bridge inputs are now
  sharp tail asymptotics, profile continuity, stability, Cauchy uniqueness,
  and resolvent identification
- `Theorem_1_3_profile_eq_of_remark43_second_tail_continuous`:
  the regular Remark 4.3 bridge with the second-profile `IsCUnifBdd` input
  likewise derived from the second upper-tail bound and continuity
- `Lemma_A_6_direct` (Paper3)
- `FrozenStationaryWaveProfile.mk_auto_limits`
- `FrozenStationaryWaveProfile.mk_from_paper_stationarity_of_tail_continuous`
  and `FrozenStationaryWaveProfile.mk_auto_limits_of_tail_continuous`: profile
  constructors that derive positivity and `IsCUnifBdd` from
  `HasWaveUpperTailBound` plus continuity instead of taking those profile facts
  as separate inputs
- `Theorem_1_1.of_raw_frozen_stationary_branches`: raw fixed-point data
  bridge for Paper1 Theorem 1.1.  Positivity, boundedness, stationarity,
  endpoint limits, monotonicity/tail data, and upper barriers are assembled
  into `FrozenStationaryWaveProfile`s internally, then converted to the paper
  traveling-wave existence conclusion without projecting from
  `Paper1AnalyticData.travelingWaveExistence`.
- `Theorem_1_1.of_raw_frozen_stationary_tail_continuous_branches`: the same
  raw fixed-point bridge with the profile positivity and bounded-continuous
  inputs derived from upper-tail bounds plus continuity
- `ShenUpperBoundPositive.hasWaveUpperTailBound_of_chi_lt_half_chiStar` and
  `Theorem_1_1.of_raw_frozen_stationary_positive_upper_continuous_branches`:
  positive-sensitivity bridge deriving the `HasWaveUpperTailBound` input from
  the paper's `ShenUpperBoundPositive` upper barrier and
  `χ < min(1/2,χ*)`
- `Theorem_1_1.of_raw_frozen_stationary_speed_branches`: raw fixed-point bridge
  that derives the auxiliary `0 < c` input from `cStarLower p < c` in the
  negative branch and from `2 < c` in the positive branch
- `NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_speed_bridge_data`,
  `PositiveSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_speed_bridge_data`,
  and `Theorem_1_1.of_assumed_fixed_point_construction_branches`: construction-level
  bridges that use the actual fixed point, trap-set continuity, monotonicity,
  tail bounds, and right-end limits from `FrozenWaveMapConstruction`.  They
  keep stationarity, left-end convergence, the sharp paper upper bound, and
  right-tail asymptotics as explicit fixed-point obligations, so they do not
  count as a completed Theorem 1.1 proof.
- `InWaveTrapSet.tendsto_atTop_zero`,
  `InWaveTrapSet.frozenElliptic_tendsto_atTop_zero`,
  `InMonotoneWaveTrapSet.tendsto_atTop_zero`,
  `InMonotoneWaveTrapSet.frozenElliptic_tendsto_atTop_zero`,
  `HasWaveUpperTailBound.tendsto_atTop_zero`,
  `HasWaveUpperTailBound.inWaveTrapSet_of_continuous`,
  `HasWaveUpperTailBound.inMonotoneWaveTrapSet_of_continuous`,
  `HasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero`,
  `HasWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero_of_continuous`,
  `HasStrictWaveUpperTailBound.tendsto_atTop_zero`,
  `HasStrictWaveUpperTailBound.inWaveTrapSet_of_continuous`,
  `HasStrictWaveUpperTailBound.inMonotoneWaveTrapSet_of_continuous`,
  `HasStrictWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero`,
  `HasStrictWaveUpperTailBound.frozenElliptic_tendsto_atTop_zero_of_continuous`,
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
     `Lemma_4_1_strengthened_away_from_interface_direct`; downstream Paper1
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
     corrected slices are proved by `Lemma_4_2_chi_zero_strengthened_direct`,
     `Lemma_4_2_chi_zero_D_ge_one_strengthened_direct`, and
     `Lemma_4_2_chi_zero_alpha_one_strengthened_direct`. Downstream Paper1
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
- `BoundedDomainData`: abstract smooth bounded domain API (Point, boundary,
  norms, Laplacian, admissibility, regularity predicates).  It is still an
  interface, not a proof of any paper theorem.
- `SpectralData` / `HasNeumannSpectrum`: Neumann eigenvalue API.  Spectrum
  facts are explicit hypotheses, not hidden fields inside `SpectralData`.
- `HeatSemigroupEstimateData` and `SemigroupEstimateData`: semigroup/norm
  operation APIs only.  The semigroup estimates themselves are no longer fields
  of these structures.
- `StabilityNorms`: two distance functionals only.
- `Paper2Constants`: just a nonnegative real constant `K`.
- `Paper3Constants`: threshold functions and a positive Gaussian lower
  constant; no linear-stability, compactness, persistence, or convergence
  theorem fields remain.

### Remaining explicit theorem-scale assumptions:
- `Lemma_A_1`, `Lemma_A_7`, `Lemma_A_8`, and `Corollary_5_1` are still Prop
  statements.  Accessor lemmas must keep those names visible.
- `SectorialLocalExponentialRaw` and related raw convergence/local-stability
  hypotheses are explicit Prop inputs.  Bridges depending on them are named
  `*_of_raw` or `*_of_sectorial`.
- `CompactnessData` contains abstract relation predicates such as
  `locallyConverges` and `neumannResolventGradientBound`; a theorem assuming
  those predicates is conditional on that analytic input.

### Assessment:
The abstract interfaces are acceptable as interfaces, but any theorem that
assumes one of the explicit theorem-scale Props or abstract analytic relation
predicates is conditional and must not be counted as an end-to-end proof.
The remaining open challenges require bounded-domain PDE, sectorial stability,
compactness, and convergence infrastructure not yet formalized here.

Per Playbook §1 Point 11 (honest reporting):
- Paper1: "unconditionally proved" for Lemma 2.2-2.4, Lemma 4.1/4.2 strengthened, chemotaxis resolvent, Psi ODE
- Paper2/Paper3: the concrete branch theorems named `_direct`, `_of_raw`,
  `_of_Lemma_*`, and `_of_sectorial` should be reported with exactly those
  dependencies; the abstract domain interface is not itself a proof of the
  needed semigroup/stability/compactness estimates.

## Phase 4 Classification (current naming)

The Lean sources no longer contain theorem declarations with `_proved` in
their names.  Former `_proved` wrappers were either removed or renamed to
`_direct` / explicit branch names so the theorem name does not imply an
end-to-end paper theorem proof.

### Paper3 direct / branch theorems — actual classification:

| Theorem | Uses abstract structure? | Correct classification |
|---------|--------------------------|------------------------|
| `Lemma_A_6_direct` | No | genuinely proved |
| `Lemma_3_1_from_global_solution_regular_components` | Removed | deleted because it was only a regularity-field accessor, not an end-to-end proof |
| `Theorem_2_2_linear_stability_chi_nonpos_branch_direct` | `SpectralData` + `HasNeumannSpectrum` | genuine relative spectral branch; does not prove PDE/local stability |
| `Theorem_2_2_linear_threshold_branch_direct` | `SpectralData` + `HasNeumannSpectrum` | genuine relative spectral branch using the explicit `paperCriticalSensitivity` formula |
| `Theorem_2_2_linear_critical_spectrum_branch_direct` | `SpectralData` + `Paper3ConstantsUsesCriticalSpectrum` | genuine bridge once `C.chiCritical` is identified with the explicit spectral threshold |
| `Theorem_2_2_xpSigma_local_exponential_branch_of_Lemma_A_1` | `Lemma_A_1` + critical-spectrum bridge | bridge from explicit Lemma A.1 local-stability input; not a proof of Lemma A.1 |
| `Theorem_2_2_xpSigma_local_exponential_branch_of_raw` | `SectorialLocalExponentialRaw` + critical-spectrum bridge | bridge from exposed sectorial local-stability input; not a proof of the raw sectorial estimate |
| `LinearStabilityInstabilityRaw_of_sectorial_paperCriticalSensitivity` | `SectorialLocalExponentialRaw` + explicit `paperCriticalSensitivity` + `X^σ_p ≤ supNorm` + small-data existence | proves the raw Paper3 Theorem 2.2 local-stability shapes from exposed analytic inputs; not a proof of the sectorial or Cauchy-existence inputs |
| `LinearStabilityInstabilityRaw_of_sectorial_critical_spectrum` | `SectorialLocalExponentialRaw` + `Paper3ConstantsUsesCriticalSpectrum` + `X^σ_p ≤ supNorm` + small-data existence | same raw local-stability bridge when `C.chiCritical` is audited against the explicit spectral threshold |
| `Theorem_2_4_linear_stability_branch_of_Lemma_A_7` | `Lemma_A_7` + critical-spectrum bridge | bridge from explicit A.7 threshold comparisons; not a proof of global stability |
| `Theorem_2_5_linear_stability_branch_of_Lemma_A_8` | `Lemma_A_8` + critical-spectrum bridge | bridge from explicit A.8 threshold comparisons; not a proof of global stability |
| `SupControlsXpSigmaDistance.of_xpSigma_le_supNorm` | pointwise comparison `X^σ_p ≤ supNorm` | reduces the norm-control package to a primitive comparison against the exposed `supNorm` |
| `SectorialLocalExponentialRaw.locally_from_sup_control` | `SectorialLocalExponentialRaw` + `SupControlsXpSigmaDistance` + `SmallDataGlobalExistence` | bridge from exposed sectorial `X^σ_p` decay to ordinary sup-norm local stability; the norm-control and Cauchy-existence inputs remain explicit |
| `SectorialLocalExponentialRaw.locally_from_xpSigma_le_supNorm` | `SectorialLocalExponentialRaw` + pointwise `X^σ_p ≤ supNorm` + `SmallDataGlobalExistence` | ordinary local-stability bridge with the norm-control input reduced to the primitive comparison |
| `SectorialLocalExponentialRaw.massConstrained_from_sup_control` | `SectorialLocalExponentialRaw` + `SupControlsXpSigmaDistance` + `MassConstrainedSmallDataGlobalExistence` | bridge from exposed sectorial `X^σ_p` decay to mass-constrained sup-norm local stability; the norm-control and Cauchy-existence inputs remain explicit |
| `SectorialLocalExponentialRaw.massConstrained_from_xpSigma_le_supNorm` | `SectorialLocalExponentialRaw` + pointwise `X^σ_p ≤ supNorm` + `MassConstrainedSmallDataGlobalExistence` | same bridge with the norm-control input reduced to the primitive comparison |
| `Corollary_5_1_nonminimal_exponential_formula_condition_critical_of_raw` | raw nonminimal convergence-to-exponential upgrade + explicit `paperCriticalSensitivity` threshold bound | formula-level exponential-upgrade bridge; not a proof of the raw convergence-to-exponential estimate itself |
| `Corollary_5_1_nonminimal_exponential_formula_condition_firstNonzero_of_raw` | raw nonminimal convergence-to-exponential upgrade + explicit first-mode threshold bound | formula-level exponential-upgrade bridge; not a proof of the raw convergence-to-exponential estimate itself |
| `Corollary_5_1_minimal_exponential_formula_condition_critical_of_raw` | raw minimal convergence-to-exponential upgrade + explicit `paperCriticalSensitivity` threshold bound | formula-level exponential-upgrade bridge; not a proof of the raw convergence-to-exponential estimate itself |
| `Corollary_5_1_minimal_exponential_formula_condition_firstNonzero_of_raw` | raw minimal convergence-to-exponential upgrade + explicit first-mode threshold bound | formula-level exponential-upgrade bridge; not a proof of the raw convergence-to-exponential estimate itself |
| `Theorem_2_3_negative_sensitivity_local_formula_branch_of_raw` | negative-sensitivity spectral sign + raw sectorial bridge | ordinary formula-level local-stability bridge; not a proof of negative-sensitivity global stability |
| `Theorem_2_3_negative_sensitivity_local_formula_branch_of_xpSigma_le_supNorm` | negative-sensitivity spectral sign + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | ordinary formula-level local-stability bridge with theorem-level primitive norm comparison; not a proof of negative-sensitivity global stability |
| `Theorem_2_3_negative_sensitivity_mass_constrained_formula_branch_of_raw` | negative-sensitivity spectral sign + raw sectorial bridge | formula-level bridge; not a proof of negative-sensitivity global stability |
| `Theorem_2_3_negative_sensitivity_mass_constrained_formula_branch_of_xpSigma_le_supNorm` | negative-sensitivity spectral sign + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | mass-constrained formula-level bridge with theorem-level primitive norm comparison; not a proof of negative-sensitivity global stability |
| `Theorem_2_4_local_stability_formula_branch_of_raw` | explicit strong-threshold formulas + raw sectorial bridge | ordinary formula-level local-stability bridge; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_local_stability_formula_branch_of_xpSigma_le_supNorm` | explicit strong-threshold formulas + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | ordinary formula-level local-stability bridge with theorem-level primitive norm comparison; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_local_stability_first_mode_branch_of_raw` | explicit first-mode strong-threshold bound + raw sectorial bridge | first-mode ordinary local-stability bridge; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_local_stability_first_mode_branch_of_xpSigma_le_supNorm` | explicit first-mode strong-threshold bound + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | first-mode ordinary local-stability bridge with theorem-level primitive norm comparison; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_full_stability_formula_branch_of_raw` | explicit strong-threshold formulas + raw sectorial bridge | formula-level bridge; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_full_stability_formula_branch_of_xpSigma_le_supNorm` | explicit strong-threshold formulas + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | mass-constrained formula-level bridge with theorem-level primitive norm comparison; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_full_stability_first_mode_branch_of_raw` | explicit first-mode strong-threshold bound + raw sectorial bridge | first-mode formula-level bridge; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_4_full_stability_first_mode_branch_of_xpSigma_le_supNorm` | explicit first-mode strong-threshold bound + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | first-mode mass-constrained formula-level bridge with theorem-level primitive norm comparison; not a proof of the nonlinear global-stability estimate |
| `Theorem_2_5_full_stability_formula_branch_of_raw` | explicit minimal threshold formulas + raw sectorial bridge | formula-level bridge; not a proof of the nonlinear minimal-model stability estimate |
| `Theorem_2_5_full_stability_formula_branch_of_xpSigma_le_supNorm` | explicit minimal threshold formulas + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | minimal-model formula-level bridge with theorem-level primitive norm comparison; not a proof of the nonlinear minimal-model stability estimate |
| `Theorem_2_5_full_stability_first_mode_branch_of_raw` | explicit first-mode minimal threshold bound + raw sectorial bridge | first-mode minimal-model formula-level bridge; not a proof of the nonlinear minimal-model stability estimate |
| `Theorem_2_5_full_stability_first_mode_branch_of_xpSigma_le_supNorm` | explicit first-mode minimal threshold bound + raw sectorial bridge + pointwise `X^σ_p ≤ supNorm` | first-mode minimal-model formula-level bridge with theorem-level primitive norm comparison; not a proof of the nonlinear minimal-model stability estimate |

### Paper2 direct / branch theorems:

| Theorem | Uses abstract structure? | Correct classification |
|---------|--------------------------|------------------------|
| `Lemma_2_5_full_statement` and `Lemma_2_5_full_range_statement` | No | genuinely proved scalar `Psi_beta` results |

### Paper1 direct / branch theorems:

| Theorem | Uses abstract structure? | Correct classification |
|---------|--------------------------|------------------------|
| `Lemma_2_2_direct`, `Lemma_2_3_direct`, `Lemma_2_4_direct` | No | genuinely proved |
| All `_strengthened_direct` / corrected-slice branches | No | genuinely proved |
| All `not_*` counterexamples | No | genuinely proved |

### Naming policy after v4 proposal
Full theorem-shaped accessors from assumption components should not be named
`_proved`.  Direct theorem names should use `_direct`, and conditional results
should say `branch`, `raw`, `of_...`, or otherwise expose their remaining
inputs in the declaration name and theorem type.

---

## 2026-06-06 — F2 interface faithfulness finding (χ₀ ≠ 0)

**Finding**: `IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData`
(the hMildLocal hypothesis of `paper2_theorem_1_1_from_three`/`_from_two`)
requires `GradientMildHalfStepLogisticSourceData`, whose `hagree` field
represents every mild slice `u(t)` as a restart cosine series whose Duhamel
source family is the cosine coefficients of a *pure logistic* source
`L(profile t σ) = g(a − b·g^α)`.  The gradient mild map
(`intervalGradientDuhamelMap`) contains the chemotaxis flux term
`−χ₀ ∫₀ᵗ ∂ₓ[S(t−s) Q(u s)] ds`; for `χ₀ ≠ 0` the effective restart source
contains a flux-divergence component that is in general NOT realizable as
`L(g)` for positive C² `g` (for `α ≥ 1` the logistic range is bounded above
by `max_{z>0} z(a−bz^α)`, the flux component is not).  **The logistic-only
hMildLocal interface is expected to be satisfiable only when the flux term
vanishes (`χ₀ = 0`)** — proving it for `χ₀ < 0` is likely impossible, and any
"close hMildLocal" plan routed through the logistic package is a dead end for
the general regime.

**Fix (committed)**: `IntervalDomainRestartLocalWiring.lean` defines the
faithful abstract-restart interface
`IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData` (uses
`GradientMildHalfStepRestartData`: arbitrary `DuhamelSourceTimeC1` source
family — accommodates flux) + `paper2_theorem_1_1_from_two_restart`.
The logistic interface remains usable for the `χ₀ = 0` sub-regime and implies
the abstract one (`restartLocalData_of_logisticLocalData`).

**Remaining genuine math core behind the abstract interface** (the real F2):
construct, for the Picard-limit mild solution, a half-step restart source
family `a t : ℝ → ℕ → ℝ` with (i) the restart cosine agreement and (ii) the
`DuhamelSourceTimeC1` envelope `∑ₙ supₛ |aₙ(s)| < ∞`.  The envelope for the
flux part needs the cosine coefficients of `∂ₓQ(u(s))` to be absolutely
summable — i.e. slightly more than C² regularity of `Q` (Wiener-algebra /
Hölder-C² class).  This requires a second bootstrap round (or Lᵖ-smoothing
Schauder-type estimates), and is the true mathematical frontier of Paper 2
Theorem 1.1; it was previously hidden inside the unsatisfiable logistic
interface.

**hQuant note**: the current Picard existence
(`intervalMildSolution_exists_picard`) picks the horizon via
`A√T + BT < min(1, inf u₀)` — the `inf u₀` dependence (crude positivity)
breaks the uniform-in-datum δ(M) needed by hQuant.  Design for the fix:
two-sided cone invariance `θ(s)·S(s)u₀ ≤ w(s) ≤ e^{as}·S(s)u₀` through the
mild map (uses semigroup property `S(t−s)S(s) = S(t)` and positivity of the
semigroup); for `χ₀ = 0` this gives an inf-independent horizon directly; for
`χ₀ ≠ 0` the flux term additionally needs a pointwise kernel-derivative
comparison `|∂ₓK(r,x,y)| ≤ C r^{−1/2} K(2r,x,y)`-type estimate.

## 2026-06-06 — Doc-vs-reality: Thm11Assembly hpde_u claim

The IntervalDomainThm11Assembly.lean status table marks "hpde_u ✓ proved |
G4n-p (spectral PDE identity + bridge)". Ledger-sweep archaeology (commit
1e6903f) found this is ROUTE-LEVEL only: the sole producer
(mildSolution_parabolicPDE) delegates circularly to IsPaper2ClassicalSolution;
no theorem concludes the pointwise parabolic identity from
HasTimeNeighborhoodSpectralAgreement. The genuine spectral→pointwise PDE
bridge (laplacian-of-cosine-series identity + reaction coefficient identity)
remains to be built. Do not cite the table row as a proof.

Final χ₀=0 residual ledger (ReducedLimitRegularityInputs +
paper2_theorem_1_1_chiZero_of_reduced_inputs, IntervalDomainLedgerSweep.lean):
K1/K2 families (n→∞ images of M-final Data) + 4 analytic modules:
hpde_u (spectral→pointwise PDE bridge), Hvsrc (power-source TimeC1 analogue
of logisticSource_duhamelSourceTimeC1), Hvpos (elliptic strict min principle),
HsupNorm (parabolic max principle producer).

## 2026-07-19 — Thm 1.2 stability: weighted-L² dissipation PROVED; residual χ∈[1/2,χ*) gap is in the PAPER too

The co-moving weighted-L² energy **dissipation** inequality — the analytic
core of the Section-5 stability argument — is now proved unconditionally for
the full stable regime, at any fixed ceiling `M > MChi p`:

- `paperNonnegativeInitialDatum_hcore_energy_available_data_natural`
  (WholeLineWeightedRegularityHCoreEnergyNatural.lean) gives the global
  solution, energy control `coMovingWeightedL2Energy ≤ E`, positive-time
  differentiability of `E`, the dissipation
  `deriv E t ≤ 2·paper531Quadratic c (paper531CommonA p M) (paper531CommonB p M) η · E t`,
  integrability, and the spatial modulus — clean-3, verified through the root.
- Supporting: `...FixedBoundEnergyNatural` (fixed-M dissipation +
  positive-time differentiability), `...EnergyEnvelope` (global exponential
  energy envelope). All merged to main (commits caa767cf..6626bb77).

**What is NOT closed — the literal `hcore`, and why it caps at χ<1/2.**
Two independent gaps remain between the proved dissipation package and the
top-level `hcore` hypothesis of
`paper1_Theorem_1_2_amended_of_concrete_wholeLineCauchyEnergyStep4`:

1. **Initial-data regularity mismatch.** Top-level `hcore` is stated over the
   historical `NonnegativeInitialDatum` (continuous + bounded only), but every
   whole-line Cauchy producer requires the uniformly-continuous
   `PaperNonnegativeInitialDatum`. The remaining `hcore` hypotheses do not
   supply uniform continuity — there is an explicit left-end oscillation
   counterexample. This is a hypothesis-strength gap, not a missing estimate.

2. **Left-tail uniform convergence caps at χ<1/2 — IN THE PAPER, not just the
   formalization.** `hcore` also demands `UniformMovingFrameLeftTailConvergence`.
   Producing it requires eventual absorption of the far-left supremum, which
   both the rectangle two-sided comparison (contraction factor `2χ`) and the
   constant-plateau ledger (trap condition `χ·Q^γ<1`, which at `Q=MChi` is
   exactly `χ<1/2`) can only deliver for `χ<1/2`. The weighted-L² weight
   `e^{2ηz}` degenerates as `z→−∞`, so the energy method itself cannot control
   the far-left supremum. Concretely, for the stable parameters
   `m=α=γ=1, χ=3/4` no rectangle seed exists and the gap recursion does not
   contract. **The source paper reaches this same step by invoking a
   proposition that only covers `χ<1/2`, i.e. it over-reaches to the full
   `χ∈[1/2,χ*)` window.** Closing it honestly needs a genuinely new
   uniformly-local-entropy or entire-solution (Liouville-type) PDE estimate
   for the far-left tail — this is the true residual frontier of Theorem 1.2.

Cross-check: this χ<1/2 barrier was found independently two ways — by the
Codex dissipation lane and by direct reconnaissance of the ceiling machinery
(`wholeLineCauchyParameterCeiling = MChi` in the critical branch; all absorption
tools share the `2χ<1` / `χ·Q^γ<1` cap). Do NOT present `Theorem_1_2_amended`
as unconditional: the dissipation is discharged, the left-tail is not.

## 2026-07-20 — Prop 1.1 residual 1<χ: local-Lp chain PROVABLY can't reach L∞ (why the import is a genuine citation)

Follow-up to the `Proposition_1_1_large_chi_critical_branch` reduction
(commit 79f56496): that theorem closes the residual `1≤χ` critical window from
two inputs — the imported maximal-BUC local theory (`WholeLineMaximalBUCImport`)
and one uniform a-priori L∞ bound (`WholeLineLargeChiAPrioriBound`). Question:
can the a-priori bound be discharged from the repo's own local-Lp chain
instead of imported? Answer: NO for `1<χ`, and here is the exact obstruction.

The local-Lp producer `wholeLineCauchyGlobal_uniformlyLocalLpBounded`
(WholeLineLocalMomentGlobalProducer.lean:465) requires the admissibility
condition `p.χ * (P - 1) < P + p.m - 1`, i.e. `(χ-1)(P-1) < m`. Alikakos–Moser
iteration bootstraps a uniform local-`L^P` bound to `L^∞` only in the limit
`P → ∞`. But:

- `χ ≤ 1`: `(χ-1)(P-1) < m` holds for ALL `P` → `P→∞` admissible → the chain
  CAN reach `L^∞`.
- `χ > 1`: `(χ-1)(P-1) < m` forces `P < 1 + m/(χ-1)`, a FINITE integrability
  ceiling (e.g. `m=1, χ=1.5 ⇒ P<3`; `χ=2 ⇒ P<2`). Moser stalls at finite `P`;
  no `L^∞` bound is available from this chain.

So the local-Lp route caps exactly at `χ ≤ 1`, mirroring the box-gluing
obstruction (`not_wholeLineBoxMargin_of_one_le_chi_critical`, which caps at
`χ < 1`). For `1 < χ` the uniform-`L^∞` a-priori bound genuinely requires the
imported local/maximal theory's own parabolic smoothing — it is a real
citation, not a formalization shortcut we declined to grind. Do NOT dispatch a
"prove the a-priori bound from local-Lp" lane for `1<χ`: it would rediscover
this finite-`P` cap. (At `χ = 1` exactly the chain admits all `P`, so a
Moser-to-`L^∞` closure there is not obstructed — a genuine but single-point
increment, of marginal value against the full iteration-infrastructure cost.)

## 2026-07-20 — CORRECTION to the 2026-07-19 "paper over-reaches" claim (retracted as too strong)

The 2026-07-19 entry stated the source paper "over-reaches" on the Theorem 1.2
left-tail. On re-examination that assertion is WITHDRAWN — it was inferred from
our formalization's toolkit, not verified against the paper. Corrected picture:

- The wave satisfies `Tendsto U atBot (𝓝 1)` (Statements.lean:2935,
  `FrozenStationaryWaveProfile.lim_neg_inf`): the FAR-LEFT limit is the
  EQUILIBRIUM `u ≡ 1`, and the far-RIGHT is `0` (controlled by the growing
  weight `e^{2ηz}`). So "left-tail convergence" is convergence to the
  equilibrium at `z → −∞`, exactly where the weight `e^{2ηz}` degenerates.
- Our ONLY formalized far-left tool is the half-line rectangle
  (`uniformCoMovingLeftEquilibriumConvergence_of_halfLine_successors`,
  WholeLineChiPosHalfLineRectangle.lean:77), whose gap contracts by factor
  `2χ` (`ChiPosHalfLineRectangleStep.gap_le`), forcing `χ < 1/2`. The sharp
  variant `χ/(1-χ)` caps at the SAME `χ<1/2`. So the `χ<1/2` cap is a property
  of the RECTANGLE mechanism, not a proven property of the paper's argument.
- Two independent indicators say the true threshold is higher, not `1/2`:
  (i) mere far-left BOUNDEDNESS via the plateau trap at the equilibrium height
  `Q = 1` needs only `χ·1^γ < 1`, i.e. `χ < 1` (WavePositivePlateauTrapHeight);
  (ii) the equilibrium `u≡1` is LINEARLY STABLE with spectral gap `−α` for
  `χγ ≤ 1` (proved: `dispersion_le_neg_alpha`), far beyond `χ<1/2`.

Corrected verdict: the left-tail `χ<1/2` cap is a limitation of the crude
rectangle convergence tool we formalized, NOT an established defect of the
paper. The linear spectral gap indicates a sharper convergence mechanism —
a far-left-non-degenerate weighted energy, or a spectral/comparison argument
around `u≡1` — should extend far-left equilibrium convergence toward `χγ ≤ 1`
(covering the whole window, since `χ* ≤ 1`). Whether the paper uses exactly
this is unverified from the source and should be checked against the PDF, not
asserted. This is the genuine open frontier of Theorem 1.2, and it is
plausibly closable — the prior entry overstated it as a paper defect.

## 2026-07-20 — The rectangle wall is now a THEOREM, and its exact location

The 2026-07-19 retraction above left the frontier described qualitatively
("the `χ<1/2` cap is a property of the rectangle mechanism"). That is now
proved, and the wall's exact location is known.

**Where the `χ<1/2` came from.** The ceiling budget was absorbed with the crude
bound `M'^(m-1)(M'^γ - ell'^γ) ≤ M'^α - ell'^α`, coefficient `1`. That is what
produces the `(1-χ)` factor in the gap recursion. Two successive sharpenings:

1. Keeping the small-endpoint factor `ell^(m-1)` in the FLOOR budget gives the
   exact coefficient `γ/α` there (`rpow_small_prefactor_gap_le_ratio`), hence
   contraction under `χγ < α(1-χ)`, i.e. `χ < α/(α+γ)`. Strictly better than
   `1/2` for every `m>1` (`one_half_lt_critical_sharp_threshold`).
2. The CEILING absorption is in fact an IDENTITY with coefficient
   `c(t) = (1-t^γ)/(1-t^α)`, `t = ell/M`, and `c` is non-increasing with
   `c(0⁺)=1`, `c(1⁻)=γ/α` (`WholeLineChiPosCeilingRatio.lean`). Since `ell`
   increases and `M` decreases along the chain, `t` is bounded below by the
   SEED's aspect ratio — which comes from the `χ<1` trap, not from the
   contraction being proved, so there is no circularity. Contraction then holds
   under `χ < α/(γ + α·c0)`, interpolating from `α/(α+γ)` at `c0=1` to
   `α/(2γ)` as `c0 ↓ γ/α`.

**The wall.** `2χγ < α` is the intrinsic limit of ANY two-endpoint rectangle:
the endpoint model has discarded diffusion at the max/min and permits the worst
anti-correlation between `u` and the resolver. At `m=γ=α=1` this reads
`χ<1/2`, and that case is now proved SHARP rather than asserted:
`chiPos_budget_stationary_of_half_le_chi` exhibits, for every `χ ≥ 1/2`, every
slack `δ>0` and every gap `d`, a pair `(1-d/2, 1+d/2)` satisfying BOTH budgets
with `new = old`. The budget system therefore has stationary points of
arbitrary gap, and no rearrangement of the two scalar inequalities can force
contraction. (`chiPos_combined_budget_vacuous_of_half_le_chi` records that the
combined inequality `(1-2χ)·gap ≤ 2δ` is satisfied by every gap once `χ ≥ 1/2`.)
Since `chiStar p = 1` at `m=γ=1`, the window the rectangle genuinely cannot
reach there is all of `[1/2, 1)`.

**Coverage of the paper's window.** `chiStar p ≤ α/(α+γ)` exactly when
`P = m³+m²(γ-2)+m(1-3γ)-2γ² ≥ 0` (`chiStar_le_sharpThreshold_of_cubic`), and
`chiStar p ≤ α/(2γ)` exactly when `Q = m³+γm²-(γ+1)m-2γ²-2γ ≥ 0`
(`chiStar_le_limitThreshold_of_poly`). Roots in `m` at `γ=1`: `2.2695` and
`1.6590`. Below those the window `[threshold, chiStar)` stays open.

**HONEST LIMIT — do not quote a widened threshold yet.** The refinement's
machinery is proved and the coefficient is discharged, but the current seed's
floor comes from a continuity-at-`0` argument
(`exists_small_chiPos_floor_with_halfKernel_reserve`), so `t0 ≈ 0`, `c0 ≈ 1`,
and the refined condition degenerates to the old `χ < α/(α+γ)`. A seed with an
aspect ratio bounded below explicitly in `χ` is the missing piece; the route is
to rebuild the floor against the settled ceiling `Q = MChi p + 1` instead of the
crude global `G`. Until that lands, the unconditional threshold is unchanged.

**PENDING, not a finding.** An external reading suggests the paper's
Proposition 1.2(2) is stated and proved only for `χ<1/2` while Theorem 1.2's
Step 4 invokes it throughout `χ<χ*`. A verification question against the actual
PDF is in flight. Given that the 2026-07-19 entry above had to be retracted for
exactly this class of unverified inference, this is recorded as OPEN and must
NOT be cited as a paper defect until the source text is checked.

### Quantified: what the `Q`-seed can actually buy (computed 2026-07-20)

Before investing further in the seed-quality route, the achievable threshold was
computed numerically. Taking the best floor available against the settled
ceiling `Q = MChi p + 1` — i.e. `ell0` the root of
`1 - ell^α = χ·ell^(m-1)·(Q^γ - ell^γ)`, `t0 = ell0/Q`, `c0 = c(t0)` — and
solving for the largest self-consistent `χ < α/(γ + α·c0)`:

| `m`, `γ` | old `α/(α+γ)` | ideal `α/(2γ)` | achieved with `Q`-seed | `χ*` |
|---|---|---|---|---|
| 1.2, 1 | 0.5455 | 0.6000 | **0.5497** | 0.9483 |
| 1.5, 1 | 0.6000 | 0.7500 | **0.6248** | 0.8696 |
| 2.0, 1 | 0.6667 | 1.0000 | **0.7307** | 0.7500 |
| 2.5, 1 | 0.7143 | 1.2500 | **0.8138** | 0.6512 |
| 3.0, 1 | 0.7500 | 1.5000 | **0.8780** | 0.5714 |
| 2.0, 2 | 0.6000 | 0.7500 | **0.6049** | 0.8000 |

Read this carefully: the `Q`-seed gains the most exactly where the window is
ALREADY covered (large `m`), and almost nothing where the gap is real (`m` near
`1`: at `m=1.2` it moves `0.5455 → 0.5497` against a target of `0.9483`). Even
at `m=2, γ=1` it reaches `0.7307` and still falls short of `χ* = 0.75`. The
full-window boundary at `γ=1` moves from `m ≥ 2.2695` only to roughly
`m ≥ 2.1–2.2`.

Conclusion: the seed-quality route is a genuine but SMALL increment, and it
does not rescue the regime that matters. The rectangle mechanism is
substantially exhausted; the residual window for `m` near `1` — all of
`[1/2, 1)` at `m=γ=1` — is reachable only by a different mechanism
(near-equilibrium spectral / Liouville). Do not oversell a `Q`-seed result.
### The quantified-seed lane landed — and bought almost nothing (measured 2026-07-20)

`WholeLineChiPosQuantifiedFloor / QuantifiedHalfLineSeed /
QuantifiedRefinedConvergence` (commits `a4d33244`, `2da73d5d`, `0460a5b9`)
deliver what was asked: an explicit floor

`ell₀ = min(1/4, (1/(8(1+χ·Q^γ)))^(1/(m-1))) / 2`,  `Q = MChi p + 1`,

a seed restarted after the ceiling settles with `ell₀ ≤ seed.ell ∧ seed.M ≤ Q`,
and a convergence theorem whose contraction hypothesis is evaluated at the
explicit, datum-independent coefficient `c0 = c(ell₀ / Q)`. Root build green,
9976 jobs, clean-3, verified in this tree (not merely on the producer's report).

**STRUCTURALLY this is real**: the threshold is now explicit in the equation
parameters alone, and the ceiling coefficient is discharged end-to-end.

**NUMERICALLY it is negligible.** The explicit floor is far below the true root,
chiefly because of the `1/(m-1)` exponent, which collapses `ell₀` as `m → 1`:

| `m`, `γ` | old `α/(α+γ)` | this lane | best possible (root) | `χ*` |
|---|---|---|---|---|
| 1.2, 1 | 0.5455 | **0.5455** | 0.5497 | 0.9483 |
| 1.5, 1 | 0.6000 | **0.6001** | 0.6248 | 0.8696 |
| 2.0, 1 | 0.6667 | **0.6702** | 0.7307 | 0.7500 |
| 3.0, 1 | 0.7500 | **0.7722** | 0.8780 | 0.5714 |
| 2.0, 2 | 0.6000 | **0.6000** | 0.6049 | 0.8000 |

Full-window coverage boundary in `m`: at `γ=1` it moves `2.2695 → 2.2450`; at
`γ=2`, `2.8026 → 2.8009`. (The best the mechanism could ever do is the
`α/(2γ)` root, `1.6590` and `2.1117`.)

**Do not describe this lane as widening the window.** It makes the threshold
explicit; it does not materially change which parameters are covered. The
remaining distance to `α/(2γ)` is floor quality, and the distance from
`α/(2γ)` to `χ*` near `m=1` is unreachable by this mechanism at all — see the
sharpness theorems `chiPos_budget_stationary_of_half_le_chi` (at `m=γ=1`) and
`chiPos_budget_stationary_gammaOne` (the whole `γ=1` family, `2χ > m`).

### Test B (2026-07-20): the bottleneck is TRAP QUALITY, not the energy constant

Before investing in a near-equilibrium energy formalization, the decisive cheap
computation was run: for `m = γ = α = 1`, take the frozen-coefficient symbol at
a state `ubar` in the guaranteed band,

`λ(ξ, ubar) = -ξ² + f'(ubar) + χ·ubar·ξ²/(1+ξ²)`,  `f(u) = u(1-u)`, `f'(u) = 1-2u`,

and ask for which bands it is coercive.

Result 1 — **the required floor is `ell > 1/2`, and it does NOT depend on `χ`**
(0.5000 at `χ = 0.5, 0.7, 0.9, 0.99`). The binding mode is `ξ = 0`, where the
chemotaxis multiplier `ξ²/(1+ξ²)` vanishes and only the reaction survives:
coercivity is exactly `f'(ubar) < 0`, i.e. `ubar > 1/2`. The resolvent smoothing
that fixes the `ξ ≠ 0` modes is irrelevant at `ξ = 0`.

Result 2 — **what we can guarantee is `ell ≈ 0.125`**, far short of `1/2`, so the
frozen form is not coercive anywhere in the current band (sup λ = +0.75).

Interpretation, stated carefully: a positive mode at `ξ = 0` for a LOW `ubar` is
not itself a failure of convergence — it is the KPP reaction pushing `u` up
toward `1`, which is the desired behaviour. What it does establish is that a
near-equilibrium energy/spectral argument cannot be started from the band we
currently guarantee: such an argument needs a TWO-SIDED trap `1-ε ≤ u ≤ 1+ε`
with `ε` below roughly `1/2`, and we are nowhere near that.

**Consequence for the route.** The energy constant is NOT the blocker — the
smoothing `ξ²/(1+ξ²) ≤ 1` gives `χγ < 1` on the modes where it matters. The
blocker is entering the near-equilibrium band at all. Note this cannot be done
by the same rectangle: at `m = γ = α = 1` the invariance inequalities
`1 - ell ≥ χ(M - ell)` and `M - 1 ≥ χ(M - ell)` add to `g ≥ 2χ·g`, so a
nontrivial band requires `χ < 1/2` — the same wall, so improving the trap with
the rectangle is circular.

The open question is therefore sharp and different from what we have been
asking: **is there a non-rectangle route (KPP comparison / sub-solution, using
that the reaction drives `u` up toward `1` from below) that produces a floor
approaching `1` for `χ` up to `χ*`?** That, plus the drift-weight energy
(weight `e^{cz}`, which is integrable at `-∞` and so sidesteps our own
infinite-left-mass obstruction — that obstruction was specific to the GROWING
mirror weight `e^{-2ηz}`), is the live program.

### Test A (2026-07-20): the target statement is numerically robust well past `χ = 1/2`

Spectral integrating-factor scheme (diffusion exact in Fourier, RK2 on the rest),
periodic domain `L = 60`, `m = γ = α = 1`, evolving

`u_t = u_zz - χ(u·v_z)_z + u(1-u)`,  `v - v_zz = u`.

**Control retained deliberately**: `χ = 0.3`, where stability is certain. A first
attempt with explicit Euler blew up even at `χ = 0.3`, which is how the CFL
violation was caught — the control is the reason that scheme error was not
mistaken for a finding.

With the corrected scheme, `max|u-1|` at `T = 80` reaches machine precision
(`~4e-14`) for every case tried:

* data: large oscillatory perturbation; low-floor tanh front; deep localized dip
  to `0.01`; a `+3` spike next to a `-0.9` trough; flat `0.01`
* `χ = 0.3, 0.5, 0.7, 0.9, 0.99, 1.2, 1.5, 2.0`

So `u ≡ 1` attracts all of these, far beyond the rectangle's `χ < 1/2` and even
beyond `χ* = 1`.

**Read this with its caveats.** This is a periodic domain with no front and no
far-left tail; it tests global attractivity of the equilibrium for these data,
NOT the actual far-left-of-a-traveling-front problem, and the smooth data may be
unrepresentative. It is evidence, not proof.

What it does support: the `χ < 1/2` cap is a limitation of the rectangle tool,
not a property of the equation — consistent with the sharpness theorems, which
show `1/2` is sharp *for the budget system* while saying nothing against the PDE.
It also gives no sign that `χ*` is sharp for this convergence, so if a future
argument stalls exactly at `χ*` that stall should be treated as tool-limited
until shown otherwise.

### The true far-left threshold is `χγ = (1+√α)²`, NOT `χ*` — confirmed numerically

Linearizing the parabolic problem at the plateau `(u,v) = (1,1)` with mode
`e^{ikz}` (elliptic gives `q = γp/(1+k²)`, chemotaxis gives `+χγk²/(1+k²)`,
reaction gives `-α`):

`σ(k) = -k² + χγ·k²/(1+k²) - α`.

With `x = k²` there is an interior maximum only when `χγ > 1`, at
`x* = √(χγ) - 1`, giving

`σ_max = (√(χγ) - 1)² - α`,

so the plateau `u ≡ 1` loses stability (Turing onset) exactly at

`χγ = (1 + √α)²`,  which is **4** at `m = γ = α = 1`.

**Numerically confirmed, sharply.** Plateau plus a small planted dip
(`u₀ = 1 - 0.05·exp(-(z/2)²)`), `L = 60`, `T = 80`:

| `χ` | predicted `σ_max` | observed |
|---|---|---|
| 2.0 | -0.8284 | decays to `1` (`6e-14`) |
| 3.0 | -0.4641 | decays to `1` (`1e-13`) |
| 3.5 | -0.2417 | decays to `1` (`1e-11`) |
| 3.9 | -0.0497 | marginal (`6e-05`) |
| 4.5 | +0.2574 | **pattern** (`0.52`) |
| 6.0 | +1.1010 | **pattern** (`0.84`) |

The transition sits exactly where `σ_max` changes sign. This simultaneously
validates the dispersion relation AND confirms that our formalized PDE
(`Defs.lean` `pde_u`/`pde_v`) has been translated faithfully — the marginal case
landing at `χ = 3.9` is a quantitative match, not a qualitative one.

**Consequences, stated carefully.**
1. `χ* = min(1, ...)` is a SUFFICIENT condition inherited from a coercive
   free-energy estimate — it is **not** the sharp threshold for far-left plateau
   stability, which is `4` at these exponents. Our rectangle wall at `1/2` is
   therefore very far from the truth, and even the paper's window is
   conservative for this particular step.
2. Any future argument that stalls exactly at `χ*` should be treated as
   TOOL-LIMITED until shown otherwise, not as having found the real threshold.
3. This does not license weakening anything already proved: these are linear and
   numerical statements about the plateau, not a proof of the nonlinear far-left
   convergence we actually need.

### Sharp dispersion threshold + resolver identities landed (audited 2026-07-20)

`WholeLineChiPosDispersionSharp.lean` (`e87227c7`) and
`WholeLineResolverTestingIdentities.lean` (`25c441f6`). Root build 9981 jobs,
0 sorry, 0 axiom, all clean-3, verified in this tree.

**Audit point 1 — the threshold is proved SHARP, not merely sufficient.** Both
directions are present: `dispersion_le_of_lt_turing` (`χγ < (1+√α)²` ⇒ every
mode strictly negative) AND `dispersion_pos_of_gt_turing` (`(1+√α)² < χγ` ⇒
∃ an admissible mode with strictly positive growth). This genuinely upgrades
`dispersion_le_neg_alpha`, which only covered `χγ ≤ 1` and said nothing about
optimality.

**Audit point 2 — the carried boundary hypothesis is inhabited.** The smoothing
bounds carry `hboundary : v₁ b · v b - v₁ a · v a ≤ 0`. Checked non-vacuous:
trivially by `v ≡ c > 0`, `g ≡ c` (then `v₁ ≡ 0` and the flux is `0`); and
non-trivially by any even profile decaying away from the origin on `[-R, R]`,
where `v₁(R)v(R) < 0` and `v₁(-R)v(-R) > 0`. The main identity
`resolver_testing_identity` carries no boundary hypothesis at all — the flux
appears explicitly on the right-hand side, which is the correct form.

**Follow-up, not a defect — the constants are not sharp.** In Fourier,
`v̂ = ĝ/(1+k²)`, so

* `∫(v')² = ∫ k²/(1+k²)² |ĝ|²` and `sup_k k²/(1+k²)² = 1/4` (at `k = 1`),
* `∫ v² = ∫ 1/(1+k²)² |ĝ|²` and `sup_k 1/(1+k²)² = 1` (at `k = 0`).

So the delivered `∫(v')² ≤ ∫g²` is true but loses a factor `4`; the sharp form
is `∫(v')² ≤ (1/4)∫g²`. The `∫v² ≤ ∫g²` bound IS sharp. Since the gradient bound
is exactly what a future energy estimate would use to absorb the chemotaxis
cross-term, recovering the `1/4` is worth doing before any threshold is quoted
from this route — a factor 4 in that term is not cosmetic.

### The threshold formula validated for general `(m, γ, α)` — and `m` enters only via `α`

Analytically, linearizing the chemotaxis flux at `u = 1` gives
`-χ(u^m v_z)_z ≈ -χ·v_zz`, because `u^m ≈ 1` there and the cross term
`m·u^{m-1}·u_z·v_z` is second order. So the mobility exponent `m` does NOT appear
in the dispersion relation except through `α = m + γ - 1`. Predicted onset:

`χγ = (1 + √α)²`,  `α = m + γ - 1`.

Tested against the FULL nonlinear PDE (general `m`, `γ`, `α`; plateau plus a
small planted dip; spectral integrating-factor; `L = 60`, `T = 80`), at `0.7×`,
`0.9×`, `1.1×`, `1.3×` the predicted onset:

| `m`, `γ` | `α` | predicted `χ` onset | `0.9×` | `1.1×` |
|---|---|---|---|---|
| 1, 1 | 1 | 4.000 | decay (6e-10) | **pattern** (0.47) |
| 2, 1 | 2 | 5.828 | decay (1e-13) | **pattern** (0.24) |
| 3, 1 | 3 | 7.464 | decay (1e-13) | **pattern** (0.16) |
| 1, 2 | 2 | 2.914 | decay (1e-13) | **pattern** (0.35) |

Every case flips between `0.9×` and `1.1×`. This validates the formula in
general, confirms `m` enters only through `α`, and extends the earlier
faithfulness check of our PDE translation from `m = γ = α = 1` to general
exponents.

For contrast, the paper's `χ*` at these parameters is `1.0`, `0.75`, `0.5714`,
`1.0` — i.e. the sufficient condition sits a factor of roughly 3–13 below the
true linear threshold in every case. Again: this bounds how conservative `χ*`
is for the far-left step; it is not a proof about the nonlinear problem, and it
licenses weakening nothing already proved.

### Front geometry: same threshold `4`, and a convective/absolute distinction worth knowing

The tests above used a periodic plateau. Repeating in the actual geometry —
finite differences (no periodicity), Neumann ends, a `tanh` front `1 → 0`, a dip
of depth `0.15` planted at `z = -35` inside the LEFT plateau, `m = γ = α = 1`,
`L = 120`, `T = 200` — and measuring `max|u-1|` over `z < -20`:

At `c = 0`: decay at `χ = 3.0` (`2e-13`) and `χ = 3.9` (`2e-07`); **pattern** at
`χ = 4.5` (`0.53`) and `χ = 6.0` (`0.87`). Same threshold `4` as the periodic
case, now in the front geometry.

**A confound caught before recording.** A first pass ran only at `c = 2.5` and
showed clean far-left convergence even at `χ = 4.5`, i.e. apparently *above* the
threshold. That is not absolute stability: with `c = 2.5` over `T = 200` a
disturbance is advected ~500 units inside a 120-unit domain, so it is swept into
the boundary rather than decaying. Sweeping `c` at fixed `χ = 4.5` confirms it:

`c = 0, 0.25, 0.5, 1.0` all give `max|u-1| ≈ 0.53` (pattern); only `c = 2.5`
gives `4e-14`.

So the plateau is **convectively** unstable but can look stable in a co-moving
window when the drift is fast enough to evacuate the growing mode. Two
consequences: (a) any numerical claim about far-left stability must state its
`c` and check the domain is long enough for the advected mode, or it measures
the boundary condition rather than the equation; (b) this is the numerical face
of the analytic obstacle in the energy route — see below, the drift term
`(c/2)·w(Z)²` at a front cut does not vanish, i.e. the drift PUMPS energy across
the front. Same phenomenon, two guises.

### The sharp linearized dissipation brick landed (audited 2026-07-20)

`ReactionRelativeNonpos / SharpConstant / SharpDissipationCollapse /
SharpLyapunovDissipation.lean` (commits `8b3252a0`, `dc23b47f`, `944362f9`,
`004095d2`). Root build 9986 jobs, 0 sorry, 0 axiom, clean-3, verified here.

This is the "one true brick" from Fable R3: the reason the paper's `χ*` is a
lossy constant, made machine-checked. Contents, audited:

* `reaction_relative_nonpos` + `reaction_relative_eq_zero_iff`: `(u-1)(u^α-1) ≥ 0`
  for `u ≥ 0, α ≥ 1`, with the zero exactly at `u = 1`. This is the coercive,
  UNCONDITIONAL equilibrium-selection term (no `χ`), and the `iff` gives the
  rigidity ("only zero is the constant `1`") rather than just the sign.
* `sharp_constant_le_mode_ratio` + `sharp_constant_eq_mode_ratio_at_sqrt`: both
  the bound `(1+√α)² ≤ (s+α)(s+1)/s` AND equality at `s = √α`, so it is genuinely
  the minimum, not merely a lower bound.
* `sharp_linearized_dissipation_brick`: under the two resolver identities as
  hypotheses, the destabilizing pair collapses to `(χ/γ)(Zz+Z)` and the modewise
  inequality holds iff `χγ ≤ (1+√α)²`, connected to the existing `dispersion`
  object as `dispersion α (χγ) s ≤ 0`. The collapse identity was re-verified
  numerically here (residual `≤ 1e-15`).

**Scope, as written in the docstrings and enforced in the spec:** the sharp
constant `(1+√α)²` is a LINEAR / quadratic-form statement. The atoms are stated
at the quadratic-form level (`W, P, Z, Zz, S` as abstract reals satisfying the
two identities), NOT as an integral inequality on PDE solution objects, and NOT
as nonlinear stability. The nonlinear problem is controlled only on a bounded
plateau with an `[a,b]`-dependent constant that is not `(1+√α)²` except as
`u → 1`. Nothing here claims the far-left convergence we ultimately need.

### Where the program stands (honest map)

PROVED and machine-checked: (i) the rectangle mechanism and its exact wall
`2χγ < α`, with sharpness theorems; (ii) full-window coverage cubics `P`, `Q`;
(iii) the quantified explicit seed (numerically negligible gain, recorded);
(iv) the SHARP Turing threshold `(1+√α)²`, both directions; (v) the resolver
testing identities and the sharp `1/4` gradient bound; (vi) this linearized
dissipation brick tying it together.

NUMERICALLY established (evidence, not proof): the true far-left threshold is
`(1+√α)²`, validated for general `(m,γ,α)` against the full nonlinear PDE; `m`
enters only via `α`; the plateau is convectively unstable above it.

THE HONEST FRONTIER (Fable R3, unbuilt): the nonlinear + half-line/front step.
Its named obstacle is the drift boundary term `(c/2)w(Z)²` at a front cut, which
does not vanish — drift pumps energy across the front (same phenomenon as our
mirror-weight obstruction). The `ω`-limit extraction needs parabolic Schauder
regularity absent from this Mathlib. This is the multi-month piece and it is
deliberately downstream of the bricks above, which stand on their own.

### Nonlinear coercivity: crude constant `4√α·a^(α/2)/b^α`, and where sharpness lives (Fable R4, verified)

For `E = ½∫w²` on the torus, `w = u-1`, the exact dissipation is
`Ė = -∫w_z² + χ∫w_z u^m v_z + ∫w·u(1-u^α)`. Working the chemotaxis term with only
Cauchy-Schwarz + the plateau + the sharp `1/4` gradient bound gives decay under

`χγ ≤ 4√α · a^(α/2) / b^α`   (crude),

which → `4√α` as `[a,b] → {1}`. Verified numerically (0 violations / 200k):
the plateau power-gap bound `|u^γ-1| ≤ γ b^(γ-1)|u-1|`, the reaction coercivity
`u(u-1)(u^α-1) ≥ α a^α (u-1)²`, and the closure itself.

**Crude is NOT sharp for `α > 1`.** `4√α ≤ (1+√α)²` with equality only at `α=1`
(gap `(1-√α)²`): α=1 → 4 = 4; α=4 → 8 vs 9; α=9 → 12 vs 16. The Cauchy-Schwarz
throws away the spectral distribution: it bounds `∫v_z² ≤ ¼∫h²` (sharp only at
`k²=1`) while diffusion helps most at high `k`.

**The sharp constant is already ours.** The sharp inequality
`χγ∫(ψ_z²+ψ_zz²) ≤ ∫(ψ_z²+2ψ_zz²+ψ_zzz²) + α∫(ψ²+2ψ_z²+ψ_zz²)` reduces (Fourier
`x=k²`, or symbolically) to `(x+1)·q(x) ≥ 0`, `q(x) = x²+(1+α-χγ)x+α`, and
`q ≥ 0 ∀x≥0 iff χγ ≤ (1+√α)²`. That `q(x) ≥ 0` is EXACTLY the already-landed
dispersion brick (`dispersion α (χγ) s ≤ 0` unfolds to `q(s) ≥ 0`, checked by
`sympy`). So the sharp modewise content is done; the crude nonlinear closure is
the honest `[a,b]`-level statement, and the gap between them is genuine
Cauchy-Schwarz loss, not a missing lemma.

**Honest nonlinear statement (Fable R4):** for every `χγ < (1+√α)²` there is
`δ*(χγ) > 0` such that any plateau with `max(1-a, b-1) ≤ δ*` gives strict decay,
and `δ* → 0` as `χγ → (1+√α)²`. The spectral gap `min q = α - ((1+α-χγ)/2)² > 0`
is the budget that pays for the `O(δ)` plateau errors. So the margin below the
sharp threshold BUYS the plateau tightness — not the other way round.

**Frame-neutrality (Fable R4, adopted).** The abstract coercivity is frame-neutral
and IS on the critical path (the far-left plateau decay mechanism is identically
this). The torus-SPECIFIC packaging (`∫w·cw_z = 0`, global existence, time-
differentiation) is ORPHAN — on the half-line `∫w·cw_z` is a nonzero front flux.
So: build the coercivity abstractly (done as Rank 1-4 scalar/pointwise bricks),
do NOT invest in torus PDE plumbing, then pivot to the drift-boundary-flux
obstruction lemma — the exact analog of the mirror-weight obstruction we already
formalized, cheap (IBP bookkeeping, no regularity theory), and the true gate on
the half-line result.

### The drift-boundary-flux obstruction, made precise (verified, ready to formalize)

The co-moving half-line energy identity, for `E_Z = ½∫_{-∞}^Z w²` with
`w_t = w_zz + c·w_z + N(w)` and `w, w_z → 0` at `-∞`, is (verified numerically,
residual ~1e-6 at the cut):

`dE_Z/dt = -∫_{-∞}^Z w_z² + ∫_{-∞}^Z w·N + w(Z)·w_z(Z) + (c/2)·w(Z)²`.

The two boundary fluxes at the cut `Z`:
* `(c/2)·w(Z)²` — **the drift flux, `≥ 0` always** (strictly positive when
  `c > 0`, `w(Z) ≠ 0`): confirmed `+0.21` at `c=1`, `+0.54` at `c=2.5` for the
  same profile. This is ANTI-dissipative and is NOT bounded above by the bulk
  `-∫w_z²`. That is the obstruction: the far-left half-line energy is not
  monotone from the bulk dissipation alone.
* `w(Z)·w_z(Z)` — the diffusion flux, sign-indefinite (`-0.066` here).

This is the precise analog of the mirror-weight obstruction
(`not_integrable_leftGrowing_sq_...`): a clean statement that the naive energy
approach cannot close without front-localization to control the cut flux. It is
frame-neutral IBP bookkeeping (the sign fact `(c/2)w² ≥ 0` is trivial; the
identity needs `w` twice-differentiable on `[A,Z]` with decay at `A`), no
regularity theory. It is the true gate on the half-line result and is the next
brick after the plateau coercivity atoms.

### Plateau coercivity atoms landed (audited 2026-07-20)

`PlateauRpowGap / ReactionPlateauCoercive / ResolverPlateauGradient /
PlateauDissipationClosure.lean` (`dd0d8729`, `bc389c9f`, `bd594e1b`, `07fdf42d`).
Root build 9990 jobs, 0 sorry, 0 axiom, clean-3, verified here. Statements match
the specced constants exactly (all three numerically checked, 0/200k):

* `plateau_rpow_sub_one_le`: `|u^γ - 1| ≤ γ·b^(γ-1)·|u-1|` on `[a,b]`.
* `reaction_plateau_coercive`: `u(u-1)(u^α-1) ≥ α·a^α·(u-1)²` — the coercivity
  constant `α a^α → α` as `a → 1`.
* `resolver_deriv_sq_le_plateau`: `∫(v')² ≤ (γ²b^(2(γ-1))/4)∫(u-1)²`, the only
  bridge from the resolver machinery to the nonlinear chemotaxis term. Hypothesis
  interface mirrors the audited resolver identities (plateau + integrability +
  boundary-flux ≤ 0); all inhabitable.
* `plateau_dissipation_closure`: `-D + T + R ≤ 0` under the crude threshold
  `χγ·b^α ≤ 4√α·a^(α/2)`. Docstring states the non-sharpness and the PDE-coupled
  boundary explicitly.

The abstract nonlinear coercivity is now complete at the scalar/pointwise level:
these four atoms + the sharp dispersion brick are everything the far-left plateau
decay mechanism needs that is NOT PDE-coupled. The remaining pieces (time-
derivative identity `Ė = -D+T+R`, plateau invariance `a ≤ u(t) ≤ b`) are the
PDE interface, deliberately not discharged.

### UNIFICATION: rectangle and energy hit the SAME wall — plateau tightening toward 1

The repo already provides the two-sided eventual plateau on the far-left
half-line for `χ < 1`: `wholeLineCauchyGlobal_coMoving_strictlyPositiveAtLeft`
(lower floor) and `wholeLineCauchyGlobal_uniformLimsupLe_MChi_of_chi_pos` (upper
`limsup ≤ MChi`). So plateau INVARIANCE `a ≤ u ≤ b` is NOT the blocker — it is
available. But the available band is WIDE: `a ≈ 0.125` (the χ<1 trap floor),
`b = MChi + 1 ≈ 2.4–3`.

Feeding that available band into the crude energy threshold
`χγ ≤ 4√α·a^(α/2)/b^α` gives (verified):

| `m,γ` | avail `a` | avail `b` | energy thr | rectangle `α/(α+γ)` | `χ*` |
|---|---|---|---|---|---|
| 1,1 | 0.125 | 3.00 | 0.471 | 0.500 | 1.000 |
| 2,1 | 0.125 | 2.73 | 0.095 | 0.667 | 0.750 |
| 3,1 | 0.125 | 2.59 | 0.018 | 0.750 | 0.571 |
| 1,2 | 0.125 | 2.41 | 0.121 | 0.500 | 1.000 |

**The energy method on the AVAILABLE plateau is strictly BELOW the rectangle
threshold — it buys nothing.** Both the rectangle and the energy method need the
plateau TIGHT near 1 (small `δ = max(1-a, b-1)`). This is the exact same
trap-quality wall found in Test B, now seen from the energy side.

**So the entire far-left problem — for every method we have — reduces to ONE
missing ingredient: tightening the eventual plateau toward `{1}`.** This is
cleaner and more optimistic than "multi-month parabolic regularity": the blocker
is not the energy differentiation or the invariant region (both available in
essence), it is getting `a → 1`, `b → 1` eventually.

**And that is a REACTION-driven phenomenon, not a diffusion/chemotaxis one.**
The KPP reaction `u(1-u^α)` drives `u` up toward 1 from below; the chemotaxis is
a perturbation. The concrete route (Fable R2, unbuilt): the nonlocal min
identity `v_zz = v - u^γ` closed by a gradient bootstrap — at an interior min the
chemotaxis contribution is `∝ (v - u^γ)`, controlled by how far `u` is from its
own smoothing, second-order small IF the gradient is controlled; the crux is
showing the bootstrap contracts. THIS is the real crux of Theorem 1.2's
far-left, and it is a specific analytic bootstrap, not open-ended infrastructure.

RESUME HERE: the crux is plateau-tightening via a reaction-driven bootstrap,
`a → 1` eventually, decoupled from the chemotaxis (which is a controlled
perturbation once the plateau is tight). Everything else (coercivity, sharp
threshold, resolver identities, obstruction) is built and machine-checked.

### The crux is the gradient BOOTSTRAP, not a clean comparison (settled 2026-07-20)

The unification reduced everything to "tighten the eventual plateau toward 1."
The tempting clean route: show `a(t) = min_z u` is a sub-solution (nondecreasing).
Numerically, `min u → 1` monotonically in the DYNAMICS (0 decreasing steps / 1000,
χ up to 3.9, single-dip and multi-bump). That looked like a comparison-principle
brick — the repo's home turf.

**But it is NOT a clean sub-solution.** Adversarial test (worst-case over smooth
Gaussian dips, FULL `u_t` including the stabilizing diffusion `u_zz > 0` at the
min): `u_t` at the min is `≥ 0` for small χ (worst `+0.056` at χ=1) but can go
NEGATIVE for a well-chosen smooth dip above an onset (~1.5 for m=γ=α=1 over the
Gaussian family; profile-family-dependent, not a clean constant, and below the
Turing threshold 4). At χ=3, worst `-0.006` at min-value `a≈0.94`. So a narrow-
enough smooth dip can transiently DEEPEN: `min u` is not monotone pointwise.

(An earlier version of this test wrongly DROPPED the `u_zz` diffusion term and
reported failure even at χ=1; caught and corrected — diffusion is exactly what
fills a sharp dip, so omitting it is an unfair, wrong test. The corrected test is
the one above.)

**Why the dynamics still converge monotonically:** the flow's own diffusion
regularizes the profile (a sharp dip fills at rate ~1/width²) faster than
chemotaxis can deepen it, so the actual trajectory never sits at the adversarial
worst-case shape. But "diffusion keeps the profile smooth enough that `v-u` at
the min stays small" IS the gradient bootstrap Fable flagged in R2 — and it is
the genuinely hard analytic core, not a pointwise comparison.

**HONEST FRONTIER (settled).** The far-left crux is: control the gradient/
curvature so that `χ(v-u)(z*) < 1 - u(z*)` at the min throughout the evolution
(equivalently, close the bootstrap: smoothness bounds `v-u`, which keeps the min
rising, which flattens the profile, which preserves smoothness). This is genuine
PDE analysis with no shortcut through the repo's comparison machinery, and no
clean sub-solution exists up to the sharp threshold. Everything cheaper than this
is now built and machine-checked; this is where the honest work remains, and it
should NOT be described as a mechanical brick.

### SETTLED: no cheap/formalizable route beats ~1/2; the gap to the true threshold is genuine nonlinear stability

Triangulated three independent ways, all numerically verified:

| route | cap at α=1 | general |
|---|---|---|
| rectangle | 0.500 | `α/(α+γ)` |
| energy on the AVAILABLE band `[0.125, MChi+1]` | ~0.47 | below rectangle |
| pointwise comparison `χ·b ≤ 1` (b = ceiling) | 0.382 | `< rectangle` |
| TRUE (linear/Turing) threshold | 4.0 | `(1+√α)²` |

Every cheap, formalizable route caps at or below the rectangle's `α/(α+γ)`. There
is no cheap brick that beats it. The entire window from there up to `(1+√α)²` is
genuine nonlinear stability (gradient bootstrap / basin-of-attraction), not a
missing lemma.

**Two Fable-R5 claims were tested and found OVER-stated (verify-don't-transcribe):**
1. R5 predicted an extended flat `ū=0.4` patch would pattern and turn the min
   DOWN at χ=3.9 (its linear-instability-at-frozen-level analysis, rate 0.26).
   TESTED: it did NOT. The mean rose 0.40→1.0 and the min rose 0.30→1.0
   monotonically; the perturbation spread peaked at 0.2245 (only 12% above the
   0.20 seed) then decayed. The reaction drives the mean UP through the unstable
   window faster than the pattern grows — R5 froze the background, which
   over-predicts. So min-monotonicity survives even here.
2. R5's "shippable comparison brick" at `χ·b ≤ 1` gives χ≤0.382 at α=1 — WORSE
   than the rectangle. Not shippable as an improvement.

**Net refinement:** the far-left result is MORE likely true than R5's caution
suggested (the min converges robustly, the intermediate instability is
reaction-transit-suppressed), but NOT more easily provable — whether
min-monotonicity holds is a quantitative RACE between reaction transit and
pattern growth, which is precisely the bootstrap. There is no clean pointwise or
linear shortcut.

**FINAL HONEST FRONTIER for Theorem 1.2 far-left (`χ ∈ (α/(α+γ), (1+√α)²)`):**
prove `u ≡ 1` is the basin-of-attraction limit of the plateau dynamics for all
sub-Turing χ. Concretely this is: (i) local nonlinear stability near `u=1` for
all χ<(1+√α)² (reachable — spectral gap + standard estimates), giving "eventual
inf u → 1 PROVIDED u enters a fixed near-1 neighborhood"; plus (ii) GLOBAL
CAPTURE of the wide available band into that neighborhood — the genuinely hard
core, a basin result, not comparison. Everything cheaper than (ii) is built and
machine-checked. (ii) is the honest open problem; it should be reported as such,
not as a mechanical brick.

### Drift-flux obstruction brick landed (audited 2026-07-20)

`WholeLineCoMovingDriftFluxObstruction.lean` (`f9dc2996`), 8 theorems, root build
9991 jobs, 0 sorry, 0 axiom, clean-3, verified here. Matches the spec exactly:

* `coMoving_halfLine_driftFlux_energy_identity` + `..._of_quenched_left`: the
  co-moving IBP energy identity with explicit boundary terms; with `w A = 0`,
  `w' A = 0` it is `∫w(w''+cw') = -∫(w')² + w Z·w' Z + (c/2)(w Z)²`.
* `sq_endpoint_le_length_mul_integral_deriv_sq`: the Poincaré bound
  `(w Z)² ≤ (Z-A)∫(w')²` for `w A = 0` — reusable.
* `coMoving_driftFlux_net_pos_of_two_div_lt_length` +
  `..._eq_zero_of_length_eq_two_div` + `..._le_dissipation_of_length_le_two_div`:
  the SHARP onset `Z-A = 2/c` (net drift-minus-dissipation `> 0`, `= 0`, `≤ 0`
  above/at/below), matching the numerics exactly.
* `exists_linearRamp_driftFlux_gt_dissipation` + `coMoving_halfLine_driftFlux_obstruction`:
  for `0 < c`, `2/c < Z-A`, and ANY `K`, a quenched-left `C¹` profile exists whose
  drift flux `(c/2)(w Z)²` strictly exceeds the bulk dissipation `∫(w')²`. This is
  the formal obstruction: the co-moving half-line energy is not bulk-controlled on
  a half-line longer than `2/c`; front-localization is required. Precise analog of
  the mirror-weight obstruction (`not_integrable_leftGrowing_sq_...`), and it makes
  rigorous the same phenomenon the front numerics showed (advection sweeping the
  growing mode). Statement is about the METHOD, not the PDE (same framing).

## SESSION-END MAP (2026-07-20)

The cheap-brick layer for Theorem 1.2's far-left is now COMPLETE and
machine-checked. In dependency order:
- rectangle mechanism + proved-sharp wall `2χγ<α`; coverage cubics `P`,`Q`;
- quantified explicit seed (gain measured negligible);
- SHARP Turing threshold `(1+√α)²`, both directions;
- resolver testing identities + sharp `1/4` gradient bound;
- linearized dissipation brick (why `χ*` is a lossy constant);
- frame-neutral plateau coercivity atoms (rpow gap, reaction coercivity,
  resolver→plateau bridge, scalar closure);
- drift-flux obstruction (the half-line gate, sharp at length `2/c`).

The single remaining open problem is (ii) GLOBAL CAPTURE of the wide available
band into the near-1 basin for sub-Turing χ — genuine nonlinear stability, not a
comparison brick, triangulated as beyond every cheap route. This is the honest
frontier of Theorem 1.2 far-left. Resume from this section + `project_shen_fac_chain`
memory.
