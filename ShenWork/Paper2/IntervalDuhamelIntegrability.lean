/-
  ShenWork/Paper2/IntervalDuhamelIntegrability.lean

  Universal Duhamel bounds: work for ALL bounded sources regardless
  of measurability. When the integrand is not integrable, Lean's
  integral_undef gives 0, so bounds hold trivially.
-/
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.PDE.IntervalResolverPositivity

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
/-- Resolver gradient is continuous on R for continuous bounded sources.
Uses: resolverSourceCoeff_re_sq_summable_of_continuousOn + resolver_sineSeries_summable
+ continuous_tsum. This is the same proof as in IntervalResolverPositivity (hg_cont)
but extracted for continuous bounded trajectories (not classical solutions). -/
theorem resolverGradReal_continuous_of_continuousOn
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0:ℝ) 1)) :
    Continuous (fun x : ℝ => ShenWork.Paper2.resolverGradReal p w x) := by
  open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
      ShenWork.IntervalResolverWeakBounds ShenWork.Paper2 in
  -- Source coefficients are ℓ² from continuity (Bessel).
  have hl2 : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p w k).re) ^ 2 := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h
  -- Gradient weight ℓ².
  have hwg := intervalNeumannResolverGradWeight_sq_summable p
  -- Uniform summable majorant: (s_k² + Wg_k²) / 2.
  have hmaj : Summable fun k : ℕ =>
      (((intervalNeumannResolverSourceCoeff p w k).re) ^ 2 +
        (intervalNeumannResolverGradWeight p k) ^ 2) / 2 :=
    (hl2.add hwg).div_const 2
  -- Apply continuous_tsum (Weierstrass M-test).
  unfold resolverGradReal
  refine continuous_tsum (fun k => ?_) hmaj (fun k x => ?_)
  · -- Each term is continuous.
    exact continuous_const.mul (continuous_const.mul
      (Real.continuous_sin.comp (by fun_prop)))
  · -- Pointwise norm bound ≤ majorant.
    rw [Real.norm_eq_abs, abs_mul]
    set s := (intervalNeumannResolverSourceCoeff p w k).re
    set Wg := intervalNeumannResolverGradWeight p k
    have hd : 0 < p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hWgnn : 0 ≤ Wg := intervalNeumannResolverGradWeight_nonneg p k
    have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
        ≤ (k : ℝ) * Real.pi := by
      rw [abs_mul, abs_neg, abs_mul, Nat.abs_cast, abs_of_pos Real.pi_pos]
      calc (k : ℝ) * Real.pi * |Real.sin ((k : ℝ) * Real.pi * x)|
          ≤ (k : ℝ) * Real.pi * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
        _ = (k : ℝ) * Real.pi := mul_one _
    calc |(intervalNeumannResolverCoeff p w k).re| *
            |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
        = |s| / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
            |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))| := by
          rw [resolverCoeff_re_eq, abs_div, abs_of_pos hd]
      _ ≤ |s| / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
            ((k : ℝ) * Real.pi) :=
          mul_le_mul_of_nonneg_left hsin (div_nonneg (abs_nonneg _) hd.le)
      _ = |s| * Wg := by
          rw [show Wg = ((k : ℝ) * Real.pi) /
            (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) from rfl]
          ring
      _ ≤ (s ^ 2 + Wg ^ 2) / 2 := by
          have h := two_mul_le_add_sq |s| Wg
          rw [sq_abs] at h; nlinarith [h]


open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradDuhamelBound (valueDuhamel_sup_bound gradDuhamel_sup_bound)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted chemFluxLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant
  heatGradientLinftyLinftyConstant_nonneg)

noncomputable section

namespace ShenWork.IntervalDuhamelIntegrability

instance : TopologicalSpace intervalDomainPoint := instTopologicalSpaceSubtype

private theorem intervalNeumannFullKernel_pos {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    0 < ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t x y := by
  rw [ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel]
  have hsumA := ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable ht (x - y)
  have hsumB := ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable ht (x + y)
  have hsum : Summable (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ))) :=
    hsumA.add hsumB
  have hle : heatKernel t (x - y + 2 * ((0 : ℤ) : ℝ)) +
        heatKernel t (x + y + 2 * ((0 : ℤ) : ℝ))
      ≤ (∑' k : ℤ, (heatKernel t (x - y + 2 * (k : ℝ)) +
        heatKernel t (x + y + 2 * (k : ℝ)))) := by
    simpa using hsum.sum_le_tsum ({(0 : ℤ)} : Finset ℤ)
      (fun k _hk => add_nonneg (heatKernel_nonneg ht _) (heatKernel_nonneg ht _))
  have hpos : 0 < heatKernel t (x - y + 2 * ((0 : ℤ) : ℝ)) +
      heatKernel t (x + y + 2 * ((0 : ℤ) : ℝ)) :=
    add_pos (heatKernel_pos ht _) (heatKernel_pos ht _)
  exact lt_of_lt_of_le hpos hle

private theorem integrable_of_integrable_intervalNeumannFullKernel_mul
    {t z : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hprod : Integrable
      (fun y : ℝ => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t z y * f y)
      (intervalMeasure 1)) :
    Integrable f (intervalMeasure 1) := by
  let K : ℝ → ℝ := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel t z y
  have hKcont : ContinuousOn K (Set.Icc (0 : ℝ) 1) :=
    ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd ht z
  obtain ⟨y0, _hy0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by constructor <;> norm_num⟩) hKcont
  set δ : ℝ := K y0 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact intervalNeumannFullKernel_pos ht z y0
  have hKinv_meas : AEStronglyMeasurable (fun y : ℝ => (K y)⁻¹) (intervalMeasure 1) := by
    exact (hKcont.inv₀ (fun y hy =>
      ne_of_gt (lt_of_lt_of_le hδpos (isMinOn_iff.mp hmin y hy)))).aestronglyMeasurable
        measurableSet_Icc
  have hf_meas : AEStronglyMeasurable f (intervalMeasure 1) := by
    have hmul_meas : AEStronglyMeasurable
        (fun y : ℝ => (K y)⁻¹ * (K y * f y)) (intervalMeasure 1) :=
      hKinv_meas.mul hprod.aestronglyMeasurable
    exact hmul_meas.congr (by
      rw [Filter.EventuallyEq, intervalMeasure, ShenWork.IntervalDomain.intervalSet,
        MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun y hy => by
        have hKpos : 0 < K y := lt_of_lt_of_le hδpos (isMinOn_iff.mp hmin y hy)
        field_simp [ne_of_gt hKpos])
  have hdom_int : Integrable (fun y : ℝ => δ⁻¹ * ‖K y * f y‖) (intervalMeasure 1) :=
    hprod.norm.const_mul δ⁻¹
  exact hdom_int.mono hf_meas (by
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun y hy => by
      have hKge : δ ≤ K y := isMinOn_iff.mp hmin y hy
      have hKnonneg : 0 ≤ K y := le_trans hδpos.le hKge
      have hdinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
      calc ‖f y‖
          = δ⁻¹ * δ * ‖f y‖ := by field_simp [ne_of_gt hδpos]
        _ ≤ δ⁻¹ * K y * ‖f y‖ := by gcongr
        _ = δ⁻¹ * ‖K y * f y‖ := by
            simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg hKnonneg, mul_assoc]
        _ = ‖δ⁻¹ * ‖K y * f y‖‖ := by
            exact (Real.norm_of_nonneg
              (mul_nonneg hdinv_nonneg (norm_nonneg _))).symm)

theorem intervalFullSemigroupOperator_eq_zero_of_not_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_not : ¬ Integrable f (intervalMeasure 1)) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  rw [MeasureTheory.integral_undef]
  intro hprod
  exact hf_not (integrable_of_integrable_intervalNeumannFullKernel_mul ht hprod)

theorem deriv_intervalFullSemigroupOperator_eq_zero_of_not_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_not : ¬ Integrable f (intervalMeasure 1)) (x : ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x = 0 := by
  have hfun : (fun z : ℝ => intervalFullSemigroupOperator t f z) = fun _ => 0 := by
    funext z
    exact intervalFullSemigroupOperator_eq_zero_of_not_integrable ht hf_not z
  rw [hfun, deriv_const]

/-- Universal value Duhamel bound: works for ALL bounded sources, regardless
of measurability. When the integrand is IntervalIntegrable, uses the standard
semigroup L∞ bound. When not, the interval integral is 0 by integral_undef. -/
theorem valueDuhamel_sup_bound_universal
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {r : ℝ → ℝ → ℝ}
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hr_sup : ∀ s y, |r s y| ≤ Cr) (x : ℝ) :
    |∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s) (r s) x| ≤ T * Cr := by
  by_cases hint : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (r s) x) volume 0 t
  · exact valueDuhamel_sup_bound ht htT hCr hr_sup x hint
  · rw [intervalIntegral.integral_undef hint]
    simp; exact mul_nonneg (le_of_lt (lt_of_lt_of_le ht htT)) hCr

/-- Universal gradient Duhamel bound: works for ALL bounded sources. -/
theorem gradDuhamel_sup_bound_universal
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ) :
    |∫ s in (0:ℝ)..t, deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  by_cases hq_int : ∀ s, Integrable (q s) (intervalMeasure 1)
  · by_cases hg_int : IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x)
        volume 0 t
    · exact gradDuhamel_sup_bound ht htT hq_int hCq hq_sup x hg_int
    · rw [intervalIntegral.integral_undef hg_int, abs_zero]
      exact mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg T)))
        hCq
  · -- Some spatial slice is not integrable, but the time integral
    -- might or might not be IntervalIntegrable.
    by_cases hg_int : IntervalIntegrable
        (fun s : ℝ => deriv
          (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x)
        volume 0 t
    · -- Time-integrable case: bound each slice individually.
      -- For s where q(s) is not integrable, S(t-s)(q s) = 0, deriv = 0.
      -- For s where q(s) is integrable, the pointwise bound applies.
      -- Either way, |deriv| ≤ C_grad * Cq * (t-s)^{-1/2}.
      set Cg := heatGradientLinftyLinftyConstant with hCgdef
      have hCgnn : 0 ≤ Cg := heatGradientLinftyLinftyConstant_nonneg
      have hptw : ∀ s, 0 ≤ s → s < t →
          |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
            ≤ Cg * Cq * (t - s) ^ (-(1/2) : ℝ) := by
        intro s _hs0 hst
        have hts_pos : 0 < t - s := sub_pos.mpr hst
        by_cases hqs : Integrable (q s) (intervalMeasure 1)
        · have h :=
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
              (t := t - s) hts_pos (f := q s) hqs.aestronglyMeasurable
              (Cf := Cq) (hq_sup s) x
          calc |deriv (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
              ≤ Cg * (t - s) ^ (-(1 / 2) : ℝ) * Cq := by simpa [Cg] using h
            _ = Cg * Cq * (t - s) ^ (-(1 / 2) : ℝ) := by ring
        · rw [deriv_intervalFullSemigroupOperator_eq_zero_of_not_integrable hts_pos hqs x,
            abs_zero]
          exact mul_nonneg (mul_nonneg hCgnn hCq)
            (Real.rpow_nonneg (sub_nonneg.mpr hst.le) _)
      have hdom_int : IntervalIntegrable
          (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) volume 0 t :=
        ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
          (Cg * Cq))
      have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
        rw [ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      have hae : (fun s : ℝ => |deriv
            (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|)
          ≤ᵐ[volume.restrict (Set.Icc 0 t)]
          (fun s : ℝ => Cg * Cq * (t - s) ^ (-(1/2) : ℝ)) := by
        refine (ae_restrict_iff' measurableSet_Icc).2 ?_
        filter_upwards [hne] with s hs_ne hs_mem
        exact hptw s hs_mem.1 (lt_of_le_of_ne hs_mem.2 hs_ne)
      calc |∫ s in (0:ℝ)..t, deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x|
          ≤ ∫ s in (0:ℝ)..t, |deriv
              (fun z : ℝ => intervalFullSemigroupOperator (t - s) (q s) z) x| :=
            intervalIntegral.abs_integral_le_integral_abs ht.le
        _ ≤ ∫ s in (0:ℝ)..t, Cg * Cq * (t - s) ^ (-(1/2) : ℝ) :=
            intervalIntegral.integral_mono_ae_restrict ht.le hg_int.abs hdom_int hae
        _ = Cg * Cq * (2 * Real.sqrt t) := by
            rw [intervalIntegral.integral_const_mul,
              ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht.le]
        _ ≤ Cg * (2 * Real.sqrt T) * Cq := by
            have hsqrt : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
            nlinarith [hCgnn, hCq, Real.sqrt_nonneg t, Real.sqrt_nonneg T, hsqrt,
              mul_nonneg hCgnn hCq]
    · rw [intervalIntegral.integral_undef hg_int, abs_zero]
      exact mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg T)))
        hCq


/-- Continuous on compact [0,1] → AEStronglyMeasurable against intervalMeasure. -/
theorem continuousOn_aestronglyMeasurable_intervalMeasure {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0:ℝ) 1)) :
    AEStronglyMeasurable f (intervalMeasure 1) :=
  hf.aestronglyMeasurable measurableSet_Icc

/-- For positive time, the full Neumann heat semigroup maps bounded measurable
data to a function continuous on the compact interval `[0,1]`. -/
theorem continuousOn_intervalFullSemigroupOperator_of_aestronglyMeasurable_bounded
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf) :
    ContinuousOn (fun x : ℝ => intervalFullSemigroupOperator t f x) (Set.Icc (0:ℝ) 1) := by
  exact (continuous_iff_continuousAt.mpr fun x =>
    (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      ht hf_meas hf_bound x).continuousAt).continuousOn

/-- For positive time, the full Neumann heat semigroup maps any bounded input
to a function continuous on the compact interval `[0,1]`.  If the input is not
integrable against `intervalMeasure 1`, the kernel integral is identically zero
under Lean's Bochner integral convention; otherwise the differentiability theorem
for the smooth full kernel gives continuity. -/
theorem continuousOn_intervalFullSemigroupOperator_of_bounded
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    {Cf : ℝ} (hf_bound : ∀ y, |f y| ≤ Cf) :
    ContinuousOn (fun x : ℝ => intervalFullSemigroupOperator t f x) (Set.Icc (0:ℝ) 1) := by
  by_cases hf_int : Integrable f (intervalMeasure 1)
  · exact continuousOn_intervalFullSemigroupOperator_of_aestronglyMeasurable_bounded
      ht hf_int.aestronglyMeasurable hf_bound
  · have hzero : (fun x : ℝ => intervalFullSemigroupOperator t f x) = fun _ => 0 := by
      funext x
      exact intervalFullSemigroupOperator_eq_zero_of_not_integrable ht hf_int x
    rw [hzero]
    exact continuousOn_const

/-- The lift of a continuous function on intervalDomainPoint is
AEStronglyMeasurable against intervalMeasure 1, because intervalMeasure 1
only sees Icc 0 1, where the lift agrees with the continuous subtype function. -/
theorem intervalDomainLift_aestronglyMeasurable_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable (intervalDomainLift f) (intervalMeasure 1) := by
  -- intervalMeasure 1 = volume.restrict (Icc 0 1)
  -- ContinuousOn.aestronglyMeasurable needs ContinuousOn on Icc 0 1
  -- continuousOn_iff_continuous_restrict: ContinuousOn ↔ Continuous (restrict)
  -- Set.restrict (Icc 0 1) (intervalDomainLift f) = f (subtype identity)
  have hcont_on : ContinuousOn (intervalDomainLift f) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift f) = f := by
      ext ⟨x, hx⟩
      simp [Set.restrict, intervalDomainLift, hx]; rfl
    rw [heq]
    exact hf
  exact hcont_on.aestronglyMeasurable measurableSet_Icc

theorem logisticLifted_integrable_of_continuous
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (hw : ∀ x, |w x| ≤ M) (hM : 0 ≤ M)
    (hcont : Continuous w) :
    Integrable (logisticLifted p w) (intervalMeasure 1) := by
  have hsrc_cont : Continuous (ShenWork.IntervalDomainExistence.intervalLogisticSource p w) := by
    unfold ShenWork.IntervalDomainExistence.intervalLogisticSource
    exact hcont.mul
      (continuous_const.sub
        (continuous_const.mul (hcont.rpow_const (fun _ => Or.inr p.hα.le))))
  have hmeas : AEStronglyMeasurable (logisticLifted p w) (intervalMeasure 1) := by
    unfold logisticLifted
    exact intervalDomainLift_aestronglyMeasurable_of_continuous hsrc_cont
  have hMpos : 0 < M + 1 := by linarith
  have hw' : ∀ x, |w x| ≤ M + 1 := fun x => by linarith [hw x]
  exact ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
    hmeas
    (ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p hMpos hw')



/-- The resolver VALUE (cosine tsum) is continuous on ℝ for continuous sources.
Same pattern as `resolverGradReal_continuous_of_continuousOn` but for
`cos(kπx)` (bounded by 1) — simpler since no kπ factor. -/
theorem resolverValueReal_continuous_of_continuousOn
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0:ℝ) 1)) :
    Continuous (fun x : ℝ ↦ ∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverCoeff p w k).re *
        unitIntervalCosineMode k x) := by
  open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
      ShenWork.IntervalResolverWeakBounds ShenWork.Paper2 in
  have hl2 : Summable fun k : ℕ ↦
      ((intervalNeumannResolverSourceCoeff p w k).re) ^ 2 := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h
  have hw := intervalNeumannResolverWeight_sq_summable p
  have hmaj : Summable fun k : ℕ ↦
      (((intervalNeumannResolverSourceCoeff p w k).re) ^ 2 +
        (intervalNeumannResolverWeight p k) ^ 2) / 2 :=
    (hl2.add hw).div_const 2
  refine continuous_tsum (fun k ↦ ?_) hmaj (fun k x ↦ ?_)
  · exact continuous_const.mul (by unfold unitIntervalCosineMode; fun_prop)
  · rw [Real.norm_eq_abs, abs_mul]
    set s := (intervalNeumannResolverSourceCoeff p w k).re
    set W := intervalNeumannResolverWeight p k
    have hd : 0 < p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hWnn : 0 ≤ W := intervalNeumannResolverWeight_nonneg p k
    have hcos : |unitIntervalCosineMode k x| ≤ 1 := by
      unfold unitIntervalCosineMode; exact Real.abs_cos_le_one _
    calc |(intervalNeumannResolverCoeff p w k).re| * |unitIntervalCosineMode k x|
        = |s| / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
            |unitIntervalCosineMode k x| := by
          rw [resolverCoeff_re_eq, abs_div, abs_of_pos hd]
      _ ≤ |s| / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) * 1 :=
          mul_le_mul_of_nonneg_left hcos (div_nonneg (abs_nonneg _) hd.le)
      _ = |s| * W := by
          rw [show W = 1 / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k)
            from rfl]; ring
      _ ≤ (s ^ 2 + W ^ 2) / 2 := by
          have h := two_mul_le_add_sq |s| W
          rw [sq_abs] at h; nlinarith [h]

/-- For a trajectory with continuous nonneg slices, the lifted chemotaxis flux is
spatially integrable. Uses: resolver value/gradient continuity (cosine/sine tsum),
resolver positivity (1+R ≥ 1), compactness of [0,1]. -/
theorem chemFluxLifted_integrable_of_continuous
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (_hw : ∀ x, |w x| ≤ M) (_hM : 0 ≤ M)
    (hcont : Continuous w)
    (hw_nonneg : ∀ x, 0 ≤ w x) :
    Integrable (chemFluxLifted p w) (intervalMeasure 1) := by
  open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
      ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
      ShenWork.IntervalNeumannFullKernel ShenWork.IntervalResolverPositivity in
  -- Step 1: ContinuousOn of lift(w) on [0,1]
  have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift w) = w := by
      ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
    rw [this]; exact hcont
  -- Step 2: resolverGradReal is Continuous on ℝ
  have hgrad_cont : Continuous (fun x : ℝ ↦ resolverGradReal p w x) :=
    resolverGradReal_continuous_of_continuousOn p hcont_on
  -- Step 3: resolver VALUE tsum is Continuous on ℝ
  have hval_cont : Continuous (fun x : ℝ ↦ ∑' k : ℕ,
      (intervalNeumannResolverCoeff p w k).re * unitIntervalCosineMode k x) :=
    resolverValueReal_continuous_of_continuousOn p hcont_on
  -- Step 4: R ≥ 0 on the subtype (nonneg source + heat semigroup positivity)
  have hR_nonneg : ∀ x : intervalDomainPoint, 0 ≤ intervalNeumannResolverR p w x := by
    -- Construct continuous nonneg extension of source to ℝ
    have hcont_src : Continuous (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) :=
      continuous_const.mul (hcont.rpow_const (fun x ↦ Or.inr p.hγ.le))
    set clip : ℝ → intervalDomainPoint := fun x ↦
      ⟨max 0 (min x 1), le_max_left 0 _, max_le (by norm_num) (min_le_right x 1)⟩
    have hclip_cont : Continuous clip :=
      Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _
    set f : ℝ → ℝ := (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) ∘ clip
    have hf_cont : Continuous f := hcont_src.comp hclip_cont
    have hf_nonneg : ∀ y, 0 ≤ f y := fun y ↦
      mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
    -- f agrees with source on [0,1] ⇒ same cosine coefficients
    have hf_coeff : ∀ k, cosineCoeffs f k =
        (intervalNeumannResolverSourceCoeff p w k).re := by
      intro k
      have hsrc_eq : (intervalNeumannResolverSourceCoeff p w k).re =
          cosineCoeffs (fun x ↦ p.ν * intervalDomainLift w x ^ p.γ) k := by
        simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
      rw [hsrc_eq]
      exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
        simp only [f, Function.comp, clip]
        have hclip_eq : max 0 (min x 1) = x := by
          rw [min_eq_left hx.2, max_eq_right hx.1]
        simp only [hclip_eq, intervalDomainLift, dif_pos (Set.mem_Icc.mpr hx)]) k
    have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
      have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
      simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
      exact h.congr (fun k ↦ by rw [hf_coeff])
    exact fun x ↦ intervalNeumannResolverR_nonneg_of_nonneg_source
      hf_cont hf_nonneg hf_coeff hâ x
  -- Step 5: denominator (1 + R)^β > 0
  have hden_pos : ∀ x : intervalDomainPoint,
      0 < (1 + intervalNeumannResolverR p w x) ^ p.β :=
    fun x ↦ Real.rpow_pos_of_pos (by linarith [hR_nonneg x]) p.β
  -- Step 6: ContinuousOn of the flux on [0,1]
  have hflux_cont_on : ContinuousOn (chemFluxLifted p w) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    show Continuous (Set.restrict (Set.Icc (0:ℝ) 1) (chemFluxLifted p w))
    have heq : Set.restrict (Set.Icc (0:ℝ) 1) (chemFluxLifted p w) =
        fun x : ↑(Set.Icc (0:ℝ) 1) ↦
          w x * resolverGradReal p w x.1
            / (1 + intervalNeumannResolverR p w x) ^ p.β := by
      ext ⟨x, hx⟩
      simp only [Set.restrict, chemFluxLifted, intervalDomainLift, dif_pos hx]
      congr 1
    rw [heq]
    refine Continuous.div ?_ ?_ (fun x ↦ ne_of_gt (hden_pos x))
    · -- numerator: w(x) * resolverGrad(x.1)
      exact (hcont.comp (continuous_subtype_val.subtype_mk _)).mul
        (hgrad_cont.comp continuous_subtype_val)
    · -- denominator: (1 + R(x))^β
      refine (continuous_const.add ?_).rpow_const (fun x ↦ Or.inr p.hβ)
      exact hval_cont.comp continuous_subtype_val
  have hmeas : AEStronglyMeasurable (chemFluxLifted p w) (intervalMeasure 1) :=
    hflux_cont_on.aestronglyMeasurable measurableSet_Icc
  -- Step 7: Bounded (ContinuousOn on compact ⇒ bounded; outside [0,1] flux = 0)
  have hbdd : ∃ C : ℝ, ∀ y, |chemFluxLifted p w y| ≤ C := by
    have hC_bdd : BddAbove ((fun y ↦ ‖chemFluxLifted p w y‖) '' Set.Icc (0:ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn (hflux_cont_on.norm)).bddAbove
    refine ⟨max (sSup ((λ y ↦ ‖chemFluxLifted p w y‖) '' Set.Icc (0:ℝ) 1)) 0, fun y ↦ ?_⟩
    by_cases hy : y ∈ Set.Icc (0:ℝ) 1
    · have hmem : ‖chemFluxLifted p w y‖ ∈
          ((λ y ↦ ‖chemFluxLifted p w y‖) '' Set.Icc (0:ℝ) 1) := ⟨y, hy, rfl⟩
      have hle := le_csSup hC_bdd hmem
      rw [Real.norm_eq_abs] at hle
      exact hle.trans (le_max_left _ _)
    · simp only [chemFluxLifted, intervalDomainLift, dif_neg hy, zero_mul, zero_div, abs_zero]
      exact le_max_right _ _
  obtain ⟨C, hC⟩ := hbdd
  exact ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound hmeas hC
/-- Resolver gradient is continuous on R for continuous bounded sources.

Uses: resolverSourceCoeff_re_sq_summable_of_continuousOn + resolver_sineSeries_summable
+ continuous_tsum. This is the same proof as in IntervalResolverPositivity (hg_cont)
but extracted for continuous bounded trajectories (not classical solutions). -/
theorem resolverGradReal_continuous_of_continuousOn
    (p : CM2Params) {w : intervalDomainPoint → ℝ}
    (hcont : ContinuousOn (intervalDomainLift w) (Set.Icc (0:ℝ) 1)) :
    Continuous (fun x : ℝ => ShenWork.Paper2.resolverGradReal p w x) := by
  open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
      ShenWork.IntervalResolverWeakBounds ShenWork.Paper2 in
  -- Source coefficients are ℓ² from continuity (Bessel).
  have hl2 : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p w k).re) ^ 2 := by
    have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont
    simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
    exact h
  -- Gradient weight ℓ².
  have hwg := intervalNeumannResolverGradWeight_sq_summable p
  -- Uniform summable majorant: (s_k² + Wg_k²) / 2.
  have hmaj : Summable fun k : ℕ =>
      (((intervalNeumannResolverSourceCoeff p w k).re) ^ 2 +
        (intervalNeumannResolverGradWeight p k) ^ 2) / 2 :=
    (hl2.add hwg).div_const 2
  -- Apply continuous_tsum (Weierstrass M-test).
  unfold resolverGradReal
  refine continuous_tsum (fun k => ?_) hmaj (fun k x => ?_)
  · -- Each term is continuous.
    exact continuous_const.mul (continuous_const.mul
      (Real.continuous_sin.comp (by fun_prop)))
  · -- Pointwise norm bound ≤ majorant.
    rw [Real.norm_eq_abs, abs_mul]
    set s := (intervalNeumannResolverSourceCoeff p w k).re
    set Wg := intervalNeumannResolverGradWeight p k
    have hd : 0 < p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hWgnn : 0 ≤ Wg := intervalNeumannResolverGradWeight_nonneg p k
    have hsin : |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
        ≤ (k : ℝ) * Real.pi := by
      rw [abs_mul, abs_neg, abs_mul, Nat.abs_cast, abs_of_pos Real.pi_pos]
      calc (k : ℝ) * Real.pi * |Real.sin ((k : ℝ) * Real.pi * x)|
          ≤ (k : ℝ) * Real.pi * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
        _ = (k : ℝ) * Real.pi := mul_one _
    calc |(intervalNeumannResolverCoeff p w k).re| *
            |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))|
        = |s| / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
            |(-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x))| := by
          rw [resolverCoeff_re_eq, abs_div, abs_of_pos hd]
      _ ≤ |s| / (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) *
            ((k : ℝ) * Real.pi) :=
          mul_le_mul_of_nonneg_left hsin (div_nonneg (abs_nonneg _) hd.le)
      _ = |s| * Wg := by
          rw [show Wg = ((k : ℝ) * Real.pi) /
            (p.μ + ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue k) from rfl]
          ring
      _ ≤ (s ^ 2 + Wg ^ 2) / 2 := by
          have h := two_mul_le_add_sq |s| Wg
          rw [sq_abs] at h; nlinarith [h]


open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator intervalFullSemigroupOperator_hasDerivAt_fst) in
/-- Semigroup output is continuous for bounded AEStronglyMeasurable source. -/
theorem intervalFullSemigroupOperator_continuous_of_bounded
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1)) :
    Continuous (fun x => intervalFullSemigroupOperator t f x) :=
  continuous_iff_continuousAt.mpr fun x =>
    (intervalFullSemigroupOperator_hasDerivAt_fst ht hf_meas hf x).continuousAt


/-- The chemotaxis flux has a uniform sup bound for continuous bounded nonneg sources.
This extracts the compactness argument from chemFluxLifted_integrable_of_continuous. -/
theorem chemFluxLifted_bounded_of_continuous
    (p : CM2Params) {w : intervalDomainPoint -> Real} {M : Real}
    (hw : forall x, |w x| <= M) (hM : 0 <= M)
    (hcont : Continuous w) (hw_nonneg : forall x, 0 <= w x) :
    exists C_Q : Real, 0 <= C_Q /\ forall y, |chemFluxLifted p w y| <= C_Q := by
  open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
      ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
      ShenWork.IntervalNeumannFullKernel ShenWork.IntervalResolverPositivity in
  -- Step 1: ContinuousOn of lift(w) on [0,1]
  have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift w) = w := by
      ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
    rw [this]; exact hcont
  -- Step 2: resolverGradReal is Continuous on ℝ
  have hgrad_cont : Continuous (fun x : ℝ ↦ resolverGradReal p w x) :=
    resolverGradReal_continuous_of_continuousOn p hcont_on
  -- Step 3: resolver VALUE tsum is Continuous on ℝ
  have hval_cont : Continuous (fun x : ℝ ↦ ∑' k : ℕ,
      (intervalNeumannResolverCoeff p w k).re * unitIntervalCosineMode k x) :=
    resolverValueReal_continuous_of_continuousOn p hcont_on
  -- Step 4: R ≥ 0 on the subtype
  have hR_nonneg : ∀ x : intervalDomainPoint, 0 ≤ intervalNeumannResolverR p w x := by
    have hcont_src : Continuous (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) :=
      continuous_const.mul (hcont.rpow_const (fun x ↦ Or.inr p.hγ.le))
    set clip : ℝ → intervalDomainPoint := fun x ↦
      ⟨max 0 (min x 1), le_max_left 0 _, max_le (by norm_num) (min_le_right x 1)⟩
    have hclip_cont : Continuous clip :=
      Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _
    set f : ℝ → ℝ := (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) ∘ clip
    have hf_cont : Continuous f := hcont_src.comp hclip_cont
    have hf_nonneg : ∀ y, 0 ≤ f y := fun y ↦
      mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
    have hf_coeff : ∀ k, cosineCoeffs f k =
        (intervalNeumannResolverSourceCoeff p w k).re := by
      intro k
      have hsrc_eq : (intervalNeumannResolverSourceCoeff p w k).re =
          cosineCoeffs (fun x ↦ p.ν * intervalDomainLift w x ^ p.γ) k := by
        simp [cosineCoeffs, intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
      rw [hsrc_eq]
      exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
        simp only [f, Function.comp, clip]
        have hclip_eq : max 0 (min x 1) = x := by
          rw [min_eq_left hx.2, max_eq_right hx.1]
        simp only [hclip_eq, intervalDomainLift, dif_pos (Set.mem_Icc.mpr hx)]) k
    have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
      have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
      simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
      exact h.congr (fun k ↦ by rw [hf_coeff])
    exact fun x ↦ intervalNeumannResolverR_nonneg_of_nonneg_source
      hf_cont hf_nonneg hf_coeff hâ x
  -- Step 5: denominator (1 + R)^β > 0
  have hden_pos : ∀ x : intervalDomainPoint,
      0 < (1 + intervalNeumannResolverR p w x) ^ p.β :=
    fun x ↦ Real.rpow_pos_of_pos (by linarith [hR_nonneg x]) p.β
  -- Step 6: ContinuousOn of the flux on [0,1]
  have hflux_cont_on : ContinuousOn (chemFluxLifted p w) (Set.Icc (0:ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    show Continuous (Set.restrict (Set.Icc (0:ℝ) 1) (chemFluxLifted p w))
    have heq : Set.restrict (Set.Icc (0:ℝ) 1) (chemFluxLifted p w) =
        fun x : ↑(Set.Icc (0:ℝ) 1) ↦
          w x * resolverGradReal p w x.1
            / (1 + intervalNeumannResolverR p w x) ^ p.β := by
      ext ⟨x, hx⟩
      simp only [Set.restrict, chemFluxLifted, intervalDomainLift, dif_pos hx]
      congr 1
    rw [heq]
    refine Continuous.div ?_ ?_ (fun x ↦ ne_of_gt (hden_pos x))
    · exact (hcont.comp (continuous_subtype_val.subtype_mk _)).mul
        (hgrad_cont.comp continuous_subtype_val)
    · refine (continuous_const.add ?_).rpow_const (fun x ↦ Or.inr p.hβ)
      exact hval_cont.comp continuous_subtype_val
  -- Step 7: Bounded by compactness
  have hC_bdd : BddAbove ((fun y ↦ ‖chemFluxLifted p w y‖) '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn (hflux_cont_on.norm)).bddAbove
  refine ⟨max (sSup ((fun y ↦ ‖chemFluxLifted p w y‖) '' Set.Icc (0:ℝ) 1)) 0,
    le_max_right _ _, fun y ↦ ?_⟩
  by_cases hy : y ∈ Set.Icc (0:ℝ) 1
  · have hmem : ‖chemFluxLifted p w y‖ ∈
        ((fun y ↦ ‖chemFluxLifted p w y‖) '' Set.Icc (0:ℝ) 1) := ⟨y, hy, rfl⟩
    have hle := le_csSup hC_bdd hmem
    rw [Real.norm_eq_abs] at hle
    exact hle.trans (le_max_left _ _)
  · simp only [chemFluxLifted, intervalDomainLift, dif_neg hy, zero_mul, zero_div, abs_zero]
    exact le_max_right _ _




open ShenWork.IntervalNeumannFullKernel in
/-- **Kernel product integrability.** If `f` is integrable and bounded by `M`,
and the kernel `K(τ,x,·)` is nonneg and integrable (both proved for τ > 0),
then `K(τ,x,·) * f(·)` is integrable against `intervalMeasure 1`. -/
theorem kernel_mul_integrable_of_source_integrable
    {τ : ℝ} (hτ : 0 < τ) (x : ℝ) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1))
    {M : ℝ} (hM : 0 ≤ M) (hf_bdd : ∀ y, |f y| ≤ M) :
    Integrable (fun y => intervalNeumannFullKernel τ x y * f y)
      (intervalMeasure 1) := by
  have hK_int := intervalNeumannFullKernel_integrable hτ x
  have hK_nn := fun y => intervalNeumannFullKernel_nonneg hτ x y
  refine Integrable.mono (hK_int.const_mul M)
    (hK_int.aestronglyMeasurable.mul hf_int.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn y), abs_of_nonneg hM]
  calc intervalNeumannFullKernel τ x y * |f y|
      ≤ intervalNeumannFullKernel τ x y * M :=
        mul_le_mul_of_nonneg_left (hf_bdd y) (hK_nn y)
    _ = M * intervalNeumannFullKernel τ x y := mul_comm _ _

/-- **Per-slice semigroup difference L∞ bound.** For τ > 0, if f and g are
integrable and bounded, then |S(τ)(f) x - S(τ)(g) x| ≤ sup|f - g|.
Uses semigroup linearity (kernel integrability) + L∞ contraction. -/
theorem intervalFullSemigroupOperator_diff_Linfty_of_integrable
    {τ : ℝ} (hτ : 0 < τ) {f g : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1))
    (hg_int : Integrable g (intervalMeasure 1))
    {Mf : ℝ} (hMf : 0 ≤ Mf) (hf_bdd : ∀ y, |f y| ≤ Mf)
    {Mg : ℝ} (hMg : 0 ≤ Mg) (hg_bdd : ∀ y, |g y| ≤ Mg)
    {D : ℝ} (hD : 0 ≤ D) (hdiff : ∀ y, |f y - g y| ≤ D) (x : ℝ) :
    |intervalFullSemigroupOperator τ f x
      - intervalFullSemigroupOperator τ g x| ≤ D := by
  have hKf := kernel_mul_integrable_of_source_integrable hτ x hf_int hMf hf_bdd
  have hKg := kernel_mul_integrable_of_source_integrable hτ x hg_int hMg hg_bdd
  calc |intervalFullSemigroupOperator τ f x - intervalFullSemigroupOperator τ g x|
      = |intervalFullSemigroupOperator τ (fun y => f y - g y) x| :=
        congr_arg abs (ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_sub
          hKf hKg).symm
    _ ≤ D := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        hτ hD hdiff x

/-- Semigroup of bounded jointly-measurable source is IntervalIntegrable.
Given `Measurable (fun p : ℝ × ℝ => f p.1 p.2)` (joint measurability of source)
and `∀ s y, |f s y| ≤ C` (uniform bound), the time integrand
`s ↦ S(t-s)(f(s)) x` is IntervalIntegrable on `[0, t]`. -/
theorem valueDuhamel_intervalIntegrable_of_joint_measurable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ → ℝ}
    (hf_meas : Measurable (Function.uncurry f))
    {C : ℝ} (hC : 0 ≤ C) (hf_bdd : ∀ s y, |f s y| ≤ C) (x : ℝ) :
    IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (t - s) (f s) x) volume 0 t := by
  open ShenWork.IntervalNeumannFullKernel in
  rw [intervalIntegrable_iff]
  -- Step 1: AEStronglyMeasurable of the time integrand on uIoc 0 t
  have hmeas : AEStronglyMeasurable
      (fun s => intervalFullSemigroupOperator (t - s) (f s) x)
      (volume.restrict (Set.uIoc 0 t)) := by
    -- S(t-s)(f s) x = ∫ y, K(t-s,x,y) * f(s,y) d(intervalMeasure 1)
    -- by definition of intervalFullSemigroupOperator
    have hfun_eq : (fun s => intervalFullSemigroupOperator (t - s) (f s) x)
        = (fun s => ∫ y, intervalNeumannFullKernel (t - s) x y * f s y
            ∂(intervalMeasure 1)) := by
      ext s; rfl
    rw [hfun_eq]
    -- Apply AEStronglyMeasurable.integral_prod_right'
    -- Need: AEStronglyMeasurable (uncurry g) on product measure
    -- where g(s,y) = K(t-s,x,y) * f(s,y)
    refine (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (f := fun p : ℝ × ℝ => intervalNeumannFullKernel (t - p.1) x p.2 * f p.1 p.2)
      ?_).mono_measure (Measure.restrict_mono (Set.subset_univ _) le_rfl)
    -- Prove: AEStronglyMeasurable on volume.prod (intervalMeasure 1)
    -- K is continuous in (s,y) for all s (smooth Gaussian kernel)
    -- f is Measurable (hypothesis)
    -- Product of measurable functions is measurable → AEStronglyMeasurable
    have hK_nn_all : ∀ τ z, 0 ≤ heatKernel τ z :=
      fun τ z => mul_nonneg (div_nonneg one_pos.le (Real.sqrt_nonneg _)) (Real.exp_pos _).le
    have hK_meas : Measurable (fun p : ℝ × ℝ =>
        intervalNeumannFullKernel (t - p.1) x p.2) := by
      unfold intervalNeumannFullKernel
      set F : ℤ → ℝ × ℝ → ℝ := fun k p =>
        heatKernel (t - p.1) (x - p.2 + 2 * ↑k) +
        heatKernel (t - p.1) (x + p.2 + 2 * ↑k)
      have hF_meas : ∀ k, Measurable (F k) := fun k =>
        (by unfold heatKernel; fun_prop :
          Measurable (fun p : ℝ × ℝ => heatKernel (t - p.1) (x - p.2 + 2 * ↑k))).add
        (by unfold heatKernel; fun_prop :
          Measurable (fun p : ℝ × ℝ => heatKernel (t - p.1) (x + p.2 + 2 * ↑k)))
      have hF_nn : ∀ k p, 0 ≤ F k p := fun k p =>
        add_nonneg (hK_nn_all _ _) (hK_nn_all _ _)
      have hE_meas : Measurable (fun p =>
          ∑' k : ℤ, ENNReal.ofReal (F k p)) :=
        Measurable.ennreal_tsum (fun k => (hF_meas k).ennreal_ofReal)
      have hfun_eq : (fun p => ∑' k : ℤ, F k p) =
          (fun p => (∑' k : ℤ, ENNReal.ofReal (F k p)).toReal) := by
        funext p
        rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
        congr 1; ext k
        exact (ENNReal.toReal_ofReal (hF_nn k p)).symm
      rw [hfun_eq]; exact hE_meas.ennreal_toReal
    exact (hK_meas.aestronglyMeasurable.mul hf_meas.aestronglyMeasurable)
  -- Step 2: bounded a.e. by C (L∞ contraction for t - s > 0, which is a.e. on Ioc 0 t)
  have hbdd : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
      ‖intervalFullSemigroupOperator (t - s) (f s) x‖ ≤ C := by
    rw [Set.uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc]
    have hne : ∀ᵐ s ∂volume, s ≠ t := by
      rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Real.norm_eq_abs]
    have hts : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs_ne)
    exact intervalFullSemigroupOperator_Linfty_bound hts hC (hf_bdd s) x
  -- Step 3: IntegrableOn from bounded + AEStronglyMeasurable on finite measure set
  have hfin : volume (Set.uIoc 0 t) < ⊤ := by
    rw [Set.uIoc_of_le ht.le, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  exact IntegrableOn.of_bound hfin hmeas C hbdd

/-- Gradient semigroup of bounded jointly-measurable source is IntervalIntegrable.
Same chain as `valueDuhamel_intervalIntegrable_of_joint_measurable` but for
the gradient integrand `s ↦ deriv (S(t-s)(f s)) x`. -/
theorem gradDuhamel_intervalIntegrable_of_joint_measurable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ → ℝ}
    (hf_meas : Measurable (Function.uncurry f))
    {C : ℝ} (hC : 0 ≤ C) (hf_bdd : ∀ s y, |f s y| ≤ C) (x : ℝ) :
    IntervalIntegrable
      (fun s => deriv (fun z => intervalFullSemigroupOperator (t - s) (f s) z) x)
      volume 0 t := by
  open ShenWork.IntervalNeumannFullKernel in
  open ShenWork.IntervalGradDuhamelBound in
  rw [intervalIntegrable_iff]
  -- Per-slice integrability of the source
  have hf_slice_int : ∀ s, Integrable (f s) (intervalMeasure 1) := fun s =>
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      ((hf_meas.comp measurable_prodMk_left).aestronglyMeasurable)
      (hf_bdd s)
  -- Step 1: AEStronglyMeasurable of the gradient integrand on uIoc 0 t
  have hmeas : AEStronglyMeasurable
      (fun s => deriv (fun z => intervalFullSemigroupOperator (t - s) (f s) z) x)
      (volume.restrict (Set.uIoc 0 t)) :=
    intervalFullSemigroupOperator_s_dependent_deriv_aestronglyMeasurable_x₀
      ht hf_meas.aestronglyMeasurable hf_slice_int (fun s => hf_bdd s) x
  -- Step 2: Domination by Cg * C * (t-s)^(-1/2), which is integrable
  set Cg := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hdom_int : IntegrableOn
      (fun s => Cg * (t - s) ^ (-(1/2) : ℝ) * C) (Set.uIoc 0 t) volume := by
    rw [show (fun s => Cg * (t - s) ^ (-(1/2) : ℝ) * C) =
        (fun s => (Cg * C) * (t - s) ^ (-(1/2) : ℝ)) from by ext; ring]
    rw [← intervalIntegrable_iff]
    exact (intervalIntegrable_sub_rpow_neg_half t).const_mul (Cg * C)
  -- a.e. on uIoc 0 t, s < t (singleton {t} is null), giving the pointwise bound
  have hne : ∀ᵐ s ∂volume, s ≠ t := by
    rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]; exact Real.volume_singleton
  have hae : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)),
      ‖(fun s => deriv (fun z => intervalFullSemigroupOperator (t - s) (f s) z) x) s‖
        ≤ (fun s => Cg * (t - s) ^ (-(1/2) : ℝ) * C) s := by
    rw [Set.uIoc_of_le ht.le, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hne] with s hs_ne hs_mem
    rw [Real.norm_eq_abs]
    exact intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
      hs_mem.1.le (lt_of_le_of_ne hs_mem.2 hs_ne) (hf_slice_int s) hC (hf_bdd s) x
  -- Conclude: AEStronglyMeasurable + dominated by integrable → IntegrableOn
  exact Integrable.mono' hdom_int.integrable hmeas hae

end ShenWork.IntervalDuhamelIntegrability