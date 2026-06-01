/-
  ShenWork/Paper2/IntervalDuhamelIntegrability.lean

  Universal Duhamel bounds: work for ALL bounded sources regardless
  of measurability. When the integrand is not integrable, Lean's
  integral_undef gives 0, so bounds hold trivially.
-/
import ShenWork.PDE.IntervalGradDuhamelBound
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.Paper2.IntervalGradientDuhamelMap

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
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

private theorem intervalFullSemigroupOperator_eq_zero_of_not_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_not : ¬ Integrable f (intervalMeasure 1)) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  rw [MeasureTheory.integral_undef]
  intro hprod
  exact hf_not (integrable_of_integrable_intervalNeumannFullKernel_mul ht hprod)

private theorem deriv_intervalFullSemigroupOperator_eq_zero_of_not_integrable
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



/-- For a trajectory with continuous slices, the lifted chemotaxis flux is
spatially integrable at each time. The flux is a composition of
continuous functions (w, resolverGradReal, resolverR) — each continuous
when w is continuous — so the composition is continuous, hence its
lift is AEStronglyMeasurable, hence integrable (bounded on finite measure). -/
theorem chemFluxLifted_integrable_of_continuous
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {M : ℝ}
    (_hw : ∀ x, |w x| ≤ M) (_hM : 0 ≤ M)
    (hcont : Continuous w) :
    Integrable (chemFluxLifted p w) (intervalMeasure 1) := by
  -- The flux is bounded (each factor is bounded: |lift w| ≤ M, resolverGradReal bounded
  -- by Cauchy-Schwarz on the ℓ² source coefficients, denominator ≥ 1).
  -- Boundedness + AEStronglyMeasurable on finite measure → Integrable.
  -- AEStronglyMeasurable follows from the flux being a composition of continuous functions
  -- on the subtype (w continuous → lift continuous on Icc → resolver continuous on Icc).
  -- The resolver continuity uses resolverSourceCoeff_re_sq_summable_of_continuousOn +
  -- continuous_tsum (Weierstrass M-test on the cosine/sine series).
  sorry


open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator_hasDerivAt_fst) in
/-- Semigroup output is continuous for bounded AEStronglyMeasurable source. -/
theorem intervalFullSemigroupOperator_continuous_of_bounded
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M)
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1)) :
    Continuous (fun x => intervalFullSemigroupOperator t f x) :=
  continuous_iff_continuousAt.mpr fun x =>
    (intervalFullSemigroupOperator_hasDerivAt_fst ht hf_meas hf x).continuousAt


end ShenWork.IntervalDuhamelIntegrability
