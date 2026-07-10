import ShenWork.Paper2.IntervalDivergenceModeIdentity
import ShenWork.PDE.CosineParsevalBridge

/-!
# L2 bound for interval sine coefficients

The divergence-form bootstrap needs a time-uniform `l2` bound for the sine
coefficients of a bounded flux.  This file obtains it from Fourier Bessel on the
doubled interval.  The extension is zero on the left half, so a sine coefficient
is the imaginary part of one doubled-interval Fourier coefficient.
-/

open MeasureTheory

noncomputable section

namespace ShenWork.Paper2.IntervalSineCoeffL2Bound

open ShenWork.IntervalDomain (intervalMeasure intervalSet)
open ShenWork.Paper2.IntervalDivergenceModeIdentity (sineCoeffs)

/-- Extend a real unit-interval function by zero to the left half of the doubled
interval.  Values outside `(-1,1]` are irrelevant to the restricted measure. -/
def zeroLeftExtension (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x => if x ∈ Set.Ioc (0 : ℝ) 1 then (f x : ℂ) else 0

theorem zeroLeftExtension_aestronglyMeasurable
    {f : ℝ → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable (zeroLeftExtension f)
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
  have hmeas : StronglyMeasurable fun x : ℝ => (f x : ℂ) :=
    (Complex.continuous_ofReal.comp hf).stronglyMeasurable
  have hmeas' : StronglyMeasurable
      ((Set.Ioc (0 : ℝ) 1).indicator fun x : ℝ => (f x : ℂ)) :=
    hmeas.indicator measurableSet_Ioc
  have hae : AEStronglyMeasurable
      ((Set.Ioc (0 : ℝ) 1).indicator fun x : ℝ => (f x : ℂ))
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
    hmeas'.aestronglyMeasurable
  have heq : zeroLeftExtension f =
      (Set.Ioc (0 : ℝ) 1).indicator fun x : ℝ => (f x : ℂ) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
    · simp [zeroLeftExtension, hx]
    · simp [zeroLeftExtension, hx]
  rw [heq]
  exact hae

theorem zeroLeftExtension_norm_le
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) (x : ℝ) :
    ‖zeroLeftExtension f x‖ ≤ M := by
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · rw [zeroLeftExtension, if_pos hx, Complex.norm_real, Real.norm_eq_abs]
    exact hf x ⟨hx.1.le, hx.2⟩
  · rw [zeroLeftExtension, if_neg hx, norm_zero]
    exact hM

theorem zeroLeftExtension_memLp_two
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hfcont : Continuous f)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) :
    MemLp (zeroLeftExtension f) 2
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
  exact MemLp.of_bound (zeroLeftExtension_aestronglyMeasurable hfcont) M
    (Filter.Eventually.of_forall (zeroLeftExtension_norm_le hM hf))

private def doubledFourierIntegrand (f : ℝ → ℝ) (n : ℤ) : ℝ → ℂ :=
  fun x => fourier (T := (2 : ℝ)) (-n) (x : AddCircle (2 : ℝ)) •
    zeroLeftExtension f x

private theorem doubledFourierIntegrand_integrable
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hfcont : Continuous f)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) (n : ℤ) :
    Integrable (doubledFourierIntegrand f n)
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
  have hfourier : Continuous fun x : ℝ =>
      fourier (T := (2 : ℝ)) (-n) (x : AddCircle (2 : ℝ)) :=
    (map_continuous _).comp (AddCircle.continuous_mk' _)
  have hmeas : AEStronglyMeasurable (doubledFourierIntegrand f n)
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
    exact hfourier.aestronglyMeasurable.smul
      (zeroLeftExtension_aestronglyMeasurable hfcont)
  refine Integrable.of_bound hmeas M (Filter.Eventually.of_forall fun x => ?_)
  rw [doubledFourierIntegrand, norm_smul]
  have hnorm_fourier :
      ‖fourier (T := (2 : ℝ)) (-n) (x : AddCircle (2 : ℝ))‖ = 1 := by
    rw [fourier_coe_apply, Complex.norm_exp]
    simp
  rw [hnorm_fourier, one_mul]
  exact zeroLeftExtension_norm_le hM hf x

private theorem doubledFourier_im (n : ℤ) (x : ℝ) :
    (fourier (T := (2 : ℝ)) (-n) (x : AddCircle (2 : ℝ))).im =
      -Real.sin ((n : ℝ) * Real.pi * x) := by
  rw [fourier_coe_apply, Complex.exp_im]
  norm_num
  rw [show -(2 * Real.pi * (n : ℝ) * x) / 2 =
      -((n : ℝ) * Real.pi * x) by ring, Real.sin_neg]

/-- A normalized sine coefficient is `-4` times the imaginary part of the
corresponding doubled-interval Fourier coefficient of the zero-left extension. -/
theorem sineCoeffs_eq_neg_four_mul_fourierCoeff_im
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hfcont : Continuous f)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M)
    {n : ℕ} (hn : n ≠ 0) :
    sineCoeffs f n = -4 *
      (fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
        (zeroLeftExtension f) (n : ℤ)).im := by
  have hint := doubledFourierIntegrand_integrable hM hfcont hf (n : ℤ)
  have hcoeff := fourierCoeffOn_eq_integral
    (zeroLeftExtension f) (n : ℤ) (show (-1 : ℝ) < 1 by norm_num)
  have him :
      (∫ x in (-1 : ℝ)..1, doubledFourierIntegrand f (n : ℤ) x).im =
        ∫ x in (-1 : ℝ)..1,
          (-Real.sin ((n : ℝ) * Real.pi * x) *
            if x ∈ Set.Ioc (0 : ℝ) 1 then f x else 0) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    change RCLike.im
        (∫ x in Set.Ioc (-1 : ℝ) 1, doubledFourierIntegrand f (n : ℤ) x ∂volume) = _
    calc
      RCLike.im
          (∫ x in Set.Ioc (-1 : ℝ) 1,
            doubledFourierIntegrand f (n : ℤ) x ∂volume) =
          ∫ x in Set.Ioc (-1 : ℝ) 1,
            RCLike.im (doubledFourierIntegrand f (n : ℤ) x) ∂volume :=
        (integral_im hint).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
        · simp only [doubledFourierIntegrand, zeroLeftExtension, if_pos hx,
            smul_eq_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            mul_zero, RCLike.im_eq_complex_im]
          rw [doubledFourier_im]
          norm_num
        · simp [doubledFourierIntegrand, zeroLeftExtension, hx]
  have hsplit :
      (∫ x in (-1 : ℝ)..1,
          (-Real.sin ((n : ℝ) * Real.pi * x) *
            if x ∈ Set.Ioc (0 : ℝ) 1 then f x else 0)) =
        -(∫ x in (0 : ℝ)..1,
          Real.sin ((n : ℝ) * Real.pi * x) * f x) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hset :
        Set.Ioc (-1 : ℝ) 1 ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioc (0 : ℝ) 1 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨⟨by linarith [hx.1], hx.2⟩, hx⟩
    rw [show (fun x : ℝ =>
        -Real.sin ((n : ℝ) * Real.pi * x) *
          if x ∈ Set.Ioc (0 : ℝ) 1 then f x else 0) =
        (Set.Ioc (0 : ℝ) 1).indicator
          (fun x => -(Real.sin ((n : ℝ) * Real.pi * x) * f x)) by
      funext x
      by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1 <;> simp [hx]]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, hset]
    rw [MeasureTheory.integral_neg]
  have hcoeffD :
      fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (zeroLeftExtension f) (n : ℤ) =
        (2 : ℂ)⁻¹ •
          (∫ x in (-1 : ℝ)..1, doubledFourierIntegrand f (n : ℤ) x) := by
    calc
      fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (zeroLeftExtension f) (n : ℤ) = _ := hcoeff
      _ = (2 : ℂ)⁻¹ •
          (∫ x in (-1 : ℝ)..1, doubledFourierIntegrand f (n : ℤ) x) := by
        norm_num [doubledFourierIntegrand]
        refine Complex.real_smul.trans ?_
        norm_num
        apply intervalIntegral.integral_congr
        intro x hx
        have hleft :
            -(n • (x : AddCircle ((1 : ℝ) - (-1)))) =
              (-(n : ℤ)) • (x : AddCircle ((1 : ℝ) - (-1))) := by
          simp
        have hright :
            -(n • (x : AddCircle (2 : ℝ))) =
              (-(n : ℤ)) • (x : AddCircle (2 : ℝ)) := by
          simp
        dsimp only
        rw [hleft, hright]
        rw [fourier_coe_apply', fourier_coe_apply']
        norm_num
  rw [hcoeffD, smul_eq_mul, Complex.mul_im]
  norm_num
  rw [him, hsplit, sineCoeffs]
  simp only [hn, if_false]
  ring

/-- Bessel's inequality for the normalized interval sine coefficients of a
bounded continuous flux.  The constant is deliberately non-sharp: the
zero-left extension and the full `ℤ` Parseval sum give the uniform bound needed
by the positive-time Duhamel bootstrap. -/
theorem sineCoeffs_sq_summable_and_tsum_le
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hfcont : Continuous f)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ M) :
    Summable (fun n => (sineCoeffs f n) ^ 2) ∧
      ∑' n, (sineCoeffs f n) ^ 2 ≤ 16 * M ^ 2 := by
  let cZ : ℤ → ℝ := fun k =>
    ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
      (zeroLeftExtension f) k‖ ^ 2
  have hL2 := zeroLeftExtension_memLp_two hM hfcont hf
  have hsumZ : Summable cZ := by
    exact (hasSum_sq_fourierCoeffOn
      (hab := show (-1 : ℝ) < 1 by norm_num)
      (f := zeroLeftExtension f) hL2).summable
  have hnonnegZ : ∀ k, 0 ≤ cZ k := fun k => sq_nonneg _
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro m n hmn
    exact Int.ofNat.inj hmn
  have hsumNat : Summable (fun n : ℕ => cZ (n : ℤ)) :=
    hsumZ.comp_injective hinj
  have hdom : ∀ n : ℕ, (sineCoeffs f n) ^ 2 ≤ 16 * cZ (n : ℤ) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [cZ]
    · rw [sineCoeffs_eq_neg_four_mul_fourierCoeff_im hM hfcont hf hn]
      dsimp only [cZ]
      have himsq := Complex.im_sq_le_normSq
        (fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
          (zeroLeftExtension f) (n : ℤ))
      rw [← Complex.sq_norm] at himsq
      nlinarith
  have hmajor : Summable (fun n : ℕ => 16 * cZ (n : ℤ)) :=
    Summable.mul_left 16 hsumNat
  have hsine : Summable (fun n => (sineCoeffs f n) ^ 2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hdom hmajor
  have hnat_le :
      (∑' n : ℕ, cZ (n : ℤ)) ≤ ∑' k : ℤ, cZ k := by
    simpa only [Function.comp_apply] using
      tsum_comp_le_tsum_of_inj hsumZ hnonnegZ hinj
  have hparseval :
      (∑' k : ℤ, cZ k) =
        (2 : ℝ)⁻¹ *
          ∫ x in (-1 : ℝ)..1, ‖zeroLeftExtension f x‖ ^ 2 := by
    have h := tsum_sq_fourierCoeffOn
      (hab := show (-1 : ℝ) < 1 by norm_num)
      (f := zeroLeftExtension f) hL2
    norm_num at h ⊢
    simpa [cZ] using h
  have hnormInt : IntervalIntegrable
      (fun x : ℝ => ‖zeroLeftExtension f x‖ ^ 2) volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hL2.integrable_norm_pow (by norm_num)
  have hconstInt : IntervalIntegrable (fun _ : ℝ => M ^ 2) volume (-1) 1 :=
    continuous_const.intervalIntegrable (-1) 1
  have hintegral :
      (∫ x in (-1 : ℝ)..1, ‖zeroLeftExtension f x‖ ^ 2) ≤ 2 * M ^ 2 := by
    calc
      (∫ x in (-1 : ℝ)..1, ‖zeroLeftExtension f x‖ ^ 2) ≤
          ∫ _x in (-1 : ℝ)..1, M ^ 2 := by
        apply intervalIntegral.integral_mono_on
          (by norm_num : (-1 : ℝ) ≤ 1) hnormInt hconstInt
        intro x hx
        exact pow_le_pow_left₀ (norm_nonneg _)
          (zeroLeftExtension_norm_le hM hf x) 2
      _ = 2 * M ^ 2 := by norm_num
  refine ⟨hsine, ?_⟩
  calc
    (∑' n, (sineCoeffs f n) ^ 2) ≤
        ∑' n : ℕ, 16 * cZ (n : ℤ) :=
      hsine.tsum_le_tsum hdom hmajor
    _ = 16 * ∑' n : ℕ, cZ (n : ℤ) := by rw [tsum_mul_left]
    _ ≤ 16 * ∑' k : ℤ, cZ k :=
      mul_le_mul_of_nonneg_left hnat_le (by norm_num)
    _ = 16 * ((2 : ℝ)⁻¹ *
        ∫ x in (-1 : ℝ)..1, ‖zeroLeftExtension f x‖ ^ 2) := by
      rw [hparseval]
    _ ≤ 16 * ((2 : ℝ)⁻¹ * (2 * M ^ 2)) := by
      gcongr
    _ = 16 * M ^ 2 := by ring

end ShenWork.Paper2.IntervalSineCoeffL2Bound
