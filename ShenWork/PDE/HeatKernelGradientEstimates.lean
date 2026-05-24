import ShenWork.PDE.HeatKernelLpEstimates
import ShenWork.PDE.CosineParsevalBridge

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.HeatKernelGradientEstimates

open ShenWork.IntervalDomain
open ShenWork.CosineParsevalBridge

/-! ## Unit-interval Neumann spectral heat-gradient estimates -/

/-- Raw, unnormalized cosine coefficient on the unit interval. -/
def unitIntervalCosineRawCoeff (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * f x

/-- Bessel inequality for the positive-frequency raw cosine coefficients,
transported from AddCircle Fourier Parseval through the even-reflection
bridge. -/
theorem unitIntervalCosineRawCoeff_tsum_sq_le_integral
    {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1)
    (hL2 :
      MemLp (unitIntervalEvenReflection f) 2
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)))
    (hf_sq : IntervalIntegrable (fun x : ℝ => ‖f x‖ ^ 2) volume 0 1) :
    Summable (fun n : ℕ => ‖unitIntervalCosineRawCoeff f n‖ ^ 2) ∧
      (∑' n : ℕ, ‖unitIntervalCosineRawCoeff f n‖ ^ 2) ≤
        ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 := by
  let cZ : ℤ → ℝ := fun k =>
    ‖fourierCoeffOn (show (-1 : ℝ) < 1 by norm_num)
      (unitIntervalEvenReflection f) k‖ ^ 2
  have hsumZ : Summable cZ := by
    exact (hasSum_sq_fourierCoeffOn
      (hab := show (-1 : ℝ) < 1 by norm_num)
      (f := unitIntervalEvenReflection f) hL2).summable
  have hnonneg : ∀ k : ℤ, 0 ≤ cZ k := by
    intro k
    exact sq_nonneg _
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro m n hmn
    exact Int.ofNat.inj hmn
  have hraw_eq :
      (fun n : ℕ => ‖unitIntervalCosineRawCoeff f n‖ ^ 2) =
        fun n : ℕ => cZ (n : ℤ) := by
    funext n
    have hcoeff :=
      unitIntervalEvenReflection_fourierCoeffOn_eq_cosineCoeff
        (f := f) hf (n : ℤ)
    simpa [unitIntervalCosineRawCoeff, cZ] using
      congrArg (fun z : ℂ => ‖z‖) hcoeff.symm
  have hsumNat : Summable (fun n : ℕ => cZ (n : ℤ)) :=
    hsumZ.comp_injective hinj
  refine ⟨?_, ?_⟩
  · simpa [hraw_eq] using hsumNat
  · rw [hraw_eq]
    calc
      (∑' n : ℕ, cZ (n : ℤ)) ≤ ∑' k : ℤ, cZ k :=
        tsum_comp_le_tsum_of_inj hsumZ hnonneg hinj
      _ = ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 :=
        unitIntervalEvenReflection_fourier_parseval_unit_mass hL2 hf_sq

/-- The pointwise cosine heat-gradient `L² → L∞` estimate as an `LpSeminorm`
bound on the unit interval. -/
theorem unitIntervalCosineHeatGradientValue_L2_Linfty_lpNorm_smoothing
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    lpNorm (fun x => unitIntervalCosineHeatGradientValue t a x)
        ∞ (intervalMeasure 1) ≤
      (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
        unitIntervalCosineL2TsumNorm a := by
  let g : ℝ → ℝ := fun x => unitIntervalCosineHeatGradientValue t a x
  let C : ℝ :=
    (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
      unitIntervalCosineL2TsumNorm a
  have hpoint_abs :
      ∀ x, |g x| ≤ C := by
    intro x
    exact unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing
      (t := t) ht hrecip ha x
  have hpoint_norm : ∀ x, ‖g x‖ ≤ C := by
    intro x
    simpa [g, Real.norm_eq_abs] using hpoint_abs x
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (div_nonneg (Real.sqrt_nonneg _) ht.le)
      (Real.sqrt_nonneg _)
  by_cases hg_meas : AEStronglyMeasurable g (intervalMeasure 1)
  · have hess :
        eLpNormEssSup g (intervalMeasure 1) ≤ ENNReal.ofReal C :=
      eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hpoint_norm)
    calc
      lpNorm g ∞ (intervalMeasure 1)
          = (eLpNorm g ∞ (intervalMeasure 1)).toReal := by
            exact (toReal_eLpNorm hg_meas).symm
      _ = (eLpNormEssSup g (intervalMeasure 1)).toReal := by
            rw [eLpNorm_exponent_top]
      _ ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
      _ = C := ENNReal.toReal_ofReal hC_nonneg
      _ =
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm a := rfl
  · have hlp_zero : lpNorm g ∞ (intervalMeasure 1) = 0 := by
      simp [lpNorm, hg_meas]
    calc
      lpNorm g ∞ (intervalMeasure 1) = 0 := hlp_zero
      _ ≤ C := hC_nonneg
      _ =
          (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
            unitIntervalCosineL2TsumNorm a := rfl

end ShenWork.HeatKernelGradientEstimates
