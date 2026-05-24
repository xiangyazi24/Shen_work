import ShenWork.PDE.HeatKernelLpEstimates
import ShenWork.PDE.CosineParsevalBridge

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ShenWork.HeatKernelGradientEstimates

open ShenWork.IntervalDomain

/-! ## Unit-interval Neumann spectral heat-gradient estimates -/

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

