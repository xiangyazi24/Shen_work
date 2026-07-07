/-
  Restart-coefficient absolute summability for the B-form route.

  This extracts the homogeneous-plus-Duhamel estimate that was previously
  inlined inside downstream PDE producers.  The theorem is upstream of any
  classical-solution or PDE identity: it uses only a bounded initial coefficient
  family and source time-C1 data.
-/
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalConjugatePicard

open MeasureTheory Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.BFormRestartCoeffSummability

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On
  (DuhamelSourceTimeC1On)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardLimit)

/-- Absolute summability of restart coefficients from window-local source data. -/
theorem localRestartCoeff_abs_summable_of_sourceC1On
    {aInit : ℕ → ℝ} {aB : ℝ → ℕ → ℝ} {T MInit t : ℝ}
    (hsrc : DuhamelSourceTimeC1On aB 0 T)
    (ht : 0 < t) (htT : t ≤ T)
    (haInit : ∀ n, |aInit n| ≤ MInit) :
    Summable (fun n : ℕ => |localRestartCoeff aInit aB t n|) := by
  have hhom : Summable (fun n : ℕ =>
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * aInit n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right MInit)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (haInit n) (Real.exp_pos _).le
  have hduh : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff aB t n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (hsrc.henv_summable.mul_left t)
    unfold duhamelSpectralCoeff
    rw [← Real.norm_eq_abs]
    calc ‖∫ s in (0 : ℝ)..t,
          Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) * aB s n‖
        ≤ hsrc.envelope n * |t - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro s hs
          rw [Set.uIoc_of_le ht.le] at hs
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          calc Real.exp (-(t - s) * unitIntervalCosineEigenvalue n) *
                |aB s n|
              ≤ 1 * |aB s n| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                rw [Real.exp_le_one_iff]
                have hts : 0 ≤ t - s := by linarith [hs.2]
                have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
                  unfold unitIntervalCosineEigenvalue
                  positivity
                nlinarith [mul_nonneg hts hlam]
            _ = |aB s n| := one_mul _
            _ ≤ hsrc.envelope n :=
                hsrc.henv_bound s ⟨le_of_lt hs.1, le_trans hs.2 htT⟩ n
        _ = t * hsrc.envelope n := by
          rw [sub_zero, abs_of_pos ht]
          ring
  exact (hhom.add hduh).of_nonneg_of_le
    (fun n => abs_nonneg _)
    (fun n => by
      simp only [localRestartCoeff]
      exact abs_add_le _ _)

/-- Global-source corollary of `localRestartCoeff_abs_summable_of_sourceC1On`. -/
theorem localRestartCoeff_abs_summable_of_sourceC1
    {aInit : ℕ → ℝ} {aB : ℝ → ℕ → ℝ} {MInit t : ℝ}
    (hsrc : DuhamelSourceTimeC1 aB)
    (ht : 0 < t)
    (haInit : ∀ n, |aInit n| ≤ MInit) :
    Summable (fun n : ℕ => |localRestartCoeff aInit aB t n|) := by
  exact localRestartCoeff_abs_summable_of_sourceC1On
    (hsrc :=
      ShenWork.IntervalDuhamelSourceTimeC1On.DuhamelSourceTimeC1.toOn
        hsrc 0 t (by norm_num))
    ht le_rfl haInit

/-- Conjugate-Picard B-form restart summability from global source time-C1. -/
theorem conjugatePicardLimit_B_global_summable_of_sourceC1
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)))
    (hu₀_bound : ∀ n,
      |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀) :
    ∀ t, 0 < t → t ≤ T →
      Summable (fun n : ℕ =>
        |localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) t n|) := by
  intro t ht _htT
  exact localRestartCoeff_abs_summable_of_sourceC1
    (aInit := cosineCoeffs (intervalDomainLift u₀))
    (aB := bFormSourceCoeffs p (conjugatePicardLimit p u₀ T))
    (MInit := M₀) hsrcB ht hu₀_bound

/-- Bank-facing windowed B-form restart summability from source time-C1 on `[0,T]`. -/
theorem conjugatePicardLimit_B_global_summable_of_sourceC1On
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hsrcB : DuhamelSourceTimeC1On
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) 0 T)
    (hu₀_bound : ∀ n,
      |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀) :
    ∀ t, 0 < t → t ≤ T →
      Summable (fun n : ℕ =>
        |localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p (conjugatePicardLimit p u₀ T)) t n|) := by
  intro t ht htT
  exact localRestartCoeff_abs_summable_of_sourceC1On
    (aInit := cosineCoeffs (intervalDomainLift u₀))
    (aB := bFormSourceCoeffs p (conjugatePicardLimit p u₀ T))
    (T := T) (MInit := M₀) hsrcB ht htT hu₀_bound

#print axioms localRestartCoeff_abs_summable_of_sourceC1On
#print axioms localRestartCoeff_abs_summable_of_sourceC1
#print axioms conjugatePicardLimit_B_global_summable_of_sourceC1
#print axioms conjugatePicardLimit_B_global_summable_of_sourceC1On

end ShenWork.Paper2.BFormRestartCoeffSummability
