import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.PDE.HeatKernelGradientEstimates

/-!
# A far-time `L¹ → L∞` bound for the interval conjugate kernel

The near-diagonal conjugate Duhamel estimate is integrable when its source is
bounded in `L∞`.  For the complementary time interval we only need a crude
positive-lag estimate.  This file obtains it directly from the cosine series:
the differentiated heat weight is bounded by a reciprocal-cubic summable
majorant, while the normalized sine coefficient is controlled by twice the
`L¹` mass of the source.
-/

open MeasureTheory Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper2.IntervalConjugateKernelL1FarBound

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries
  (intervalSineInner intervalConjugateKernelOperator_cosineSeries)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.HeatKernelGradientEstimates

/-- The scalar frequency occurring in the conjugate cosine series has the
same reciprocal-cubic majorant as the differentiated heat series. -/
theorem frequency_exp_le_reciprocal_cube
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (n : ℝ) * Real.pi *
        Real.exp (-t * unitIntervalCosineEigenvalue n) ≤
      (4 / (t ^ 2 * Real.pi ^ 3)) *
        unitIntervalCosineReciprocalCubeTerm n := by
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalCosineReciprocalCubeTerm,
      unitIntervalCosineEigenvalue]
  · have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hpi : 0 < Real.pi := Real.pi_pos
    let lambda : ℝ := unitIntervalCosineEigenvalue n
    let z : ℝ := t * lambda
    have hz : 0 ≤ z := by
      dsimp [z, lambda, unitIntervalCosineEigenvalue]
      positivity
    have hgauss : z ^ 2 * Real.exp (-z) ≤ 4 :=
      real_sq_mul_exp_neg_le_four hz
    have hscale :
        0 ≤ 1 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3) := by
      positivity
    calc
      (n : ℝ) * Real.pi *
            Real.exp (-t * unitIntervalCosineEigenvalue n) =
          (1 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3)) *
            (z ^ 2 * Real.exp (-z)) := by
              dsimp [z, lambda, unitIntervalCosineEigenvalue]
              field_simp [ne_of_gt ht, ne_of_gt hpi, ne_of_gt hnpos]
      _ ≤ (1 / (t ^ 2 * Real.pi ^ 3 * (n : ℝ) ^ 3)) * 4 :=
        mul_le_mul_of_nonneg_left hgauss hscale
      _ = (4 / (t ^ 2 * Real.pi ^ 3)) *
            unitIntervalCosineReciprocalCubeTerm n := by
              dsimp [unitIntervalCosineReciprocalCubeTerm]
              field_simp [ne_of_gt ht, ne_of_gt hpi, ne_of_gt hnpos]

/-- The normalized sine coefficient is controlled by twice the interval
`L¹` mass. -/
theorem intervalSineInner_abs_le_two_integral_abs
    {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 1) (n : ℕ) :
    |intervalSineInner g n| ≤
      2 * ∫ y in (0 : ℝ)..1, |g y| := by
  unfold intervalSineInner
  by_cases hn : n = 0
  · simp [hn, intervalIntegral.integral_nonneg]
  · simp only [hn, if_false]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      |∫ y in (0 : ℝ)..1,
          Real.sin ((n : ℝ) * Real.pi * y) * g y| ≤
          ∫ y in (0 : ℝ)..1,
            |Real.sin ((n : ℝ) * Real.pi * y) * g y| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ y in (0 : ℝ)..1, |g y| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · have hsin : Continuous
              (fun y : ℝ => Real.sin ((n : ℝ) * Real.pi * y)) := by
            fun_prop
          exact (hg.continuousOn_mul hsin.continuousOn).abs
        · exact hg.abs
        · intro y _
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)

/-- Crude positive-lag smoothing for the conjugate kernel.  The `t⁻²` rate
is intentionally non-sharp; on a time interval separated from the diagonal it
is sufficient for the critical two-scale argument. -/
theorem intervalConjugateKernelOperator_abs_le_L1_far
    {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg : Continuous g) (x : ℝ) :
    |intervalConjugateKernelOperator t g x| ≤
      (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        ∫ y in (0 : ℝ)..1, |g y| := by
  let I : ℝ := ∫ y in (0 : ℝ)..1, |g y|
  let B : ℝ := 8 * I / (t ^ 2 * Real.pi ^ 3)
  have hgint : IntervalIntegrable g volume 0 1 :=
    hg.intervalIntegrable 0 1
  have hI : 0 ≤ I := by
    dsimp [I]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun y _ => abs_nonneg (g y))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmajor : Summable (fun n : ℕ =>
      B * unitIntervalCosineReciprocalCubeTerm n) :=
    unitIntervalCosineReciprocalCubeTerm_summable.mul_left B
  have hterm : ∀ n : ℕ,
      ‖(Real.exp (-t * unitIntervalCosineEigenvalue n) *
          (((n : ℝ) * Real.pi) * intervalSineInner g n)) *
            cosineMode n x‖ ≤
        B * unitIntervalCosineReciprocalCubeTerm n := by
    intro n
    have hfreq := frequency_exp_le_reciprocal_cube ht n
    have hsine := intervalSineInner_abs_le_two_integral_abs hgint n
    have hcos : |cosineMode n x| ≤ 1 := by
      simp only [cosineMode]
      exact Real.abs_cos_le_one _
    have hfreq0 :
        0 ≤ (n : ℝ) * Real.pi *
          Real.exp (-t * unitIntervalCosineEigenvalue n) := by positivity
    have hmaj0 :
        0 ≤ (4 / (t ^ 2 * Real.pi ^ 3)) *
          unitIntervalCosineReciprocalCubeTerm n :=
      mul_nonneg (by positivity)
        (unitIntervalCosineReciprocalCubeTerm_nonneg n)
    have hsine0 : 0 ≤ 2 * I := mul_nonneg (by norm_num) hI
    have hprod :
        ((n : ℝ) * Real.pi *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) *
            |intervalSineInner g n| ≤
          ((4 / (t ^ 2 * Real.pi ^ 3)) *
            unitIntervalCosineReciprocalCubeTerm n) * (2 * I) :=
      mul_le_mul hfreq (by simpa [I] using hsine)
        (abs_nonneg _) hmaj0
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) * Real.pi)]
    calc
      Real.exp (-t * unitIntervalCosineEigenvalue n) *
              ((n : ℝ) * Real.pi * |intervalSineInner g n|) *
            |cosineMode n x| ≤
          ((((n : ℝ) * Real.pi *
              Real.exp (-t * unitIntervalCosineEigenvalue n)) *
            |intervalSineInner g n|) * |cosineMode n x|) := by
              ring_nf
              exact le_rfl
      _ ≤
          (((4 / (t ^ 2 * Real.pi ^ 3)) *
              unitIntervalCosineReciprocalCubeTerm n) *
            (2 * I)) * 1 := by
              exact mul_le_mul hprod hcos (abs_nonneg _)
                (mul_nonneg hmaj0 hsine0)
      _ = B * unitIntervalCosineReciprocalCubeTerm n := by
            dsimp [B]
            ring
  have hnorm : Summable (fun n : ℕ =>
      ‖(Real.exp (-t * unitIntervalCosineEigenvalue n) *
          (((n : ℝ) * Real.pi) * intervalSineInner g n)) *
            cosineMode n x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmajor
  rw [intervalConjugateKernelOperator_cosineSeries ht hg x]
  calc
    |∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          (((n : ℝ) * Real.pi) * intervalSineInner g n)) *
            cosineMode n x| =
        ‖∑' n : ℕ,
          (Real.exp (-t * unitIntervalCosineEigenvalue n) *
            (((n : ℝ) * Real.pi) * intervalSineInner g n)) *
              cosineMode n x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ,
        ‖(Real.exp (-t * unitIntervalCosineEigenvalue n) *
          (((n : ℝ) * Real.pi) * intervalSineInner g n)) *
            cosineMode n x‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ,
        B * unitIntervalCosineReciprocalCubeTerm n :=
      hnorm.tsum_le_tsum hterm hmajor
    _ = (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) * I := by
      dsimp [B, unitIntervalCosineGradientL1LinftyConstant,
        unitIntervalCosineReciprocalCubeTrace]
      rw [tsum_mul_left]
      ring
    _ = (unitIntervalCosineGradientL1LinftyConstant / t ^ 2) *
        ∫ y in (0 : ℝ)..1, |g y| := rfl

#print axioms frequency_exp_le_reciprocal_cube
#print axioms intervalSineInner_abs_le_two_integral_abs
#print axioms intervalConjugateKernelOperator_abs_le_L1_far

end ShenWork.Paper2.IntervalConjugateKernelL1FarBound

end
