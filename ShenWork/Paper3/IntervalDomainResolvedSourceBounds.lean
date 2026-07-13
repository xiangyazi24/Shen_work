/-
  Sup and gradient bounds for an arbitrary real elliptic source coefficient
  sequence.  This is the resolver estimate needed for the exact linear and
  quadratic source pieces separately; unlike the older Lipschitz theorem it
  does not require representing the source as a difference of two powers.
-/
import ShenWork.Paper3.IntervalDomainLogisticRemainderCoeffs

namespace ShenWork.Paper3

open Real
open ShenWork.PDE
open ShenWork.PDE.SectorialOperator
open ShenWork.HeatKernelGradientEstimates

noncomputable section

/-- Value reconstruction after applying the diagonal Neumann resolvent to a
real source coefficient sequence. -/
def paper3ResolvedSourceValue
    (p : CM2Params) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, a k * intervalNeumannResolverWeight p k *
    unitIntervalCosineMode k x

/-- Gradient reconstruction after applying the same resolvent. -/
def paper3ResolvedSourceGradient
    (p : CM2Params) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, a k * intervalNeumannResolverGradWeight p k *
    (-Real.sin ((k : ℝ) * Real.pi * x))

lemma paper3ResolvedSourceValue_series_summable
    (p : CM2Params) {a : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2) (x : ℝ) :
    Summable fun k : ℕ =>
      a k * intervalNeumannResolverWeight p k *
        unitIntervalCosineMode k x := by
  let m : ℕ → ℝ := fun k =>
    intervalNeumannResolverWeight p k * unitIntervalCosineMode k x
  have hm : Summable fun k => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (unitIntervalCosineMode k x) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    dsimp [m]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hcos
  have hprod : Summable fun k : ℕ => a k * m k := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_
      ((ha.add hm).mul_left (1 / 2))
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (a k), sq_abs (m k),
      sq_nonneg (|a k| - |m k|)]
  convert hprod using 1
  funext k
  dsimp [m]
  ring

lemma paper3ResolvedSourceGradient_series_summable
    (p : CM2Params) {a : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2) (x : ℝ) :
    Summable fun k : ℕ =>
      a k * intervalNeumannResolverGradWeight p k *
        (-Real.sin ((k : ℝ) * Real.pi * x)) := by
  let m : ℕ → ℝ := fun k =>
    intervalNeumannResolverGradWeight p k *
      (-Real.sin ((k : ℝ) * Real.pi * x))
  have hm : Summable fun k => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hsin : (-Real.sin ((k : ℝ) * Real.pi * x)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_neg]
      exact Real.abs_sin_le_one _
    dsimp [m]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hsin
  have hprod : Summable fun k : ℕ => a k * m k := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_
      ((ha.add hm).mul_left (1 / 2))
    intro k
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (a k), sq_abs (m k),
      sq_nonneg (|a k| - |m k|)]
  convert hprod using 1
  funext k
  dsimp [m]
  ring

theorem paper3ResolvedSourceValue_add
    (p : CM2Params) {a b : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2)
    (hb : Summable fun k => (b k) ^ 2) (x : ℝ) :
    paper3ResolvedSourceValue p (fun k => a k + b k) x =
      paper3ResolvedSourceValue p a x + paper3ResolvedSourceValue p b x := by
  unfold paper3ResolvedSourceValue
  rw [← (paper3ResolvedSourceValue_series_summable p ha x).tsum_add
    (paper3ResolvedSourceValue_series_summable p hb x)]
  refine tsum_congr (fun k => ?_)
  ring

theorem paper3ResolvedSourceGradient_add
    (p : CM2Params) {a b : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2)
    (hb : Summable fun k => (b k) ^ 2) (x : ℝ) :
    paper3ResolvedSourceGradient p (fun k => a k + b k) x =
      paper3ResolvedSourceGradient p a x +
        paper3ResolvedSourceGradient p b x := by
  unfold paper3ResolvedSourceGradient
  rw [← (paper3ResolvedSourceGradient_series_summable p ha x).tsum_add
    (paper3ResolvedSourceGradient_series_summable p hb x)]
  refine tsum_congr (fun k => ?_)
  ring

/-- Arbitrary `ell^2` real source coefficients give a pointwise resolver value
bound by the `ell^2` resolvent weight. -/
theorem paper3ResolvedSourceValue_abs_le
    (p : CM2Params) {a : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2) (x : ℝ) :
    |paper3ResolvedSourceValue p a x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        Real.sqrt (∑' k : ℕ, (a k) ^ 2) := by
  let m : ℕ → ℝ := fun k =>
    intervalNeumannResolverWeight p k * unitIntervalCosineMode k x
  have hm : Summable fun k => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (unitIntervalCosineMode k x) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    dsimp [m]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hcos
  have hCS := real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq ha hm
  have hmWeight : Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm.tsum_le_tsum ?_ (intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hcos : (unitIntervalCosineMode k x) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact Real.abs_cos_le_one _
    dsimp [m]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hcos
  rw [paper3ResolvedSourceValue]
  have hseries :
      (fun k : ℕ => a k * intervalNeumannResolverWeight p k *
        unitIntervalCosineMode k x) = fun k => a k * m k := by
    funext k
    dsimp [m]
    ring
  rw [hseries]
  calc
    |∑' k : ℕ, a k * m k| ≤
        Real.sqrt (∑' k : ℕ, (a k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ Real.sqrt (∑' k : ℕ, (a k) ^ 2) *
        Real.sqrt (∑' k : ℕ,
          (intervalNeumannResolverWeight p k) ^ 2) :=
      mul_le_mul_of_nonneg_left hmWeight (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑' k : ℕ,
          (intervalNeumannResolverWeight p k) ^ 2) *
        Real.sqrt (∑' k : ℕ, (a k) ^ 2) := by ring

/-- Corresponding pointwise gradient bound. -/
theorem paper3ResolvedSourceGradient_abs_le
    (p : CM2Params) {a : ℕ → ℝ}
    (ha : Summable fun k => (a k) ^ 2) (x : ℝ) :
    |paper3ResolvedSourceGradient p a x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        Real.sqrt (∑' k : ℕ, (a k) ^ 2) := by
  let m : ℕ → ℝ := fun k =>
    intervalNeumannResolverGradWeight p k *
      (-Real.sin ((k : ℝ) * Real.pi * x))
  have hm : Summable fun k => (m k) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_
      (intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hsin : (-Real.sin ((k : ℝ) * Real.pi * x)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_neg]
      exact Real.abs_sin_le_one _
    dsimp [m]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hsin
  have hCS := real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq ha hm
  have hmWeight : Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
      Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm.tsum_le_tsum ?_
      (intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hsin : (-Real.sin ((k : ℝ) * Real.pi * x)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one, abs_neg]
      exact Real.abs_sin_le_one _
    dsimp [m]
    rw [mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) hsin
  rw [paper3ResolvedSourceGradient]
  have hseries :
      (fun k : ℕ => a k * intervalNeumannResolverGradWeight p k *
        (-Real.sin ((k : ℝ) * Real.pi * x))) = fun k => a k * m k := by
    funext k
    dsimp [m]
    ring
  rw [hseries]
  calc
    |∑' k : ℕ, a k * m k| ≤
        Real.sqrt (∑' k : ℕ, (a k) ^ 2) *
          Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ Real.sqrt (∑' k : ℕ, (a k) ^ 2) *
        Real.sqrt (∑' k : ℕ,
          (intervalNeumannResolverGradWeight p k) ^ 2) :=
      mul_le_mul_of_nonneg_left hmWeight (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑' k : ℕ,
          (intervalNeumannResolverGradWeight p k) ^ 2) *
        Real.sqrt (∑' k : ℕ, (a k) ^ 2) := by ring

#print axioms paper3ResolvedSourceValue_abs_le
#print axioms paper3ResolvedSourceGradient_abs_le
#print axioms paper3ResolvedSourceValue_add
#print axioms paper3ResolvedSourceGradient_add

end

end ShenWork.Paper3
