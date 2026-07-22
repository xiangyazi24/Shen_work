import ShenWork.Paper2.IntervalFractionalSubordinationFullQ
import ShenWork.Paper2.IntervalFullKernelFullQGradient

/-!
# Fractional full-`q` Neumann divergence smoothing

The conjugate-kernel operator in the Paper 2 interval development is the
Neumann divergence heat operator.  Splitting the heat time in half gives

`A^sigma exp (-t A / 2) (B_N(t/2) f)`,

where `A = -Delta_N`.  The first factor is controlled by derivative
subordination and the second by the already proved full-`q` conjugate-kernel
estimate.  This yields the expected order `t^(-sigma-1/2)` without multiplier
theory.
-/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

namespace ShenWork.Paper2.IntervalFractionalSubordinationDivergenceFullQ

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalConjugateKernelJointMeas
open ShenWork.IntervalConjugateCosineSeries
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper2.IntervalFullKernelFullQGradient
open ShenWork.Paper2.IntervalFullKernelFullQGenerator
open ShenWork.Paper2.IntervalFractionalSubordinationScalar
open ShenWork.Paper2.IntervalFractionalSubordinationFullQ

/-! ## The missing `MemLp` packaging for the conjugate kernel -/

/-- The physical conjugate-kernel/divergence heat operator maps every finite
`L^q`, `1 < q < infinity`, back into `L^q`.  The existing norm theorem only
stated a real `lpNorm` inequality; this lemma supplies the membership needed
to feed its output into the fractional Neumann operator.

For membership alone a crude positive-time uniform kernel bound suffices.  It
is used only as an existence bound; the sharp `t^(-1/2)` estimate below still
comes from `intervalConjugateKernelOperator_lpNorm_le`. -/
theorem intervalConjugateKernelOperator_memLp
    {t q r : ℝ} (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    MemLp (intervalConjugateKernelOperator t f)
      (ENNReal.ofReal q) (intervalMeasure 1) := by
  let μ : Measure ℝ := intervalMeasure 1
  let B : ℝ := ∑' k : ℤ,
    (heatGradWindowBound t 0 2 k + heatGradWindowBound t 0 2 k)
  have h1q : (1 : ENNReal) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hrq.symm.lt.le
  have hfint : Integrable f μ :=
    memLp_one_iff_integrable.mp (hf.mono_exponent h1q)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun k => by
      unfold heatGradWindowBound heatGradPointwiseBound
      positivity
  have hbound : ∀ᵐ x ∂μ,
      ‖intervalConjugateKernelOperator t f x‖ ≤
        B * ∫ y, ‖f y‖ ∂μ := by
    change ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hxabs : |x| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [Real.norm_eq_abs,
      intervalConjugateKernelOperator_eq_neg_derivSeries_integral,
      abs_neg]
    calc
      |∫ y, intervalNeumannFullKernelDerivSeries t y x * f y ∂μ| ≤
          ∫ y, ‖intervalNeumannFullKernelDerivSeries t y x * f y‖ ∂μ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, B * ‖f y‖ ∂μ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y => norm_nonneg _
        · exact hfint.norm.const_mul B
        · change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), _
          rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
          refine Filter.Eventually.of_forall fun y hy => ?_
          change ‖intervalNeumannFullKernelDerivSeries t y x * f y‖ ≤
            B * ‖f y‖
          rw [norm_mul, Real.norm_eq_abs]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have hyabs : |y| ≤ 1 :=
            abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
          rw [intervalNeumannFullKernelDerivSeries_eq_deriv_fst ht]
          exact abs_deriv_intervalNeumannFullKernel_fst_le_const
            ht 0 (by simpa using hyabs) hxabs
      _ = B * ∫ y, ‖f y‖ ∂μ := by
        rw [MeasureTheory.integral_const_mul]
  apply MemLp.of_bound
    (intervalConjugateKernelOperator_aestronglyMeasurable
      hf.aestronglyMeasurable)
    (B * ∫ y, ‖f y‖ ∂μ)
  simpa [μ] using hbound

/-! ## Fractional divergence and its full-`q` estimate -/

/-- The fractional Neumann divergence heat operator, factored at half time.
The proof argument records the Banach `Lp` range for the fractional factor. -/
def intervalFractionalNeumannDivergenceLp
    (sigma t q : ℝ) (hq : 1 ≤ ENNReal.ofReal q) (f : ℝ → ℝ) :
    Lp ℝ (ENNReal.ofReal q) (intervalMeasure 1) :=
  intervalFractionalNeumannLp sigma (t / 2) q hq
    (intervalConjugateKernelOperator (t / 2) f)

/-- **Fractional full-`q` divergence estimate.**  For `0 < sigma < 1` and
every conjugate pair `r,q`, the half-time factorization has order
`t^(-sigma-1/2)` (written exactly as `(t/2)^(-sigma-1/2)`). -/
theorem intervalFractionalNeumannDivergenceLp_norm_le
    {sigma t q r : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    ‖intervalFractionalNeumannDivergenceLp sigma t q
        (by simpa using ENNReal.ofReal_le_ofReal hrq.symm.lt.le) f‖ ≤
      heatGradientLinftyLinftyConstant *
        fractionalSubordinationConstant sigma * fullGeneratorKernelConstant *
        (1 / (1 - sigma) + 1 / sigma) *
        (t / 2) ^ (-sigma - 1 / 2) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  have hh : 0 < t / 2 := by positivity
  have hgmem : MemLp (intervalConjugateKernelOperator (t / 2) f)
      (ENNReal.ofReal q) (intervalMeasure 1) :=
    intervalConjugateKernelOperator_memLp hh hrq hf
  have hfrac := intervalFractionalNeumannLp_norm_le
    hsigma0 hsigma1 hh hrq hgmem
  have hgrad := intervalConjugateKernelOperator_lpNorm_le hh hrq hf
  have hleft : 0 ≤
      fractionalSubordinationConstant sigma * fullGeneratorKernelConstant *
        (1 / (1 - sigma) + 1 / sigma) * (t / 2) ^ (-sigma) := by
    have hc : 0 ≤ fractionalSubordinationConstant sigma :=
      (fractionalSubordinationConstant_pos hsigma1).le
    have hsplit : 0 ≤ 1 / (1 - sigma) + 1 / sigma := by
      exact add_nonneg (one_div_nonneg.mpr (by linarith))
        (one_div_nonneg.mpr hsigma0.le)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hc fullGeneratorKernelConstant_pos.le) hsplit)
      (Real.rpow_nonneg hh.le _)
  have hcombine :
      (t / 2) ^ (-sigma) * (t / 2) ^ (-(1 / 2 : ℝ)) =
        (t / 2) ^ (-sigma - 1 / 2) := by
    rw [← Real.rpow_add hh]
    congr 1
  calc
    ‖intervalFractionalNeumannDivergenceLp sigma t q
        (by simpa using ENNReal.ofReal_le_ofReal hrq.symm.lt.le) f‖ ≤
      fractionalSubordinationConstant sigma * fullGeneratorKernelConstant *
        (1 / (1 - sigma) + 1 / sigma) * (t / 2) ^ (-sigma) *
          lpNorm (intervalConjugateKernelOperator (t / 2) f)
            (ENNReal.ofReal q) (intervalMeasure 1) := by
      simpa [intervalFractionalNeumannDivergenceLp] using hfrac
    _ ≤ fractionalSubordinationConstant sigma * fullGeneratorKernelConstant *
        (1 / (1 - sigma) + 1 / sigma) * (t / 2) ^ (-sigma) *
          ((heatGradientLinftyLinftyConstant *
              (t / 2) ^ (-(1 / 2 : ℝ))) *
            lpNorm f (ENNReal.ofReal q) (intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_left hgrad hleft
    _ = heatGradientLinftyLinftyConstant *
        fractionalSubordinationConstant sigma * fullGeneratorKernelConstant *
        (1 / (1 - sigma) + 1 / sigma) *
        (t / 2) ^ (-sigma - 1 / 2) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
      rw [← hcombine]
      ring

/-- Mode multiplier produced by the half-time factorization.  It is the
expected `lambda_n^sigma exp (-t lambda_n)` times the divergence coefficient
`n*pi*a`; the zero Neumann mode is included. -/
theorem neumannDivergenceMode_fractional_factorization
    {sigma t a : ℝ} (n : ℕ) :
    ((unitIntervalCosineEigenvalue n) ^ sigma *
        Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n))) *
      (Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n)) *
        (((n : ℝ) * Real.pi) * a)) =
      (unitIntervalCosineEigenvalue n) ^ sigma *
        Real.exp (-(t * unitIntervalCosineEigenvalue n)) *
          (((n : ℝ) * Real.pi) * a) := by
  calc
    ((unitIntervalCosineEigenvalue n) ^ sigma *
          Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n))) *
        (Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n)) *
          (((n : ℝ) * Real.pi) * a)) =
      (unitIntervalCosineEigenvalue n) ^ sigma *
        (Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n)) *
          Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n))) *
            (((n : ℝ) * Real.pi) * a) := by ring
    _ = (unitIntervalCosineEigenvalue n) ^ sigma *
        Real.exp (-(t * unitIntervalCosineEigenvalue n)) *
          (((n : ℝ) * Real.pi) * a) := by
      rw [← Real.exp_add]
      have harg :
          -((t / 2) * unitIntervalCosineEigenvalue n) +
              -((t / 2) * unitIntervalCosineEigenvalue n) =
            -(t * unitIntervalCosineEigenvalue n) := by ring
      rw [harg]

#print axioms intervalConjugateKernelOperator_memLp
#print axioms intervalFractionalNeumannDivergenceLp_norm_le
#print axioms neumannDivergenceMode_fractional_factorization

end ShenWork.Paper2.IntervalFractionalSubordinationDivergenceFullQ
