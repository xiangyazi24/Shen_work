import ShenWork.Paper1.WholeLineWeightedRegularityMatchedSourceDQ
import ShenWork.Paper1.WholeLineWeightedRegularityMatchedReactionDQ

open Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Step-uniform traveling-wave data for the raw-DQ closure

The canonical difference steps are `(n+1)^{-1}`.  This file replaces every
remaining dependence on such a step by constants valid for all `|h| <= 1`.
-/

/-- The logarithmic-derivative relative quotient estimate is uniform over
all nonzero spatial steps of absolute value at most one. -/
theorem profile_shift_quotient_le_convex_uniform_of_logDerivative_bound
    {U : ℝ → ℝ} {B h : ℝ}
    (hB : 0 ≤ B)
    (hUpos : ∀ y, 0 < U y)
    (hUdiff : Differentiable ℝ U)
    (hlog : ∀ y, |deriv U y / U y| ≤ B)
    (hh : h ≠ 0) (hh_one : |h| ≤ 1) :
    ∀ x, ∀ tau ∈ Set.Icc (0 : ℝ) 1,
      |(U (x + h) - U x) / h| ≤
        (B * Real.exp (2 * B)) *
          (tau * U (x + h) + (1 - tau) * U x) := by
  intro x tau htau
  have hraw := profile_shift_quotient_le_convex_of_logDerivative_bound
    hB hUpos hUdiff hlog hh (x := x) tau htau
  have hexp : Real.exp (2 * B * |h|) ≤ Real.exp (2 * B) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcombo : 0 ≤ tau * U (x + h) + (1 - tau) * U x := by
    exact add_nonneg
      (mul_nonneg htau.1 (hUpos (x + h)).le)
      (mul_nonneg (sub_nonneg.mpr htau.2) (hUpos x).le)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp hB) hcombo)

/-- The only step dependence in the matched-flux value coefficient is an
exponential of `|h|`; hence its value at step one dominates every canonical
step. -/
theorem matchedFluxQuotientWSquareConstant_le_one
    (p : CMParams) {M Brel DU eta h : ℝ}
    (heta : 0 ≤ eta) (hh_one : |h| ≤ 1) :
    matchedFluxQuotientWSquareConstant p M Brel DU eta h ≤
      matchedFluxQuotientWSquareConstant p M Brel DU eta 1 := by
  have hE : Real.exp (2 * eta * |h|) ≤ Real.exp (2 * eta) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simp only [matchedFluxQuotientWSquareConstant, abs_one]
  gcongr

/-- Raw-source version of the preceding step-uniform coefficient bound. -/
theorem matchedFluxRawWSquareConstant_le_one
    (p : CMParams) {M Brel DU eta h : ℝ}
    (heta : 0 ≤ eta) (hh_one : |h| ≤ 1) :
    matchedFluxRawWSquareConstant p M Brel DU eta h ≤
      matchedFluxRawWSquareConstant p M Brel DU eta 1 := by
  unfold matchedFluxRawWSquareConstant
  gcongr
  exact matchedFluxQuotientWSquareConstant_le_one p heta hh_one

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.profile_shift_quotient_le_convex_uniform_of_logDerivative_bound
#print axioms ShenWork.Paper1.matchedFluxQuotientWSquareConstant_le_one
#print axioms ShenWork.Paper1.matchedFluxRawWSquareConstant_le_one
