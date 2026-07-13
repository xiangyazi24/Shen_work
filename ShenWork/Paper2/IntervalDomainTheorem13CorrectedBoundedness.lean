import ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness
import ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap

/-!
# Faithful a-priori boundedness for Paper 2, Theorem 1.3

This file assembles the four strong-logistic alternatives on the published
general-`m` interval equation.  The fourth alternative includes the missing
exponent-domain condition needed by the proof in Section 5.4 of the paper.

The conclusion concerns every finite classical branch.  It is deliberately
separate from local existence and maximal continuation, so an existence
package cannot masquerade as the analytic boundedness proof.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainTheorem13CriticalConstants
open ShenWork.Paper2.IntervalDomainTheorem13CriticalBootstrap
open ShenWork.Paper2.IntervalDomainTheorem13StrictBoundedness

/-- The four alternatives of Theorem 1.3 with the literal interval value of
`K`.  Alternative (iv) contains the additional exponent-domain condition
`q_* > 2 - 2m` required to invoke Proposition 2.2 at the threshold. -/
def CorrectedStrongLogisticCondition (p : CM2Params) : Prop :=
  (0 ≤ p.β ∧ p.m + p.γ - 1 < p.α) ∨
    ((1 / 2 : ℝ) ≤ p.β ∧ 2 * p.m + p.γ - 2 < p.α) ∨
    (0 ≤ p.β ∧ p.α = p.m + p.γ - 1 ∧
      (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ <
          ((positivePart ((p.N : ℝ) * p.α - 2) + 2 * p.m) * p.b) /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              (p.ν + Psi_beta p.β * theorem13CriticalK p)))) ∨
    ((1 / 2 : ℝ) ≤ p.β ∧ p.α = 2 * p.m + p.γ - 2 ∧
      2 - 2 * p.m < theorem13CriticalQStar p ∧
      (positivePart ((p.N : ℝ) * p.α - 2) = 0 ∨
        p.χ₀ < Real.sqrt
          (8 * p.b /
            (positivePart ((p.N : ℝ) * p.α - 2) *
              Theta_beta (2 * p.β - 1) * theorem13CriticalK p))))

/-- Every finite classical branch of the faithful general-`m` equation is
bounded under one of the four corrected strong-logistic alternatives and
positive sensitivity. -/
theorem boundedBefore_of_correctedStrongLogistic_positive_chi
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀)
    (hstrong : CorrectedStrongLogisticCondition p) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  rcases hstrong with hI | hII | hIII | hIV
  · exact boundedBefore_strict_case_i_positive_chi
      hu₀ hsol htrace hb hchi hI.2
  · exact boundedBefore_strict_case_ii
      hu₀ hsol htrace hb hII.1 hII.2
  · exact boundedBefore_critical_case_iii
      hN hb hu₀ hsol htrace hchi hIII.1 hIII.2.1 hIII.2.2
  · exact boundedBefore_critical_case_iv_corrected
      hN hb hu₀ hsol htrace hchi hIV.1 hIV.2.1 hIV.2.2.1 hIV.2.2.2

#print axioms boundedBefore_of_correctedStrongLogistic_positive_chi

end ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness
