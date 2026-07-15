import ShenWork.Paper2.IntervalDomainTheorem12PositiveCriticalAllExponents
import ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline
import ShenWork.Paper3.Statements

/-!
# Concrete recalled Paper 2 boundedness results in Paper 3

Paper 3 recalls the global boundedness results of Paper 2 as Propositions 1.3
and 1.4.  This file connects the actual one-dimensional continuation
constructions to those recalled conclusions.  No theorem-shaped existence or
boundedness package is assumed.
-/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedContinuation
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline

noncomputable section

/-- Corrected one-dimensional form of the recalled Proposition 1.3.  The
fourth critical alternative contains the exponent-domain condition required
by its weighted-gradient proof. -/
def CorrectedProposition_1_3_OneDimensional (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 1 ≤ p.m → 0 < p.χ₀ →
    CorrectedStrongLogisticCondition p →
      ∀ u₀ : intervalDomainPoint → ℝ,
        PaperPositiveInitialDatum intervalDomainM u₀ →
          ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomainM p u v ∧
            InitialTrace intervalDomainM u₀ u ∧
            IsPaper2Bounded intervalDomainM u

/-- The recalled strong-logistic proposition, with its corrected fourth
alternative, follows from the constructive general-`m` continuation theorem
and the horizon-independent global estimate. -/
theorem correctedProposition13_intervalDomainM
    (p : CM2Params) (hN : p.N = 1) :
    CorrectedProposition_1_3_OneDimensional p := by
  intro _ha hb hm hchi hstrong u₀ hu₀
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolution_of_correctedStrongLogistic_positive_chi
      hN hb hm hchi hstrong u₀ hu₀
  exact ⟨u, v, hglobal, htrace,
    boundedGlobal_of_correctedStrongLogistic_positive_chi
      hN hb hu₀.toPositive hglobal htrace hchi hstrong⟩

/-- The positive-sensitivity part of recalled Proposition 1.4 is fully
unconditional on the physical interval.  The two allowed reaction regimes
both imply the guard used by the all-exponent positive-critical continuation
theorem. -/
theorem intervalDomain_Proposition_1_4_positiveCritical
    (p : CM2Params) (hchi : 0 < p.χ₀) :
    Proposition_1_4 intervalDomain p := by
  intro hm hbeta hab hthreshold u₀ hu₀
  have hguard : p.a = 0 ∨ 0 < p.b := by
    rcases hab with hab0 | habp
    · exact Or.inl hab0.1
    · exact Or.inr habp.2
  exact positiveCriticalGlobalSolution_allExponents
    p hguard hbeta hm hchi hthreshold u₀ hu₀

#print axioms correctedProposition13_intervalDomainM
#print axioms intervalDomain_Proposition_1_4_positiveCritical

end

end ShenWork.Paper3
