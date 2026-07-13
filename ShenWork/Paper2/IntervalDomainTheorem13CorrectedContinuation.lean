/-
  Non-vacuous maximal continuation for the corrected positive-sensitivity
  branch of Paper 2, Theorem 1.3.

  The finite-horizon analytic estimate and the continuation mechanism are
  kept separate: boundedness at a hypothetical finite reachable supremum
  supplies exactly the positive strip needed to restart past that supremum.
-/
import ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness
import ShenWork.Paper2.IntervalDomainMContinuationExtension

open Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CorrectedContinuation

open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness

/-- Under the corrected strong-logistic condition, the faithful positive-
sensitivity Cauchy problem reaches every finite horizon when `m >= 1`.

This is a constructive maximal-continuation argument.  If the reachable set
had a finite supremum, the canonical branch at that supremum would be bounded
by the direct Theorem 1.3 estimate and hence restart strictly past it. -/
theorem reachableArbitrarilyLong_of_correctedStrongLogistic_positive_chi
    {p : CM2Params}
    (hN : p.N = 1) (hb : 0 < p.b) (hm : 1 <= p.m)
    (hchi : 0 < p.χ₀) (hstrong : CorrectedStrongLogisticCondition p)
    (u₀ : intervalDomainPoint -> ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    ReachableArbitrarilyLongM p u₀ := by
  obtain ⟨T, hT, u, v, hsol, htrace⟩ :=
    intervalDomainM_localExistence_paperPositive_allExponents p u₀ hu₀
  have hne : (reachableClassicalHorizonSetM p u₀).Nonempty :=
    ⟨T, hT, u, v, hsol, htrace⟩
  have huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀ :=
    intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hu₀
  by_cases hbdd : BddAbove (reachableClassicalHorizonSetM p u₀)
  · let Tmax := finiteMaximalReachableHorizonM p u₀
    have hTmax : 0 < Tmax := finiteMaximalReachableHorizonM_pos hbdd hne
    obtain ⟨U, V, hsolMax, htraceMax⟩ :=
      realize_at_finiteMaximalReachableHorizonM_of_overlapUnique
        huniq hbdd hne
    have hbounded : IsPaper2BoundedBefore intervalDomainM Tmax U :=
      boundedBefore_of_correctedStrongLogistic_positive_chi
        hN hb hu₀.toPositive hsolMax htraceMax hchi hstrong
    have hpast : ReachablePastM p u₀ Tmax :=
      reachablePastM_of_bounded p hm hu₀ hTmax hsolMax htraceMax hbounded
    exact False.elim
      ((not_reachablePast_finiteMaximalReachableHorizonM hbdd) hpast)
  · exact reachableArbitrarilyLongM_of_not_bddAbove hbdd

/-- The arbitrarily-long result glues to one canonical global classical pair
with the prescribed initial trace; arbitrary values outside a local lifespan
are never reused. -/
theorem globalSolution_of_correctedStrongLogistic_positive_chi
    {p : CM2Params}
    (hN : p.N = 1) (hb : 0 < p.b) (hm : 1 <= p.m)
    (hchi : 0 < p.χ₀) (hstrong : CorrectedStrongLogisticCondition p)
    (u₀ : intervalDomainPoint -> ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    ∃ u v : ℝ -> intervalDomainPoint -> ℝ,
      IsPaper2GlobalClassicalSolution intervalDomainM p u v ∧
      InitialTrace intervalDomainM u₀ u := by
  have hreach :=
    reachableArbitrarilyLong_of_correctedStrongLogistic_positive_chi
      hN hb hm hchi hstrong u₀ hu₀
  exact globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt
    (intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hu₀) hreach

section AxiomAudit

#print axioms reachableArbitrarilyLong_of_correctedStrongLogistic_positive_chi
#print axioms globalSolution_of_correctedStrongLogistic_positive_chi

end AxiomAudit

end ShenWork.Paper2.IntervalDomainTheorem13CorrectedContinuation
