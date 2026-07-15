/-
# Global continuation for nonpositive sensitivity at the critical exponent

The horizon-independent maximum-principle bound rules out a finite maximal
reachable horizon.  Canonical reachable-horizon gluing then produces one
global classical solution with the prescribed trace and global bound.
-/
import ShenWork.Paper2.IntervalDomainMChiNonposBound
import ShenWork.Paper2.IntervalDomainMContinuationExtension

open Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMChiNonposGlobal

open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.Paper2.IntervalDomainMChiNonposBound

/-- For nonpositive sensitivity and `m = 1`, every positive finite horizon is
reachable under the reaction guard appearing in the corrected theorem. -/
theorem reachableArbitrarilyLongM_chiNonpos_m_one
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : p.m = 1)
    (u₀ : intervalDomainPoint → ℝ)
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
      critical_bounded_before_nonpos
        hguard hchi hm hu₀.toPositive hsolMax htraceMax
    have hmge : 1 ≤ p.m := by rw [hm]
    have hpast : ReachablePastM p u₀ Tmax :=
      reachablePastM_of_bounded
        p hmge hu₀ hTmax hsolMax htraceMax hbounded
    exact False.elim
      ((not_reachablePast_finiteMaximalReachableHorizonM hbdd) hpast)
  · exact reachableArbitrarilyLongM_of_not_bddAbove hbdd

/-- Canonical global solution and horizon-independent bound for the
nonpositive-sensitivity critical branch. -/
theorem globalSolution_chiNonpos_m_one
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : p.m = 1)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomainM p u v ∧
      InitialTrace intervalDomainM u₀ u ∧
      IsPaper2Bounded intervalDomainM u := by
  have hreach :=
    reachableArbitrarilyLongM_chiNonpos_m_one
      p hguard hchi hm u₀ hu₀
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt
      (intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hu₀) hreach
  exact ⟨u, v, hglobal, htrace,
    critical_bounded_global_nonpos
      hguard hchi hm hu₀.toPositive hglobal htrace⟩

section AxiomAudit

#print axioms reachableArbitrarilyLongM_chiNonpos_m_one
#print axioms globalSolution_chiNonpos_m_one

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMChiNonposGlobal
