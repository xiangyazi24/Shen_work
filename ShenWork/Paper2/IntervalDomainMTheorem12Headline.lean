import ShenWork.Paper2.IntervalDomainMSlowGlobalBoundedness
import ShenWork.Paper2.IntervalDomainMMaximalContinuationAlternative
import ShenWork.Paper2.IntervalDomainMChiNonposBound

/-!
# Corrected Paper 2 Theorem 1.2 on the faithful interval model

This file closes both branches of `CorrectedTheorem_1_2 intervalDomainM p`.
The slow branch bounds both finite and global maximal-continuation carriers.
In the critical branch the finite alternative is incompatible with the proved
finite-horizon bound, so every carrier is global and bounded.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMTheorem12Headline

open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation
open ShenWork.Paper2.IntervalDomainMChiNonposBound
open ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer

/-- A finite-horizon supremum bound contradicts the faithful upper blow-up
alternative.  Spatial boundedness comes from the classical slice itself, so
no extra sup-norm-control hypothesis is carried. -/
private theorem not_mgeOneFiniteHorizonAlternativeM_of_boundedBefore
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hbdd : IsPaper2BoundedBefore intervalDomainM T u) :
    ¬ MGeOneFiniteHorizonAlternative intervalDomainM T u := by
  intro hblow
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨t, x, ht0, htT, _hx, hlt⟩ := hblow M
  have habs : |u t x| ≤ intervalDomainM.supNorm (u t) := by
    change |u t x| ≤ intervalDomainSupNorm (u t)
    unfold intervalDomainSupNorm
    exact le_csSup (solution_slice_abs_bddAbove hsol ⟨ht0, htT⟩) ⟨x, rfl⟩
  have hpoint : u t x ≤ intervalDomainM.supNorm (u t) :=
    (le_abs_self (u t x)).trans habs
  exact not_lt_of_ge (hpoint.trans (hM t ht0 htT)) hlt

/-- Every canonical maximal-continuation carrier in the slow-diffusion regime
is bounded in the sense appropriate to its finite or global branch. -/
theorem correctedTheorem12_slowBranch_intervalDomainM
    (p : CM2Params)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hbeta : 1 ≤ p.β) (hm1 : p.m < 1) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomainM u₀ →
        Nonempty (Paper2MaximalContinuation intervalDomainM p u₀) ∧
          ∀ branch : Paper2MaximalContinuation intervalDomainM p u₀,
            branch.IsBounded := by
  intro u₀ hu₀
  constructor
  · exact paper2MaximalContinuation_intervalDomainM_nonempty p u₀ hu₀
  · intro branch
    cases branch with
    | finite T U V _hT hsol htrace _halt _hmge =>
        exact slow_bounded_before
          hguard hu₀.toPositive hsol htrace hbeta hm1
    | global U V hglobal htrace =>
        exact slow_bounded_global
          hguard hu₀.toPositive hglobal htrace hbeta hm1

/-- In the critical regime every canonical maximal-continuation carrier is
global and bounded, for either sign of the sensitivity. -/
theorem correctedTheorem12_criticalBranch_intervalDomainM
    (p : CM2Params)
    (hguard : p.a = 0 ∨ 0 < p.b)
    (hbeta : 1 ≤ p.β) (hm : p.m = 1)
    (hthreshold : p.χ₀ < chiBeta p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomainM u₀ →
        Nonempty (Paper2MaximalContinuation intervalDomainM p u₀) ∧
          ∀ branch : Paper2MaximalContinuation intervalDomainM p u₀,
            branch.IsGlobal ∧ branch.IsBounded := by
  intro u₀ hu₀
  constructor
  · exact paper2MaximalContinuation_intervalDomainM_nonempty p u₀ hu₀
  · intro branch
    cases branch with
    | global U V hglobal htrace =>
        constructor
        · exact True.intro
        · by_cases hchi : 0 < p.χ₀
          · exact critical_bounded_global_positive_restarted_affine
              hguard hu₀.toPositive hglobal htrace hbeta hm hchi hthreshold
          · exact critical_bounded_global_nonpos
              hguard (le_of_not_gt hchi) hm hu₀.toPositive hglobal htrace
    | finite T U V _hT hsol htrace _halt hmge =>
        have hbdd : IsPaper2BoundedBefore intervalDomainM T U := by
          by_cases hchi : 0 < p.χ₀
          · exact critical_bounded_before_positive_restarted_affine
              hguard hu₀.toPositive hsol htrace hbeta hm hchi hthreshold
          · exact critical_bounded_before_nonpos
              hguard (le_of_not_gt hchi) hm hu₀.toPositive hsol htrace
        have hfalse : False :=
          (not_mgeOneFiniteHorizonAlternativeM_of_boundedBefore hsol hbdd)
            (hmge (by rw [hm]))
        exact False.elim hfalse

/-- Unconditional, non-vacuous, paper-faithful corrected Theorem 1.2 for the
general-`m` interval equation.  Its only hypotheses are the theorem's original
parameter guards and initial data quantified inside the statement. -/
theorem correctedTheorem12_intervalDomainM
    (p : CM2Params) :
    CorrectedTheorem_1_2 intervalDomainM p := by
  intro hguard hbeta
  constructor
  · intro _hm0 hm1
    exact correctedTheorem12_slowBranch_intervalDomainM
      p hguard hbeta hm1
  · intro hm hthreshold
    exact correctedTheorem12_criticalBranch_intervalDomainM
      p hguard hbeta hm hthreshold

#print axioms correctedTheorem12_slowBranch_intervalDomainM
#print axioms correctedTheorem12_criticalBranch_intervalDomainM
#print axioms correctedTheorem12_intervalDomainM

end ShenWork.Paper2.IntervalDomainMTheorem12Headline

