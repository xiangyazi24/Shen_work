import ShenWork.Paper2.IntervalDomainTheorem13CorrectedContinuation
import ShenWork.Paper2.IntervalDomainTheorem13CriticalGlobalBoundedness
import ShenWork.PDE.IntervalDomainExistence

/-!
# Corrected one-dimensional headline for Paper 2, Theorem 1.3

This file joins the four genuine a-priori estimates to the canonical
continuation construction.  It does not use the legacy
`Theorem_1_3.of_assumed_solutions_branch` wrapper.

For every positive datum, local existence is constructed and every finite
classical branch is bounded.  When `m >= 1`, the canonical maximal branch is
global, every finite maximal carrier is excluded by the sharper upper-blowup
alternative, and every global carrier has the horizon-independent bound.
-/

open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13CorrectedContinuation
open ShenWork.Paper2.IntervalDomainTheorem13StrictGlobalBoundedness
open ShenWork.Paper2.IntervalDomainTheorem13CriticalGlobalBoundedness
open ShenWork.IntervalDomainExistence

/-- The corrected one-dimensional content of Paper 2, Theorem 1.3.

The first conjunct records genuine local inhabitation and the a-priori bound
for every finite classical branch.  The second conjunct is the faithful
maximal-continuation conclusion in the paper's `m >= 1` global regime. -/
def CorrectedTheorem_1_3_OneDimensional (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ →
    CorrectedStrongLogisticCondition p →
      ((∀ u₀ : intervalDomainPoint → ℝ,
          PaperPositiveInitialDatum intervalDomainM u₀ →
            (∃ T > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
              IsPaper2ClassicalSolution intervalDomainM p T u v ∧
                InitialTrace intervalDomainM u₀ u ∧
                IsPaper2BoundedBefore intervalDomainM T u) ∧
            (∀ T, ∀ u v : ℝ → intervalDomainPoint → ℝ,
              IsPaper2ClassicalSolution intervalDomainM p T u v →
                InitialTrace intervalDomainM u₀ u →
                  IsPaper2BoundedBefore intervalDomainM T u)) ∧
       (1 ≤ p.m →
          ∀ u₀ : intervalDomainPoint → ℝ,
            PaperPositiveInitialDatum intervalDomainM u₀ →
              Nonempty (Paper2MaximalContinuation intervalDomainM p u₀) ∧
              ∀ branch : Paper2MaximalContinuation intervalDomainM p u₀,
                branch.IsGlobal ∧ branch.IsBounded))

/-- Closed spatial regularity gives bounded absolute-value range for every
interior slice of a faithful general-`m` classical solution. -/
theorem classicalSolutionM_u_range_bddAbove
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomainPoint => |u t x|)) := by
  classical
  have hcont : ContinuousOn (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨B, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hBx : |intervalDomainLift (u t) x.1| ≤ B :=
    hB ⟨x.1, x.2, rfl⟩
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift]
  simpa only [hlift] using hBx

/-- The four corrected alternatives give one horizon-independent bound for
every global classical solution. -/
theorem boundedGlobal_of_correctedStrongLogistic_positive_chi
    {p : CM2Params}
    {u₀ : intervalDomainPoint -> ℝ}
    {u v : ℝ -> intervalDomainPoint -> ℝ}
    (hN : p.N = 1) (hb : 0 < p.b)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hchi : 0 < p.χ₀)
    (hstrong : CorrectedStrongLogisticCondition p) :
    IsPaper2Bounded intervalDomainM u := by
  rcases hstrong with hI | hII | hIII | hIV
  · exact boundedGlobal_strict_case_i_positive_chi
      hu₀ hglobal htrace hb hchi hI.2
  · exact boundedGlobal_strict_case_ii
      hu₀ hglobal htrace hb hII.1 hII.2
  · exact boundedGlobal_critical_case_iii
      hN hb hu₀ hglobal htrace hchi hIII.1 hIII.2.1 hIII.2.2
  · exact boundedGlobal_critical_case_iv_corrected
      hN hb hu₀ hglobal htrace hchi hIV.1 hIV.2.1 hIV.2.2.1 hIV.2.2.2

/-- In the global regime, every maximal-continuation carrier is global and
bounded.  A finite carrier would carry the `m >= 1` upper-blowup alternative,
contradicting the direct finite-horizon bound. -/
theorem every_maximalContinuation_global_bounded_of_correctedStrongLogistic
    {p : CM2Params}
    (hN : p.N = 1) (hb : 0 < p.b) (hm : 1 <= p.m)
    (hchi : 0 < p.χ₀) (hstrong : CorrectedStrongLogisticCondition p)
    (u₀ : intervalDomainPoint -> ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    Nonempty (Paper2MaximalContinuation intervalDomainM p u₀) ∧
      forall branch : Paper2MaximalContinuation intervalDomainM p u₀,
        branch.IsGlobal ∧ branch.IsBounded := by
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolution_of_correctedStrongLogistic_positive_chi
      hN hb hm hchi hstrong u₀ hu₀
  constructor
  · exact ⟨Paper2MaximalContinuation.global u v hglobal htrace⟩
  · intro branch
    cases branch with
    | global U V hglob htr =>
        exact ⟨True.intro,
          boundedGlobal_of_correctedStrongLogistic_positive_chi
            hN hb hu₀.toPositive hglob htr hchi hstrong⟩
    | finite T U V hT hsol htr _halt hmge =>
        have hbdd : IsPaper2BoundedBefore intervalDomainM T U :=
          boundedBefore_of_correctedStrongLogistic_positive_chi
            hN hb hu₀.toPositive hsol htr hchi hstrong
        obtain ⟨M, hM⟩ := hbdd
        obtain ⟨t, x, ht0, htT, _hx, hlt⟩ := hmge hm M
        have hrange :
            BddAbove (Set.range (fun y : intervalDomainPoint => |U t y|)) :=
          classicalSolutionM_u_range_bddAbove hsol ⟨ht0, htT⟩
        have habs_le : |U t x| ≤ intervalDomainM.supNorm (U t) := by
          change |U t x| ≤ intervalDomainSupNorm (U t)
          unfold intervalDomainSupNorm
          exact le_csSup hrange ⟨x, rfl⟩
        have hUxM : U t x ≤ M :=
          (le_abs_self (U t x)).trans (habs_le.trans (hM t ht0 htT))
        exact False.elim (not_lt_of_ge hUxM hlt)

/-- Unconditional corrected one-dimensional Theorem 1.3 under its explicit
paper hypotheses and the corrected alternative (iv) exponent guard. -/
theorem correctedTheorem13_intervalDomainM
    (p : CM2Params) (hN : p.N = 1) :
    CorrectedTheorem_1_3_OneDimensional p := by
  intro _ha hb hchi hstrong
  constructor
  · intro u₀ hu₀
    constructor
    · obtain ⟨T, hT, u, v, hsol, htrace⟩ :=
        intervalDomainM_localExistence_paperPositive_allExponents p u₀ hu₀
      exact ⟨T, hT, u, v, hsol, htrace,
        boundedBefore_of_correctedStrongLogistic_positive_chi
          hN hb hu₀.toPositive hsol htrace hchi hstrong⟩
    · intro T u v hsol htrace
      exact boundedBefore_of_correctedStrongLogistic_positive_chi
        hN hb hu₀.toPositive hsol htrace hchi hstrong
  · intro hm u₀ hu₀
    exact every_maximalContinuation_global_bounded_of_correctedStrongLogistic
      hN hb hm hchi hstrong u₀ hu₀

#print axioms boundedGlobal_of_correctedStrongLogistic_positive_chi
#print axioms every_maximalContinuation_global_bounded_of_correctedStrongLogistic
#print axioms correctedTheorem13_intervalDomainM

end ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline
