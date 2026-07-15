import ShenWork.Paper2.IntervalDomainTheorem12PositiveCriticalAllExponents
import ShenWork.Paper2.IntervalDomainMChiNonposGlobal
import ShenWork.Paper2.IntervalDomainMCriticalGlobalLinfBound
import ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline

/-!
# Paper 2 Lp headline assembly

This file joins the positive-sensitivity critical Lp bootstrap to the
nonpositive-sensitivity maximum-principle branch.  It also records the exact
slow-regime residual left after the critical branch is closed.

The legacy theorem statements are retained only behind their necessary
parameter guards.  In particular, the false `a > 0, b = 0` slice is not
reintroduced through an unconditional wrapper.
-/

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainLpHeadline

open ShenWork.IntervalDomainExistence
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMChiNonposBound
open ShenWork.Paper2.IntervalDomainMChiNonposGlobal

/-- The critical branch of the legacy interval-domain Theorem 1.2, for both
sensitivity signs.  The positive sign is the Lp-bootstrap route; the
nonpositive sign is the maximum-principle route. -/
theorem Theorem_1_2_intervalDomain_critical_branch_unconditional
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b) :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
          InitialTrace intervalDomain u₀ u ∧
          IsPaper2Bounded intervalDomain u := by
  intro hβ hm hthreshold u₀ hu₀
  by_cases hchi : 0 < p.χ₀
  · exact Theorem_1_2_intervalDomain_positive_critical_branch_unconditional
      p hguard hchi hβ hm hthreshold u₀ hu₀
  · have hchi' : p.χ₀ ≤ 0 := le_of_not_gt hchi
    have hu₀M : PaperPositiveInitialDatum intervalDomainM u₀ := by
      simpa [intervalDomainM, intervalDomain] using hu₀
    obtain ⟨u, v, hglobalM, htraceM, hboundedM⟩ :=
      globalSolution_chiNonpos_m_one p hguard hchi' hm u₀ hu₀M
    refine ⟨u, v, ?_, ?_, ?_⟩
    · intro T hT
      exact classicalSolution_intervalDomain_of_m_eq_one hm
        (hglobalM.classical hT)
    · simpa [intervalDomainM, intervalDomain] using htraceM
    · simpa [intervalDomainM, intervalDomain] using hboundedM

/-- Paper-faithful maximal-continuation form of the all-sign critical branch. -/
theorem correctedTheorem12_criticalBranch_unconditional
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hthreshold : p.χ₀ < chiBeta p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        Nonempty (Paper2MaximalContinuation intervalDomain p u₀) ∧
        ∀ branch : Paper2MaximalContinuation intervalDomain p u₀,
          branch.IsGlobal ∧ branch.IsBounded := by
  intro u₀ hu₀
  by_cases hchi : 0 < p.χ₀
  · exact correctedTheorem12_positiveCriticalBranch_unconditional
      p hguard hchi hβ hm hthreshold u₀ hu₀
  · have hchi' : p.χ₀ ≤ 0 := le_of_not_gt hchi
    have hu₀M : PaperPositiveInitialDatum intervalDomainM u₀ := by
      simpa [intervalDomainM, intervalDomain] using hu₀
    obtain ⟨u, v, hglobalM, htraceM, _hboundedM⟩ :=
      globalSolution_chiNonpos_m_one p hguard hchi' hm u₀ hu₀M
    have hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v := by
      intro T hT
      exact classicalSolution_intervalDomain_of_m_eq_one hm
        (hglobalM.classical hT)
    have htrace : InitialTrace intervalDomain u₀ u := by
      simpa [intervalDomainM, intervalDomain] using htraceM
    constructor
    · exact ⟨Paper2MaximalContinuation.global u v hglobal htrace⟩
    · intro branch
      cases branch with
      | global U V hglob htr =>
          have hglobM : IsPaper2GlobalClassicalSolution intervalDomainM p U V :=
            globalClassicalSolution_intervalDomainM_of_m_eq_one hm hglob
          have htrM : InitialTrace intervalDomainM u₀ U := by
            simpa [intervalDomainM, intervalDomain] using htr
          have hbddM : IsPaper2Bounded intervalDomainM U :=
            critical_bounded_global_nonpos
              hguard hchi' hm hu₀M.toPositive hglobM htrM
          exact ⟨True.intro, by
            simpa [intervalDomainM, intervalDomain] using hbddM⟩
      | finite T U V hT hsol htr _halt hmge =>
          have hsolM : IsPaper2ClassicalSolution intervalDomainM p T U V :=
            classicalSolution_intervalDomainM_of_m_eq_one hm hsol
          have htrM : InitialTrace intervalDomainM u₀ U := by
            simpa [intervalDomainM, intervalDomain] using htr
          have hbddM : IsPaper2BoundedBefore intervalDomainM T U :=
            critical_bounded_before_nonpos
              hguard hchi' hm hu₀M.toPositive hsolM htrM
          have hbdd : IsPaper2BoundedBefore intervalDomain T U := by
            simpa [intervalDomainM, intervalDomain] using hbddM
          have hcontrols : SupNormControlsPointwiseBefore T U :=
            supNormControlsPointwiseBefore_of_bddAbove_abs
              (fun t ht0 htT =>
                classicalSolution_u_range_bddAbove hsol ⟨ht0, htT⟩)
          have hpw : PointwiseBoundedBefore T U :=
            pointwiseBoundedBefore_of_boundedBefore_and_supNormControls
              hbdd hcontrols
          have hfalse : False :=
            (not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore hpw)
              (hmge (by rw [hm]))
          exact False.elim hfalse

/-- The only unresolved regime in the corrected Theorem 1.2 after the
critical Lp frontier is closed. -/
def IntervalDomainCorrectedTheorem12SlowBranchResidual
    (p : CM2Params) : Prop :=
  0 < p.m → p.m < 1 →
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        Nonempty (Paper2MaximalContinuation intervalDomain p u₀) ∧
        ∀ branch : Paper2MaximalContinuation intervalDomain p u₀,
          branch.IsBounded

/-- Corrected Theorem 1.2 with only the genuine `0 < m < 1` residual. -/
theorem correctedTheorem12_intervalDomain_of_slowBranchResidual
    (p : CM2Params)
    (hslow : IntervalDomainCorrectedTheorem12SlowBranchResidual p) :
    CorrectedTheorem_1_2 intervalDomain p := by
  intro hguard hβ
  constructor
  · exact hslow
  · intro hm hthreshold
    exact correctedTheorem12_criticalBranch_unconditional
      p hguard hβ hm hthreshold

/-- Legacy slow-branch residual, kept separate from the corrected maximal
continuation formulation. -/
def IntervalDomainTheorem12SlowBranchResidual (p : CM2Params) : Prop :=
  0 < p.m → p.m < 1 →
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u ∧
          IsPaper2BoundedBefore intervalDomain Tmax u

/-- Legacy Theorem 1.2 on its mathematically valid parameter slice.  Besides
the named slow residual, the guard is necessary because the unguarded legacy
statement is refuted when `a > 0` and `b = 0`. -/
theorem Theorem_1_2_intervalDomain_of_slowBranchResidual
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hslow : IntervalDomainTheorem12SlowBranchResidual p) :
    Theorem_1_2 intervalDomain p := by
  intro _ha _hb hβ
  constructor
  · exact hslow
  · exact Theorem_1_2_intervalDomain_critical_branch_unconditional
      p hguard hβ

/-- In the nonpositive-sensitivity critical slice, the legacy Theorem 1.3 is
unconditional.  Its strong-logistic premise is not used: the maximum principle
provides both the finite-horizon and global bounds directly. -/
theorem Theorem_1_3_intervalDomain_chiNonpos_m_one
    (p : CM2Params) (C : Paper2Constants p)
    (hchi : p.χ₀ ≤ 0) (hm : p.m = 1) :
    Theorem_1_3 intervalDomain p C := by
  intro _ha hb _hmpos _hstrong
  constructor
  · intro u₀ hu₀
    have hu₀M : PaperPositiveInitialDatum intervalDomainM u₀ := by
      simpa [intervalDomainM, intervalDomain] using hu₀
    obtain ⟨u, v, hglobalM, htraceM, _hboundedM⟩ :=
      globalSolution_chiNonpos_m_one p (Or.inr hb) hchi hm u₀ hu₀M
    have hsolM : IsPaper2ClassicalSolution intervalDomainM p 1 u v :=
      hglobalM.classical zero_lt_one
    have hbddM : IsPaper2BoundedBefore intervalDomainM 1 u :=
      critical_bounded_before_nonpos
        (Or.inr hb) hchi hm hu₀M.toPositive hsolM htraceM
    refine ⟨1, zero_lt_one, u, v, ?_, ?_, ?_⟩
    · exact classicalSolution_intervalDomain_of_m_eq_one hm hsolM
    · simpa [intervalDomainM, intervalDomain] using htraceM
    · simpa [intervalDomainM, intervalDomain] using hbddM
  · intro _hmge u₀ hu₀
    have hu₀M : PaperPositiveInitialDatum intervalDomainM u₀ := by
      simpa [intervalDomainM, intervalDomain] using hu₀
    obtain ⟨u, v, hglobalM, htraceM, hboundedM⟩ :=
      globalSolution_chiNonpos_m_one p (Or.inr hb) hchi hm u₀ hu₀M
    refine ⟨u, v, ?_, ?_, ?_⟩
    · intro T hT
      exact classicalSolution_intervalDomain_of_m_eq_one hm
        (hglobalM.classical hT)
    · simpa [intervalDomainM, intervalDomain] using htraceM
    · simpa [intervalDomainM, intervalDomain] using hboundedM

end ShenWork.Paper2.IntervalDomainLpHeadline

end
