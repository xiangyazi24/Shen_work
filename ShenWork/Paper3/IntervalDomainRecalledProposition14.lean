/-
  Unconditional realization of Paper 3's recalled Proposition 1.4 on the
  physical interval.  The sign split joins the independent constructive
  continuation theorems for positive and nonpositive sensitivity.
-/
import ShenWork.Paper2.IntervalDomainMChiNonposGlobal
import ShenWork.Paper3.IntervalDomainRecalledPropositionsPositive

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMChiNonposGlobal

noncomputable section

/-- The nonpositive-sensitivity part of recalled Proposition 1.4.  Its
threshold hypothesis is automatic for negative sensitivity but remains in
the proposition's faithful public signature. -/
theorem intervalDomain_Proposition_1_4_nonpos
    (p : CM2Params) (hchi : p.χ₀ ≤ 0) :
    Proposition_1_4 intervalDomain p := by
  intro hm _hbeta hab _hthreshold u₀ hu₀
  have hguard : p.a = 0 ∨ 0 < p.b := by
    rcases hab with hab0 | habp
    · exact Or.inl hab0.1
    · exact Or.inr habp.2
  have hu₀M : PaperPositiveInitialDatum intervalDomainM u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  obtain ⟨u, v, hglobalM, htraceM, hbddM⟩ :=
    globalSolution_chiNonpos_m_one p hguard hchi hm u₀ hu₀M
  have hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v := by
    intro T hT
    exact classicalSolution_intervalDomain_of_m_eq_one hm
      (hglobalM.classical hT)
  have htrace : InitialTrace intervalDomain u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htraceM
  have hbdd : IsPaper2Bounded intervalDomain u := by
    simpa [intervalDomainM, intervalDomain] using hbddM
  exact ⟨u, v, hglobal, htrace, hbdd⟩

/-- Paper 3 Proposition 1.4 on the physical interval, for every sensitivity
covered by its own threshold.  No existence or continuation package is
carried as a hypothesis. -/
theorem intervalDomain_Proposition_1_4_unconditional
    (p : CM2Params) : Proposition_1_4 intervalDomain p := by
  by_cases hchi : 0 < p.χ₀
  · exact intervalDomain_Proposition_1_4_positiveCritical p hchi
  · exact intervalDomain_Proposition_1_4_nonpos p (le_of_not_gt hchi)

section AxiomAudit

#print axioms intervalDomain_Proposition_1_4_nonpos
#print axioms intervalDomain_Proposition_1_4_unconditional

end AxiomAudit

end

end ShenWork.Paper3
