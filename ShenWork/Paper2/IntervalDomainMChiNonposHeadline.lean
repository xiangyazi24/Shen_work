/-
  Theorem 1.3 headline for nonpositive sensitivity and m >= 1.
-/
import ShenWork.Paper2.IntervalDomainMChiNonposGeneral
import ShenWork.Paper2.IntervalDomainTheorem13CorrectedHeadline

open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMChiNonpos

/-- For the faithful interval equation, nonpositive sensitivity gives the
finite-horizon and global conclusions of Theorem 1.3 for every `m >= 1`. -/
theorem Theorem_1_3_intervalDomainM_chiNonpos_m_ge_one
    (p : CM2Params) (C : Paper2Constants p)
    (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) :
    Theorem_1_3 intervalDomainM p C := by
  intro _ha hb _hmpos _hstrong
  constructor
  · intro u₀ hu₀
    obtain ⟨u, v, hglobal, htrace, _hbounded⟩ :=
      globalSolution_chiNonpos_m_ge_one
        p (Or.inr hb) hchi hm u₀ hu₀
    have hsol : IsPaper2ClassicalSolution intervalDomainM p 1 u v :=
      hglobal.classical zero_lt_one
    have hbdd : IsPaper2BoundedBefore intervalDomainM 1 u :=
      critical_bounded_before_nonpos_m_ge_one
        (Or.inr hb) hchi hm hu₀.toPositive hsol htrace
    exact ⟨1, zero_lt_one, u, v, hsol, htrace, hbdd⟩
  · intro _hm u₀ hu₀
    exact globalSolution_chiNonpos_m_ge_one
      p (Or.inr hb) hchi hm u₀ hu₀

end ShenWork.Paper2.IntervalDomainMChiNonpos
