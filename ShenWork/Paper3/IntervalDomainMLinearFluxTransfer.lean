import ShenWork.Paper2.IntervalDomainMCriticalLpSeed
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit
import ShenWork.Paper3.IntervalDomainPersistenceGeneralMPart3

open Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- A faithful `intervalDomainM` solution in the `m = 1` branch can be read as
a solution of the legacy linear-flux domain.  All non-PDE fields of the two
domain records are definitionally identical. -/
theorem positiveGlobalBoundedSolution_intervalDomain_of_M_m_one
    {p : CM2Params} {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : p.m = 1)
    (hsol : PositiveGlobalBoundedSolution intervalDomainM p u v) :
    PositiveGlobalBoundedSolution intervalDomain p u v := by
  rcases hsol with ⟨hglobal, hbdd, hposInside⟩
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    have hM := hglobal T hT
    exact ShenWork.Paper2.IntervalDomainM.classicalSolution_intervalDomain_of_m_eq_one
      hm hM
  · exact hbdd
  · intro t x ht hx
    exact hposInside t x ht hx

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.positiveGlobalBoundedSolution_intervalDomain_of_M_m_one
