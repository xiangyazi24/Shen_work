import ShenWork.Paper3.IntervalDomainMinimalEntropyGlobal
import ShenWork.Paper3.IntervalDomainMinimalSignalEnergyGlobal

/-! # Faithful eventual Theorem 2.5 on the unit interval -/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Package-free faithful eventual form of Paper 3 Theorem 2.5 for the
implemented one-dimensional `m = 1` equation.  The explicit upper and lower
constants are the canonical orbit-independent producers at each physical
equilibrium mass. -/
theorem intervalDomain_Theorem_2_5_EventualGlobalStabilityFormula
    (p : CM2Params) (hN : p.N = 1) :
    Theorem_2_5_EventualGlobalStabilityFormula intervalDomain p
      intervalDomainSectorialStabilityNorms
      (fun uStar =>
        (intervalDomainMinimalEventualBoxConstants p uStar).1)
      (fun uStar =>
        (intervalDomainMinimalEventualBoxConstants p uStar).2) := by
  intro ha0 hb0 hm hbeta uStar huStar
  dsimp
  intro hcond
  rcases hcond with hcond | hcond
  · exact
      intervalDomain_eventuallyGloballyExponentiallyStableMinimal_minimal1
        p hN hm ha0 hb0 hbeta huStar hcond.1 hcond.2
  · exact
      intervalDomain_eventuallyGloballyExponentiallyStableMinimal_minimal2
        p hN hm ha0 hb0 hcond.1 hbeta huStar hcond.2.1 hcond.2.2

#print axioms
  intervalDomain_Theorem_2_5_EventualGlobalStabilityFormula

end

end ShenWork.Paper3
