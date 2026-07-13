import ShenWork.Paper3.IntervalDomainEntropyStrong1Global
import ShenWork.Paper3.IntervalDomainEntropyStrong2Global
import ShenWork.Paper3.IntervalDomainRectangleGlobal

/-! # Faithful eventual Theorem 2.4 on the unit interval -/

namespace ShenWork.Paper3

open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

/-- Package-free faithful eventual form of Paper 3 Theorem 2.4 for the
implemented one-dimensional `m = 1` equation.  Each explicit formula branch
is discharged by its concrete entropy or rectangle producer. -/
theorem intervalDomain_Theorem_2_4_EventualGlobalStabilityFormula
    (p : CM2Params) (hm : p.m = 1) :
    Theorem_2_4_EventualGlobalStabilityFormula intervalDomain p
      intervalDomainSectorialStabilityNorms
      (unitIntervalNormalizedResolverGradientConstant p) := by
  intro ha0 hb0 hβ0 hα0 hγ0 ha hb
  dsimp
  intro hcond
  rcases hcond with hcond | hcond | hcond | hcond
  · exact
      intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong1
        p hm ha hb hcond.2.1 hcond.2.2.1 hcond.2.2.2
  · exact
      intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong2
        p hm ha hb hcond.2.1 hcond.2.2.1 hcond.2.2.2.1
          hcond.2.2.2.2
  · exact
      intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong3
        p hm ha hb hcond.2.1 hcond.2.2.1 hcond.2.2.2
  · exact
      intervalDomain_eventuallyGloballyExponentiallyStableNonminimal_strong4
        p hm ha hb hcond.2.1 hcond.2.2.1 hcond.2.2.2.1
          hcond.2.2.2.2

#print axioms intervalDomain_Theorem_2_4_EventualGlobalStabilityFormula

end

end ShenWork.Paper3
