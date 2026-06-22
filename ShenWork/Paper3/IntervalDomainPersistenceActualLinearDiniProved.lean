import ShenWork.Paper3.IntervalDomainPersistenceActualLinearDini
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearCompactFamily
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearRightDeriv
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearTimeContinuity
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearNearArgmin
import ShenWork.Paper3.IntervalDomainPersistenceSlopeBound
import ShenWork.Paper3.IntervalDomainPersistenceSlopeCobound

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_actualLinearSpatialMinimumDini_of_positiveGlobalBoundedSolution
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ}
    (hχ0 : 0 ≤ p.χ₀) (hβ : 1 ≤ p.β)
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ActualLinearSpatialMinimumDini p u :=
  ActualLinearSpatialMinimumDini.of_Danskin
    (intervalDomain_actualLinear_compactMinFamily (p := p) (v := v) hsol)
    (intervalDomain_actualLinear_uniformRightDerivLower hsol)
    (intervalDomain_actualLinear_uniformTimeContinuity hsol)
    (intervalDomain_actualLinear_nearArgmin_ft_lower hχ0 hβ hsol)
    (intervalDomainSpatialMin_slope_isCoboundedUnder_of_positiveGlobalBoundedSolution
      hsol)
    (intervalDomainSpatialMin_slope_isBoundedUnder_of_positiveGlobalBoundedSolution
      hsol)

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomain_actualLinearSpatialMinimumDini_of_positiveGlobalBoundedSolution
