import ShenWork.Paper3.IntervalDomainPersistenceActualLinearPart2
import ShenWork.Paper3.IntervalDomainPersistenceSlopeBound
import ShenWork.Paper3.IntervalDomainPersistenceVCobounds

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Part2 liminf persistence after discharging the generic slope-boundedness
and `v`-coboundedness side inputs from a positive global bounded solution.

The only remaining analytic input is the actual-linear spatial-minimum Dini
inequality itself. -/
theorem intervalDomain_part2_liminfUV_of_actualLinearDini_proven_inputs
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hD : ActualLinearSpatialMinimumDini p u)
    (hT0 : 0 < T0) :
    theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u ∧
      p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
        liminfInfValue intervalDomain v :=
  intervalDomain_part2_liminfUV_of_actualLinearDini
    ha hb hχ0 hm hβ hχ hsol hD
    (intervalDomainSpatialMin_slope_isBoundedUnder_of_positiveGlobalBoundedSolution
      hsol)
    hT0
    (intervalDomain_infValue_v_isCoboundedUnder_of_positiveGlobalBoundedSolution
      hsol)

/-- Raw Part2 package from a per-solution proof of the actual-linear Dini
minimum inequality. -/
theorem intervalDomain_uniformPersistencePart2Raw_of_actualLinearDini
    {p : CM2Params}
    (hDini : ∀ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
        ActualLinearSpatialMinimumDini p u) :
    UniformPersistencePart2Raw intervalDomain p := by
  intro ha hb hχ0 hm hβ hχ u v hsol
  simpa [theorem21Part2LowerU] using
    intervalDomain_part2_liminfUV_of_actualLinearDini_proven_inputs
      ha hb hχ0 hm hβ hχ hsol (hDini u v hsol)
      (by norm_num : 0 < (1 : ℝ))

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_part2_liminfUV_of_actualLinearDini_proven_inputs
#print axioms ShenWork.Paper3.intervalDomain_uniformPersistencePart2Raw_of_actualLinearDini
