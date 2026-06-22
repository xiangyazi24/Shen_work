import ShenWork.Paper3.IntervalDomainPersistenceActualLinearDiniProved
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearPart2ClosedInputs

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_part2_liminfUV_proven
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hT0 : 0 < T0) :
    theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u ∧
      p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
        liminfInfValue intervalDomain v := by
  have hD : ActualLinearSpatialMinimumDini p u :=
    intervalDomain_actualLinearSpatialMinimumDini_of_positiveGlobalBoundedSolution
      (le_of_lt hχ0) hβ hsol
  exact intervalDomain_part2_liminfUV_of_actualLinearDini_proven_inputs
    ha hb hχ0 hm hβ hχ hsol hD hT0

theorem intervalDomain_uniformPersistencePart2Raw_proven
    {p : CM2Params} :
    UniformPersistencePart2Raw intervalDomain p := by
  intro ha hb hχ0 hm hβ hχ u v hsol
  simpa [theorem21Part2LowerU] using
    intervalDomain_part2_liminfUV_proven
      ha hb hχ0 hm hβ hχ hsol (by norm_num : 0 < (1 : ℝ))

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_part2_liminfUV_proven
#print axioms ShenWork.Paper3.intervalDomain_uniformPersistencePart2Raw_proven
