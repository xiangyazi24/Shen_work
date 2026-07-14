import ShenWork.Paper3.IntervalDomainMLinearFluxTransfer
import ShenWork.Paper3.IntervalDomainPersistenceActualLinearPart2Proved

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

/-- Paper 3, Theorem 2.1(2), transported to the paper-faithful interval model
on its stated `m = 1` branch. -/
theorem intervalDomainM_part2_liminfUV_proven
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {T0 : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ₀ : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hsolM : PositiveGlobalBoundedSolution intervalDomainM p u v)
    (hT0 : 0 < T0) :
    theorem21Part2LowerU p ≤ liminfInfValue intervalDomainM u ∧
      p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
        liminfInfValue intervalDomainM v := by
  have hsol : PositiveGlobalBoundedSolution intervalDomain p u v :=
    positiveGlobalBoundedSolution_intervalDomain_of_M_m_one hm hsolM
  have hlegacy := intervalDomain_part2_liminfUV_proven
    ha hb hχ₀ hm hβ hχ hsol hT0
  simpa [liminfInfValue, intervalDomain, intervalDomainM] using hlegacy

theorem intervalDomainM_uniformPersistencePart2Raw_proven
    {p : CM2Params} :
    UniformPersistencePart2Raw intervalDomainM p := by
  intro ha hb hχ₀ hm hβ hχ u v hsol
  simpa [theorem21Part2LowerU] using
    intervalDomainM_part2_liminfUV_proven
      ha hb hχ₀ hm hβ hχ hsol (T0 := 1) one_pos

theorem Theorem_2_1_part2_intervalDomainM_proven
    (p : CM2Params) :
    Theorem_2_1_part2 intervalDomainM p := by
  exact intervalDomainM_uniformPersistencePart2Raw_proven

end


end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_part2_liminfUV_proven
#print axioms ShenWork.Paper3.intervalDomainM_uniformPersistencePart2Raw_proven
#print axioms ShenWork.Paper3.Theorem_2_1_part2_intervalDomainM_proven
