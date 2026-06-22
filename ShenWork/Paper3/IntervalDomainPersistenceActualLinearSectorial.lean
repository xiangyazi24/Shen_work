import ShenWork.Paper3.IntervalDomainPersistenceActualLinearPart2Proved
import ShenWork.Paper3.IntervalDomainPersistenceLogistic

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_uniformPersistencePart1Raw_of_part2_smallLinear
    {p : CM2Params}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    UniformPersistencePart1Raw intervalDomain p := by
  intro _hm_ge u v hsol
  have hUV :
      theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u ∧
        p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
          liminfInfValue intervalDomain v :=
    intervalDomain_part2_liminfUV_proven ha hb hχ0 hm hβ hχ hsol
      (by norm_num : 0 < (1 : ℝ))
  have hδ : 0 < theorem21Part2LowerU p := by
    simpa [theorem21Part2LowerU] using
      theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ
  have huinf_pos : 0 < liminfInfValue intervalDomain u :=
    lt_of_lt_of_le hδ hUV.1
  have hv :
      p.ν / p.μ * (liminfInfValue intervalDomain u) ^ p.γ ≤
        liminfInfValue intervalDomain v :=
    intervalDomain_liminf_v_ge_of_u_liminf_lower' hsol huinf_pos
      (intervalDomain_infValue_v_isCoboundedUnder_of_positiveGlobalBoundedSolution
        hsol)
      le_rfl
  exact ⟨theorem21Part2LowerU p, hδ, hUV.1, hv⟩

theorem intervalDomain_uniformPersistencePart3Raw_vacuous_of_m_eq_one
    {p : CM2Params}
    (hm : p.m = 1) :
    UniformPersistencePart3Raw intervalDomain p := by
  intro _ha _hb _hχ0 hm_gt _hβ
  exact False.elim (by linarith)

theorem intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
    {p : CM2Params} {uBar : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1))) :
    IntervalDomainSectorialTheorem21Persistence p uBar where
  part1 :=
    intervalDomain_uniformPersistencePart1Raw_of_part2_smallLinear
      ha hb hχ0 hm hβ hχ
  part2 := intervalDomain_uniformPersistencePart2Raw_proven
  part3 := intervalDomain_uniformPersistencePart3Raw_vacuous_of_m_eq_one hm
  part4 := intervalDomain_uniformPersistencePart4Raw_vacuous_of_a_pos ha

end

end ShenWork.Paper3

#print axioms
  ShenWork.Paper3.intervalDomain_uniformPersistencePart1Raw_of_part2_smallLinear
#print axioms
  ShenWork.Paper3.intervalDomain_uniformPersistencePart3Raw_vacuous_of_m_eq_one
#print axioms
  ShenWork.Paper3.intervalDomain_sectorialTheorem21Persistence_actualLinearSmall
