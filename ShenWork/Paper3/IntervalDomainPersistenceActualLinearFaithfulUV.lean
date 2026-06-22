import ShenWork.Paper3.IntervalDomainPersistenceActualLinearDini
import ShenWork.Paper3.IntervalDomainPersistenceFaithfulUV
import ShenWork.Paper3.IntervalDomainTheorem21Part1

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

theorem intervalDomain_liminf_v_ge_of_eventually_u_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {δ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hδ : 0 < δ)
    (hcv : IsCoboundedUnder GE.ge atTop
      (fun t => intervalDomain.infValue (v t)))
    (hu : ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, δ ≤ u t x) :
    p.ν / p.μ * δ ^ p.γ ≤
      Filter.liminf (fun t => intervalDomain.infValue (v t)) atTop := by
  have hv :
      ∀ᶠ t in atTop,
        ∀ x : intervalDomain.Point, p.ν / p.μ * δ ^ p.γ ≤ v t x :=
    intervalDomain_eventually_v_lower_of_eventually_u_lower hsol hδ hu
  have hVpos : 0 < p.ν / p.μ * δ ^ p.γ :=
    mul_pos (div_pos p.hν p.hμ) (Real.rpow_pos_of_pos hδ _)
  exact liminf_ge_of_eventuallyLowerBound hcv
    (intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower hVpos hv)

theorem paperFaithfulLiminfLowerUV_of_eventually_u_lower
    {p : CM2Params} {u v : ℝ → intervalDomain.Point → ℝ} {δ : ℝ}
    (hsol : PositiveGlobalBoundedSolution intervalDomain p u v)
    (hδ : 0 < δ)
    (hcobdd : PaperFaithfulLiminfCoboundedUV intervalDomain u v)
    (hu : ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, δ ≤ u t x) :
    PaperFaithfulLiminfLowerUV intervalDomain p u v δ := by
  rcases hcobdd with ⟨hcu, hcv⟩
  refine ⟨?_, ?_⟩
  · exact liminf_ge_of_eventuallyLowerBound hcu
      (intervalDomain_eventuallyLowerBound_of_eventually_pointwise_lower hδ hu)
  · exact intervalDomain_liminf_v_ge_of_eventually_u_lower hsol hδ hcv hu

def ActualLinearPart2EventualU (p : CM2Params) : Prop :=
  0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
    p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∀ᶠ t in atTop,
            ∀ x : intervalDomain.Point, theorem21Part2LowerU p ≤ u t x

theorem ActualLinearPart2EventualU.to_liminfUVRaw
    {p : CM2Params}
    (h : ActualLinearPart2EventualU p)
    (hcobdd : ∀ u v : ℝ → intervalDomain.Point → ℝ,
      PositiveGlobalBoundedSolution intervalDomain p u v →
        PaperFaithfulLiminfCoboundedUV intervalDomain u v) :
    UniformPersistencePart2LiminfUVRaw intervalDomain p := by
  intro ha hb hχ0 hm hβ hχ u v hsol
  have hδ : 0 < theorem21Part2LowerU p := by
    simpa [theorem21Part2LowerU] using
      theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ
  have hu := h ha hb hχ0 hm hβ hχ u v hsol
  simpa [theorem21Part2LowerU] using
    paperFaithfulLiminfLowerUV_of_eventually_u_lower
      hsol hδ (hcobdd u v hsol) hu

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomain_liminf_v_ge_of_eventually_u_lower
#print axioms ShenWork.Paper3.ActualLinearPart2EventualU.to_liminfUVRaw
