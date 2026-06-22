import ShenWork.Paper3.IntervalDomainPersistenceElliptic
import ShenWork.Paper3.IntervalDomainSectorialNonlinearBridges

open Filter Topology
open ShenWork.IntervalDomain

namespace ShenWork.Paper3

noncomputable section

def theorem21Part2LowerU (p : CM2Params) : ℝ :=
  ((p.a - p.χ₀ * p.μ * Theta_beta (p.β - 1)) / p.b) ^ (1 / p.α)

def theorem21Part3LowerU (p : CM2Params) : ℝ :=
  min 1 (p.a / (p.b + p.χ₀ * p.μ * Theta_beta (p.β - 1))) ^
    max (1 / (p.m - 1)) (1 / p.α)

structure IntervalDomainLogisticPersistenceInputs
    (p : CM2Params) : Prop where
  part1ULower :
    0 < p.a → 0 < p.b → 1 ≤ p.m →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∃ deltaU > 0,
            ∀ᶠ t in atTop, ∀ x : intervalDomain.Point, deltaU ≤ u t x
  part1Liminf :
    0 < p.a → 0 < p.b → 1 ≤ p.m →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∃ deltaU > 0,
            deltaU ≤ liminfInfValue intervalDomain u ∧
            p.ν / p.μ * (liminfInfValue intervalDomain u) ^ p.γ ≤
              liminfInfValue intervalDomain v ∧
            (∀ᶠ t in atTop, ∀ x : intervalDomain.Point, deltaU ≤ u t x) ∧
            (∀ᶠ t in atTop, ∀ x : intervalDomain.Point,
              p.ν / p.μ * deltaU ^ p.γ ≤ v t x)
  part2ULower :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            ∀ᶠ t in atTop,
              ∀ x : intervalDomain.Point, theorem21Part2LowerU p ≤ u t x
  part2Liminf :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → p.m = 1 → 1 ≤ p.β →
      p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)) →
        ∀ u v : ℝ → intervalDomain.Point → ℝ,
          PositiveGlobalBoundedSolution intervalDomain p u v →
            theorem21Part2LowerU p ≤ liminfInfValue intervalDomain u ∧
            p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤
              liminfInfValue intervalDomain v
  part3ULower :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          ∀ᶠ t in atTop,
            ∀ x : intervalDomain.Point, theorem21Part3LowerU p ≤ u t x
  part3Liminf :
    0 < p.a → 0 < p.b → 0 < p.χ₀ → 1 < p.m → 1 ≤ p.β →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        PositiveGlobalBoundedSolution intervalDomain p u v →
          theorem21Part3LowerU p ≤ liminfInfValue intervalDomain u ∧
          p.ν / p.μ * theorem21Part3LowerU p ^ p.γ ≤
            liminfInfValue intervalDomain v

theorem intervalDomain_uniformPersistencePart4Raw_vacuous_of_a_pos
    {p : CM2Params} {uBar : ℝ}
    (ha : 0 < p.a) :
    UniformPersistencePart4Raw intervalDomain p (fun _ => uBar) 1 := by
  intro _hgaussian ha0
  exact False.elim ((ne_of_gt ha) ha0)

theorem IntervalDomainLogisticPersistenceInputs.to_pointwise_part1
    {p : CM2Params}
    (h : IntervalDomainLogisticPersistenceInputs p)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    IntervalDomainUniformPersistencePart1PointwiseRaw p := by
  intro hm u v hsol
  exact h.part1Liminf ha hb hm u v hsol

theorem IntervalDomainLogisticPersistenceInputs.to_pointwise_part2
    {p : CM2Params}
    (h : IntervalDomainLogisticPersistenceInputs p) :
    IntervalDomainUniformPersistencePart2PointwiseRaw p := by
  intro ha hb hχ0 hm hβ hχ u v hsol
  have hpointU :
      ∀ᶠ t in atTop,
        ∀ x : intervalDomain.Point, theorem21Part2LowerU p ≤ u t x :=
    h.part2ULower ha hb hχ0 hm hβ hχ u v hsol
  have hdelta :
      0 < theorem21Part2LowerU p := by
    simpa [theorem21Part2LowerU] using
      theorem_2_1_part2_lowerU_pos p ha hb hχ0 hm hβ hχ
  have hpointV :
      ∀ᶠ t in atTop,
        ∀ x : intervalDomain.Point,
          p.ν / p.μ * theorem21Part2LowerU p ^ p.γ ≤ v t x :=
    intervalDomain_eventually_v_lower_of_eventually_u_lower
      hsol hdelta hpointU
  rcases h.part2Liminf ha hb hχ0 hm hβ hχ u v hsol with
    ⟨huLower, hvLower⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [theorem21Part2LowerU] using huLower
  · simpa [theorem21Part2LowerU] using hvLower
  · simpa [theorem21Part2LowerU] using hpointU
  · simpa [theorem21Part2LowerU] using hpointV

theorem IntervalDomainLogisticPersistenceInputs.to_pointwise_part3
    {p : CM2Params}
    (h : IntervalDomainLogisticPersistenceInputs p) :
    IntervalDomainUniformPersistencePart3PointwiseRaw p := by
  intro ha hb hχ0 hm hβ u v hsol
  have hpointU :
      ∀ᶠ t in atTop,
        ∀ x : intervalDomain.Point, theorem21Part3LowerU p ≤ u t x :=
    h.part3ULower ha hb hχ0 hm hβ u v hsol
  have hdelta :
      0 < theorem21Part3LowerU p := by
    simpa [theorem21Part3LowerU] using
      theorem_2_1_part3_lowerU_pos p ha hb hχ0 hm hβ
  have hpointV :
      ∀ᶠ t in atTop,
        ∀ x : intervalDomain.Point,
          p.ν / p.μ * theorem21Part3LowerU p ^ p.γ ≤ v t x :=
    intervalDomain_eventually_v_lower_of_eventually_u_lower
      hsol hdelta hpointU
  rcases h.part3Liminf ha hb hχ0 hm hβ u v hsol with
    ⟨huLower, hvLower⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [theorem21Part3LowerU] using huLower
  · simpa [theorem21Part3LowerU] using hvLower
  · simpa [theorem21Part3LowerU] using hpointU
  · simpa [theorem21Part3LowerU] using hpointV

theorem IntervalDomainLogisticPersistenceInputs.to_part1Raw
    {p : CM2Params}
    (h : IntervalDomainLogisticPersistenceInputs p)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    UniformPersistencePart1Raw intervalDomain p :=
  intervalDomain_uniformPersistencePart1Raw_of_pointwise
    (h.to_pointwise_part1 ha hb)

theorem IntervalDomainLogisticPersistenceInputs.to_part2Raw
    {p : CM2Params}
    (h : IntervalDomainLogisticPersistenceInputs p) :
    UniformPersistencePart2Raw intervalDomain p :=
  intervalDomain_uniformPersistencePart2Raw_of_pointwise
    h.to_pointwise_part2

theorem IntervalDomainLogisticPersistenceInputs.to_part3Raw
    {p : CM2Params}
    (h : IntervalDomainLogisticPersistenceInputs p) :
    UniformPersistencePart3Raw intervalDomain p :=
  intervalDomain_uniformPersistencePart3Raw_of_pointwise
    h.to_pointwise_part3

def IntervalDomainLogisticPersistenceInputs.to_persistence
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainLogisticPersistenceInputs p)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    IntervalDomainSectorialTheorem21Persistence p uBar where
  part1 := h.to_part1Raw ha hb
  part2 := h.to_part2Raw
  part3 := h.to_part3Raw
  part4 := intervalDomain_uniformPersistencePart4Raw_vacuous_of_a_pos ha

theorem IntervalDomainLogisticPersistenceInputs.to_persistenceFrontiers
    {p : CM2Params} {uBar : ℝ}
    (h : IntervalDomainLogisticPersistenceInputs p)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    IntervalDomainSectorialTheorem21PersistenceFrontiers p uBar :=
  (h.to_persistence ha hb).to_persistenceFrontiers

end

end ShenWork.Paper3
