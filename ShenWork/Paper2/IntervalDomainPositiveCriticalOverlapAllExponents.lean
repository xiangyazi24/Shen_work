import ShenWork.Paper2.IntervalDomainLocalExistenceAllExponents
import ShenWork.Paper2.IntervalDomainTheorem12PositiveCriticalUnconditional
import ShenWork.Paper2.IntervalDomainL2USubHorizonGluing

/-!
# Positive-critical overlap uniqueness for all positive exponents
-/

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.Paper2.IntervalDomainRestartedLpLinfProducer

/-- For the paper's uniformly positive datum, the positive-critical affine
upper estimate and compact sub-horizon positivity give the two-sided bounds
needed by the arbitrary-`γ` L² uniqueness argument. -/
def positiveCriticalOverlapUniqueAt_allExponents
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hβ : 1 ≤ p.β) (hm : p.m = 1)
    (hχ : 0 < p.χ₀) (hthreshold : p.χ₀ < chiBeta p)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomain u₀) :
    IntervalClassicalSolutionOverlapUniqueAt p u₀ := by
  intro T₁ T₂ d₁ d₂ t ht0 htmin x
  have hbdd₀ := hu₀.admissible.1
  have hPos : IntervalDomainPosDatumLowerBound u₀ := hu₀.floor
  have hb₁ := critical_bounded_before_positive_restarted_affine_intervalDomain
    hguard hu₀.toPositive d₁.sol d₁.trace hβ hm hχ hthreshold
  have hb₂ := critical_bounded_before_positive_restarted_affine_intervalDomain
    hguard hu₀.toPositive d₂.sol d₂.trace hβ hm hχ hthreshold
  obtain ⟨M₁, hM₁⟩ := hb₁
  obtain ⟨M₂, hM₂⟩ := hb₂
  refine intervalDomain_classicalSolution_overlap_unique_of_subHorizonBound
    d₁.sol d₂.sol d₁.trace d₂.trace hbdd₀ ?_ t ht0 htmin x
  intro T' hT' hT'min
  have hT'₁ : T' < T₁ := hT'min.trans_le (min_le_left _ _)
  have hT'₂ : T' < T₂ := hT'min.trans_le (min_le_right _ _)
  obtain ⟨δ₁, hδ₁, hlo₁⟩ := lift_u_uniformPositive_on_halfHorizon
    d₁.sol d₁.trace hPos hu₀.admissible hT' hT'₁
  obtain ⟨δ₂, hδ₂, hlo₂⟩ := lift_u_uniformPositive_on_halfHorizon
    d₂.sol d₂.trace hPos hu₀.admissible hT' hT'₂
  refine ⟨min δ₁ δ₂, max M₁ M₂, lt_min hδ₁ hδ₂, ?_⟩
  intro τ hτ hτT'
  have hτ₁ : τ < T₁ := lt_of_le_of_lt hτT' hT'₁
  have hτ₂ : τ < T₂ := lt_of_le_of_lt hτT' hT'₂
  constructor
  · intro y hy
    have hpos := solution_lift_pos d₁.sol ⟨hτ, hτ₁⟩ y hy
    have habs := abs_lift_le_supNorm d₁.sol ⟨hτ, hτ₁⟩ hy
    rw [abs_of_pos hpos] at habs
    exact ⟨(min_le_left _ _).trans (hlo₁ τ hτ hτT' y hy),
      (habs.trans (hM₁ τ hτ hτ₁)).trans (le_max_left _ _)⟩
  · intro y hy
    have hpos := solution_lift_pos d₂.sol ⟨hτ, hτ₂⟩ y hy
    have habs := abs_lift_le_supNorm d₂.sol ⟨hτ, hτ₂⟩ hy
    rw [abs_of_pos hpos] at habs
    exact ⟨(min_le_right _ _).trans (hlo₂ τ hτ hτT' y hy),
      (habs.trans (hM₂ τ hτ hτ₂)).trans (le_max_right _ _)⟩

#print axioms positiveCriticalOverlapUniqueAt_allExponents

end ShenWork.Paper2.IntervalDomainM

end
