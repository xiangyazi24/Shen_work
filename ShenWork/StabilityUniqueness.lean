/-
  ShenWork/StabilityUniqueness.lean
  Section 5: Uniqueness and stability of traveling wave solutions.
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

variable {p : CMParams} [PDETheory p]

theorem stability_traveling_wave
    (hparam : (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
              (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (c : ℝ) (hc : cStarStar p < c)
    (U V : ℝ → ℝ) (hTW : IsTravelingWave p c U V)
    (u₀ : ℝ → ℝ) (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - U (x - c * t)| < ε) :=
  PDETheory.tw_stability hparam c hc U V hTW u₀ hu₀_nn

theorem uniqueness_traveling_wave
    (hparam : (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
              (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (c : ℝ) (hc : cStarStar p < c)
    (U₁ V₁ U₂ V₂ : ℝ → ℝ)
    (hTW₁ : IsTravelingWave p c U₁ V₁)
    (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : ∀ x, U₁ x < Real.exp (-kappa c * x))
    (hbound₂ : ∀ x, U₂ x < Real.exp (-kappa c * x)) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x) :=
  PDETheory.tw_uniqueness hparam c hc U₁ V₁ U₂ V₂ hTW₁ hTW₂ hbound₁ hbound₂

end
