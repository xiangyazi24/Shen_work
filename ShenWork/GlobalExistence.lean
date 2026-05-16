/-
  ShenWork/GlobalExistence.lean
  Section 3: Global existence, boundedness, and stabilization.
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

theorem global_existence_negative_sensitivity (p : CMParams) (hp : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ t x, 0 ≤ t → u t x ≤ max 1 (⨆ x, u₀ x)) ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → u t x ≤ 1 + ε) :=
  cm_global_exist_neg p hp u₀ hu₀_cont hu₀_bdd hu₀_nn

theorem global_existence_positive_sensitivity (p : CMParams) (hp : 0 < p.χ)
    (hα : p.α > p.m + p.γ - 1 ∨
      (p.α = p.m + p.γ - 1 ∧
       p.χ < min ((2 * p.m - 1) / (p.m - 1)) ((p.m + p.γ - 1) / (p.γ - 1))))
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v ∧ IsBoundedGlobal u :=
  cm_global_exist_pos p hp hα u₀ hu₀_cont hu₀_bdd hu₀_nn

theorem stabilization_negative_sensitivity (p : CMParams) (hp : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) (hu₀_inf : ∃ δ > 0, ∀ x, δ ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0) :=
  cm_stabilize_neg p hp u₀ hu₀_cont hu₀_bdd hu₀_nn hu₀_inf

theorem stabilization_small_positive_sensitivity (p : CMParams)
    (hp : 0 < p.χ) (hp2 : p.χ < 1 / 2) (hα : p.m + p.γ - 1 ≤ p.α)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) (hu₀_inf : ∃ δ > 0, ∀ x, δ ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0) :=
  cm_stabilize_small_pos p hp hp2 hα u₀ hu₀_cont hu₀_bdd hu₀_nn hu₀_inf

end
