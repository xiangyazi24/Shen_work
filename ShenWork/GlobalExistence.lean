/-
  ShenWork/GlobalExistence.lean

  Section 3: Global existence, boundedness, and stabilization of positive
  classical solutions. Proofs of Propositions 1.1 and 1.2.
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

/-! ## Proposition 1.1: Global existence and boundedness -/

/-- Proposition 1.1(1): If χ ≤ 0 and m,α,γ ≥ 1, then for any u₀ ∈ C^b_unif(ℝ)
    with u₀ ≥ 0, the classical solution exists globally (T_max = ∞),
    u(t,x;u₀) ≤ max{1, sup u₀(x)} for all t ≥ 0, x ∈ ℝ,
    and lim sup_{t→∞} sup_x u(t,x;u₀) ≤ 1. -/
theorem global_existence_negative_sensitivity (p : CMParams) (hp : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ t x, 0 ≤ t → u t x ≤ max 1 (⨆ x, u₀ x)) ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → u t x ≤ 1 + ε) := by
  sorry

/-- Proposition 1.1(2): If χ > 0 and either α > m+γ−1, or
    0 < χ < min{(2m−1)/(m−1), (m+γ−1)/(γ−1)} and α = m+γ−1,
    then the solution exists globally and lim sup is bounded. -/
theorem global_existence_positive_sensitivity (p : CMParams) (hp : 0 < p.χ)
    (hα : p.α > p.m + p.γ - 1 ∨
      (p.α = p.m + p.γ - 1 ∧
       p.χ < min ((2 * p.m - 1) / (p.m - 1)) ((p.m + p.γ - 1) / (p.γ - 1))))
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      IsBoundedGlobal u := by
  sorry

/-! ## Proposition 1.2: Stability of the positive constant solution (1,1) -/

/-- Proposition 1.2(1): If χ ≤ 0, then for any u₀ ∈ C^b_unif(ℝ) with u₀ ≥ 0
    and inf u₀(x) > 0, the solution stabilizes:
    lim_{t→∞} ‖u(t,·;u₀) − 1‖_∞ = 0. -/
theorem stabilization_negative_sensitivity (p : CMParams) (hp : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) (hu₀_inf : ∃ δ > 0, ∀ x, δ ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0) := by
  sorry

/-- Proposition 1.2(2): If 0 < χ < 1/2 and α ≥ m+γ−1, then stabilization holds. -/
theorem stabilization_small_positive_sensitivity (p : CMParams)
    (hp : 0 < p.χ) (hp2 : p.χ < 1 / 2) (hα : p.m + p.γ - 1 ≤ p.α)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) (hu₀_inf : ∃ δ > 0, ∀ x, δ ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0) := by
  sorry

end
