/-
  ShenWork/Paper3/Defs.lean
  Chen-Ruau-Shen (arXiv:2604.02599): Persistence and stabilization
-/
import ShenWork.Paper2.Defs

open Filter Topology

noncomputable section

def equilibrium (p : CM2Params) (_hab : 0 < p.a ∧ 0 < p.b) : ℝ × ℝ :=
  ((p.a / p.b) ^ (1 / p.α), p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ)

def IsGloballyAsymptoticallyStable (p : CM2Params) (u_star v_star : ℝ) : Prop :=
  ∀ u v : ℝ → ℝ → ℝ,
    IsGlobalClassicalSolution2 p u v → IsBounded2 u →
    Tendsto (fun t => ⨆ x, |u t x - u_star|) atTop (𝓝 0) ∧
    Tendsto (fun t => ⨆ x, |v t x - v_star|) atTop (𝓝 0)

theorem cm3_persistence (p : CM2Params) (hm : 1 ≤ p.m) :
    ∀ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 p u v → IsBounded2 u →
      (∃ δ > 0, ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x) := by sorry

theorem cm3_global_stability_neg (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (hab : 0 < p.a ∧ 0 < p.b) :
    let (u_star, v_star) := equilibrium p hab
    IsGloballyAsymptoticallyStable p u_star v_star := by sorry

end
