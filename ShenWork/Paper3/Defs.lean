/-
  ShenWork/Paper3/Defs.lean

  Definitions for Chen-Ruau-Shen (arXiv:2604.02599):
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type source,
   II: Persistence and stabilization"

  Same system as Paper 2, Part II focuses on long-time behavior:
  persistence, linear stability/instability, global stabilization.
-/
import ShenWork.Paper2.Defs

open Filter Topology

noncomputable section

/-! ## Positive constant equilibrium -/

/-- The unique positive constant equilibrium (u*, v*) when a, b > 0. -/
def equilibrium (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) : ℝ × ℝ :=
  ((p.a / p.b) ^ (1 / p.α), p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ)

/-! ## Stability definitions -/

/-- Linear stability: all eigenvalues σ_n of the linearization have negative real part. -/
def IsLinearlyStable (p : CM2Params) (u_star : ℝ) : Prop :=
  ∀ n : ℕ, -n + p.χ₀ * p.ν * p.γ * u_star ^ (p.m + p.γ - 1) /
    ((1 + p.ν / p.μ * u_star ^ p.γ) ^ p.β) * (n / (p.μ + n)) - p.a * p.α < 0

/-- Global asymptotic stability: all bounded positive solutions converge to (u*, v*). -/
def IsGloballyAsymptoticallyStable (p : CM2Params) (u_star v_star : ℝ) : Prop :=
  ∀ u v : ℝ → ℝ → ℝ,
    IsGlobalClassicalSolution2 p u v → IsBounded2 u →
    Tendsto (fun t => ⨆ x, |u t x - u_star|) atTop (𝓝 0) ∧
    Tendsto (fun t => ⨆ x, |v t x - v_star|) atTop (𝓝 0)

/-! ## Main theorems -/

/-- Theorem 2.1: Uniform persistence when m ≥ 1. -/
theorem cm3_persistence (p : CM2Params) (hm : 1 ≤ p.m) :
    ∀ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 p u v → IsBounded2 u →
      (∃ δ > 0, ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x) := by
  sorry

/-- Theorem 2.2: Linear stability/instability dichotomy. -/
theorem cm3_linear_stability (p : CM2Params)
    (hab : 0 < p.a ∧ 0 < p.b) :
    let (u_star, _) := equilibrium p hab
    -- χ₀ < χ* → linearly stable; χ₀ > χ* → unstable
    True := by
  sorry

/-- Theorem 2.3: Global stability with negative sensitivity (χ₀ ≤ 0, m ≥ 1). -/
theorem cm3_global_stability_neg (p : CM2Params)
    (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m) (hab : 0 < p.a ∧ 0 < p.b) :
    let (u_star, v_star) := equilibrium p hab
    IsGloballyAsymptoticallyStable p u_star v_star := by
  sorry

/-- Theorem 2.4: Global stability with strong logistic source. -/
theorem cm3_global_stability_strong_logistic (p : CM2Params)
    (hab : 0 < p.a ∧ 0 < p.b) (hm : 1 ≤ p.m)
    (hα : 1 ≤ p.α) (hγ : 0 < p.γ) :
    -- Under conditions (i)-(iv) on χ₀ smallness
    let (u_star, v_star) := equilibrium p hab
    True := by -- placeholder for the conditional stability result
  sorry

/-- Theorem 2.5: Global stability in minimal model (a = b = 0). -/
theorem cm3_minimal_model_stability (p : CM2Params)
    (ha : p.a = 0) (hb : p.b = 0)
    (hm : 1 ≤ p.m) (hβ : 1 ≤ p.β)
    (hχ_small : p.χ₀ < min (1/2) (1 / p.β)) :
    ∀ u_star : ℝ, 0 < u_star →
    -- Mass conservation: ∫ u₀ = |Ω| u*
    -- then u → u* uniformly
    True := by
  sorry

end
