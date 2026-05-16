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

/-- PDE Theory for Part II: persistence and stabilization. -/
class PDETheory3 (p : CM2Params) : Prop where
  persistence : 1 ≤ p.m →
    ∀ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v → IsBounded2 u →
    ∃ δ > 0, ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x
  global_stability_neg : p.χ₀ ≤ 0 → 1 ≤ p.m → 0 < p.a → 0 < p.b →
    let (u_star, v_star) := equilibrium p ⟨‹_›, ‹_›⟩
    IsGloballyAsymptoticallyStable p u_star v_star

variable {p : CM2Params} [PDETheory3 p]

theorem cm3_persistence (hm : 1 ≤ p.m)
    (u v : ℝ → ℝ → ℝ) (hg : IsGlobalClassicalSolution2 p u v) (hb : IsBounded2 u) :
    ∃ δ > 0, ∀ ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x :=
  PDETheory3.persistence hm u v hg hb

theorem cm3_global_stability_neg (hχ : p.χ₀ ≤ 0) (hm : 1 ≤ p.m)
    (ha : 0 < p.a) (hb : 0 < p.b) :
    let (u_star, v_star) := equilibrium p ⟨ha, hb⟩
    IsGloballyAsymptoticallyStable p u_star v_star :=
  PDETheory3.global_stability_neg hχ hm ha hb

end
