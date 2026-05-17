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

theorem cm3_persistence (_p : CM2Params) (_hm : 1 ≤ _p.m) :
    ∀ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 _p u v → IsBounded2 u →
      (∃ δ > 0, ∀ _ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x) := by
  intro u v hg _hb
  -- IsGlobalClassicalSolution2 gives u_pos: ∀ t x, 0 < t → t < T → 0 < u t x
  -- For t = 1: take T₀ = 2, then u_pos gives 0 < u 1 x for all x.
  -- Use δ = u 1 0 (a specific positive value) as a witness.
  -- But we need UNIFORM lower bound for ALL x and t ≥ T...
  -- From u_pos at t=1 and the specific value:
  have hu_pos_1 : 0 < u 1 0 := by
    have h2 := hg 2 (by norm_num : (0:ℝ) < 2)
    exact h2.u_pos 1 0 (by norm_num) (by norm_num)
  exact ⟨u 1 0, hu_pos_1, fun _ _ => ⟨1, fun t x ht => by
    -- This needs: u t x ≥ u 1 0 for t ≥ 1
    -- Not provable from u_pos alone (u could decrease)
    sorry⟩⟩

theorem cm3_global_stability_neg (p : CM2Params)
    (_hχ : p.χ₀ ≤ 0) (_hm : 1 ≤ p.m) (hab : 0 < p.a ∧ 0 < p.b) :
    let (u_star, v_star) := equilibrium p hab
    IsGloballyAsymptoticallyStable p u_star v_star := by
  -- For any globally defined bounded positive solution (u,v):
  -- need Tendsto (sup|u - u*|) and Tendsto (sup|v - v*|).
  -- Construct using constant equilibrium as the solution itself.
  intro u v hg hb
  -- Need u → u* and v → v*. Without PDE structure, can't prove convergence.
  sorry

end
