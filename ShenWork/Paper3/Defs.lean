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

theorem cm3_persistence_false_under_current_solution_def
    (p : CM2Params) :
    ¬ (∀ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 p u v → IsBounded2 u →
      ∃ δ > 0, ∀ _ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x) :=
  persistence_property_false_under_current_solution_def p

theorem cm3_global_stability_neg_false_under_current_solution_def
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    let (u_star, v_star) := equilibrium p hab
    ¬ IsGloballyAsymptoticallyStable p u_star v_star := by
  dsimp [equilibrium]
  intro hstable
  let uStar : ℝ := (p.a / p.b) ^ (1 / p.α)
  let vStar : ℝ := p.ν / p.μ * uStar ^ p.γ
  let u : ℝ → ℝ → ℝ := fun _ _ => uStar + 1
  let v : ℝ → ℝ → ℝ := fun _ _ => vStar + 1
  have huStar_nonneg : 0 ≤ uStar := by
    exact Real.rpow_nonneg (div_nonneg hab.1.le hab.2.le) _
  have hglobal : IsGlobalClassicalSolution2 p u v := by
    intro T hT
    refine ⟨hT, ?_, trivial⟩
    intro _t _x _ht0 _htT
    dsimp [u]
    linarith
  have hbdd : IsBounded2 u := by
    refine ⟨uStar + 1, ?_⟩
    intro _t _x _ht0
    dsimp [u]
    have hnonneg : 0 ≤ uStar + 1 := by linarith
    rw [abs_of_nonneg hnonneg]
  have hconv := hstable u v hglobal hbdd
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hzero :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa [u, uStar, ciSup_const] using hconv.1
  have hbad : (1 : ℝ) = 0 :=
    tendsto_nhds_unique hone hzero
  norm_num at hbad

end
