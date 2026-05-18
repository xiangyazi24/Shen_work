/-
  ShenWork/Paper2/Defs.lean
  Chen-Ruau-Shen (arXiv:2512.14858): Boundedness and global existence
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open Filter Topology

noncomputable section

structure CM2Params where
  N : ℕ
  hN : 0 < N
  α : ℝ
  γ : ℝ
  m : ℝ
  μ : ℝ
  ν : ℝ
  χ₀ : ℝ
  a : ℝ
  b : ℝ
  β : ℝ
  hα : 0 < α
  hγ : 0 < γ
  hm : 0 < m
  hμ : 0 < μ
  hν : 0 < ν
  ha : 0 ≤ a
  hb : 0 ≤ b
  hβ : 0 ≤ β

def Psi_beta (β : ℝ) : ℝ := (β / (1 + β)) ^ (1 + β)
def Theta_beta (β : ℝ) : ℝ := β ^ β * (1 + β) ^ (-(1 + β))

/-!
This is a toy placeholder, not the bounded-domain parabolic-elliptic PDE from
the paper.  It is kept only to document why the old paper-level theorem shapes
were unsound under the current definitions.
-/
structure IsToyClassicalSolution2 (p : CM2Params) (T : ℝ) (u _v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
  pde_satisfied : True

def IsToyGlobalClassicalSolution2 (p : CM2Params) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsToyClassicalSolution2 p T u v

def IsToyBounded2 (u : ℝ → ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

theorem persistence_property_false_under_current_solution_def
    (p : CM2Params) :
    ¬ (∀ u v : ℝ → ℝ → ℝ,
      IsToyGlobalClassicalSolution2 p u v → IsToyBounded2 u →
      ∃ δ > 0, ∀ _ε > 0, ∃ T, ∀ t x, T ≤ t → δ ≤ u t x) := by
  intro h
  let u : ℝ → ℝ → ℝ := fun t _x => Real.exp (-t)
  let v : ℝ → ℝ → ℝ := fun _t _x => 0
  have hglobal : IsToyGlobalClassicalSolution2 p u v := by
    intro T hT
    refine ⟨hT, ?_, trivial⟩
    intro t _x _ht0 _htT
    dsimp [u]
    positivity
  have hbdd : IsToyBounded2 u := by
    refine ⟨1, ?_⟩
    intro t _x ht0
    dsimp [u]
    rw [abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨δ, hδ_pos, hpersist⟩ := h u v hglobal hbdd
  obtain ⟨T, hT⟩ := hpersist 1 one_pos
  let t : ℝ := max T (-Real.log δ + 1)
  have htT : T ≤ t := le_max_left _ _
  have htlog : -Real.log δ + 1 ≤ t := le_max_right _ _
  have hδ_le : δ ≤ u t 0 := hT t 0 htT
  have hlt_log : -t < Real.log δ := by linarith
  have hexp_lt : u t 0 < δ := by
    dsimp [u]
    calc
      Real.exp (-t) < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr hlt_log
      _ = δ := Real.exp_log hδ_pos
  linarith

/-- Under the current toy solution definition, the positive equilibrium is a global solution. -/
theorem cm2_constant_solution_under_current_solution_def
    (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    let c := (p.a / p.b) ^ (1 / p.α)
    ∃ u v : ℝ → ℝ → ℝ, IsToyGlobalClassicalSolution2 p u v ∧ IsToyBounded2 u := by
  refine ⟨fun _ _ => (p.a / p.b) ^ (1 / p.α),
         fun _ _ => p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ,
         fun T hT => ⟨hT, fun _ _ _ _ => by positivity, trivial⟩,
         ⟨(p.a / p.b) ^ (1 / p.α), fun t x _ => by
            simp only; rw [abs_of_nonneg (Real.rpow_nonneg (div_nonneg (le_of_lt ha) (le_of_lt hb)) _)]⟩⟩

end
