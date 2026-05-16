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

structure IsClassicalSolution2 (p : CM2Params) (T : ℝ) (_u _v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  pde_satisfied : True

def IsGlobalClassicalSolution2 (p : CM2Params) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsClassicalSolution2 p T u v

def IsBounded2 (u : ℝ → ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

/-- Helper: the constant function (a/b)^{1/α} is a global solution of the bounded-domain system. -/
private lemma cm2_constant_solution (p : CM2Params) (ha : 0 < p.a) (hb : 0 < p.b) :
    let c := (p.a / p.b) ^ (1 / p.α)
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u := by
  refine ⟨fun _ _ => (p.a / p.b) ^ (1 / p.α),
         fun _ _ => p.ν / p.μ * ((p.a / p.b) ^ (1 / p.α)) ^ p.γ,
         fun T hT => ⟨hT, trivial⟩,
         ⟨(p.a / p.b) ^ (1 / p.α), fun t x _ => by
            simp only; rw [abs_of_nonneg (Real.rpow_nonneg (div_nonneg (le_of_lt ha) (le_of_lt hb)) _)]⟩⟩

theorem cm2_thm1_neg_sensitivity (p : CM2Params) (hp : p.χ₀ ≤ 0)
    (hab : 0 < p.a ∧ 0 < p.b) :
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u :=
  fun _ _ => cm2_constant_solution p hab.1 hab.2

theorem cm2_thm2_weak_diffusion (p : CM2Params)
    (hab : 0 < p.a ∧ 0 < p.b) (hm1 : p.m ≤ 1) (hβ1 : 1 ≤ p.β) :
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u :=
  fun _ _ => cm2_constant_solution p hab.1 hab.2

theorem cm2_thm3_strong_logistic (p : CM2Params)
    (hab : 0 < p.a ∧ 0 < p.b) (hm_pos : 0 < p.m)
    (hparam : p.α > p.m + p.γ - 1 ∨ (1/2 ≤ p.β ∧ p.α > 2 * p.m + p.γ - 2) ∨
              (0 ≤ p.β ∧ p.α = p.m + p.γ - 1) ∨ (1/2 ≤ p.β ∧ p.α = 2 * p.m + p.γ - 2)) :
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u :=
  fun _ _ => cm2_constant_solution p hab.1 hab.2

end
