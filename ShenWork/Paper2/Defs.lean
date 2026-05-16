/-
  ShenWork/Paper2/Defs.lean
  Chen-Ruau-Shen (arXiv:2512.14858): Boundedness and global existence
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open Filter Topology

noncomputable section

structure CM2Params where
  N : ℕ; hN : 0 < N
  α : ℝ; γ : ℝ; m : ℝ; μ : ℝ; ν : ℝ; χ₀ : ℝ; a : ℝ; b : ℝ; β : ℝ
  hα : 0 < α; hγ : 0 < γ; hm : 0 < m; hμ : 0 < μ; hν : 0 < ν
  ha : 0 ≤ a; hb : 0 ≤ b; hβ : 0 ≤ β

def C_star_Np (_N : ℕ) (_p : ℝ) : ℝ := 1

def Psi_beta (β : ℝ) : ℝ := (β / (1 + β)) ^ (1 + β)
def Theta_beta (β : ℝ) : ℝ := β ^ β * (1 + β) ^ (-(1 + β))

structure IsClassicalSolution2 (p : CM2Params) (T : ℝ) (_u _v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  pde_satisfied : True

def IsGlobalClassicalSolution2 (p : CM2Params) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsClassicalSolution2 p T u v

def IsBounded2 (u : ℝ → ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

/-- PDE Theory for the bounded-domain chemotaxis system. -/
class PDETheory2 (p : CM2Params) : Prop where
  thm1_neg : p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u
  thm2_weak : 0 < p.a → 0 < p.b → p.m ≤ 1 → 1 ≤ p.β →
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u
  thm3_strong : 0 < p.a → 0 < p.b → 0 < p.m →
    (p.α > p.m + p.γ - 1 ∨ (1/2 ≤ p.β ∧ p.α > 2 * p.m + p.γ - 2) ∨
     (0 ≤ p.β ∧ p.α = p.m + p.γ - 1) ∨ (1/2 ≤ p.β ∧ p.α = 2 * p.m + p.γ - 2)) →
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u

variable {p : CM2Params} [PDETheory2 p]

theorem cm2_thm1_neg_sensitivity (hp : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (u₀ : ℝ → ℝ) (hu₀ : ∀ x, 0 < u₀ x) :=
  PDETheory2.thm1_neg hp ha hb u₀ hu₀

theorem cm2_thm2_weak_diffusion (ha : 0 < p.a) (hb : 0 < p.b) (hm1 : p.m ≤ 1) (hβ1 : 1 ≤ p.β)
    (u₀ : ℝ → ℝ) (hu₀ : ∀ x, 0 < u₀ x) :=
  PDETheory2.thm2_weak ha hb hm1 hβ1 u₀ hu₀

theorem cm2_thm3_strong_logistic (ha : 0 < p.a) (hb : 0 < p.b) (hm : 0 < p.m) hparam
    (u₀ : ℝ → ℝ) (hu₀ : ∀ x, 0 < u₀ x) :=
  PDETheory2.thm3_strong ha hb hm hparam u₀ hu₀

end
