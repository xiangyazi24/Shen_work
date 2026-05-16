/-
  ShenWork/Paper2/Defs.lean

  Definitions for Chen-Ruau-Shen (arXiv:2512.14858):
  "Chemotaxis models with signal-dependent sensitivity and a logistic-type source,
   I: Boundedness and global existence"

  System (CM) on bounded Ω ⊂ ℝ^N with Neumann BC:
    u_t = Δu − χ₀ ∇·(uᵐ/(1+v)^β ∇v) + au − buᵅ⁺¹,   x ∈ Ω
    0   = Δv − μv + νuᵞ,                                 x ∈ Ω
    ∂u/∂n = ∂v/∂n = 0,                                    x ∈ ∂Ω
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open Filter Topology

noncomputable section

/-- Parameters for the bounded-domain chemotaxis system. -/
structure CM2Params where
  N : ℕ         -- spatial dimension
  hN : 0 < N
  α : ℝ         -- logistic exponent
  γ : ℝ         -- signal production exponent
  m : ℝ         -- cross-diffusion exponent
  μ : ℝ         -- signal decay rate
  ν : ℝ         -- signal production rate
  χ₀ : ℝ        -- chemotaxis sensitivity coefficient
  a : ℝ         -- logistic growth rate
  b : ℝ         -- logistic damping
  β : ℝ         -- signal-dependent sensitivity decay
  hα : 0 < α
  hγ : 0 < γ
  hm : 0 < m
  hμ : 0 < μ
  hν : 0 < ν
  ha : 0 ≤ a
  hb : 0 ≤ b
  hβ : 0 ≤ β

/-! ## Key constants -/

def C_star_Np (_N : ℕ) (_p : ℝ) : ℝ := 1 -- placeholder; depends on Calderon-Zygmund theory

/-- M*(N, p, μ, ν): auxiliary constant, eq (1.18). -/
def M_star (p : CM2Params) (q : ℝ) : ℝ :=
  p.ν ^ q * ((8 ^ q / q) * C_star_Np p.N q * (2 ^ q + 1 / p.μ ^ q) +
    2 ^ (2 * q) / ((q - 1) * q ^ q))

/-- Ψ_β := (β/(1+β))^{1+β}, eq (1.20). -/
def Psi_beta (β : ℝ) : ℝ :=
  (β / (1 + β)) ^ (1 + β)

/-- Θ_β := β^β (1+β)^{-(1+β)}, eq (1.20). -/
def Theta_beta (β : ℝ) : ℝ :=
  β ^ β * (1 + β) ^ (-(1 + β))

/-! ## Classical solutions on bounded domains -/

/-- Classical solution of (CM2) on (0, T) × Ω.
    Encoded abstractly — Ω is represented via dimension N. -/
structure IsClassicalSolution2 (p : CM2Params) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  u_pos : ∀ t x, 0 < t → t < T → 0 < u t x
  pde_satisfied : True -- abstract; detailed regularity omitted

def IsGlobalClassicalSolution2 (p : CM2Params) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsClassicalSolution2 p T u v

def IsBounded2 (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

/-! ## Main theorems -/

/-- Theorem 1.1: Boundedness and global existence with negative sensitivity (χ₀ ≤ 0). -/
theorem cm2_thm1_neg_sensitivity (p : CM2Params) (hp : p.χ₀ ≤ 0)
    (hab : 0 < p.a ∧ 0 < p.b) :
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 p u v ∧
      IsBounded2 u ∧
      (∀ t x, 0 ≤ t → u t x ≤ max (⨆ x, u₀ x) ((p.a / p.b) ^ (1 / p.α))) := by
  sorry

/-- Theorem 1.2: Boundedness with weak nonlinear cross diffusion (0 < m ≤ 1, β ≥ 1). -/
theorem cm2_thm2_weak_diffusion (p : CM2Params)
    (hab : 0 < p.a ∧ 0 < p.b) (hm1 : p.m ≤ 1) (hβ1 : 1 ≤ p.β) :
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u := by
  sorry

/-- Theorem 1.3: Boundedness with strong logistic source (a, b > 0). -/
theorem cm2_thm3_strong_logistic (p : CM2Params)
    (hab : 0 < p.a ∧ 0 < p.b) (hm_pos : 0 < p.m)
    (hparam : -- condition (i): α > m + γ - 1
              p.α > p.m + p.γ - 1 ∨
              -- condition (ii): β ≥ 1/2, α > 2m + γ - 2
              (1/2 ≤ p.β ∧ p.α > 2 * p.m + p.γ - 2) ∨
              -- condition (iii): β ≥ 0, α = m + γ - 1, smallness on χ₀
              (0 ≤ p.β ∧ p.α = p.m + p.γ - 1) ∨
              -- condition (iv): β ≥ 1/2, α = 2m + γ - 2, smallness on χ₀
              (1/2 ≤ p.β ∧ p.α = 2 * p.m + p.γ - 2)) :
    ∀ u₀ : ℝ → ℝ, (∀ x, 0 < u₀ x) →
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution2 p u v ∧ IsBounded2 u := by
  sorry

end
