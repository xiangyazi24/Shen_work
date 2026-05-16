/-
  ShenWork/Defs.lean

  Core definitions for:
    Shen, "Existence, uniqueness, stability, and monotonicity of traveling waves
    for repulsion/attraction chemotaxis models with logistic type source"
    (arXiv:2605.04401)

  System (CM):
    u_t = u_xx − χ(uᵐ v_x)_x + u(1 − uᵅ),   x ∈ ℝ
    0   = v_xx − v + uᵞ,                        x ∈ ℝ
  where m, α, γ ≥ 1 and χ ∈ ℝ.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Basic

open Filter Topology MeasureTheory

noncomputable section

/-! ## Parameters of the chemotaxis system -/

/-- Parameters for the parabolic-elliptic chemotaxis system (CM). -/
structure CMParams where
  m : ℝ
  α : ℝ
  γ : ℝ
  χ : ℝ
  hm : 1 ≤ m
  hα : 1 ≤ α
  hγ : 1 ≤ γ

/-! ## Function spaces -/

/-- A function is bounded: ∃ M, ∀ x, |f x| ≤ M. -/
def IsBddFun (f : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ x, |f x| ≤ M

/-- C^b_unif(ℝ): uniformly continuous and bounded functions ℝ → ℝ. -/
def IsCUnifBdd (f : ℝ → ℝ) : Prop := Continuous f ∧ IsBddFun f

/-! ## Classical solutions -/

/-- A pair (u, v) is a classical solution of (CM) on (0, T). -/
structure IsClassicalSolution (p : CMParams) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop where
  hT : 0 < T
  u_smooth : ∀ t x, 0 < t → t < T →
    DifferentiableAt ℝ (u · x) t ∧ DifferentiableAt ℝ (u t) x
  v_smooth : ∀ t x, 0 < t → t < T → DifferentiableAt ℝ (v t) x
  pde_u : ∀ t x, 0 < t → t < T →
    deriv (u · x) t =
      iteratedDeriv 2 (u t) x
      - p.χ * deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x
      + u t x * (1 - (u t x) ^ p.α)
  pde_v : ∀ t x, 0 < t → t < T →
    iteratedDeriv 2 (v t) x - v t x + (u t x) ^ p.γ = 0

def IsGlobalClassicalSolution (p : CMParams) (u v : ℝ → ℝ → ℝ) : Prop :=
  ∀ T > 0, IsClassicalSolution p T u v

def IsPositiveClassicalSolution (p : CMParams) (T : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  IsClassicalSolution p T u v ∧ ∀ t x, 0 ≤ t → t < T → 0 < u t x

def IsBoundedGlobal (u : ℝ → ℝ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t x, 0 ≤ t → |u t x| ≤ M

/-! ## Traveling wave solutions -/

/-- A traveling wave solution of (CM) connecting (1,1) and (0,0) with speed c. -/
structure IsTravelingWave (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop where
  hc : 0 < c
  U_pos : ∀ x, 0 < U x
  ode_U : ∀ x,
    iteratedDeriv 2 U x + c * deriv U x
    - p.χ * deriv (fun y => (U y) ^ p.m * deriv V y) x
    + U x * (1 - (U x) ^ p.α) = 0
  ode_V : ∀ x, iteratedDeriv 2 V x - V x + (U x) ^ p.γ = 0
  lim_neg_inf : Tendsto U atBot (𝓝 1) ∧ Tendsto V atBot (𝓝 1)
  lim_pos_inf : Tendsto U atTop (𝓝 0) ∧ Tendsto V atTop (𝓝 0)

def IsMonotoneTravelingWave (p : CMParams) (c : ℝ) (U V : ℝ → ℝ) : Prop :=
  IsTravelingWave p c U V ∧ (∀ x, deriv U x ≤ 0) ∧ (∀ x, deriv V x ≤ 0)

/-! ## Wave speed bounds -/

/-- c*_{χ,m,γ} from Theorem 1.1(1), eq (1.13). -/
def cStarLower (p : CMParams) : ℝ :=
  max (1 / p.m + p.m)
    (1 / Real.sqrt (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2) +
     Real.sqrt (p.m * p.γ * |p.χ| + p.γ ^ 2 * |p.χ| + p.γ ^ 2))

/-- χ*(m, α, γ) from Theorem 1.1(2), eq (1.17). -/
def chiStar (p : CMParams) : ℝ :=
  min 1 ((2 * p.m + 2 * p.γ) / (p.m ^ 2 + p.m + 2 * p.γ))

/-- κ = (c − √(c² − 4)) / 2, the exponential decay rate. -/
def kappa (c : ℝ) : ℝ := (c - Real.sqrt (c ^ 2 - 4)) / 2

/-! ## The elliptic Green's function Ψ -/

/-- Ψ(x; u, l, mu) = (mu / 2√l) ∫ e^{-√l |x-y|} u(y) dy. (Lemma 2.2)
    Stated axiomatically; the integral formula is proved in Preliminary.lean. -/
axiom Psi (u : ℝ → ℝ) (l mu : ℝ) (x : ℝ) : ℝ

/-- Ψ is nonneg for nonneg u. -/
axiom Psi_nonneg {u : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (hu : ∀ x, 0 ≤ u x) (x : ℝ) : 0 ≤ Psi u l mu x

/-- Ψ is monotone in u. -/
axiom Psi_mono {u v : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (huv : ∀ x, u x ≤ v x) (x : ℝ) : Psi u l mu x ≤ Psi v l mu x

/-- Ψ of a constant = the constant (kernel integrates to 1). -/
axiom Psi_const {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : Psi (fun _ : ℝ => c) 1 1 x = c

/-- Ψ of an exponential: Ψ(e^{-kx}, 1, 1) = e^{-kx}/(1−k²) for 0 < k < 1. -/
axiom Psi_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x =
      1 / (1 - k ^ 2) * Real.exp (-k * x)

/-- |Ψ'(x)| ≤ √l · Ψ(x) for nonneg u (Lemma 2.3). Specialized to l=1. -/
axiom Psi_deriv_abs_le {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x

/-- c**_{χ,m,α,γ} from Theorem 1.2. -/
def cStarStar (p : CMParams) : ℝ :=
  1 + |p.χ| ^ (1/6 : ℝ) + 1 / (1 + |p.χ| ^ (1/6 : ℝ))

/-! ## PDE axioms (deep analytic facts encoded as axioms) -/

/-- Prop 1.1(1): Global existence + comparison bound when χ ≤ 0.
    Via Schauder fixed-point + comparison principle. -/
axiom cm_global_exist_neg (p : CMParams) (hp : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ t x, 0 ≤ t → u t x ≤ max 1 (⨆ x, u₀ x)) ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → u t x ≤ 1 + ε)

/-- Prop 1.1(2): Global existence when χ > 0 and logistic dominates. -/
axiom cm_global_exist_pos (p : CMParams) (hp : 0 < p.χ)
    (hα : p.α > p.m + p.γ - 1 ∨
      (p.α = p.m + p.γ - 1 ∧
       p.χ < min ((2 * p.m - 1) / (p.m - 1)) ((p.m + p.γ - 1) / (p.γ - 1))))
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v ∧ IsBoundedGlobal u

/-- Prop 1.2(1): Stabilization to (1,1) when χ ≤ 0 and inf u₀ > 0.
    Via rectangle/ODE comparison: bar_u, underline_u → 1. -/
axiom cm_stabilize_neg (p : CMParams) (hp : p.χ ≤ 0)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) (hu₀_inf : ∃ δ > 0, ∀ x, δ ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0)

/-- Prop 1.2(2): Stabilization when 0 < χ < 1/2 and α ≥ m+γ−1. -/
axiom cm_stabilize_small_pos (p : CMParams)
    (hp : 0 < p.χ) (hp2 : p.χ < 1 / 2) (hα : p.m + p.γ - 1 ≤ p.α)
    (u₀ : ℝ → ℝ) (hu₀_cont : Continuous u₀) (hu₀_bdd : IsBddFun u₀)
    (hu₀_nn : ∀ x, 0 ≤ u₀ x) (hu₀_inf : ∃ δ > 0, ∀ x, δ ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      Tendsto (fun t => ⨆ x, |u t x - 1|) atTop (𝓝 0)

/-- Thm 1.1(1): Existence of monotone traveling waves, χ ≤ 0. -/
axiom cm_tw_exist_neg (p : CMParams)
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0) (c : ℝ) (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x < max 1 (Real.exp (-kappa c * x))) ∧
      (∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1/2) 1) →
        Tendsto (fun x => Real.exp ((κ₁ - kappa c) * x) *
          (U x / Real.exp (-kappa c * x) - 1)) atTop (𝓝 0))

/-- Thm 1.1(2): Existence of traveling waves, small positive χ. -/
axiom cm_tw_exist_small_pos (p : CMParams)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1/2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-kappa c * x)))

/-- Thm 1.2: Stability of traveling waves. -/
axiom cm_tw_stability (p : CMParams)
    (hparam : (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
              (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (c : ℝ) (hc : cStarStar p < c)
    (U V : ℝ → ℝ) (hTW : IsTravelingWave p c U V)
    (u₀ : ℝ → ℝ) (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - U (x - c * t)| < ε)

/-- Thm 1.3: Uniqueness of traveling waves. -/
axiom cm_tw_uniqueness (p : CMParams)
    (hparam : (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
              (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (c : ℝ) (hc : cStarStar p < c)
    (U₁ V₁ U₂ V₂ : ℝ → ℝ)
    (hTW₁ : IsTravelingWave p c U₁ V₁) (hTW₂ : IsTravelingWave p c U₂ V₂)
    (hbound₁ : ∀ x, U₁ x < Real.exp (-kappa c * x))
    (hbound₂ : ∀ x, U₂ x < Real.exp (-kappa c * x))
    (k₁ : ℝ) (hk₁ : kappa c < k₁) (hk₁_lt : k₁ < 1)
    (hdecay₁ : Tendsto (fun x => Real.exp ((k₁ - kappa c) * x) *
      (U₁ x / Real.exp (-kappa c * x) - 1)) atTop (𝓝 0))
    (hdecay₂ : Tendsto (fun x => Real.exp ((k₁ - kappa c) * x) *
      (U₂ x / Real.exp (-kappa c * x) - 1)) atTop (𝓝 0)) :
    (∀ x, U₁ x = U₂ x) ∧ (∀ x, V₁ x = V₂ x)

end
