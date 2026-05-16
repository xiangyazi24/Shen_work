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

/-- c**_{χ,m,α,γ} from Theorem 1.2. -/
def cStarStar (p : CMParams) : ℝ :=
  1 + |p.χ| ^ (1/6 : ℝ) + 1 / (1 + |p.χ| ^ (1/6 : ℝ))

end
