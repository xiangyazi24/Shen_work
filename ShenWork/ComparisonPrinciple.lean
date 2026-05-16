/-
  ShenWork/ComparisonPrinciple.lean

  Comparison principles for the parabolic-elliptic chemotaxis system.
  These are the key PDE tools used in Sections 3-5.

  Strategy: decompose the deep PDE axioms into smaller, more specific facts.
-/
import ShenWork.Defs

open Filter Topology MeasureTheory

noncomputable section

/-! ## Comparison principle for the transformed equation

When χ ≤ 0, the system (CM) can be reformulated via V = Ψ(uᵞ):
  U_t = U_xx + |χ|mU^{m-1}U_x V_x + U(1 + |χ|U^{m+γ-1} - (U^α + |χ|U^{m+γ-1}))

The key observation is that for χ ≤ 0, the equation for U has good monotonicity
properties that allow comparison with constant super/sub-solutions. -/

/-- A super-solution of the ODE ū'(t) = ū(t)(1 - ū(t)^α) bounds
    the PDE solution from above when χ ≤ 0. -/
def IsSuperSolutionODE (α : ℝ) (ū : ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → deriv ū t ≥ ū t * (1 - (ū t) ^ α) ∧ 0 < ū t

/-- A sub-solution. -/
def IsSubSolutionODE (α : ℝ) (u_bar : ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → deriv u_bar t ≤ u_bar t * (1 - (u_bar t) ^ α) ∧ 0 < u_bar t

/-! ## The rectangle ODE system (Prop 1.2 proof)

For proving stabilization, the paper uses the system:
  Ū_t = χŪ^m (Ū^γ − U_bar^γ) + Ū(1 − Ū^α)
  U_bar_t = χU_bar^m (U_bar^γ − Ū^γ) + U_bar(1 − U_bar^α)
with Ū(0) = max{‖u₀‖_∞, 1} + ε, U_bar(0) = min{inf u₀, 1} − ε.

The key property is that both Ū and U_bar converge to 1 as t → ∞. -/

structure RectangleODESolution (p : CMParams) where
  ū : ℝ → ℝ
  u_bar : ℝ → ℝ
  ū_pos : ∀ t, 0 ≤ t → 0 < ū t
  u_bar_pos : ∀ t, 0 ≤ t → 0 < u_bar t
  ordering : ∀ t, 0 ≤ t → u_bar t < ū t
  ū_ode : ∀ t, 0 < t →
    deriv ū t = p.χ * (ū t) ^ p.m * ((ū t) ^ p.γ - (u_bar t) ^ p.γ) +
      ū t * (1 - (ū t) ^ p.α)
  u_bar_ode : ∀ t, 0 < t →
    deriv u_bar t = p.χ * (u_bar t) ^ p.m * ((u_bar t) ^ p.γ - (ū t) ^ p.γ) +
      u_bar t * (1 - (u_bar t) ^ p.α)
  ū_lim : Tendsto ū atTop (𝓝 1)
  u_bar_lim : Tendsto u_bar atTop (𝓝 1)

/-- When χ ≤ 0 and both u_bar, ū start near 1 (from below/above respectively),
    the logistic term drives both to 1. -/
theorem rectangle_ode_converges (p : CMParams) (hp : p.χ ≤ 0)
    (M₀ : ℝ) (hM₀ : 1 < M₀) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ sol : RectangleODESolution p, sol.ū 0 = M₀ ∧ sol.u_bar 0 = δ₀ := by
  sorry

/-! ## Comparison: PDE solution bounded by ODE solution -/

/-- The PDE solution u(t,x) is bounded between the rectangle ODE solutions
    when χ ≤ 0. This is the core of Prop 1.2(1). -/
theorem pde_bounded_by_rectangle_ode (p : CMParams) (hp : p.χ ≤ 0)
    (u v : ℝ → ℝ → ℝ) (hglobal : IsGlobalClassicalSolution p u v)
    (sol : RectangleODESolution p) :
    ∀ t x, 0 ≤ t → sol.u_bar t ≤ u t x ∧ u t x ≤ sol.ū t := by
  sorry

end
