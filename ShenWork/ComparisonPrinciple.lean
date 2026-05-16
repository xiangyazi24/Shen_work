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

/-! ### Key monotonicity: when χ ≤ 0, ū > 1 is decreasing -/

/-- When χ ≤ 0 and ū > 1 > u_bar > 0, the derivative of ū is negative. -/
lemma ode_ū_decreasing (p : CMParams) (hp : p.χ ≤ 0)
    (ū u_bar : ℝ) (hū : 1 < ū) (hu_bar_pos : 0 < u_bar) (hu_bar_lt : u_bar < ū) :
    p.χ * ū ^ p.m * (ū ^ p.γ - u_bar ^ p.γ) + ū * (1 - ū ^ p.α) < 0 := by
  have hū_pos : 0 < ū := by linarith
  have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le one_pos p.hγ
  have h_first_nonpos : p.χ * ū ^ p.m * (ū ^ p.γ - u_bar ^ p.γ) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg hp (Real.rpow_nonneg (le_of_lt hū_pos) p.m)
    · exact sub_nonneg.mpr (Real.rpow_le_rpow (le_of_lt hu_bar_pos) (le_of_lt hu_bar_lt) (le_of_lt hγ_pos))
  have h_second_neg : ū * (1 - ū ^ p.α) < 0 := by
    apply mul_neg_of_pos_of_neg hū_pos
    exact sub_neg.mpr (Real.one_lt_rpow hū hα_pos)
  linarith

/-- When χ ≤ 0 and 0 < u_bar < 1 < ū, the derivative of u_bar is positive. -/
lemma ode_u_bar_increasing (p : CMParams) (hp : p.χ ≤ 0)
    (ū u_bar : ℝ) (hū : 1 < ū) (hu_bar_pos : 0 < u_bar) (hu_bar_lt : u_bar < 1) :
    0 < p.χ * u_bar ^ p.m * (u_bar ^ p.γ - ū ^ p.γ) + u_bar * (1 - u_bar ^ p.α) := by
  have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le one_pos p.hγ
  have h_first_nonneg : 0 ≤ p.χ * u_bar ^ p.m * (u_bar ^ p.γ - ū ^ p.γ) := by
    have h1 : p.χ * u_bar ^ p.m ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hp (Real.rpow_nonneg (le_of_lt hu_bar_pos) p.m)
    have h2 : u_bar ^ p.γ - ū ^ p.γ ≤ 0 :=
      sub_nonpos.mpr (Real.rpow_le_rpow (le_of_lt hu_bar_pos) (le_of_lt (lt_trans hu_bar_lt hū)) (le_of_lt hγ_pos))
    exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have h_second_pos : 0 < u_bar * (1 - u_bar ^ p.α) := by
    apply mul_pos hu_bar_pos
    exact sub_pos.mpr (Real.rpow_lt_one (le_of_lt hu_bar_pos) hu_bar_lt hα_pos)
  linarith

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
