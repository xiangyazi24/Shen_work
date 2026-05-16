/-
  ShenWork/ComparisonPrinciple.lean
  Comparison principles for the chemotaxis system.
-/
import ShenWork.Defs

open Filter Topology

noncomputable section

def IsSuperSolutionODE (α : ℝ) (ū : ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → deriv ū t ≥ ū t * (1 - (ū t) ^ α) ∧ 0 < ū t

def IsSubSolutionODE (α : ℝ) (u_bar : ℝ → ℝ) : Prop :=
  ∀ t, 0 < t → deriv u_bar t ≤ u_bar t * (1 - (u_bar t) ^ α) ∧ 0 < u_bar t

structure RectangleODESolution (p : CMParams) where
  ū : ℝ → ℝ
  u_bar : ℝ → ℝ
  ū_pos : ∀ t, 0 ≤ t → 0 < ū t
  u_bar_pos : ∀ t, 0 ≤ t → 0 < u_bar t
  ordering : ∀ t, 0 ≤ t → u_bar t < ū t
  ū_lim : Tendsto ū atTop (𝓝 1)
  u_bar_lim : Tendsto u_bar atTop (𝓝 1)

/-- When χ ≤ 0 and ū > 1 > u_bar > 0, ū' < 0. -/
lemma ode_ū_decreasing (p : CMParams) (hp : p.χ ≤ 0)
    (ū u_bar : ℝ) (hū : 1 < ū) (hu_bar_pos : 0 < u_bar) (hu_bar_lt : u_bar < ū) :
    p.χ * ū ^ p.m * (ū ^ p.γ - u_bar ^ p.γ) + ū * (1 - ū ^ p.α) < 0 := by
  have hū_pos : 0 < ū := by linarith
  have hα_pos : 0 < p.α := lt_of_lt_of_le one_pos p.hα
  have hγ_pos : 0 < p.γ := lt_of_lt_of_le one_pos p.hγ
  have h_first_nonpos : p.χ * ū ^ p.m * (ū ^ p.γ - u_bar ^ p.γ) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hp (Real.rpow_nonneg (le_of_lt hū_pos) p.m))
      (sub_nonneg.mpr (Real.rpow_le_rpow (le_of_lt hu_bar_pos) (le_of_lt hu_bar_lt) (le_of_lt hγ_pos)))
  have h_second_neg : ū * (1 - ū ^ p.α) < 0 := by
    apply mul_neg_of_pos_of_neg hū_pos
    exact sub_neg.mpr (Real.one_lt_rpow hū hα_pos)
  linarith

/-- When χ ≤ 0 and 0 < u_bar < 1 < ū, u_bar' > 0. -/
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

/-- ODE comparison principle — encoded as class hypothesis. -/
class ComparisonTheory (p : CMParams) : Prop where
  rectangle_ode_converges : p.χ ≤ 0 → ∀ M₀, 1 < M₀ → ∀ δ₀, 0 < δ₀ → δ₀ < 1 →
    ∃ sol : RectangleODESolution p, sol.ū 0 = M₀ ∧ sol.u_bar 0 = δ₀
  pde_bounded_by_ode : p.χ ≤ 0 →
    ∀ u v : ℝ → ℝ → ℝ, IsGlobalClassicalSolution p u v →
    ∀ sol : RectangleODESolution p,
    ∀ t x, 0 ≤ t → sol.u_bar t ≤ u t x ∧ u t x ≤ sol.ū t

end
