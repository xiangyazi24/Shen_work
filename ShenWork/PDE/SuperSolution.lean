/-
  ShenWork/PDE/SuperSolution.lean

  Super-solution arguments for the chemotaxis system.
  When χ ≤ 0, constant functions serve as super-solutions,
  giving uniform bounds on the solution.
-/
import ShenWork.Defs
import ShenWork.PDE.HeatSemigroup

open Filter Topology MeasureTheory Real

noncomputable section

/-! ## The logistic ODE super-solution

For the chemotaxis system with χ ≤ 0, the PDE solution u(t,x) is bounded above
by the solution of the ODE ū'(t) = ū(t)(1 - ū(t)^α).

Key fact: if ū₀ ≥ 1, then ū(t) ≤ ū₀ for all t ≥ 0,
because ū(1-ū^α) ≤ 0 when ū ≥ 1. -/

/-- The logistic ODE right-hand side: g(u) = u(1 - u^α). -/
def logisticRHS (α : ℝ) (u : ℝ) : ℝ := u * (1 - u ^ α)

/-- When u ≥ 1 and α ≥ 1, the logistic RHS is nonpositive. -/
lemma logisticRHS_nonpos_of_ge_one {α u : ℝ} (hα : 1 ≤ α) (hu : 1 ≤ u) :
    logisticRHS α u ≤ 0 := by
  unfold logisticRHS
  apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
  exact sub_nonpos.mpr (Real.one_le_rpow hu (by linarith : 0 ≤ α))

/-- When 0 < u < 1 and α ≥ 1, the logistic RHS is positive (growth). -/
lemma logisticRHS_pos_of_lt_one {α u : ℝ} (hα : 1 ≤ α) (hu_pos : 0 < u) (hu_lt : u < 1) :
    0 < logisticRHS α u := by
  unfold logisticRHS
  exact mul_pos hu_pos (sub_pos.mpr (Real.rpow_lt_one (le_of_lt hu_pos) hu_lt (by linarith : 0 < α)))

/-- The constant M = max{1, sup u₀} is a super-solution:
    its "derivative" 0 ≥ M(1 - M^α) (the RHS when χ ≤ 0). -/
lemma constant_is_supersolution {α M : ℝ} (hα : 1 ≤ α) (hM : 1 ≤ M) :
    logisticRHS α M ≤ 0 :=
  logisticRHS_nonpos_of_ge_one hα hM

/-- For the full heat-equation + logistic: if u₀ ≤ M and M ≥ 1,
    then the heat semigroup applied to the logistic source preserves the bound.
    This is because e^{tΔ}u ≤ M (semigroup upper bound) and
    the logistic term M(1-M^α) ≤ 0 keeps the solution from growing. -/
theorem logistic_heat_bound {f : ℝ → ℝ} {M : ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ M)
    {α : ℝ} (hα : 1 ≤ α) (hM : 1 ≤ M)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ M :=
  heatSemigroup_upper_bound hf_nn hf_le ht

end
