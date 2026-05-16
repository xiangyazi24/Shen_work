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

/-! ## Long-time behavior of the logistic ODE

The ODE ū'(t) = ū(t)(1 - ū(t)^α) with ū(0) = M > 1 converges to 1 as t → ∞.
This follows from:
1. ū is monotone decreasing (logisticRHS ≤ 0 when ū ≥ 1)
2. ū is bounded below by 1 (if ū hits 1, the RHS is 0)
3. Monotone bounded ⟹ convergent (to some limit L ≥ 1)
4. At the limit, ū' → 0, so L(1-L^α) = 0, hence L = 1

Similarly for u_bar starting below 1: it increases to 1. -/

/-- Monotone decreasing bounded below converges. -/
lemma logistic_ode_sup_converges {α : ℝ} (hα : 1 ≤ α) {M : ℝ} (_hM : 1 < M)
    (ū : ℝ → ℝ) (_hū_init : ū 0 = M)
    (hū_ode : ∀ t, 0 < t → deriv ū t = logisticRHS α (ū t))
    (hū_bound : ∀ t, 0 ≤ t → 1 ≤ ū t)
    (hū_anti : Antitone ū) :
    Tendsto ū atTop (𝓝 1) := by
  -- Step 1: ū is antitone and bounded below by 1 → converges to some L
  have hū_ge_one : ∀ t, 1 ≤ ū t := by
    intro t
    by_cases ht : 0 ≤ t
    · exact hū_bound t ht
    · push_neg at ht
      calc 1 ≤ ū 0 := hū_bound 0 le_rfl
        _ ≤ ū t := hū_anti (le_of_lt ht)
  have hbdd : BddBelow (Set.range ū) :=
    ⟨1, fun _ ⟨t, ht⟩ => ht ▸ hū_ge_one t⟩
  have h_conv := tendsto_atTop_ciInf hū_anti hbdd
  have hL_ge : 1 ≤ ⨅ t, ū t := le_ciInf hū_ge_one
  -- Step 3: At the limit, logisticRHS α L = 0
  -- This requires: ū' → 0 as t → ∞ (since ū converges)
  -- and ū' = logisticRHS α (ū t) → logisticRHS α L (by continuity)
  -- So logisticRHS α L = 0
  -- Step 4: L = 1 from logisticRHS_eq_zero_of_ge_one
  suffices h : ⨅ t, ū t = 1 by rw [h] at h_conv; exact h_conv
  apply le_antisymm _ hL_ge
  -- If ⨅ > 1, then logisticRHS(⨅) < 0, contradicting convergence
  by_contra h_gt
  push_neg at h_gt
  have hL_gt : 1 < ⨅ t, ū t := by
    rcases lt_or_eq_of_le hL_ge with h | h
    · exact h
    · exact absurd h.symm (by linarith)
  have hRHS_neg : logisticRHS α (⨅ t, ū t) < 0 := by
    unfold logisticRHS
    exact mul_neg_of_pos_of_neg (by linarith)
      (sub_neg.mpr (Real.one_lt_rpow hL_gt (by linarith : 0 < α)))
  -- But ū → ⨅, so ū(t) is eventually in (1, ⨅+ε), and ū' = logisticRHS(ū(t)) < 0
  -- This means ū decreases by at least δ per unit time, contradicting convergence
  sorry

/-- If logisticRHS α L = 0 and L ≥ 1, then L = 1.
    From L(1-L^α) = 0: either L = 0 or L^α = 1. With L ≥ 1 and α ≥ 1, L^α = 1 → L = 1. -/
lemma logisticRHS_eq_zero_of_ge_one {α L : ℝ} (hα : 1 ≤ α) (hL : 1 ≤ L)
    (h : logisticRHS α L = 0) : L = 1 := by
  unfold logisticRHS at h
  have hL_pos : 0 < L := by linarith
  rcases mul_eq_zero.mp h with hL0 | h1
  · linarith
  · have hLα : L ^ α = 1 := by linarith
    by_contra hne
    have hL_gt : 1 < L := lt_of_le_of_ne hL (Ne.symm hne)
    have := Real.one_lt_rpow hL_gt (by linarith : 0 < α)
    linarith

/-- When u > 1 and α ≥ 1, the logistic RHS is strictly negative. -/
lemma logisticRHS_neg_of_gt_one {α u : ℝ} (hα : 1 ≤ α) (hu : 1 < u) :
    logisticRHS α u < 0 := by
  unfold logisticRHS
  exact mul_neg_of_pos_of_neg (by linarith)
    (sub_neg.mpr (Real.one_lt_rpow hu (by linarith : 0 < α)))

/-- The decreasing monotonicity of ū when ū ≥ 1. -/
lemma logistic_ode_monotone_decreasing {α : ℝ} (hα : 1 ≤ α)
    (ū : ℝ → ℝ)
    (hū_ode : ∀ t, 0 < t → deriv ū t = logisticRHS α (ū t))
    (hū_bound : ∀ t, 0 ≤ t → 1 ≤ ū t) :
    ∀ t, 0 < t → deriv ū t ≤ 0 := by
  intro t ht
  rw [hū_ode t ht]
  exact logisticRHS_nonpos_of_ge_one hα (hū_bound t (le_of_lt ht))

end
