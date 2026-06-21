import ShenWork.PDE.UnitPointLogisticODE

/-!
  A small, formal obstruction to the zero-state small-orbit bootstrap for the
  logistic source with positive growth.

  If `a > 0` and `b > 0`, the scalar spatially constant logistic solution tends
  to the positive equilibrium.  Hence data below half of that equilibrium must
  eventually leave the `2 * u0` ball.  This is the precise obstruction to a
  global `‖u(t)‖ ≤ 2δ` bootstrap around zero in the positive-growth regime.
-/

open Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

/-- Positive-growth logistic data below half equilibrium eventually leaves the
`2 * u₀` small orbit. -/
theorem bernoulliLogisticSolution_eventually_exceeds_two_mul_initial
    (p : CM2Params) {u₀ : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hu₀ : 0 < u₀)
    (hsmall : 2 * u₀ < (p.a / p.b) ^ (1 / p.α)) :
    ∃ t : ℝ, 0 ≤ t ∧
      2 * u₀ < bernoulliLogisticSolution p u₀ t := by
  have hlim :
      Tendsto (fun t : ℝ => bernoulliLogisticSolution p u₀ t)
        atTop (𝓝 ((p.a / p.b) ^ (1 / p.α))) :=
    bernoulliLogisticSolution_tendsto_atTop p ha hb hu₀
  have hgt :
      ∀ᶠ t : ℝ in atTop,
        2 * u₀ < bernoulliLogisticSolution p u₀ t :=
    (tendsto_order.mp hlim).1 (2 * u₀) hsmall
  rcases (hgt.and (eventually_ge_atTop (0 : ℝ))).exists with
    ⟨t, ht_gt, ht_nonneg⟩
  exact ⟨t, ht_nonneg, ht_gt⟩

/-- The same obstruction in negated-bootstrap form. -/
theorem not_bernoulliLogisticSolution_le_two_mul_initial_for_all_nonneg_time
    (p : CM2Params) {u₀ : ℝ}
    (ha : 0 < p.a) (hb : 0 < p.b) (hu₀ : 0 < u₀)
    (hsmall : 2 * u₀ < (p.a / p.b) ^ (1 / p.α)) :
    ¬ ∀ t : ℝ, 0 ≤ t →
      bernoulliLogisticSolution p u₀ t ≤ 2 * u₀ := by
  rintro hbound
  rcases bernoulliLogisticSolution_eventually_exceeds_two_mul_initial
      p ha hb hu₀ hsmall with
    ⟨t, ht_nonneg, ht_gt⟩
  exact not_lt_of_ge (hbound t ht_nonneg) ht_gt

end ShenWork.Paper2

end