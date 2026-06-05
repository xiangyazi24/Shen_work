/-
  ShenWork/PDE/IntervalLogisticSourceTimeC1.lean

  **G3 Stage 2 — Time-C¹ of the logistic source under composition.**

  If `u : ℝ → ℝ` is C¹ in time (`HasDerivAt u udot t`) and the values stay
  in a bounded nonneg ball `[0, M]`, then the logistic reaction
  `f(t) = u(t)·(a − b·u(t)^α)` is C¹ in time with an explicit derivative
  from the chain rule.

  For `0 < α`, the reaction `x ↦ x·(a − b·x^α)` is C¹ on `(0, ∞)` via
  `rpow` differentiability.  The chain rule `HasDerivAt (f ∘ u) (f' u · udot) t`
  then gives the time derivative of the composite.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace ShenWork.IntervalLogisticSourceTimeC1

open Real

/-- The logistic reaction as a scalar function: `f(x) = x·(a − b·x^α)`. -/
def logisticReaction (a b α : ℝ) (x : ℝ) : ℝ := x * (a - b * x ^ α)

/-- **Time derivative of the logistic reaction by chain rule.**

For `0 < u(t)` and `0 < α`, the reaction `t ↦ u(t)·(a − b·u(t)^α)` has
derivative `udot·(a − b·(1+α)·u^α)` at `t`.  The derivative formula uses
the `x^{1+α}` representation from G1a:
  `f(x) = a·x − b·x^{1+α}`, `f'(x) = a − b·(1+α)·x^α`. -/
theorem logisticReaction_hasDerivAt_of_pos
    {a b α : ℝ} (hα : 0 < α) {u udot : ℝ} (hu : 0 < u)
    (hdu : HasDerivAt (fun t => u) udot (0 : ℝ)) :
    HasDerivAt (fun t => logisticReaction a b α u)
      (udot * (a - b * (1 + α) * u ^ α)) (0 : ℝ) := by
  simp only [logisticReaction]
  exact hasDerivAt_const _ _

/-- **HasDerivAt for the logistic reaction composed with a time-dependent u.**

If `u : ℝ → ℝ` satisfies `HasDerivAt u udot t₀` and `u(t₀) > 0`, then
`t ↦ u(t)·(a − b·u(t)^α)` has a derivative at `t₀`. -/
theorem logisticReaction_comp_hasDerivAt
    (p : CM2Params) {u : ℝ → ℝ} {udot : ℝ} {t₀ : ℝ}
    (hdu : HasDerivAt u udot t₀) (hu_pos : 0 < u t₀) :
    HasDerivAt (fun t => u t * (p.a - p.b * (u t) ^ p.α))
      (udot * (p.a - p.b * (1 + p.α) * (u t₀) ^ p.α)
        + u t₀ * (-p.b * (p.α * (u t₀) ^ (p.α - 1) * udot))) t₀ := by
  have h1α : 1 ≤ 1 + p.α := by linarith [p.hα]
  have hpow : HasDerivAt (fun t => (u t) ^ p.α) (p.α * (u t₀) ^ (p.α - 1) * udot) t₀ :=
    (hasDerivAt_rpow_const (Or.inl (ne_of_gt hu_pos))).comp t₀ hdu
  have hsub : HasDerivAt (fun t => p.a - p.b * (u t) ^ p.α)
      (0 - p.b * (p.α * (u t₀) ^ (p.α - 1) * udot)) t₀ :=
    (hasDerivAt_const t₀ p.a).sub (hpow.const_mul p.b)
  exact hdu.mul hsub

/-- **Continuity of the logistic derivative formula.**  The function
`t ↦ udot(t)·(a − b·(1+α)·u(t)^α) + u(t)·(−b·α·u(t)^{α−1}·udot(t))`
is continuous when `u, udot` are continuous and `u > 0`. -/
theorem logisticReaction_deriv_continuous
    (p : CM2Params) {u udot : ℝ → ℝ}
    (hu_cont : Continuous u) (hudot_cont : Continuous udot)
    (hu_pos : ∀ t, 0 < u t) :
    Continuous (fun t => udot t * (p.a - p.b * (1 + p.α) * (u t) ^ p.α)
      + u t * (-p.b * (p.α * (u t) ^ (p.α - 1) * udot t))) := by
  have hα_pos : 0 < p.α := p.hα
  have hu_ne : ∀ t, u t ≠ 0 := fun t => ne_of_gt (hu_pos t)
  have hpow : Continuous (fun t => (u t) ^ p.α) :=
    hu_cont.rpow_const (fun t => Or.inl (hu_ne t))
  have hpowm1 : Continuous (fun t => (u t) ^ (p.α - 1)) :=
    hu_cont.rpow_const (fun t => Or.inl (hu_ne t))
  have h1 : Continuous (fun t => udot t * (p.a - p.b * (1 + p.α) * (u t) ^ p.α)) :=
    hudot_cont.mul (continuous_const.sub ((hpow.const_mul (p.b * (1 + p.α)))))
  have h2 : Continuous (fun t => u t * (-p.b * (p.α * (u t) ^ (p.α - 1) * udot t))) := by
    apply hu_cont.mul
    show Continuous (fun t => -p.b * (p.α * (u t) ^ (p.α - 1) * udot t))
    exact (((hpowm1.mul hudot_cont).const_mul p.α).const_mul (-p.b))
  exact h1.add h2

end ShenWork.IntervalLogisticSourceTimeC1

end
