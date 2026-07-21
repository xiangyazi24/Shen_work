import ShenWork.Paper1.WholeLineScalarFirstTouch

/-!
# Parabolic lower/upper barrier from the scalar first-touch

Lifts `scalar_first_touch` to a PDE barrier via the inf/sup trajectory.  If a
differentiable function `a` is a pointwise lower bound for `u(t,·)` (think
`a t = inf_z u(t,z)`, the argmin trajectory), starts above the sub-barrier
`α`, and at every touch `α t = a t` has the strict slope gap `dα t < da t`, then
`α t ≤ u(t,z)` for all `t ≥ 0`, `z`.

The two carried hypotheses — `a` differentiable (the Danskin/attainment content:
the inf trajectory is `C¹`) and the touch-slope condition (from the pointwise
`min_rise` at the argmin) — are the genuinely-remaining analytic obligations; the
reduction to `scalar_first_touch` and thence to convergence is complete here.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **Parabolic lower barrier.**  A differentiable lower-bound trajectory `a` with
`α 0 ≤ a 0` and the touch-slope gap gives `α t ≤ u(t,z)` for all `t ≥ 0`, `z`. -/
theorem parabolic_lower_barrier
    {u : ℝ → ℝ → ℝ} {a α da dα : ℝ → ℝ}
    (ha : ∀ t, HasDerivAt a (da t) t)
    (hα : ∀ t, HasDerivAt α (dα t) t)
    (hlb : ∀ t z, a t ≤ u t z)
    (h0 : α 0 ≤ a 0)
    (htouch : ∀ t, 0 ≤ t → α t = a t → dα t < da t) :
    ∀ t z, 0 ≤ t → α t ≤ u t z := by
  intro t z ht
  have hαa : α t ≤ a t := scalar_first_touch ha hα h0 htouch t ht
  exact le_trans hαa (hlb t z)

/-- **Parabolic upper barrier.**  A differentiable upper-bound trajectory `b` with
`b 0 ≤ β 0` and the touch-slope gap `db t < dβ t` gives `u(t,z) ≤ β t`. -/
theorem parabolic_upper_barrier
    {u : ℝ → ℝ → ℝ} {b β db dβ : ℝ → ℝ}
    (hb : ∀ t, HasDerivAt b (db t) t)
    (hβ : ∀ t, HasDerivAt β (dβ t) t)
    (hub : ∀ t z, u t z ≤ b t)
    (h0 : b 0 ≤ β 0)
    (htouch : ∀ t, 0 ≤ t → b t = β t → db t < dβ t) :
    ∀ t z, 0 ≤ t → u t z ≤ β t := by
  intro t z ht
  -- apply scalar_first_touch with sub = b, super = β
  have hbβ : b t ≤ β t := scalar_first_touch hβ hb h0 htouch t ht
  exact le_trans (hub t z) hbβ

/-- **Two-sided barrier confinement.**  Combining the lower and upper barriers with
the symmetric exponential barriers `α = 1 − D e^{−λt}`, `β = 1 + D e^{−λt}` gives the
confinement hypothesis of `far_left_convergence_of_barrier`. -/
theorem barrier_confinement_of_trajectories
    {u : ℝ → ℝ → ℝ} {a b α β da db dα dβ : ℝ → ℝ}
    (ha : ∀ t, HasDerivAt a (da t) t) (hb : ∀ t, HasDerivAt b (db t) t)
    (hα : ∀ t, HasDerivAt α (dα t) t) (hβ : ∀ t, HasDerivAt β (dβ t) t)
    (hlb : ∀ t z, a t ≤ u t z) (hub : ∀ t z, u t z ≤ b t)
    (h0lo : α 0 ≤ a 0) (h0hi : b 0 ≤ β 0)
    (htouchLo : ∀ t, 0 ≤ t → α t = a t → dα t < da t)
    (htouchHi : ∀ t, 0 ≤ t → b t = β t → db t < dβ t) :
    ∀ t z, 0 ≤ t → α t ≤ u t z ∧ u t z ≤ β t := by
  intro t z ht
  exact ⟨parabolic_lower_barrier ha hα hlb h0lo htouchLo t z ht,
    parabolic_upper_barrier hb hβ hub h0hi htouchHi t z ht⟩

section AxiomAudit

#print axioms parabolic_lower_barrier
#print axioms parabolic_upper_barrier
#print axioms barrier_confinement_of_trajectories

end AxiomAudit

end ShenWork.Paper1
