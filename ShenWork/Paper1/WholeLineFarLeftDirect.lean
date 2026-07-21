import ShenWork.Paper1.WholeLineParabolicDirect
import ShenWork.Paper1.WholeLineParabolicDirectUpper
import ShenWork.Paper1.WholeLineFarLeftBarrierCapstone
import ShenWork.Paper1.WholeLineExpBarrierConsistency

/-!
# Far-left convergence, direct route (continuous envelopes + hstart)

Combines the two direct parabolic barriers (which need only CONTINUOUS attained
inf/sup envelopes plus the initial-interval `hstart`, no differentiability of the
envelope) with the symmetric exponential barriers `α = 1 − D e^{−λt}`,
`β = 1 + D e^{−λt}` and the convergence endpoint.

This is the far-left convergence theorem whose remaining obligations are the
weakest available: inf/sup CONTINUITY + attainment + `hstart` + the pointwise
touch-slope (from `min_rise`/`max_fall`), and the solution's time-derivative and
regularity — all solution-specific PDE facts, no Danskin differentiability.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **Far-left convergence, direct route.** -/
theorem far_left_convergence_direct
    {u : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} {ut : ℝ → ℝ → ℝ} {D lam : ℝ} (hlam : 0 < lam)
    (hut : ∀ t z, HasDerivAt (fun s => u s z) (ut t z) t)
    (ha_cont : Continuous a) (hb_cont : Continuous b)
    (ha_lb : ∀ t z, a t ≤ u t z) (hb_ub : ∀ t z, u t z ≤ b t)
    (ha_attain : ∀ t, ∃ z0, a t = u t z0) (hb_attain : ∀ t, ∃ z0, b t = u t z0)
    (hstartLo : ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → 1 - D * Real.exp (-lam * t) ≤ a t)
    (hstartHi : ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → b t ≤ 1 + D * Real.exp (-lam * t))
    (hrateLo : ∀ t z0, 0 ≤ t → (∀ z, u t z0 ≤ u t z) →
      u t z0 = 1 - D * Real.exp (-lam * t) →
      lam * (D * Real.exp (-lam * t)) < ut t z0)
    (hrateHi : ∀ t z0, 0 ≤ t → (∀ z, u t z ≤ u t z0) →
      u t z0 = 1 + D * Real.exp (-lam * t) →
      ut t z0 < -(lam * (D * Real.exp (-lam * t)))) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t → |u t z - 1| < ε := by
  set α : ℝ → ℝ := fun t => 1 - D * Real.exp (-lam * t) with hαdef
  set β : ℝ → ℝ := fun t => 1 + D * Real.exp (-lam * t) with hβdef
  have hαderiv : ∀ t, HasDerivAt α (lam * (D * Real.exp (-lam * t))) t :=
    fun t => expBarrier_deriv t
  have hβderiv : ∀ t, HasDerivAt β (-(lam * (D * Real.exp (-lam * t)))) t := by
    intro t
    have h := (expBarrier_deriv (D := -D) (lam := lam) t)
    have heq : (fun t => 1 - (-D) * Real.exp (-lam * t)) = β := by
      funext s; rw [hβdef]; ring
    rw [heq] at h; convert h using 1; ring
  -- lower barrier
  have hlow : ∀ t z, 0 ≤ t → α t ≤ u t z :=
    parabolic_lower_barrier_direct_of_initial_interval hαderiv hut ha_cont ha_lb
      ha_attain hstartLo hrateLo
  -- upper barrier
  have hup : ∀ t z, 0 ≤ t → u t z ≤ β t :=
    parabolic_upper_barrier_direct_of_initial_interval hβderiv hut hb_cont hb_ub
      hb_attain hstartHi hrateHi
  -- confinement → convergence
  exact far_left_convergence_of_barrier hlam
    (fun t z ht => ⟨hlow t z ht, hup t z ht⟩)

section AxiomAudit

#print axioms far_left_convergence_direct

end AxiomAudit

end ShenWork.Paper1
