import ShenWork.Paper1.WholeLineParabolicBarrier
import ShenWork.Paper1.WholeLineFarLeftBarrierCapstone
import ShenWork.Paper1.WholeLineExpBarrierConsistency

/-!
# Far-left convergence assembly (exponential barriers instantiated)

The complete chain, with the symmetric exponential barriers `α(t) = 1 − D e^{−λt}`,
`β(t) = 1 + D e^{−λt}` instantiated:

`inf/sup trajectories (C¹, touch-slope) → barrier confinement → uniform u → 1`.

This capstone takes the genuinely-remaining PDE obligations as NAMED hypotheses —
the inf/sup trajectories `a, b` being `C¹` (Danskin/envelope), bounding `u`, and
having the touch-slope gap against the exponential barriers (from the pointwise
`min_rise`/`max_fall` at the argmin) — and produces the uniform far-left
convergence conclusion.  Everything between the hypotheses and the conclusion is
machine-checked.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- **Far-left convergence from inf/sup trajectories** (exponential barriers). -/
theorem far_left_convergence_from_trajectories
    {u : ℝ → ℝ → ℝ} {a b da db : ℝ → ℝ} {D lam : ℝ} (hlam : 0 < lam)
    (ha : ∀ t, HasDerivAt a (da t) t) (hb : ∀ t, HasDerivAt b (db t) t)
    (hlb : ∀ t z, a t ≤ u t z) (hub : ∀ t z, u t z ≤ b t)
    (h0lo : 1 - D * Real.exp (-lam * 0) ≤ a 0)
    (h0hi : b 0 ≤ 1 + D * Real.exp (-lam * 0))
    (htouchLo : ∀ t, 0 ≤ t → 1 - D * Real.exp (-lam * t) = a t →
      lam * (D * Real.exp (-lam * t)) < da t)
    (htouchHi : ∀ t, 0 ≤ t → b t = 1 + D * Real.exp (-lam * t) →
      db t < -(lam * (D * Real.exp (-lam * t)))) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t → |u t z - 1| < ε := by
  -- the two exponential barriers and their derivatives
  set α : ℝ → ℝ := fun t => 1 - D * Real.exp (-lam * t) with hαdef
  set β : ℝ → ℝ := fun t => 1 + D * Real.exp (-lam * t) with hβdef
  have hαderiv : ∀ t, HasDerivAt α (lam * (D * Real.exp (-lam * t))) t :=
    fun t => expBarrier_deriv t
  have hβderiv : ∀ t, HasDerivAt β (-(lam * (D * Real.exp (-lam * t)))) t := by
    intro t
    have h := (expBarrier_deriv (D := -D) (lam := lam) t)
    -- β t = 1 + D e^{-λt} = 1 - (-D) e^{-λt}, deriv = λ((-D)e) = -λ D e
    have heq : (fun t => 1 - (-D) * Real.exp (-lam * t)) = β := by
      funext s; rw [hβdef]; ring
    rw [heq] at h
    convert h using 1; ring
  -- barrier confinement from the trajectories
  have hconf : ∀ t z, 0 ≤ t → α t ≤ u t z ∧ u t z ≤ β t :=
    barrier_confinement_of_trajectories ha hb hαderiv hβderiv hlb hub
      h0lo h0hi htouchLo htouchHi
  -- convergence from confinement
  exact far_left_convergence_of_barrier hlam
    (fun t z ht => ⟨(hconf t z ht).1, (hconf t z ht).2⟩)

section AxiomAudit

#print axioms far_left_convergence_from_trajectories

end AxiomAudit

end ShenWork.Paper1
