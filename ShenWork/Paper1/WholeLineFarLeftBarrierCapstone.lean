import ShenWork.Paper1.WholeLineExpBarrierConvergence

/-!
# Global constant-equilibrium convergence from barrier confinement

This wires the abstract assembly's endpoint to barrier confinement.  If a
whole-line spatial family is confined between the symmetric exponential barriers
`1 − D e^{−λt} ≤ u(t,z) ≤ 1 + D e^{−λt}` (the output of the deferred first-touch
comparison lemma), then `u(t,·) → 1` uniformly.

For the full real line this is stronger than, and incompatible with, a
traveling front whose right tail tends to zero.  The actual front proof uses
the buffered half-line rectangle chain.  The lemmas here are endpoint wiring
only; they do not claim that a front satisfies global barrier confinement.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- The barrier confinement `1 − D e^{−λt} ≤ u ≤ 1 + D e^{−λt}` gives the
symmetric deviation bound `|u(t,z) − 1| ≤ D e^{−λt}`. -/
theorem abs_sub_one_le_of_barrier {u : ℝ → ℝ → ℝ} {D lam : ℝ}
    (hconf : ∀ t z, 0 ≤ t →
      1 - D * Real.exp (-lam * t) ≤ u t z ∧ u t z ≤ 1 + D * Real.exp (-lam * t))
    (t z : ℝ) (ht : 0 ≤ t) :
    |u t z - 1| ≤ D * Real.exp (-lam * t) := by
  rw [abs_le]
  obtain ⟨hlo, hhi⟩ := hconf t z ht
  constructor <;> linarith

/-- **Uniform convergence from barrier confinement.**  Confinement between the
symmetric exponential barriers implies uniform `u(t,·) → 1`. -/
theorem far_left_convergence_of_barrier
    {u : ℝ → ℝ → ℝ} {D lam : ℝ} (hlam : 0 < lam)
    (hconf : ∀ t z, 0 ≤ t →
      1 - D * Real.exp (-lam * t) ≤ u t z ∧ u t z ≤ 1 + D * Real.exp (-lam * t)) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t → |u t z - 1| < ε :=
  uniform_convergence_of_expBarrier hlam
    (fun t z ht => abs_sub_one_le_of_barrier hconf t z ht)

/-- The per-`z` `Tendsto` form. -/
theorem far_left_tendsto_of_barrier
    {u : ℝ → ℝ → ℝ} {D lam : ℝ} (hlam : 0 < lam) (hD : 0 ≤ D)
    (hconf : ∀ t z, 0 ≤ t →
      1 - D * Real.exp (-lam * t) ≤ u t z ∧ u t z ≤ 1 + D * Real.exp (-lam * t))
    (z : ℝ) :
    Tendsto (fun t => u t z) atTop (𝓝 1) :=
  tendsto_one_of_expBarrier hlam hD
    (fun t z ht => abs_sub_one_le_of_barrier hconf t z ht) z

section AxiomAudit

#print axioms far_left_convergence_of_barrier
#print axioms far_left_tendsto_of_barrier

end AxiomAudit

end ShenWork.Paper1
