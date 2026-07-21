import ShenWork.Paper1.WholeLineAbstractEnergyDecay

/-!
# From the exponential barrier to uniform far-left convergence

Fable R2's assembly (2026-07-21) produces, via a first-touch comparison lemma, a
uniform-in-`z` exponential barrier

`|u(t,z) − 1| ≤ D e^{−λt}`   (`λ > 0`),

and concludes `u(t,·) → 1` uniformly.  This file proves that final conclusion —
the endpoint of the assembly chain — as a clean `Tendsto`/squeeze statement,
independent of the (deferred) comparison lemma that supplies the barrier.

Two forms are given: the `ε`-`T` uniform-convergence statement matching
`UniformCoMovingLeftEquilibriumConvergence`'s shape, and the sup-norm `Tendsto`.
-/

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- `D e^{−λt} → 0` (the barrier envelope vanishes). -/
theorem expBarrier_tendsto_zero {D lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun t : ℝ => D * Real.exp (-lam * t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => lam * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hlam tendsto_id
  have hlin : Tendsto (fun t : ℝ => -lam * t) atTop atBot := by
    have h2 := tendsto_neg_atTop_atBot.comp h1
    have heq : (fun t : ℝ => -lam * t) = (Neg.neg ∘ fun t : ℝ => lam * t) := by
      funext s; simp only [Function.comp]; ring
    rw [heq]; exact h2
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-lam * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa using (tendsto_const_nhds (x := D)).mul hexp0

/-- **Uniform far-left convergence from the exponential barrier.**  If
`|u(t,z) − 1| ≤ D e^{−λt}` for all `z` and all `t ≥ 0` (`λ > 0`), then for every
`ε > 0` there is a time `T` past which `|u(t,z) − 1| < ε` uniformly in `z`. -/
theorem uniform_convergence_of_expBarrier
    {u : ℝ → ℝ → ℝ} {D lam : ℝ} (hlam : 0 < lam)
    (hbd : ∀ t z, 0 ≤ t → |u t z - 1| ≤ D * Real.exp (-lam * t)) :
    ∀ ε > 0, ∃ T : ℝ, ∀ t z, T ≤ t → 0 ≤ t → |u t z - 1| < ε := by
  intro ε hε
  have htend := expBarrier_tendsto_zero (D := D) hlam
  have : ∀ᶠ t in atTop, D * Real.exp (-lam * t) < ε := by
    have hball := htend (Iio_mem_nhds hε)
    simpa [Set.mem_Iio] using hball
  obtain ⟨T, hT⟩ := eventually_atTop.1 this
  refine ⟨T, ?_⟩
  intro t z htT ht0
  exact lt_of_le_of_lt (hbd t z ht0) (hT t htT)

/-- The barrier's `sup`-form: the pointwise deviation tends to `0` uniformly, i.e.
for each `z` the trajectory `t ↦ u(t,z)` tends to `1`, with a `z`-uniform rate. -/
theorem tendsto_one_of_expBarrier
    {u : ℝ → ℝ → ℝ} {D lam : ℝ} (hlam : 0 < lam) (_hD : 0 ≤ D)
    (hbd : ∀ t z, 0 ≤ t → |u t z - 1| ≤ D * Real.exp (-lam * t))
    (z : ℝ) :
    Tendsto (fun t => u t z) atTop (𝓝 1) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (g := fun t => D * Real.exp (-lam * t))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact dist_nonneg
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [Real.dist_eq]
    exact hbd t z ht
  · exact expBarrier_tendsto_zero hlam

section AxiomAudit

#print axioms uniform_convergence_of_expBarrier
#print axioms tendsto_one_of_expBarrier

end AxiomAudit

end ShenWork.Paper1
