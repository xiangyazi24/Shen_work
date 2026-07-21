import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Abstract `hstart` producer

`parabolic_lower_barrier_direct_of_initial_interval` requires the initial-
confinement clause

`hstart : ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → α t ≤ a t`.

This file manufactures that clause from a **strict initial gap** plus **right-
continuity at `0`**: if the barrier `α` and the spatial envelope `a` are
continuous within `[0,∞)` at `0` and `α 0 < a 0` (strictly), then `α ≤ a` on a
whole right-neighbourhood `[0,ε]`.  For the symmetric exponential barrier
`α 0 = 1 − D` this reduces to the checkable initial condition `1 − D < ⨅_z u₀(z)`.

It is pure topology (`ContinuousWithinAt.sub` + `mem_nhdsWithin_iff`), independent
of the PDE and of how the infimum is realized, so it is banked ahead of the
design questions.  Combined with `ciInf_dist_le` (sup-norm controls the inf) and
the BUC semigroup's strong continuity, it discharges `hstart` for the concrete
solution.
-/

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper1

/-- **Abstract `hstart` from a strict initial gap.**  If `α` and `a` are
continuous within `[0,∞)` at `0` and `α 0 < a 0`, then `α t ≤ a t` on some
`[0,ε]` with `ε > 0`. -/
theorem hstart_of_strict_gap {α a : ℝ → ℝ}
    (hα : ContinuousWithinAt α (Set.Ici 0) 0)
    (ha : ContinuousWithinAt a (Set.Ici 0) 0)
    (hgap : α 0 < a 0) :
    ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → α t ≤ a t := by
  have hg0 : 0 < a 0 - α 0 := by linarith
  have hg : ContinuousWithinAt (fun t => a t - α t) (Set.Ici 0) 0 := ha.sub hα
  -- the set where `a − α > 0` is a within-`Ici 0` neighbourhood of `0`
  have hmem : {t : ℝ | 0 < a t - α t} ∈ nhdsWithin 0 (Set.Ici 0) :=
    hg (Ioi_mem_nhds hg0)
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨ε, hε0, hsub⟩ := hmem
  refine ⟨ε / 2, by linarith, ?_⟩
  intro t ht0 htε
  have hball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith
  have hIci : t ∈ Set.Ici (0 : ℝ) := ht0
  have : t ∈ {t : ℝ | 0 < a t - α t} := hsub ⟨hball, hIci⟩
  simp only [Set.mem_setOf_eq] at this
  linarith

/-- Right-continuity at `0` of the symmetric exponential lower barrier
`α t = 1 − D e^{−λ t}` (in fact continuity, restricted to `Ici 0`). -/
theorem expBarrier_continuousWithinAt_zero {D lam : ℝ} :
    ContinuousWithinAt (fun t => 1 - D * Real.exp (-lam * t)) (Set.Ici 0) 0 := by
  apply Continuous.continuousWithinAt
  fun_prop

/-- Specialization: for the exponential lower barrier with `1 − D < a 0`
(the checkable initial condition `1 − D < ⨅_z u₀`), `hstart` holds. -/
theorem hstart_expBarrier_of_initial {a : ℝ → ℝ} {D lam : ℝ}
    (ha : ContinuousWithinAt a (Set.Ici 0) 0)
    (hinit : 1 - D < a 0) :
    ∃ ε, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε →
      (1 - D * Real.exp (-lam * t)) ≤ a t := by
  apply hstart_of_strict_gap (expBarrier_continuousWithinAt_zero) ha
  -- α 0 = 1 − D e^{0} = 1 − D < a 0
  simpa using hinit

section AxiomAudit

#print axioms hstart_of_strict_gap
#print axioms hstart_expBarrier_of_initial

end AxiomAudit

end ShenWork.Paper1
