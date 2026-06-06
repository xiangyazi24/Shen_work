/-
  Phase C (MinPersistence): a uniform datum bound from PID admissibility.

  A positive initial datum's admissibility includes `BddAbove (range |u₀|)`,
  so there is a positive `M` with `|u₀ x| ≤ M` for all `x`.  This is the `M`
  feeding `regimeBound`/`hSupNorm` in the `ClassicalMinPersistence` assembly.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain ShenWork.Paper2 Set

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- **Uniform datum bound from PID.** -/
theorem pid_exists_bound {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : intervalDomainPoint, |u₀ x| ≤ M := by
  obtain ⟨B, hB⟩ := hu₀.1.1
  refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right B 1), fun x => ?_⟩
  exact le_trans (hB (Set.mem_range_self x)) (le_max_left B 1)

end ShenWork.MinPersistenceAtoms
