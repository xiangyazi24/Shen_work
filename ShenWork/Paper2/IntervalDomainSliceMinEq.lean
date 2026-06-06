/-
  Phase C (MinPersistence): the spatial minimum is slice-determined.

  If two solution slices agree pointwise (`∀ x, f x = g x` — the conclusion of
  overlap uniqueness `OverlapUniqueForPID` at a common time), their spatial
  minima coincide:
    `sInf (lift f '' [0,1]) = sInf (lift g '' [0,1])`.
  This is the uniformity core of `ClassicalMinPersistence`: all solutions with
  the same trace `u₀` agree at `t₁/2`, so share `m_u(t₁/2)`, so share the
  Hamilton floor `c = m·e^{−K(δ−t₁/2)}`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalDomain

open ShenWork.IntervalDomain Set

noncomputable section

namespace ShenWork.MinPersistenceAtoms

/-- Equal slices have equal lifts. -/
theorem intervalDomainLift_congr {f g : intervalDomainPoint → ℝ}
    (h : ∀ x, f x = g x) : intervalDomainLift f = intervalDomainLift g := by
  funext y
  rw [intervalDomainLift, intervalDomainLift]
  split_ifs with hy
  · exact h ⟨y, hy⟩
  · rfl

/-- **The spatial minimum is slice-determined.** -/
theorem sliceMin_eq_of_slices_eq {f g : intervalDomainPoint → ℝ}
    (h : ∀ x, f x = g x) :
    sInf (intervalDomainLift f '' Set.Icc (0:ℝ) 1)
      = sInf (intervalDomainLift g '' Set.Icc (0:ℝ) 1) := by
  rw [intervalDomainLift_congr h]

end ShenWork.MinPersistenceAtoms
