import ShenWork.PDE.P3MoserFirstCrossingContinuation
import ShenWork.PDE.IntervalDomainAPrioriGlobal

/-!
# Continuity extension residual for the concrete interval domain

The abstract `ExtensionByContinuityResidual` asks for bounded-before on the
whole positive-time interval below `τ + δ`.  For the concrete interval domain
this follows from the closed-interval spatial continuity already packaged in
`intervalDomainClassicalRegularity`: every interior positive-time slice is
bounded on `[0,1]`.
-/

open Set
open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserContinuityExtension

open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation

/-- A bounded-above absolute-value range gives the existential pointwise bound
used by `BoundedBeforeOnSubinterval`. -/
theorem exists_pointwise_abs_bound_of_bddAbove
    {X : Type*} {f : X → ℝ}
    (hbdd : BddAbove (Set.range f)) :
    ∃ M, ∀ x, f x ≤ M := by
  rcases hbdd with ⟨M, hM⟩
  exact ⟨M, fun x => hM ⟨x, rfl⟩⟩

/-- Every positive interior time slice of a classical interval-domain solution
has a pointwise absolute-value bound. -/
theorem intervalDomain_solution_slice_abs_bound
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    ∃ M, ∀ x : intervalDomain.Point, |u t x| ≤ M :=
  exists_pointwise_abs_bound_of_bddAbove
    (intervalDomain_solution_slice_abs_bddAbove hsol ht)

/-- Concrete discharge of Residual C for the unit interval.

The proof chooses `δ = (T - τ) / 2`; then every `0 < t < τ + δ` is an interior
time, and the previous slice-boundedness lemma supplies the bound required by
`BoundedBeforeOnSubinterval`.
-/
theorem intervalDomain_extensionByContinuityResidual
    (p : CM2Params) :
    ExtensionByContinuityResidual intervalDomain p := by
  intro T τ M u v hτT hsol _hbound_at_τ
  refine ⟨(T - τ) / 2, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · refine ⟨?_, ?_⟩
    · linarith
    · intro t ht0 httauδ
      exact intervalDomain_solution_slice_abs_bound hsol
        (show t ∈ Set.Ioo (0 : ℝ) T from ⟨ht0, by linarith⟩)

#print axioms exists_pointwise_abs_bound_of_bddAbove
#print axioms intervalDomain_solution_slice_abs_bound
#print axioms intervalDomain_extensionByContinuityResidual

end ShenWork.IntervalDomainExistence.P3MoserContinuityExtension

end
