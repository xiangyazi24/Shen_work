import ShenWork.PDE.P3MoserRealInduction

/-!
# Real-induction closure for the Moser first-crossing argument

This file discharges the order-theoretic part of
`FirstCrossingPointwiseUniformClosureResidual`: short-time membership and a
right-extension step force `BoundedBeforeOnSubinterval` all the way up to `T`.

The remaining conversion from pointwise-in-time existential bounds to a single
uniform constant is kept as a named residual, as allowed by
`CODEX_SPEC_task32_real_induction_closure.md`.
-/

open Set
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRealInductionClosure

open ShenWork.IntervalDomainExistence.P3MoserFirstCrossingContinuation
open ShenWork.IntervalDomainExistence.P3MoserRealInduction

/-- The fully order-theoretic first-crossing closure.  This is the part proved
by real induction: the good set of subinterval endpoints has supremum `T`. -/
theorem firstCrossing_boundedBeforeOnSubinterval_T
    {D : BoundedDomainData} {p : CM2Params}
    {T : ℝ} {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hshort : ShortTimeBoundedBeforeResidual D p)
    (hright :
      ∀ {τ : ℝ},
        0 < τ →
          τ < T →
            BoundedBeforeOnSubinterval D u τ T →
              ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
                BoundedBeforeOnSubinterval D u (τ + δ) T) :
    BoundedBeforeOnSubinterval D u T T := by
  rcases hshort hsol with ⟨τ₀, hτ₀_pos, hτ₀_sub⟩
  let S : Set ℝ := {τ | BoundedBeforeOnSubinterval D u τ T}
  have hτ₀_mem : τ₀ ∈ S := hτ₀_sub
  have hS_nonempty : S.Nonempty := ⟨τ₀, hτ₀_mem⟩
  have hS_bdd : BddAbove S := ⟨T, fun τ hτ => hτ.1⟩
  let τstar : ℝ := sSup S
  have hτ₀_le_star : τ₀ ≤ τstar := by
    exact le_csSup hS_bdd hτ₀_mem
  have hstar_pos : 0 < τstar := by
    linarith
  have hstar_le_T : τstar ≤ T := by
    exact csSup_le hS_nonempty (fun τ hτ => hτ.1)
  have hstar_sub : BoundedBeforeOnSubinterval D u τstar T := by
    refine ⟨hstar_le_T, ?_⟩
    intro t ht0 htstar
    obtain ⟨τ, hτ_mem, htτ⟩ := exists_lt_of_lt_csSup hS_nonempty htstar
    exact hτ_mem.2 t ht0 htτ
  have hstar_eq_T : τstar = T := by
    rcases lt_or_eq_of_le hstar_le_T with hstar_lt_T | hstar_eq_T
    · rcases hright hstar_pos hstar_lt_T hstar_sub with
        ⟨δ, hδ_pos, _hδT, hδ_sub⟩
      have hδ_le_star : τstar + δ ≤ τstar := by
        exact le_csSup hS_bdd hδ_sub
      have : δ ≤ 0 := by linarith
      exact False.elim ((not_le_of_gt hδ_pos) this)
    · exact hstar_eq_T
  simpa [τstar, hstar_eq_T] using hstar_sub

/-- The per-time pointwise conclusion produced by the proved real-induction
closure. -/
theorem firstCrossing_pointwise_exists_bound_before_T
    {D : BoundedDomainData} {p : CM2Params}
    {T : ℝ} {u v : ℝ → D.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution D p T u v)
    (hshort : ShortTimeBoundedBeforeResidual D p)
    (hright :
      ∀ {τ : ℝ},
        0 < τ →
          τ < T →
            BoundedBeforeOnSubinterval D u τ T →
              ∃ δ, 0 < δ ∧ τ + δ ≤ T ∧
                BoundedBeforeOnSubinterval D u (τ + δ) T) :
    ∀ t, 0 < t → t < T → ∃ M, ∀ x, |u t x| ≤ M := by
  have hsub : BoundedBeforeOnSubinterval D u T T :=
    firstCrossing_boundedBeforeOnSubinterval_T hsol hshort hright
  exact hsub.2

/-- The remaining analytic uniformization step: convert the per-time pointwise
bounds delivered by real induction into one constant on `(0,T)`. -/
def PointwiseUniformizationResidual
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  ∀ {T : ℝ} {u v : ℝ → D.Point → ℝ},
    IsPaper2ClassicalSolution D p T u v →
      BoundedBeforeOnSubinterval D u T T →
        ∃ M, ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M

/-- For `intervalDomain`, the original pointwise-uniform closure follows from
the proved real-induction closure plus the explicitly named uniformization
residual. -/
theorem intervalDomain_FirstCrossingPointwiseUniformClosureResidual
    {p : CM2Params}
    (huniform : PointwiseUniformizationResidual intervalDomain p) :
    FirstCrossingPointwiseUniformClosureResidual intervalDomain p := by
  intro T u v hsol hshort hright
  exact huniform hsol
    (firstCrossing_boundedBeforeOnSubinterval_T hsol hshort hright)

#print axioms firstCrossing_boundedBeforeOnSubinterval_T
#print axioms firstCrossing_pointwise_exists_bound_before_T
#print axioms intervalDomain_FirstCrossingPointwiseUniformClosureResidual

end ShenWork.IntervalDomainExistence.P3MoserRealInductionClosure

end
