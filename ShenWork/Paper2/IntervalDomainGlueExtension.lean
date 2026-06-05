/-
  Glue extension: overlap-glue two classical solutions with the same
  values on their time overlap to produce a solution on the union.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation
import ShenWork.Paper2.IntervalDomainTimeShift

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.GlueExtension

/-- **Glue extension: restrict the fresh solution to cover T₀ + δ/2.**
When the fresh solution from u₀ has horizon δ ≥ T₀ + δ/2 (i.e.,
δ/2 ≥ T₀), just restrict it. -/
theorem extend_when_fresh_covers
    {p : CM2Params} {δ : ℝ} (hδ : 0 < δ)
    {u₀ : intervalDomainPoint → ℝ}
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    {uf vf : ℝ → intervalDomainPoint → ℝ}
    (hsolf : IsPaper2ClassicalSolution intervalDomain p δ uf vf)
    (htracef : InitialTrace intervalDomain u₀ uf)
    (hcover : T₀ + δ / 2 ≤ δ) :
    ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
      InitialTrace intervalDomain u₀ u' :=
  ⟨uf, vf, hsolf.restrict_horizon (by linarith) hcover, htracef⟩

/-- **Glue two overlapping classical solutions from the SAME initial data.**
If S₁ on [0, T₁] and S₂ on [0, T₂] both have initial trace u₀ and
T₂ > T₁, then S₂ restricted to [0, T₁ + T₂/2] works (since T₂ ≥ T₁ + T₂/2
is NOT always true, we need T₂ ≥ T₁ + T₂/2, i.e., T₂/2 ≥ T₁).

Actually the simplest approach: just return the LONGER solution S₂. -/
theorem extend_by_longer_solution
    {p : CM2Params}
    {T₁ T₂ : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (h₂ : IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂)
    {u₀ : intervalDomainPoint → ℝ}
    (ht₂ : InitialTrace intervalDomain u₀ u₂)
    {Tnew : ℝ} (hle : Tnew ≤ T₂) (hpos : 0 < Tnew) :
    ∃ u' v', IsPaper2ClassicalSolution intervalDomain p Tnew u' v' ∧
      InitialTrace intervalDomain u₀ u' :=
  ⟨u₂, v₂, h₂.restrict_horizon hpos hle, ht₂⟩

/-- **RestartAndGlueWorks proof for the case T₀ ≤ δ/2.**
When T₀ ≤ δ/2, the fresh solution from u₀ on [0, δ] covers
[0, δ] ⊃ [0, T₀ + δ/2], so just restrict. -/
theorem restartAndGlue_small_T₀
    {p : CM2Params} {M δ : ℝ} (hM : 0 < M) (hδ : 0 < δ)
    (hfactory : ∀ {w : intervalDomainPoint → ℝ},
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hbound : ∀ x, |u₀ x| ≤ M)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (_hsol : IsPaper2ClassicalSolution intervalDomain p T₀ u v)
    (_htrace : InitialTrace intervalDomain u₀ u)
    (_hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M)
    (hsmall : T₀ ≤ δ / 2) :
    ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
      InitialTrace intervalDomain u₀ u' := by
  obtain ⟨uf, vf, hsolf, htracef⟩ := hfactory hu₀ hbound
  exact ⟨uf, vf, hsolf.restrict_horizon (by linarith) (by linarith), htracef⟩

end ShenWork.Paper2.GlueExtension
