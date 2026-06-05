/-
  PiecewiseClassicalWorks: the splice-is-classical hypothesis.
  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainRestartExtension

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PiecewiseGlue

/-- The splice of two overlapping classical solutions is classical. -/
def PiecewiseClassicalWorks (p : CM2Params) : Prop :=
  ∀ {T₁ T₂ τ : ℝ}, 0 < T₁ → 0 < T₂ → 0 < τ → τ < T₁ →
  ∀ {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
    IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
    IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
    (∀ s, τ < s → s < T₁ → ∀ x, u₁ s x = u₂ (s - τ) x) →
    (∀ s, τ < s → s < T₁ → ∀ x, v₁ s x = v₂ (s - τ) x) →
    ∀ T', 0 < T' → T' ≤ τ + T₂ →
      IsPaper2ClassicalSolution intervalDomain p T'
        (fun t x => if t ≤ T₁ then u₁ t x else u₂ (t - τ) x)
        (fun t x => if t ≤ T₁ then v₁ t x else v₂ (t - τ) x)

end ShenWork.Paper2.PiecewiseGlue
