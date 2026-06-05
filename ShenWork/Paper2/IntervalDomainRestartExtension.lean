/-
  F1 reduction: IntervalDomainUniformLocalExistence from
  QuantitativeLocalExistence + RestartAndGlueWorks.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainUniformContinuation

open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.RestartExtension

/-- The restart-and-glue hypothesis: an existing solution + a fresh
solution from an interior slice produce an extended solution. -/
def RestartAndGlueWorks (p : CM2Params) : Prop :=
  ∀ {M : ℝ}, 0 < M → ∀ {δ : ℝ}, 0 < δ →
    -- Fresh solution from any PID w with |w| ≤ M
    (∀ {w : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw) →
    -- Existing solution + extension
    ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
    ∀ {T₀}, 0 < T₀ →
    ∀ {u v}, IsPaper2ClassicalSolution intervalDomain p T₀ u v →
      InitialTrace intervalDomain u₀ u →
      ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ) u' v' ∧
        InitialTrace intervalDomain u₀ u'

/-- **F1 from QuantitativeLocalExistence + RestartAndGlueWorks.** -/
theorem uniformLocalExistence_of_quantitative_and_restart
    (p : CM2Params)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x : intervalDomain.Point, |u₀ x| ≤ M) →
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hRestart : RestartAndGlueWorks p) :
    IntervalDomainUniformLocalExistence p := by
  intro M hM
  obtain ⟨δ, hδ, hex⟩ := hQuant M hM
  refine ⟨δ, hδ, fun {u₀} hu₀ hbound {T₀} hT₀ {u v} hsol htrace => ?_⟩
  exact hRestart hM hδ (fun {w} hw hbound_w => hex hw hbound_w) hu₀ hbound hT₀ hsol htrace

end ShenWork.Paper2.RestartExtension
