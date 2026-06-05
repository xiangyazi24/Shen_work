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

/-- The restart-and-glue hypothesis: given an existing solution on
[0, T₀] and a fresh-solution factory on [0, δ], produce a solution on
[0, T₀ + δ/2] with the same initial trace.

The construction: restart from u(T₀ − δ/2), time-shift the fresh
solution, glue via overlap uniqueness on (T₀−δ/2, T₀). -/
def RestartAndGlueWorks (p : CM2Params) : Prop :=
  ∀ {M δ : ℝ}, 0 < M → 0 < δ →
    -- Fresh factory
    (∀ {w : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain w →
      (∀ x, |w x| ≤ M) →
      ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
        InitialTrace intervalDomain w uw) →
    -- Existing solution
    ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
    ∀ {T₀}, 0 < T₀ →
    ∀ {u v}, IsPaper2ClassicalSolution intervalDomain p T₀ u v →
      InitialTrace intervalDomain u₀ u →
      -- Interior sup-norm bound (from Lemma 3.1)
      (∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M) →
      -- Extension
      ∃ u' v', IsPaper2ClassicalSolution intervalDomain p (T₀ + δ / 2) u' v' ∧
        InitialTrace intervalDomain u₀ u'

/-- **F1 from QuantitativeLocalExistence + RestartAndGlueWorks +
uniform sup-norm bound (Lemma 3.1).** -/
theorem uniformLocalExistence_of_quantitative_restart_supNorm
    (p : CM2Params)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v, IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hRestart : RestartAndGlueWorks p)
    (hSupNorm : ∀ {M : ℝ}, 0 < M →
      ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
      ∀ {T₀}, 0 < T₀ →
      ∀ {u v}, IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M) :
    IntervalDomainUniformLocalExistence p := by
  intro M hM
  obtain ⟨δ, hδ, hex⟩ := hQuant M hM
  exact ⟨δ / 2, by linarith, fun {u₀} hu₀ hb {T₀} hT₀ {u v} hsol htrace =>
    hRestart hM hδ (fun {w} hw hbw => hex hw hbw)
      hu₀ hb hT₀ hsol htrace (hSupNorm hM hu₀ hb hT₀ hsol htrace)⟩

end ShenWork.Paper2.RestartExtension
