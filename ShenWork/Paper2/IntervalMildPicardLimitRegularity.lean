/-
  Picard iterate regularity pass-to-limit.

  `DuhamelSourceTimeC1` passes to pointwise limits under uniform
  derivative convergence (Mathlib `hasDerivAt_of_tendstoUniformly`).
  This is the bridge from per-iterate regularity to limit regularity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildPicardRegularity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open ShenWork.IntervalDuhamelClosedC2
open Filter

noncomputable section

namespace ShenWork.IntervalMildPicardLimitRegularity

/-- `DuhamelSourceTimeC1` passes to pointwise limits when the derivatives
converge uniformly and the coefficients share a common summable envelope
and derivative bound. Uses Mathlib `hasDerivAt_of_tendstoUniformly`. -/
def duhamelSourceTimeC1_of_uniform_limit
    {a : ℝ → ℕ → ℝ}
    {aSeq : ℕ → ℝ → ℕ → ℝ}
    (hconv : ∀ s k, Tendsto (fun n => aSeq n s k) atTop (nhds (a s k)))
    {adotSeq : ℕ → ℝ → ℕ → ℝ}
    (hderiv_each : ∀ n s k, HasDerivAt (fun r => aSeq n r k) (adotSeq n s k) s)
    {adot : ℝ → ℕ → ℝ}
    (hadot_unif : ∀ k,
      TendstoUniformly (fun n s => adotSeq n s k) (fun s => adot s k) atTop)
    (hadot_cont : ∀ k, Continuous (fun s => adot s k))
    {envelope : ℕ → ℝ}
    (henv_summable : Summable envelope)
    (henv_bound : ∀ n s, 0 ≤ s → ∀ k, |aSeq n s k| ≤ envelope k)
    {D : ℝ}
    (hderiv_bound : ∀ n s, 0 ≤ s → ∀ k, |adotSeq n s k| ≤ D) :
    DuhamelSourceTimeC1 a where
  adot := adot
  hderiv := by
    intro s k
    exact hasDerivAt_of_tendstoUniformly (hadot_unif k)
      (Eventually.of_forall (fun n x => hderiv_each n x k))
      (fun x => hconv x k) s
  hadotcont := hadot_cont
  envelope := envelope
  henv_summable := henv_summable
  henv_bound := by
    intro s hs k
    have htendsto := (continuous_abs.tendsto _).comp (hconv s k)
    simp only [Function.comp] at htendsto
    exact le_of_tendsto htendsto
      (Eventually.of_forall (fun n => henv_bound n s hs k))
  derivBound := D
  hderivBound := by
    intro s hs k
    have htendsto := (continuous_abs.tendsto _).comp
      ((hadot_unif k).tendsto_at s)
    simp only [Function.comp] at htendsto
    exact le_of_tendsto htendsto
      (Eventually.of_forall (fun n => hderiv_bound n s hs k))

end ShenWork.IntervalMildPicardLimitRegularity
