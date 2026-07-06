/-
  ShenWork/Paper2/IntervalResolverSourceWindowEnvelopeOnlyInputs.lean

  Resolver-source envelope inputs with the per-time eigenvalue summability
  field discharged from singleton compact-window envelopes.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeInputs

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Envelope primitive inputs with no separate per-time eigenvalue summability
field.  The summability needed by the cosine derivative-transfer lemmas follows
from `henv` on singleton compact time windows. -/
structure ResolverSourceWindowEnvelopeOnlyInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  bc : ℝ → ℕ → ℝ
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
  hliftCont :
    ContinuousOn
      (Function.uncurry
        (fun (σ : ℝ) (x : ℝ) => intervalDomainLift (D.u σ) x))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1)
  henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
    ∃ E : ℕ → ℝ,
      Summable E ∧
      (∀ n, 0 ≤ E n) ∧
      (∀ σ ∈ Set.Icc a b, ∀ n,
        unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n)
  adotPow : ℝ → ℕ → ℝ
  hderivPow : ∀ σ, 0 < σ → σ < D.T → ∀ n,
    HasDerivAt
      (fun r => cosineCoeffs
        (fun x => p.ν * intervalDomainLift (D.u r) x ^ p.γ) n)
      (adotPow σ n) σ
  hadotPowCont : ∀ n, ContinuousOn (fun σ => adotPow σ n) (Set.Ioo 0 D.T)
  hMdotPow : ∀ a b, 0 < a → b < D.T →
    ∃ Mdot, ∀ σ ∈ Set.Icc a b, ∀ n, |adotPow σ n| ≤ Mdot

/-- A compact-window eigenvalue envelope gives the per-time summability needed
by the cosine-series derivative-transfer lemmas, by applying it to the singleton
window `[σ, σ]`. -/
theorem hbsum_of_envelope
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (bc : ℝ → ℕ → ℝ)
    (henv : ∀ a b, 0 < a → b < D.T → a ≤ b →
      ∃ E : ℕ → ℝ,
        Summable E ∧
        (∀ n, 0 ≤ E n) ∧
        (∀ σ ∈ Set.Icc a b, ∀ n,
          unitIntervalCosineEigenvalue n * |bc σ n| ≤ E n)) :
    ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|) := by
  intro σ hσpos hσT
  obtain ⟨E, hEsum, _hEnn, hdom⟩ := henv σ σ hσpos hσT le_rfl
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hEsum
  · exact mul_nonneg (by unfold unitIntervalCosineEigenvalue; positivity) (abs_nonneg _)
  · exact hdom σ ⟨le_rfl, le_rfl⟩ n

/-- The no-`hbsum` envelope surface produces the Task264 envelope input surface. -/
def resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeOnlyInputs p D) :
    ResolverSourceWindowEnvelopeInputs p D where
  bc := H.bc
  hbsum := hbsum_of_envelope H.bc H.henv
  hagree := H.hagree
  hliftCont := H.hliftCont
  henv := H.henv
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- The no-`hbsum` envelope surface produces the Task259 joint input surface. -/
def resolverSourceWindowJointInputs_of_envelopeOnlyInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeOnlyInputs p D) :
    ResolverSourceWindowJointInputs p D :=
  resolverSourceWindowJointInputs_of_envelopeInputs
    (resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs H)

/-- The no-`hbsum` envelope surface produces the Task255 primitive inputs. -/
def resolverSourceWindowInputs_of_envelopeOnlyInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeOnlyInputs p D) :
    ResolverSourceWindowInputs p D :=
  resolverSourceWindowInputs_of_envelopeInputs
    (resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs H)

/-- The no-`hbsum` envelope surface produces the Task246 window data. -/
theorem resolverSourceWindowData_of_envelopeOnlyInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeOnlyInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D :=
  resolverSourceWindowData_of_envelopeInputs
    (resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs H)

/-- The no-`hbsum` envelope surface also produces the raw clamped
resolver-source witness. -/
theorem resolverSourceWitness_of_envelopeOnlyInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (H : ResolverSourceWindowEnvelopeOnlyInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  resolverSourceWitness_of_envelopeInputs
    (resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs H)

end ShenWork.Paper2.ResolverSourceWindowInput
