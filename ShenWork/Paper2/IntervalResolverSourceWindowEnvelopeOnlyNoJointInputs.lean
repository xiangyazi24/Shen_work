/-
  ShenWork/Paper2/IntervalResolverSourceWindowEnvelopeOnlyNoJointInputs.lean

  Resolver-source envelope inputs with both redundant fields removed:
  per-time eigenvalue summability comes from singleton envelopes, and lifted
  joint continuity comes from u-side spectral agreement.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyInputs
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Envelope-only primitive resolver-source inputs without a separate lifted
joint-continuity field.  The missing `hbsum` is derivable from singleton
envelopes, and the missing `hliftCont` is supplied by u-side spectral agreement
on the PPID source surface. -/
structure ResolverSourceWindowEnvelopeOnlyNoJointInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) where
  bc : ℝ → ℕ → ℝ
  hagree : ∀ σ, 0 < σ → σ < D.T →
    Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)
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

/-- Fill the no-`hbsum` envelope-input structure from the thinner
envelope/no-joint package and u-side spectral agreement. -/
def resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointInputs p D) :
    ResolverSourceWindowEnvelopeOnlyInputs p D where
  bc := H.bc
  hagree := H.hagree
  hliftCont :=
    RegularityFrontierAssembly.jointSolutionClosed_u_of_spectralAgreement Hu
  henv := H.henv
  adotPow := H.adotPow
  hderivPow := H.hderivPow
  hadotPowCont := H.hadotPowCont
  hMdotPow := H.hMdotPow

/-- Fill the Task264 envelope-input structure from the thinner envelope/no-joint
package and u-side spectral agreement. -/
def resolverSourceWindowEnvelopeInputs_of_envelopeOnlyNoJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointInputs p D) :
    ResolverSourceWindowEnvelopeInputs p D :=
  resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs
    (resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs Hu H)

/-- Fill the Task259 joint-input structure from the thinner envelope/no-joint
package and u-side spectral agreement. -/
def resolverSourceWindowJointInputs_of_envelopeOnlyNoJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointInputs p D) :
    ResolverSourceWindowJointInputs p D :=
  resolverSourceWindowJointInputs_of_envelopeOnlyInputs
    (resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs Hu H)

/-- Fill the Task255 primitive input structure from the thinner envelope/no-joint
package and u-side spectral agreement. -/
def resolverSourceWindowInputs_of_envelopeOnlyNoJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointInputs p D) :
    ResolverSourceWindowInputs p D :=
  resolverSourceWindowInputs_of_envelopeOnlyInputs
    (resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs Hu H)

/-- The thinner envelope/no-joint package produces the Task246 window data once
u-side spectral agreement supplies lifted joint continuity. -/
theorem resolverSourceWindowData_of_envelopeOnlyNoJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWindowData p D :=
  resolverSourceWindowData_of_envelopeOnlyInputs
    (resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs Hu H)

/-- The thinner envelope/no-joint package also produces the raw clamped
resolver-source witness once u-side spectral agreement supplies lifted joint
continuity. -/
theorem resolverSourceWitness_of_envelopeOnlyNoJointInputs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (H : ResolverSourceWindowEnvelopeOnlyNoJointInputs p D) :
    ShenWork.Paper2.ResolverSourceWitnessFrontier.ResolverSourceWitness p D :=
  resolverSourceWitness_of_envelopeOnlyInputs
    (resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs Hu H)

end ShenWork.Paper2.ResolverSourceWindowInput
