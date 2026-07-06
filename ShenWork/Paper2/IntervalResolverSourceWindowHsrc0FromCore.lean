/-
  ShenWork/Paper2/IntervalResolverSourceWindowHsrc0FromCore.lean

  Bridge from the narrowed Hres core provider to the Task270 hsrc0-only
  resolver-source input surface.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs
import ShenWork.Paper2.IntervalDomainHresWiring

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardIter picardLimit)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2 (PositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Hres core data plus tower coefficient-time continuity produce the Task270
hsrc0-only resolver-source input package. -/
noncomputable def resolverSourceWindowHsrc0Inputs_of_hresCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (C : ShenWork.Paper2.HresWiring.PicardIterateResidualCore p u₀ D)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ)) :
    ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D where
  hsrc0 :=
    ShenWork.Paper2.HresWiring.duhamelSourceBddOn_of_core
      hα ha hb hu₀ hDu C hiter_cont

/-- Directly fill the Task268 envelope/no-joint package from Hres core data in
the chi-zero branch. -/
noncomputable def resolverSourceWindowEnvelopeOnlyNoJointInputs_of_hresCore
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (C : ShenWork.Paper2.HresWiring.PicardIterateResidualCore p u₀ D)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ)) :
    ResolverSourceWindowEnvelopeOnlyNoJointInputs p D :=
  resolverSourceWindowEnvelopeOnlyNoJointInputs_of_hsrc0Inputs
    hχ0 hα ha hb hu₀
    (resolverSourceWindowHsrc0Inputs_of_hresCore
      hα ha hb hu₀ hDu C hiter_cont)

end ShenWork.Paper2.ResolverSourceWindowInput
