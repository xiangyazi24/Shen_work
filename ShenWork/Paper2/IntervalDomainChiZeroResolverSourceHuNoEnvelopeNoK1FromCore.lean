/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceHuNoEnvelopeNoK1FromCore.lean

  Connect the Hres-core hsrc0 producer to the chi-zero Hu/no-envelope/no-K1
  resolver-source frontier.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceHuNoEnvelopeNoK1Frontier
import ShenWork.Paper2.IntervalResolverSourceWindowHsrc0FromCore

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData picardIter picardLimit)
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Fill the chi-zero Hu/no-envelope/no-K1 input package from the committed
Hres-core hsrc0 producer. -/
noncomputable def huNoEnvelopeNoK1Inputs_of_hresCore
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    {Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hDu : D.u = picardLimit p u₀ D.T)
    (C : HresWiring.PicardIterateResidualCore p u₀ D)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ)) :
    ResolverSourceWindowHuNoEnvelopeNoK1Inputs p D Hu where
  hsrc0 :=
    (resolverSourceWindowHsrc0Inputs_of_hresCore
      hα ha hb hu₀ hDu C hiter_cont).hsrc0

end ShenWork.Paper2.ResolverSourceWindowInput

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- Hres-core version of the chi-zero Hu/no-envelope/no-K1 window source
frontier. -/
theorem windowHuNoEnvelopeNoK1Frontier_of_hresCore
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (S : GradientMildHalfStepLogisticSourceData D)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (C : HresWiring.PicardIterateResidualCore p u₀ D)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))
    (hpde_u : ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)) :
    PerDatumWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D := by
  exact ⟨S, Hu,
    ResolverSourceWindowInput.huNoEnvelopeNoK1Inputs_of_hresCore
      hα ha hb hu₀ hDu C hiter_cont,
    hpde_u⟩

/-- Iterate-data version of the Hres-core bridge to the chi-zero
Hu/no-envelope/no-K1 source frontier. -/
theorem iterateHuNoEnvelopeNoK1Frontier_of_hresCore
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (I : PicardIterateConvergenceData D)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (C : HresWiring.PicardIterateResidualCore p u₀ D)
    (hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
      ContinuousOn
        (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        (Set.Icc a' τ))
    (hpde_u : ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α)) :
    PerDatumIterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D := by
  exact ⟨I, Hu,
    ResolverSourceWindowInput.huNoEnvelopeNoK1Inputs_of_hresCore
      hα ha hb hu₀ hDu C hiter_cont,
    hpde_u⟩

section AxiomAudit

#print axioms ResolverSourceWindowInput.huNoEnvelopeNoK1Inputs_of_hresCore
#print axioms windowHuNoEnvelopeNoK1Frontier_of_hresCore
#print axioms iterateHuNoEnvelopeNoK1Frontier_of_hresCore

end AxiomAudit

end ShenWork.Paper2.PPIDThresholdReachability
