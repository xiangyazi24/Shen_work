/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceHuNoEnvelopeNoK1Frontier.lean

  Chi-zero frontier after producing the compact Hu coefficient envelope directly
  from `Hu`, with K1 still obtained from the bounded patched-source package.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceHuCoeffNoK1Frontier
import ShenWork.Paper2.IntervalHuRestartCoeffFiniteCoverProducer

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- Chi-zero source frontier after deleting the explicit compact Hu-envelope
field.  The remaining resolver-source input is the bounded patched-source
package that supplies K1. -/
def PerDatumWindowHuNoEnvelopeNoK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuNoEnvelopeNoK1Inputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source version of the chi-zero no-envelope/no-K1 Hu frontier. -/
def PerDatumIterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuNoEnvelopeNoK1Inputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- No-envelope/no-K1 source data fills the existing HuCoeff/no-K1 source
frontier. -/
theorem windowHuCoeffNoK1SourceSpectralFrontier_of_windowHuNoEnvelopeNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    PerDatumWindowHuCoeffNoK1SourceSpectralFrontier p D := by
  obtain ⟨S, Hu, H, hpde_u⟩ := h
  exact ⟨S, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffNoK1Inputs_of_noEnvelopeNoK1Inputs H,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field. -/
theorem windowHuNoEnvelopeNoK1SourceSpectralFrontier_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    PerDatumWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    Hu, H, hpde_u⟩

/-- Iterate no-envelope/no-K1 source data fills the iterate HuCoeff/no-K1
frontier. -/
theorem iterateWindowHuCoeffNoK1SourceSpectralFrontier_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    PerDatumIterateWindowHuCoeffNoK1SourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨I, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffNoK1Inputs_of_noEnvelopeNoK1Inputs H,
    hpde_u⟩

/-- No-envelope/no-K1 source data gives the unified Picard-limit restart
frontier in the chi-zero branch. -/
theorem picardLimitRestartFrontier_of_windowHuNoEnvelopeNoK1SourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hNoEnvelopeNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowHuCoeffNoK1SourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      windowHuCoeffNoK1SourceSpectralFrontier_of_windowHuNoEnvelopeNoK1SourceSpectralFrontier
        (hNoEnvelopeNoK1 u₀ hu₀ D hD))

/-- Iterate no-envelope/no-K1 source data gives the unified Picard-limit restart
frontier in the chi-zero branch. -/
theorem picardLimitRestartFrontier_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterNoEnvelopeNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffNoK1SourceSpectralFrontier_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
        (hIterNoEnvelopeNoK1 u₀ hu₀ D hD))

end ShenWork.Paper2.PPIDThresholdReachability

namespace ShenWork.Paper2.ConeQuantBridge

open ShenWork.Paper2.PPIDThresholdReachability

/-- The chi-zero headline route after deleting the explicit compact Hu-envelope
field.  The remaining source-side producer input is the bounded-source package. -/
theorem paper2_theorem_1_1_chiZero_of_windowHuNoEnvelopeNoK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoEnvelopeNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowHuCoeffNoK1SourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowHuCoeffNoK1SourceSpectralFrontier_of_windowHuNoEnvelopeNoK1SourceSpectralFrontier
        (hNoEnvelopeNoK1 u₀ hu₀ D hD))

/-- Iterate version of the chi-zero no-envelope/no-K1 headline route. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoEnvelopeNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffNoK1SourceSpectralFrontier_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier
        (hIterNoEnvelopeNoK1 u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowHuNoEnvelopeNoK1SourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowHuNoEnvelopeNoK1SourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
