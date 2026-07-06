/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceHuFiniteCoverNoK1Frontier.lean

  Chi-zero headline wrappers from explicit finite restart-chart covers for
  Hu-selected resolver-source coefficients, with no explicit power-source K1.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceHuCoeffNoK1Frontier
import ShenWork.Paper2.IntervalHuRestartCoeffFiniteCover

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

/-- Chi-zero source frontier where the Hu coefficient envelope is supplied by
explicit finite restart-chart covers and power-source K1 is not explicit. -/
def PerDatumWindowHuFiniteCoverNoK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuFiniteCoverNoK1Inputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with finite-cover Hu coefficient envelopes and no
explicit K1 fields. -/
def PerDatumIterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuFiniteCoverNoK1Inputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Finite-cover Hu/no-K1 source data fills the HuCoeff/no-K1 source frontier. -/
theorem windowHuCoeffNoK1SourceSpectralFrontier_of_windowHuFiniteCoverNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    PerDatumWindowHuCoeffNoK1SourceSpectralFrontier p D := by
  obtain ⟨S, Hu, H, hpde_u⟩ := h
  exact ⟨S, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffNoK1Inputs_of_finiteCoverNoK1Inputs H,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the finite-cover Hu/no-K1 source surface. -/
theorem windowHuFiniteCoverNoK1SourceSpectralFrontier_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    PerDatumWindowHuFiniteCoverNoK1SourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    Hu, H, hpde_u⟩

/-- Iterate finite-cover Hu/no-K1 source data fills the iterate HuCoeff/no-K1
source frontier. -/
theorem iterateWindowHuCoeffNoK1SourceSpectralFrontier_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    PerDatumIterateWindowHuCoeffNoK1SourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨I, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffNoK1Inputs_of_finiteCoverNoK1Inputs H,
    hpde_u⟩

/-- Finite-cover Hu/no-K1 source data gives the unified Picard-limit restart
frontier in the chi-zero branch. -/
theorem picardLimitRestartFrontier_of_windowHuFiniteCoverNoK1SourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hFiniteCoverNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowHuCoeffNoK1SourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      windowHuCoeffNoK1SourceSpectralFrontier_of_windowHuFiniteCoverNoK1SourceSpectralFrontier
        (hFiniteCoverNoK1 u₀ hu₀ D hD))

/-- Iterate finite-cover Hu/no-K1 source data gives the unified Picard-limit
restart frontier in the chi-zero branch. -/
theorem picardLimitRestartFrontier_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterFiniteCoverNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffNoK1SourceSpectralFrontier_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
        (hIterFiniteCoverNoK1 u₀ hu₀ D hD))

end ShenWork.Paper2.PPIDThresholdReachability

namespace ShenWork.Paper2.ConeQuantBridge

open ShenWork.Paper2.PPIDThresholdReachability

/-- The chi-zero headline route with finite-cover Hu resolver-source
coefficients and no explicit power-source K1 fields.  The remaining source-side
producer inputs are the finite chart covers and `hsrc0`. -/
theorem paper2_theorem_1_1_chiZero_of_windowHuFiniteCoverNoK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hFiniteCoverNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowHuCoeffNoK1SourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowHuCoeffNoK1SourceSpectralFrontier_of_windowHuFiniteCoverNoK1SourceSpectralFrontier
        (hFiniteCoverNoK1 u₀ hu₀ D hD))

/-- Iterate version of the chi-zero headline route with finite-cover
Hu-selected coefficients and no explicit K1 fields. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterFiniteCoverNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuFiniteCoverNoK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffNoK1SourceSpectralFrontier_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier
        (hIterFiniteCoverNoK1 u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowHuFiniteCoverNoK1SourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowHuFiniteCoverNoK1SourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
