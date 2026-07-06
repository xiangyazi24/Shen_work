/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceHuCoeffNoK1Frontier.lean

  Chi-zero headline wrappers from resolver-source inputs carrying neither
  explicit `bc/hagree` nor explicit power-source K1 fields.  The remaining
  producer fields are the compact Hu-coefficient envelope and `hsrc0`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointNoK1InputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowHuCoeffNoK1Inputs

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

/-- Chi-zero source frontier with Hu-selected resolver-source coefficients and
no explicit power-source K1 fields.  The compact coefficient envelope and
bounded patched-source package remain explicit in the input structure. -/
def PerDatumWindowHuCoeffNoK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuCoeffNoK1Inputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with Hu-selected coefficients and no explicit K1
fields. -/
def PerDatumIterateWindowHuCoeffNoK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuCoeffNoK1Inputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Hu/no-K1 source data fills the Task269 no-K1 source frontier. -/
theorem windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier_of_windowHuCoeffNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHuCoeffNoK1SourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D := by
  obtain ⟨S, Hu, H, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs_of_huCoeffNoK1Inputs H,
    Hu, hpde_u⟩

/-- Iterate Hu/no-K1 source data fills the Task269 iterate no-K1 source
frontier. -/
theorem iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuCoeffNoK1SourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs_of_huCoeffNoK1Inputs H,
    Hu, hpde_u⟩

/-- Hu/no-K1 source data gives the unified Picard-limit restart frontier in the
chi-zero branch. -/
theorem picardLimitRestartFrontier_of_windowHuCoeffNoK1SourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hHuNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuCoeffNoK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier_of_windowHuCoeffNoK1SourceSpectralFrontier
        (hHuNoK1 u₀ hu₀ D hD))

/-- Iterate Hu/no-K1 source data gives the unified Picard-limit restart frontier
in the chi-zero branch. -/
theorem picardLimitRestartFrontier_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterHuNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuCoeffNoK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
        (hIterHuNoK1 u₀ hu₀ D hD))

end ShenWork.Paper2.PPIDThresholdReachability

namespace ShenWork.Paper2.ConeQuantBridge

open ShenWork.Paper2.PPIDThresholdReachability

/-- The chi-zero headline route with Hu-selected resolver-source coefficients
and no explicit power-source K1 fields.  The remaining source-side producer
inputs are the compact Hu-coefficient envelope and `hsrc0`. -/
theorem paper2_theorem_1_1_chiZero_of_windowHuCoeffNoK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hHuNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuCoeffNoK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier_of_windowHuCoeffNoK1SourceSpectralFrontier
        (hHuNoK1 u₀ hu₀ D hD))

/-- Iterate version of the chi-zero headline route with Hu-selected coefficients
and no explicit K1 fields. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterHuNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuCoeffNoK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier
        (hIterHuNoK1 u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowHuCoeffNoK1SourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowHuCoeffNoK1SourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
