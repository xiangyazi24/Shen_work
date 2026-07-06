/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointHsrc0InputsFrontier.lean

  χ₀ = 0 headline wrappers from resolver-source inputs where the coefficient
  representation, compact envelope, lifted joint continuity, and power-source K1
  fields are all derived; the bounded patched-source package remains explicit.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs
import ShenWork.Paper2.IntervalResolverSourceWindowHsrc0FromCore

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- χ₀ = 0 source frontier where the resolver-source input is reduced to the
bounded patched-source package `hsrc0`; the canonical `limitCoeff` representation
and compact eigenvalue envelope are derived from it. -/
def PerDatumWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with resolver-source inputs reduced to `hsrc0`. -/
def PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- hsrc0-only source data fills the existing envelope/no-joint source frontier
in the χ₀ = 0 branch. -/
theorem windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hSrc, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointInputs_of_hsrc0Inputs
      hχ0 hα ha hb hu₀ hSrc,
    hTimeNhd, hpde_u⟩

/-- Iterate hsrc0-only source data fills the existing iterate
envelope/no-joint source frontier in the χ₀ = 0 branch. -/
theorem iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hSrc, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointInputs_of_hsrc0Inputs
      hχ0 hα ha hb hu₀ hSrc,
    hTimeNhd, hpde_u⟩

/-- Window hsrc0-only source data gives the unified Picard-limit restart
frontier in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
        hχ0 hα ha hb hu₀ (hSrc u₀ hu₀ D hD))

/-- Iterate hsrc0-only source data gives the unified Picard-limit restart
frontier in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
        hχ0 hα ha hb hu₀ (hIterSrc u₀ hu₀ D hD))

/-- χ₀ = 0 source frontier with the resolver-source input reduced to `hsrc0`;
the u-side time-neighborhood spectral agreement is derived from the same
`hsrc0` package rather than carried as a sibling input. -/
def PerDatumWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source version of the hsrc0-only frontier with no separate Hu
input. -/
def PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs p D,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- The no-Hu hsrc0-only source frontier fills the existing hsrc0 source
frontier by reconstructing the u-side time-neighborhood spectral agreement. -/
theorem windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D := by
  obtain ⟨S, H, hpde_u⟩ := h
  exact ⟨S, H,
    ResolverSourceWindowInput.timeNeighborhoodSpectralAgreement_of_hsrc0Inputs
      hχ0 hα ha hb hu₀ H,
    hpde_u⟩

/-- Iterate version of the no-Hu hsrc0-only source frontier bridge. -/
theorem iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D := by
  obtain ⟨I, H, hpde_u⟩ := h
  exact ⟨I, H,
    ResolverSourceWindowInput.timeNeighborhoodSpectralAgreement_of_hsrc0Inputs
      hχ0 hα ha hb hu₀ H,
    hpde_u⟩

/-- Window hsrc0-only source data, with no separate Hu input, gives the unified
Picard-limit restart frontier in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
        hχ0 hα ha hb hu₀ (hSrc u₀ hu₀ D hD))

/-- Iterate hsrc0-only source data, with no separate Hu input, gives the unified
Picard-limit restart frontier in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
        hχ0 hα ha hb hu₀ (hIterSrc u₀ hu₀ D hD))

/-- Source frontier where the remaining hsrc0 package is produced from
iterate-side bootstrap inputs; neither hsrc0 nor Hu is carried explicitly. -/
def PerDatumWindowHsrc0BootstrapNoHuSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _B : ResolverSourceWindowInput.ResolverSourceWindowHsrc0BootstrapInputs p D,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate frontier where hsrc0 is produced from iterate-side bootstrap inputs;
neither hsrc0 nor Hu is carried explicitly. -/
def PerDatumIterateHsrc0BootstrapNoHuSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _B : ResolverSourceWindowInput.ResolverSourceWindowHsrc0BootstrapInputs p D,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Bootstrap source data fills the no-Hu hsrc0-only source frontier by producing
the hsrc0 package from iterate-side bounded-source inputs. -/
theorem windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_windowHsrc0BootstrapNoHuSourceSpectralFrontier
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHsrc0BootstrapNoHuSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D := by
  obtain ⟨S, B, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowHsrc0Inputs_of_bootstrapInputs
      hα ha hb hu₀ B,
    hpde_u⟩

/-- Iterate bootstrap source data fills the no-Hu hsrc0-only iterate frontier. -/
theorem iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_iterateHsrc0BootstrapNoHuSourceSpectralFrontier
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateHsrc0BootstrapNoHuSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D := by
  obtain ⟨I, B, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowHsrc0Inputs_of_bootstrapInputs
      hα ha hb hu₀ B,
    hpde_u⟩

/-- Window bootstrap source data gives the unified Picard-limit restart frontier
in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_windowHsrc0BootstrapNoHuSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHsrc0BootstrapNoHuSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_windowHsrc0BootstrapNoHuSourceSpectralFrontier
        hα ha hb hu₀ (hSrc u₀ hu₀ D hD))

/-- Iterate bootstrap source data gives the unified Picard-limit restart frontier
in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_iterateHsrc0BootstrapNoHuSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateHsrc0BootstrapNoHuSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_iterateHsrc0BootstrapNoHuSourceSpectralFrontier
        hα ha hb hu₀ (hIterSrc u₀ hu₀ D hD))

/-- Source frontier where the hsrc0 input is produced from the narrowed Hres
core and the per-iterate coefficient time-continuity provider. -/
def PerDatumWindowHsrc0CoreNoHuSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _C : HresWiring.PicardIterateResidualCore p u₀ D,
  ∃ _hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
    ContinuousOn
      (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      (Set.Icc a' τ),
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate frontier where the hsrc0 input is produced from the narrowed Hres
core and per-iterate coefficient time continuity. -/
def PerDatumIterateHsrc0CoreNoHuSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _C : HresWiring.PicardIterateResidualCore p u₀ D,
  ∃ _hiter_cont : ∀ (a' τ : ℝ), 0 < a' → a' ≤ τ → τ ≤ D.T → ∀ (n k : ℕ),
    ContinuousOn
      (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
      (Set.Icc a' τ),
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- The narrowed Hres core surface fills the hsrc0/no-Hu source frontier. -/
theorem windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_windowHsrc0CoreNoHuSourceSpectralFrontier
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (h : PerDatumWindowHsrc0CoreNoHuSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D := by
  obtain ⟨S, C, hiter_cont, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowHsrc0Inputs_of_hresCore
      hα ha hb hu₀ hDu C hiter_cont,
    hpde_u⟩

/-- Iterate version of the narrowed Hres core to hsrc0/no-Hu bridge. -/
theorem iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_iterateHsrc0CoreNoHuSourceSpectralFrontier
    {p : CM2Params}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (h : PerDatumIterateHsrc0CoreNoHuSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D := by
  obtain ⟨I, C, hiter_cont, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowHsrc0Inputs_of_hresCore
      hα ha hb hu₀ hDu C hiter_cont,
    hpde_u⟩

/-- Window Hres-core source data gives the unified Picard-limit restart frontier
in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_windowHsrc0CoreNoHuSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHsrc0CoreNoHuSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_windowHsrc0CoreNoHuSourceSpectralFrontier
        hα ha hb hu₀ hD (hSrc u₀ hu₀ D hD))

/-- Iterate Hres-core source data gives the unified Picard-limit restart
frontier in the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_iterateHsrc0CoreNoHuSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateHsrc0CoreNoHuSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    hχ0 hα ha hb
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_iterateHsrc0CoreNoHuSourceSpectralFrontier
        hα ha hb hu₀ hD (hIterSrc u₀ hu₀ D hD))

end ShenWork.Paper2.PPIDThresholdReachability

namespace ShenWork.Paper2.ConeQuantBridge

open ShenWork.Paper2.PPIDThresholdReachability

/-- The χ₀ = 0 headline route reduced to the explicit bounded patched-source
package `hsrc0` for resolver-source representation/envelope/K1 data. -/
theorem paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
        hχ hα_ge ha.le hb.le hu₀ (hSrc u₀ hu₀ D hD))

/-- Iterate version of the χ₀ = 0 hsrc0-only headline route. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
        hχ hα_ge ha.le hb.le hu₀ (hIterSrc u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route reduced to `hsrc0` without a separate Hu input;
Hu is reconstructed from the same hsrc0 package. -/
theorem paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
        hχ hα_ge ha.le hb.le hu₀ (hSrc u₀ hu₀ D hD))

/-- Iterate version of the χ₀ = 0 hsrc0-only headline route with no separate
Hu input. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
        hχ hα_ge ha.le hb.le hu₀ (hIterSrc u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route where hsrc0 is produced from iterate-side
bootstrap inputs and Hu is not carried separately. -/
theorem paper2_theorem_1_1_chiZero_of_windowHsrc0BootstrapNoHuSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHsrc0BootstrapNoHuSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_windowHsrc0BootstrapNoHuSourceSpectralFrontier
        hα_ge ha.le hb.le hu₀ (hSrc u₀ hu₀ D hD))

/-- Iterate version of the χ₀ = 0 bootstrap headline route with no separate Hu
input. -/
theorem paper2_theorem_1_1_chiZero_of_iterateHsrc0BootstrapNoHuSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateHsrc0BootstrapNoHuSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_iterateHsrc0BootstrapNoHuSourceSpectralFrontier
        hα_ge ha.le hb.le hu₀ (hIterSrc u₀ hu₀ D hD))

/-- The χ₀ = 0 headline route where hsrc0 is produced from the narrowed Hres
core and Hu is not carried separately. -/
theorem paper2_theorem_1_1_chiZero_of_windowHsrc0CoreNoHuSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHsrc0CoreNoHuSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_windowHsrc0CoreNoHuSourceSpectralFrontier
        hα_ge ha.le hb.le hu₀ hD (hSrc u₀ hu₀ D hD))

/-- Iterate version of the χ₀ = 0 Hres-core headline route with no separate Hu
input. -/
theorem paper2_theorem_1_1_chiZero_of_iterateHsrc0CoreNoHuSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSrc : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateHsrc0CoreNoHuSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier_of_iterateHsrc0CoreNoHuSourceSpectralFrontier
        hα_ge ha.le hb.le hu₀ hD (hIterSrc u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0NoHuInputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_windowHsrc0BootstrapNoHuSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateHsrc0BootstrapNoHuSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_windowHsrc0CoreNoHuSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateHsrc0CoreNoHuSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
