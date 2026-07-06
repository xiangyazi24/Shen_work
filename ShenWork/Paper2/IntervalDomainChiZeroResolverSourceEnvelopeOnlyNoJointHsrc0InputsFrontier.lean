/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointHsrc0InputsFrontier.lean

  χ₀ = 0 headline wrappers from resolver-source inputs where the coefficient
  representation, compact envelope, lifted joint continuity, and power-source K1
  fields are all derived; the bounded patched-source package remains explicit.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointHsrc0Inputs

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

#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointHsrc0InputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
