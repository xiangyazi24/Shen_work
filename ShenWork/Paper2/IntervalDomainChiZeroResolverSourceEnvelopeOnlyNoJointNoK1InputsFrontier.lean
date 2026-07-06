/-
  ShenWork/Paper2/IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointNoK1InputsFrontier.lean

  χ₀ = 0 headline wrappers from resolver-source envelope inputs carrying neither
  hbsum, lifted joint continuity, nor explicit power-source K1 fields.  The
  remaining source package `hsrc0` is kept explicit in the no-K1 input structure.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainChiZeroResolverSourceEnvelopeOnlyNoJointInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs

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

/-- χ₀ = 0 source frontier with resolver-source envelope/no-joint inputs where
the power-source K1 fields are derived from the explicit bounded patched-source
package carried by `H.hsrc0`. -/
def PerDatumWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with resolver-source envelope/no-joint/no-K1 inputs. -/
def PerDatumIterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointNoK1Inputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- No-K1 source data fills the existing envelope/no-joint source frontier in
the χ₀ = 0 branch by deriving the power-source K1 fields. -/
theorem windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hNoK1, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointInputs_of_envelopeOnlyNoJointNoK1Inputs
      hχ0 hα ha hb hu₀ hNoK1,
    hTimeNhd, hpde_u⟩

/-- Iterate/no-K1 source data fills the existing iterate envelope/no-joint
source frontier in the χ₀ = 0 branch. -/
theorem iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hNoK1, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointInputs_of_envelopeOnlyNoJointNoK1Inputs
      hχ0 hα ha hb hu₀ hNoK1,
    hTimeNhd, hpde_u⟩

/-- Window no-K1 source data gives the unified Picard-limit restart frontier in
the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
        hχ0 hα ha hb hu₀ (hNoK1 u₀ hu₀ D hD))

/-- Iterate no-K1 source data gives the unified Picard-limit restart frontier in
the χ₀ = 0 branch. -/
theorem picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hIterNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
        hχ0 hα ha hb hu₀ (hIterNoK1 u₀ hu₀ D hD))

end ShenWork.Paper2.PPIDThresholdReachability

namespace ShenWork.Paper2.ConeQuantBridge

open ShenWork.Paper2.PPIDThresholdReachability

/-- The χ₀ = 0 headline route with resolver-source compact coefficient
envelopes and no explicit power-source K1 fields.  The explicit residual source
package is `H.hsrc0` inside the no-K1 input structure. -/
theorem paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
        hχ hα_ge ha.le hb.le hu₀ (hNoK1 u₀ hu₀ D hD))

/-- Iterate version of the χ₀ = 0 headline route with no explicit power-source
K1 fields in the resolver-source input package. -/
theorem paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
        hχ hα_ge ha.le hb.le hu₀ (hIterNoK1 u₀ hu₀ D hD))

#print axioms paper2_theorem_1_1_chiZero_of_windowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier
#print axioms paper2_theorem_1_1_chiZero_of_iterateWindowEnvelopeOnlyNoJointNoK1InputsSourceSpectralFrontier

end ShenWork.Paper2.ConeQuantBridge
