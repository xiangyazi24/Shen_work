/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceHuNoEnvelopeFrontier.lean

  PPID restart-core frontier after producing the compact Hu coefficient envelope
  directly from the carried time-neighborhood spectral agreement.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceHuCoeffFrontier
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

/-- PPID source frontier after deleting the explicit compact Hu-envelope field.
The remaining resolver-source producer data are the power-source K1 fields. -/
def PerDatumWindowHuNoEnvelopeSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuNoEnvelopeInputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source version of the no-envelope Hu frontier. -/
def PerDatumIterateWindowHuNoEnvelopeSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuNoEnvelopeInputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- No-envelope Hu source data fills the existing HuCoeff source frontier. -/
theorem windowHuCoeffSourceSpectralFrontier_of_windowHuNoEnvelopeSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    PerDatumWindowHuCoeffSourceSpectralFrontier p D := by
  obtain ⟨S, Hu, H, hpde_u⟩ := h
  exact ⟨S, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffInputs_of_noEnvelopeInputs H,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field. -/
theorem windowHuNoEnvelopeSourceSpectralFrontier_of_iterateWindowHuNoEnvelopeSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    PerDatumWindowHuNoEnvelopeSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    Hu, H, hpde_u⟩

/-- Iterate no-envelope Hu source data fills the iterate HuCoeff frontier. -/
theorem iterateWindowHuCoeffSourceSpectralFrontier_of_iterateWindowHuNoEnvelopeSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨I, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffInputs_of_noEnvelopeInputs H,
    hpde_u⟩

/-- No-envelope Hu source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowHuNoEnvelopeSourceSpectralFrontier
    {p : CM2Params}
    (hNoEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowHuCoeffSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowHuCoeffSourceSpectralFrontier_of_windowHuNoEnvelopeSourceSpectralFrontier
        (hNoEnvelope u₀ hu₀ D hD))

/-- Iterate no-envelope Hu source version of the Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowHuNoEnvelopeSourceSpectralFrontier
    {p : CM2Params}
    (hIterNoEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffSourceSpectralFrontier_of_iterateWindowHuNoEnvelopeSourceSpectralFrontier
        (hIterNoEnvelope u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Hu-selected coefficients
and power-source K1 fields.  The compact Hu envelope is no longer an input. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowHuNoEnvelopeSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowHuCoeffSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowHuCoeffSourceSpectralFrontier_of_windowHuNoEnvelopeSourceSpectralFrontier
        (hNoEnvelope u₀ hu₀ D hD))

/-- Strict-negative specialization of the no-envelope Hu PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowHuNoEnvelopeSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hNoEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowHuNoEnvelopeSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hNoEnvelope

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, iterate no-envelope version. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowHuNoEnvelopeSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowHuCoeffSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffSourceSpectralFrontier_of_iterateWindowHuNoEnvelopeSourceSpectralFrontier
        (hIterNoEnvelope u₀ hu₀ D hD))

/-- Strict-negative iterate/no-envelope specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowHuNoEnvelopeSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterNoEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuNoEnvelopeSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowHuNoEnvelopeSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterNoEnvelope

#print axioms theorem_1_1_intervalDomain_of_ppid_windowHuNoEnvelopeSourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateWindowHuNoEnvelopeSourceSpectralFrontier_chiNonpos

end ShenWork.Paper2.PPIDThresholdReachability
