/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceEnvelopeInputsFrontier.lean

  PPID restart-core frontier from resolver-source primitive inputs whose spatial
  K2 fields are discharged from a per-compact eigenvalue envelope.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceJointInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeInputs

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

/-- PPID source frontier where resolver-source spatial K2 is replaced by a
compact-window coefficient envelope. -/
def PerDatumWindowEnvelopeInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with the envelope resolver-source input package. -/
def PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Envelope source data fills the Task259 joint-input source frontier. -/
theorem windowJointInputsSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D) :
    PerDatumWindowJointInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hEnvelope, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowJointInputs_of_envelopeInputs hEnvelope,
    hTimeNhd, hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the envelope-input source surface. -/
theorem windowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hEnvelope, hTimeNhd, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hEnvelope, hTimeNhd, hpde_u⟩

/-- Fill the Task259 joint-input surface while preserving the iterate/source
surface. -/
theorem iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hEnvelope, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowJointInputs_of_envelopeInputs hEnvelope,
    hTimeNhd, hpde_u⟩

/-- Envelope-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowJointInputsSourceSpectralFrontier
    (windowJointInputsSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier h)

/-- Iterate/envelope-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    (windowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier h)

/-- Envelope-input source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params}
    (hEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowJointInputsSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
        (hEnvelope u₀ hu₀ D hD))

/-- Iterate/envelope-input source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    {p : CM2Params}
    (hIterEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
        (hIterEnvelope u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to envelope resolver-source
primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowEnvelopeInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowJointInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowJointInputsSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
        (hEnvelope u₀ hu₀ D hD))

/-- Strict-negative specialization of the envelope-input PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowEnvelopeInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowEnvelopeInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hEnvelope

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus envelope resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowJointInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
        (hIterEnvelope u₀ hu₀ D hD))

/-- Strict-negative iterate/envelope-input specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterEnvelope : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterEnvelope

end ShenWork.Paper2.PPIDThresholdReachability
