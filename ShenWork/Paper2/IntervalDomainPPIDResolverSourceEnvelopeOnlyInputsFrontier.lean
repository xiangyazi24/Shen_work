/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceEnvelopeOnlyInputsFrontier.lean

  PPID restart-core frontier from resolver-source envelope inputs where the
  per-time eigenvalue summability field is derived from singleton envelopes.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceEnvelopeInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyInputs

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

/-- PPID source frontier where resolver-source spatial K2 is supplied by compact
coefficient envelopes, and per-time eigenvalue summability is derived from those
envelopes. -/
def PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with no-`hbsum` envelope resolver-source inputs. -/
def PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- No-`hbsum` envelope source data fills the Task264 envelope-input source
frontier. -/
theorem windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hEnvelopeOnly, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs
      hEnvelopeOnly,
    hTimeNhd, hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the no-`hbsum` envelope-input source surface. -/
theorem windowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hEnvelopeOnly, hTimeNhd, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hEnvelopeOnly, hTimeNhd, hpde_u⟩

/-- No-`hbsum` iterate/envelope source data fills the Task264 iterate envelope
frontier. -/
theorem iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hEnvelopeOnly, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeInputs_of_envelopeOnlyInputs
      hEnvelopeOnly,
    hTimeNhd, hpde_u⟩

/-- No-`hbsum` envelope source data fills the Task259 joint-input source
frontier. -/
theorem windowJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumWindowJointInputsSourceSpectralFrontier p D :=
  windowJointInputsSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    (windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier h)

/-- No-`hbsum` iterate/envelope source data fills the Task259 iterate joint
frontier. -/
theorem iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowJointInputsSourceSpectralFrontier p D :=
  iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    (iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier h)

/-- No-`hbsum` envelope-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    (windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier h)

/-- No-`hbsum` iterate/envelope-input source data implies the windowed source
frontier. -/
theorem windowSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    (iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier h)

/-- No-`hbsum` envelope-input source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params}
    (hEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
        (hEnvelopeOnly u₀ hu₀ D hD))

/-- Iterate/no-`hbsum` envelope-input source version of the unified Picard-limit
frontier bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    {p : CM2Params}
    (hIterEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
        (hIterEnvelopeOnly u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to no-`hbsum` envelope
resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowEnvelopeInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
        (hEnvelopeOnly u₀ hu₀ D hD))

/-- Strict-negative specialization of the no-`hbsum` envelope-input PPID source
wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hEnvelopeOnly

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus no-`hbsum` envelope resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
        (hIterEnvelopeOnly u₀ hu₀ D hD))

/-- Strict-negative iterate/no-`hbsum` envelope-input specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterEnvelopeOnly : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterEnvelopeOnly

end ShenWork.Paper2.PPIDThresholdReachability
