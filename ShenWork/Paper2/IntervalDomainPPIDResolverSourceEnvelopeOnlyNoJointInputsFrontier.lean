/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceEnvelopeOnlyNoJointInputsFrontier.lean

  PPID restart-core frontier from resolver-source envelope inputs with both
  redundant fields removed: hbsum and lifted joint continuity.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceEnvelopeOnlyInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowEnvelopeOnlyNoJointInputs

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

/-- PPID source frontier with resolver-source envelope inputs carrying neither
per-time eigenvalue summability nor lifted joint continuity as separate fields. -/
def PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with the envelope/no-joint resolver-source input
package. -/
def PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowEnvelopeOnlyNoJointInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Envelope/no-joint source data fills the no-`hbsum` envelope-input source
frontier. -/
theorem windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyInputsSourceSpectralFrontier p D := by
  obtain ⟨S, hThin, hTimeNhd, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs
      hTimeNhd hThin,
    hTimeNhd, hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the envelope/no-joint source surface. -/
theorem windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hThin, hTimeNhd, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hThin, hTimeNhd, hpde_u⟩

/-- Iterate envelope/no-joint source data fills the no-`hbsum` iterate envelope
frontier. -/
theorem iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hThin, hTimeNhd, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyInputs_of_envelopeOnlyNoJointInputs
      hTimeNhd hThin,
    hTimeNhd, hpde_u⟩

/-- Envelope/no-joint source data fills the Task264 envelope-input source
frontier. -/
theorem windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeInputsSourceSpectralFrontier p D :=
  windowEnvelopeInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    (windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier h)

/-- Iterate envelope/no-joint source data fills the Task264 iterate envelope
frontier. -/
theorem iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeInputsSourceSpectralFrontier p D :=
  iterateWindowEnvelopeInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier h)

/-- Envelope/no-joint source data fills the Task259 joint-input source frontier. -/
theorem windowJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowJointInputsSourceSpectralFrontier p D :=
  windowJointInputsSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    (windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier h)

/-- Iterate envelope/no-joint source data fills the Task259 iterate joint
frontier. -/
theorem iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumIterateWindowJointInputsSourceSpectralFrontier p D :=
  iterateWindowJointInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier h)

/-- Envelope/no-joint source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    (windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier h)

/-- Iterate envelope/no-joint source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier h)

/-- Envelope/no-joint source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params}
    (hThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
        (hThin u₀ hu₀ D hD))

/-- Iterate envelope/no-joint source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    {p : CM2Params}
    (hIterThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
        (hIterThin u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to envelope/no-joint
resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyInputsSourceSpectralFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
        (hThin u₀ hu₀ D hD))

/-- Strict-negative specialization of the envelope/no-joint PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hThin

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus envelope/no-joint resolver-source primitive inputs. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyInputsSourceSpectralFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
        (hIterThin u₀ hu₀ D hD))

/-- Strict-negative iterate/envelope/no-joint specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterThin : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterThin

end ShenWork.Paper2.PPIDThresholdReachability
