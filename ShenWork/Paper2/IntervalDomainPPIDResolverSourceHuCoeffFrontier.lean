/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceHuCoeffFrontier.lean

  PPID restart-core frontier from resolver-source inputs whose representation
  coefficients are selected from `HasTimeNeighborhoodSpectralAgreement`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceEnvelopeOnlyNoJointInputsFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowHuCoeffInputs

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

/-- PPID source frontier where the resolver-source representation coefficients
are chosen from the carried u-side spectral agreement.  The compact eigen-envelope
and power-source K1 fields remain explicit inputs. -/
def PerDatumWindowHuCoeffSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuCoeffInputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with Hu-selected resolver-source coefficients. -/
def PerDatumIterateWindowHuCoeffSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuCoeffInputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Hu-coefficient source data fills the Task268 envelope/no-joint source
frontier. -/
theorem windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowHuCoeffSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHuCoeffSourceSpectralFrontier p D) :
    PerDatumWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨S, Hu, H, hpde_u⟩ := h
  exact ⟨S,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointInputs_of_huCoeffInputs H,
    Hu, hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the Hu-coefficient source surface. -/
theorem windowHuCoeffSourceSpectralFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D) :
    PerDatumWindowHuCoeffSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    Hu, H, hpde_u⟩

/-- Iterate Hu-coefficient source data fills the Task268 iterate
envelope/no-joint source frontier. -/
theorem iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D) :
    PerDatumIterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨I,
    ResolverSourceWindowInput.resolverSourceWindowEnvelopeOnlyNoJointInputs_of_huCoeffInputs H,
    Hu, hpde_u⟩

/-- Hu-coefficient source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowHuCoeffSourceSpectralFrontier
    {p : CM2Params}
    (hHuCoeff : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuCoeffSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowHuCoeffSourceSpectralFrontier
        (hHuCoeff u₀ hu₀ D hD))

/-- Iterate Hu-coefficient source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
    {p : CM2Params}
    (hIterHuCoeff : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
        (hIterHuCoeff u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Hu-selected
resolver-source coefficients plus the remaining envelope/K1 fields. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowHuCoeffSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hHuCoeff : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuCoeffSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_windowHuCoeffSourceSpectralFrontier
        (hHuCoeff u₀ hu₀ D hD))

/-- Strict-negative specialization of the Hu-coefficient PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowHuCoeffSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hHuCoeff : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuCoeffSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowHuCoeffSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hHuCoeff

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus Hu-selected resolver-source coefficients. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowHuCoeffSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterHuCoeff : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowEnvelopeOnlyNoJointInputsSourceSpectralFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
        (hIterHuCoeff u₀ hu₀ D hD))

/-- Strict-negative iterate/Hu-coefficient specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowHuCoeffSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterHuCoeff : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowHuCoeffSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterHuCoeff

#print axioms theorem_1_1_intervalDomain_of_ppid_windowHuCoeffSourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateWindowHuCoeffSourceSpectralFrontier_chiNonpos

end ShenWork.Paper2.PPIDThresholdReachability
