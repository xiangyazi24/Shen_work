/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceInputsFrontier.lean

  PPID restart-core frontier from global/per-compact resolver-source window
  inputs.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowInputs

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID source frontier with the resolver-source window field replaced by
global/per-compact producer-side inputs. -/
def PerDatumWindowInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with the resolver-source window field replaced by
global/per-compact producer-side inputs. -/
def PerDatumIterateWindowInputsSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowInputs p D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Primitive window inputs supply the per-window resolver-source data field. -/
theorem windowSourceSpectralFrontier_of_windowInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D := by
  obtain ⟨S, hInputs, hTimeNhd, hpde_u⟩ := h
  exact ⟨S, hTimeNhd,
    ResolverSourceWindowInput.resolverSourceWindowData_of_inputs hInputs,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the primitive-input source surface. -/
theorem windowInputsSourceSpectralFrontier_of_iterateWindowInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowInputsSourceSpectralFrontier p D) :
    PerDatumWindowInputsSourceSpectralFrontier p D := by
  obtain ⟨I, hInputs, hTimeNhd, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hInputs, hTimeNhd, hpde_u⟩

/-- Iterate/primitive-input source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_iterateWindowInputsSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowInputsSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_windowInputsSourceSpectralFrontier
    (windowInputsSourceSpectralFrontier_of_iterateWindowInputsSourceSpectralFrontier h)

/-- Primitive-input source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowInputsSourceSpectralFrontier
    {p : CM2Params}
    (hInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_windowInputsSourceSpectralFrontier
        (hInputs u₀ hu₀ D hD))

/-- Iterate/primitive-input source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowInputsSourceSpectralFrontier
    {p : CM2Params}
    (hIterInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowInputsSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_iterateWindowInputsSourceSpectralFrontier
        (hIterInputs u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to the primitive-input
source frontier package. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_windowInputsSourceSpectralFrontier
        (hInputs u₀ hu₀ D hD))

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_windowInputsSourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hInputs

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus the primitive-input source fields. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowInputsSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_iterateWindowInputsSourceSpectralFrontier
        (hIterInputs u₀ hu₀ D hD))

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_iterateWindowInputsSourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowInputsSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterInputs : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowInputsSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowInputsSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterInputs

end ShenWork.Paper2.PPIDThresholdReachability
