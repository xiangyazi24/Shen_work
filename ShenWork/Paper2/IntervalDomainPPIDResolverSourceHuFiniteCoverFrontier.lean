/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceHuFiniteCoverFrontier.lean

  PPID restart-core frontier from explicit finite restart-chart covers for the
  Hu-selected resolver-source coefficients.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceHuCoeffFrontier
import ShenWork.Paper2.IntervalHuRestartCoeffFiniteCover

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

/-- PPID source frontier where the Hu coefficient envelope is supplied by
explicit finite restart-chart covers.  The power-source K1 fields remain
explicit inputs. -/
def PerDatumWindowHuFiniteCoverSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuFiniteCoverInputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with finite-cover Hu coefficient envelopes. -/
def PerDatumIterateWindowHuFiniteCoverSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
  ∃ Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u,
  ∃ _H : ResolverSourceWindowInput.ResolverSourceWindowHuFiniteCoverInputs p D Hu,
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Finite-cover Hu source data fills the HuCoeff source frontier. -/
theorem windowHuCoeffSourceSpectralFrontier_of_windowHuFiniteCoverSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowHuFiniteCoverSourceSpectralFrontier p D) :
    PerDatumWindowHuCoeffSourceSpectralFrontier p D := by
  obtain ⟨S, Hu, H, hpde_u⟩ := h
  exact ⟨S, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffInputs_of_finiteCoverInputs H,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the finite-cover Hu source surface. -/
theorem windowHuFiniteCoverSourceSpectralFrontier_of_iterateWindowHuFiniteCoverSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuFiniteCoverSourceSpectralFrontier p D) :
    PerDatumWindowHuFiniteCoverSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    Hu, H, hpde_u⟩

/-- Iterate finite-cover Hu source data fills the iterate HuCoeff source
frontier. -/
theorem iterateWindowHuCoeffSourceSpectralFrontier_of_iterateWindowHuFiniteCoverSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowHuFiniteCoverSourceSpectralFrontier p D) :
    PerDatumIterateWindowHuCoeffSourceSpectralFrontier p D := by
  obtain ⟨I, Hu, H, hpde_u⟩ := h
  exact ⟨I, Hu,
    ResolverSourceWindowInput.resolverSourceWindowHuCoeffInputs_of_finiteCoverInputs H,
    hpde_u⟩

/-- Finite-cover Hu source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowHuFiniteCoverSourceSpectralFrontier
    {p : CM2Params}
    (hFiniteCover : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuFiniteCoverSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowHuCoeffSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowHuCoeffSourceSpectralFrontier_of_windowHuFiniteCoverSourceSpectralFrontier
        (hFiniteCover u₀ hu₀ D hD))

/-- Iterate finite-cover Hu source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowHuFiniteCoverSourceSpectralFrontier
    {p : CM2Params}
    (hIterFiniteCover : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuFiniteCoverSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_iterateWindowHuCoeffSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffSourceSpectralFrontier_of_iterateWindowHuFiniteCoverSourceSpectralFrontier
        (hIterFiniteCover u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to explicit finite covers for
Hu-selected resolver-source coefficients plus the remaining K1 fields. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowHuFiniteCoverSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hFiniteCover : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuFiniteCoverSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowHuCoeffSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowHuCoeffSourceSpectralFrontier_of_windowHuFiniteCoverSourceSpectralFrontier
        (hFiniteCover u₀ hu₀ D hD))

/-- Strict-negative specialization of the finite-cover Hu PPID source wrapper. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowHuFiniteCoverSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hFiniteCover : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowHuFiniteCoverSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowHuFiniteCoverSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hFiniteCover

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus finite-cover Hu source data. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowHuFiniteCoverSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterFiniteCover : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuFiniteCoverSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowHuCoeffSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      iterateWindowHuCoeffSourceSpectralFrontier_of_iterateWindowHuFiniteCoverSourceSpectralFrontier
        (hIterFiniteCover u₀ hu₀ D hD))

/-- Strict-negative iterate/finite-cover specialization. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowHuFiniteCoverSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterFiniteCover : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowHuFiniteCoverSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowHuFiniteCoverSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterFiniteCover

#print axioms theorem_1_1_intervalDomain_of_ppid_windowHuFiniteCoverSourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateWindowHuFiniteCoverSourceSpectralFrontier_chiNonpos

end ShenWork.Paper2.PPIDThresholdReachability
