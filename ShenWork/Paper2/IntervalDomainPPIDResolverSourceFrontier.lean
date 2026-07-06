/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceFrontier.lean

  PPID restart-core frontier with the resolver-source witness replaced by the
  producer-facing window data of `IntervalResolverSourceWitnessFrontier`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDRestartCoreFrontier
import ShenWork.Paper2.IntervalResolverSourceWitnessFrontier

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- Producer-facing replacement for the raw resolver-source witness used in
`PerDatumSourceSpectralFrontier`. -/
def PerDatumResolverSourceWindowFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ResolverSourceWitnessFrontier.ResolverSourceWindowData p D

/-- Source-frontier surface with the resolver-source witness replaced by
windowed power-source representation/decay/K1 data. -/
def PerDatumWindowSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    PerDatumResolverSourceWindowFrontier p D ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source-frontier surface with the resolver-source witness replaced
by windowed power-source representation/decay/K1 data. -/
def PerDatumIterateWindowSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    PerDatumResolverSourceWindowFrontier p D ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Windowed source data implies the source-witness spectral frontier. -/
theorem sourceSpectralFrontier_of_windowSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumWindowSourceSpectralFrontier p D) :
    PerDatumSourceSpectralFrontier p D := by
  obtain ⟨S, hTimeNhd, hResolverWindow, hpde_u⟩ := h
  exact ⟨S, hTimeNhd,
    ResolverSourceWitnessFrontier.resolverSourceWitness_of_windowData hResolverWindow,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the windowed source surface. -/
theorem windowSourceSpectralFrontier_of_iterateWindowSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowSourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D := by
  obtain ⟨I, hTimeNhd, hResolverWindow, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hTimeNhd, hResolverWindow, hpde_u⟩

/-- Iterate/windowed source data implies the source-witness spectral frontier. -/
theorem sourceSpectralFrontier_of_iterateWindowSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateWindowSourceSpectralFrontier p D) :
    PerDatumSourceSpectralFrontier p D :=
  sourceSpectralFrontier_of_windowSourceSpectralFrontier
    (windowSourceSpectralFrontier_of_iterateWindowSourceSpectralFrontier h)

/-- Windowed-source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_windowSourceSpectralFrontier
    {p : CM2Params}
    (hWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_sourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      sourceSpectralFrontier_of_windowSourceSpectralFrontier
        (hWindow u₀ hu₀ D hD))

/-- Picard-iterate/windowed-source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateWindowSourceSpectralFrontier
    {p : CM2Params}
    (hIterWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_sourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      sourceSpectralFrontier_of_iterateWindowSourceSpectralFrontier
        (hIterWindow u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to the windowed source
frontier package. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_windowSourceSpectralFrontier hWindow)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumWindowSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hWindow

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus the windowed source fields. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_iterateWindowSourceSpectralFrontier hIterWindow)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_iterateWindowSourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateWindowSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterWindow : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateWindowSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateWindowSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterWindow

end ShenWork.Paper2.PPIDThresholdReachability
