/-
  ShenWork/Paper2/IntervalDomainPPIDRestartCoreFrontier.lean

  Minimal per-datum spectral data consumed by the Picard-limit restart frontier
  bridge in the PPID Theorem 1.1 route.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDPicardLimitFrontier
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalPicardLimitLogisticSource
import ShenWork.Paper2.IntervalResolverStrictPositivity

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity (HasResolverDirectSpectralData)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.Paper2
open Filter Topology

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- The per-datum spectral data actually consumed to produce the Picard-limit
restart package and classical frontier core.

Compared with `EndToEnd.PerDatumSpectralFrontier`, this package omits the
sup-norm derivative and initial-approach fields, because the PPID Picard-limit
frontier bridge does not use them.  It also omits resolver strict positivity,
which is produced internally from `GradientMildSolutionData`. -/
def PerDatumRestartCoreSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    HasResolverDirectSpectralData D.T
      (mildChemicalConcentration p D.u) p ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Source-witness version of the consumed spectral frontier: the resolver
direct spectral field is replaced by the per-time clamped source witness consumed
by `hasResolverDirectSpectralData_of_clamped_perT0`. -/
def PerDatumSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t₀, 0 < t₀ → t₀ < D.T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k,
          aC s k = (intervalNeumannResolverSourceCoeff p (D.u s) k).re)) ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Source-witness frontier with the logistic half-step source data replaced by
the existing Picard-iterate convergence package that produces it. -/
def PerDatumIterateSourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : ShenWork.IntervalPicardLimitLogisticSource.PicardIterateConvergenceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    (∀ t₀, 0 < t₀ → t₀ < D.T →
      ∃ (aC : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 aC) (W : Set ℝ),
        W ∈ 𝓝 t₀ ∧
        (∀ s ∈ W, ∀ k,
          aC s k = (intervalNeumannResolverSourceCoeff p (D.u s) k).re)) ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- The older per-datum spectral frontier implies the smaller restart/core
package by forgetting the two fields not used by this route. -/
def restartCoreSpectralFrontier_of_perDatumSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : EndToEnd.PerDatumSpectralFrontier p D) :
    PerDatumRestartCoreSpectralFrontier p D := by
  obtain ⟨S, hTimeNhd, hResolverData, _hSupNormDeriv,
    _hVpos, _hInitialApproach, hpde_u⟩ := h
  exact ⟨S, hTimeNhd, hResolverData, hpde_u⟩

/-- The source-witness frontier implies the core spectral frontier by the
existing per-time clamped resolver-source producer. -/
theorem restartCoreSpectralFrontier_of_sourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumSourceSpectralFrontier p D) :
    PerDatumRestartCoreSpectralFrontier p D := by
  obtain ⟨S, hTimeNhd, hResolverSrc, hpde_u⟩ := h
  exact ⟨S, hTimeNhd,
    ShenWork.Paper2.RegularityFrontierAssembly.hasResolverDirectSpectralData_of_clamped_perT0
      D.u hResolverSrc,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the source-witness frontier. -/
theorem sourceSpectralFrontier_of_iterateSourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateSourceSpectralFrontier p D) :
    PerDatumSourceSpectralFrontier p D := by
  obtain ⟨I, hTimeNhd, hResolverSrc, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hTimeNhd, hResolverSrc, hpde_u⟩

/-- The restart/core spectral package discharges the unified Picard-limit
restart frontier. -/
theorem picardLimitRestartFrontier_of_restartCoreSpectralFrontier
    {p : CM2Params}
    (hCore : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumRestartCoreSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p := by
  intro u₀ hu₀ D hD
  obtain ⟨S, hTimeNhd, hResolverData, hpde_u⟩ := hCore u₀ hu₀ D hD
  refine ⟨gradientMildHalfStepRestartData_of_logisticSourceData D S, ?_⟩
  exact
    EndToEnd.gradientMildClassicalFrontierCoreData_of_perDatum
      p D S hTimeNhd hResolverData
      (ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos p D)
      hpde_u

/-- Source-witness version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_sourceSpectralFrontier
    {p : CM2Params}
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_restartCoreSpectralFrontier
    (fun u₀ hu₀ D hD =>
      restartCoreSpectralFrontier_of_sourceSpectralFrontier
        (hSource u₀ hu₀ D hD))

/-- Picard-iterate/source-witness version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateSourceSpectralFrontier
    {p : CM2Params}
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_sourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      sourceSpectralFrontier_of_iterateSourceSpectralFrontier
        (hIterSource u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to the smaller restart/core
spectral frontier package. -/
theorem theorem_1_1_intervalDomain_of_ppid_restartCoreSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hCore : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumRestartCoreSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_restartCoreSpectralFrontier hCore)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_restartCoreSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_restartCoreSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hCore : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumRestartCoreSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_restartCoreSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hCore

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to the source-witness spectral
frontier package. -/
theorem theorem_1_1_intervalDomain_of_ppid_sourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_sourceSpectralFrontier hSource)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_sourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_sourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_sourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hSource

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus the source-witness spectral fields. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateSourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_iterateSourceSpectralFrontier hIterSource)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_iterateSourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateSourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSource : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateSourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterSource

#print axioms picardLimitRestartFrontier_of_restartCoreSpectralFrontier
#print axioms picardLimitRestartFrontier_of_sourceSpectralFrontier
#print axioms picardLimitRestartFrontier_of_iterateSourceSpectralFrontier
#print axioms theorem_1_1_intervalDomain_of_ppid_restartCoreSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_restartCoreSpectralFrontier_chiNeg
#print axioms theorem_1_1_intervalDomain_of_ppid_sourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_sourceSpectralFrontier_chiNeg
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateSourceSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_iterateSourceSpectralFrontier_chiNeg

end ShenWork.Paper2.PPIDThresholdReachability
