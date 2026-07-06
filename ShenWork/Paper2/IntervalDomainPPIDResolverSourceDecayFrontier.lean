/-
  ShenWork/Paper2/IntervalDomainPPIDResolverSourceDecayFrontier.lean

  PPID restart-core frontier with resolver-source window decay produced from
  spatial K2 bounds.  The power-source K1 time-derivative data remains an
  explicit residual.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainPPIDResolverSourceFrontier
import ShenWork.Paper2.IntervalResolverSourceWindowDecayFrontier

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalPicardLimitLogisticSource
open ShenWork.IntervalMildToClassical
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID source frontier with resolver-source decay lowered to spatial K2
window data. -/
def PerDatumSpatialK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _S : GradientMildHalfStepLogisticSourceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    ResolverSourceWitnessFrontier.ResolverSourceWindowSpatialK1Data p D ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Iterate/source frontier with resolver-source decay lowered to spatial K2
window data. -/
def PerDatumIterateSpatialK1SourceSpectralFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀) : Prop :=
  ∃ _I : PicardIterateConvergenceData D,
    HasTimeNeighborhoodSpectralAgreement D.T D.u ∧
    ResolverSourceWitnessFrontier.ResolverSourceWindowSpatialK1Data p D ∧
    (∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv D.u t x =
        intervalDomain.laplacian (D.u t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p (D.u t)
              (mildChemicalConcentration p D.u t) x
          + D.u t x * (p.a - p.b * (D.u t x) ^ p.α))

/-- Spatial K2 window data supplies the resolver-source window data field. -/
theorem windowSourceSpectralFrontier_of_spatialK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumSpatialK1SourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D := by
  obtain ⟨S, hTimeNhd, hSpatialK1, hpde_u⟩ := h
  exact ⟨S, hTimeNhd,
    ResolverSourceWitnessFrontier.windowData_of_spatialK1Data hSpatialK1,
    hpde_u⟩

/-- Picard-iterate convergence data supplies the logistic source-data field of
the spatial-K1 source surface. -/
theorem spatialK1SourceSpectralFrontier_of_iterateSpatialK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateSpatialK1SourceSpectralFrontier p D) :
    PerDatumSpatialK1SourceSpectralFrontier p D := by
  obtain ⟨I, hTimeNhd, hSpatialK1, hpde_u⟩ := h
  exact ⟨
    gradientMildHalfStepLogisticSourceData_of_iterateConvergence D I,
    hTimeNhd, hSpatialK1, hpde_u⟩

/-- Iterate/spatial-K1 source data implies the windowed source frontier. -/
theorem windowSourceSpectralFrontier_of_iterateSpatialK1SourceSpectralFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (h : PerDatumIterateSpatialK1SourceSpectralFrontier p D) :
    PerDatumWindowSourceSpectralFrontier p D :=
  windowSourceSpectralFrontier_of_spatialK1SourceSpectralFrontier
    (spatialK1SourceSpectralFrontier_of_iterateSpatialK1SourceSpectralFrontier h)

/-- Spatial-K1 source version of the unified Picard-limit frontier bridge. -/
theorem picardLimitRestartFrontier_of_spatialK1SourceSpectralFrontier
    {p : CM2Params}
    (hSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSpatialK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_spatialK1SourceSpectralFrontier
        (hSpatialK1 u₀ hu₀ D hD))

/-- Iterate/spatial-K1 source version of the unified Picard-limit frontier
bridge. -/
theorem picardLimitRestartFrontier_of_iterateSpatialK1SourceSpectralFrontier
    {p : CM2Params}
    (hIterSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSpatialK1SourceSpectralFrontier p D) :
    ConeQuantBridge.PicardLimitRestartFrontier p :=
  picardLimitRestartFrontier_of_windowSourceSpectralFrontier
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_iterateSpatialK1SourceSpectralFrontier
        (hIterSpatialK1 u₀ hu₀ D hD))

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to the spatial-K1 source
frontier package. -/
theorem theorem_1_1_intervalDomain_of_ppid_spatialK1SourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSpatialK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_spatialK1SourceSpectralFrontier
        (hSpatialK1 u₀ hu₀ D hD))

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_spatialK1SourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_spatialK1SourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumSpatialK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_spatialK1SourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hSpatialK1

/-- PPID-typed Theorem 1.1 for `χ₀ ≤ 0`, reduced to Picard-iterate convergence
plus the spatial-K1 source fields. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateSpatialK1SourceSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSpatialK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_windowSourceSpectralFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (fun u₀ hu₀ D hD =>
      windowSourceSpectralFrontier_of_iterateSpatialK1SourceSpectralFrontier
        (hIterSpatialK1 u₀ hu₀ D hD))

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_iterateSpatialK1SourceSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_iterateSpatialK1SourceSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hIterSpatialK1 : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          PerDatumIterateSpatialK1SourceSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_iterateSpatialK1SourceSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hIterSpatialK1

end ShenWork.Paper2.PPIDThresholdReachability
