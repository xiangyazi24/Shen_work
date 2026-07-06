/-
  ShenWork/Paper2/IntervalDomainRestartSpectralFrontier.lean

  Smaller spectral frontier surface for the Picard-limit restart route.

  Task244 routes the PPID headline through `PerDatumSpectralFrontier`, but the
  restart/core bridge only consumes the logistic source data, time-neighborhood
  spectral agreement, resolver direct spectral data, and the pointwise `u` PDE
  identity.  Strict resolver positivity is already proved for every
  `GradientMildSolutionData`, so this file fills it internally without changing
  the older end-to-end frontier.
-/
import ShenWork.Paper2.IntervalDomainPPIDPicardLimitFrontier
import ShenWork.Paper2.IntervalResolverStrictPositivity

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalMildToLocalExistence
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.EndToEnd

/-- The per-datum spectral data actually consumed by the Picard-limit restart
frontier.  Compared with `PerDatumSpectralFrontier`, this deletes
`IntervalDomainSupNormDerivativeNonposOn`, strict resolver positivity, and the
initial-approach field; the first and third are unused by the restart/core
bridge, and strict resolver positivity is filled internally. -/
def PerDatumRestartSpectralFrontier
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

/-- The smaller restart-spectral frontier directly gives the restart package and
classical frontier core required by `PicardLimitRestartFrontier`. -/
theorem restartAndFrontierCore_of_restartSpectral
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (h : PerDatumRestartSpectralFrontier p D) :
    ∃ _R : GradientMildHalfStepRestartData D,
      GradientMildClassicalFrontierCoreData p D := by
  obtain ⟨S, hTimeNhd, hResolverData, hpde_u⟩ := h
  refine ⟨gradientMildHalfStepRestartData_of_logisticSourceData D S, ?_⟩
  exact
    gradientMildClassicalFrontierCoreData_of_perDatum
      p D S hTimeNhd hResolverData
      (ShenWork.IntervalResolverStrictPositivity.mildChemicalConcentration_pos
        p D)
      hpde_u

end ShenWork.Paper2.EndToEnd

namespace ShenWork.Paper2.ConeQuantBridge

/-- A per-datum restart-spectral producer discharges the unified
`PicardLimitRestartFrontier` residual. -/
theorem picardLimitRestartFrontier_of_restartSpectralFrontier
    {p : CM2Params}
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumRestartSpectralFrontier p D) :
    PicardLimitRestartFrontier p := by
  intro u₀ hu₀ D hD
  exact EndToEnd.restartAndFrontierCore_of_restartSpectral
    p D (hPerDatum u₀ hu₀ D hD)

/-- The χ₀ = 0 headline route with the residual reduced to the smaller
restart-spectral producer surface. -/
theorem paper2_theorem_1_1_chiZero_of_restartSpectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumRestartSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_restartSpectralFrontier hPerDatum)

end ShenWork.Paper2.ConeQuantBridge

namespace ShenWork.Paper2.PPIDThresholdReachability

/-- PPID χ₀ ≤ 0 headline wrapper from the smaller restart-spectral producer
surface. -/
theorem theorem_1_1_intervalDomain_of_ppid_restartSpectralFrontier_chiNonpos
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumRestartSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_picardLimitFrontier_chiNonpos
    p hχ ha hb hα_ge hγ_ge_one
    (ConeQuantBridge.picardLimitRestartFrontier_of_restartSpectralFrontier
      hPerDatum)

/-- Strict-negative specialization of
`theorem_1_1_intervalDomain_of_ppid_restartSpectralFrontier_chiNonpos`. -/
theorem theorem_1_1_intervalDomain_of_ppid_restartSpectralFrontier_chiNeg
    (p : CM2Params) (hχ : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumRestartSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  theorem_1_1_intervalDomain_of_ppid_restartSpectralFrontier_chiNonpos
    p (le_of_lt hχ) ha hb hα_ge hγ_ge_one hPerDatum

#print axioms EndToEnd.restartAndFrontierCore_of_restartSpectral
#print axioms ConeQuantBridge.picardLimitRestartFrontier_of_restartSpectralFrontier
#print axioms ConeQuantBridge.paper2_theorem_1_1_chiZero_of_restartSpectralFrontier
#print axioms theorem_1_1_intervalDomain_of_ppid_restartSpectralFrontier_chiNonpos
#print axioms theorem_1_1_intervalDomain_of_ppid_restartSpectralFrontier_chiNeg

end ShenWork.Paper2.PPIDThresholdReachability
