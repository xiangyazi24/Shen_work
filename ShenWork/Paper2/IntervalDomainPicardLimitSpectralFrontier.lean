import ShenWork.Paper2.IntervalDomainConeQuantBridge
import ShenWork.Paper2.IntervalDomainEndToEnd

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.ConeQuantBridge

/-- A Picard-limit per-datum spectral frontier discharges the unified
`PicardLimitRestartFrontier` residual.

The spectral frontier already contains the logistic half-step source data, which
produces the restart package, and its remaining spectral fields assemble the
classical frontier core. -/
theorem picardLimitRestartFrontier_of_spectralFrontier
    {p : CM2Params}
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumSpectralFrontier p D) :
    PicardLimitRestartFrontier p := by
  intro u₀ hu₀ D hD
  obtain ⟨S, hTimeNhd, hResolverData, _hSupNormDeriv,
    hVpos, _hInitialApproach, hpde_u⟩ := hPerDatum u₀ hu₀ D hD
  refine ⟨gradientMildHalfStepRestartData_of_logisticSourceData D S, ?_⟩
  exact
    EndToEnd.gradientMildClassicalFrontierCoreData_of_perDatum
      p D S hTimeNhd hResolverData hVpos hpde_u

/-- The χ₀ = 0 headline route with the mixed restart/core frontier replaced by
the per-datum spectral frontier used elsewhere in the end-to-end assembly. -/
theorem paper2_theorem_1_1_chiZero_of_spectralFrontier
    (p : CM2Params) (hχ : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPerDatum : ∀ (u₀ : intervalDomainPoint → ℝ),
      PositiveInitialDatum intervalDomain u₀ →
      ∀ (D : GradientMildSolutionData p u₀),
        D.u = picardLimit p u₀ D.T →
          EndToEnd.PerDatumSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_chiZero_of_frontier p hχ ha hb hα_ge hγ_ge_one
    (picardLimitRestartFrontier_of_spectralFrontier hPerDatum)

end ShenWork.Paper2.ConeQuantBridge
