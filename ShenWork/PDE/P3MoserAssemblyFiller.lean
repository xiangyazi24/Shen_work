import ShenWork.PDE.P3MoserIntegratedDissipationPDE
import ShenWork.PDE.P3MoserIntegratedDissipationPDEv2
import ShenWork.PDE.P3MoserQuantitativeEndpointDischarge
import ShenWork.PDE.P3MoserGradientIntegrabilityFromDissipation
import ShenWork.PDE.P3MoserRelativeMassGradientProducer
import ShenWork.PDE.P3MoserClosedEnergyProducer
import ShenWork.PDE.P3MoserFTCInfrastructure
import ShenWork.Paper3.IntervalDomainIntegratedMoserAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.IntervalDomainExistence.P3MoserAssemblyFiller

noncomputable section

/-- Assemble the integrated-drop Moser residual surface from the proved
frontier producers, carrying only the inputs that the current frontier APIs
still keep explicit.

The relative mass-gradient field is produced from the bounded-before supplier.
The integrated dissipation field is produced by the PDE frontier after
converting the mass-gradient tuple to relative Moser interpolation.  The
quantitative endpoint is filled by the dyadic endpoint discharge converter. -/
theorem intervalDomain_integratedDropResiduals_of_classical
    {p : CM2Params}
    (hbdns : IntervalDomainBoundednessHyp p)
    (hClosedTrace :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          Nonempty
            (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u))
    (hFTC :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hClassicalRegularity :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hBoundedBefore :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IsPaper2BoundedBefore intervalDomain T u)
    (hGap :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0)
    (hDyadicEndpoint :
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
      ∀ {T : ℝ}, 0 < T →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
      ∀ pExp,
        max (p.N : ℝ)
            (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
        LpPowerBoundedBefore intervalDomain pExp T u →
          ∃ pSeq rootBound : ℕ → ℝ,
            (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
              IntegratedMoserDissipationDropBefore
                intervalDomain u T (2 * p.γ) pExp →
              _root_.ShenWork.IntervalDomainExistence.P3MoserQuantitativeEndpointDischarge.DyadicMoserEndpointRecurrence
                u T pSeq rootBound) :
    _root_.ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p := by
  have relativeMassGradientCore :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          ∃ cGrad : ℝ → ℝ,
            (∀ pExp, p0 ≤ pExp → 0 < cGrad pExp) ∧
            (∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
              LpMassGradientInterpolationEstimate intervalDomain
                (pExp + rho) eta Ceta T u) ∧
            (∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
              intervalDomain.integral (fun x =>
                (u t x) ^ (pExp + rho - 2) *
                  (intervalDomain.gradNorm (u t) x) ^ 2) ≤
              cGrad pExp * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm
                  (fun y => (u t y) ^ (pExp / 2)) x) ^ 2)) ∧
            MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0 := by
    intro T rho p0 u v hsol hcross hboot
    exact
      _root_.ShenWork.IntervalDomainExistence.P3MoserRelativeMassGradientProducer.intervalDomain_relativeMassGradient_of_classical_boundedBefore
          hsol hcross hboot
          (hBoundedBefore hsol hcross hboot)
  have integratedMoserDissipationCore :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 := by
    intro T rho p0 u v hsol hcross hboot
    have hrel :
        RelativeMoserInterpolationBefore intervalDomain u T rho p0 := by
      rcases relativeMassGradientCore hsol hcross hboot with
        ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
      exact
        P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient
          cGrad hcGrad hMG hgrad hmassToLp
    exact
      _root_.ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2.intervalDomain_integratedMoserDissipationDropBefore_of_globalPDE_v2
          hsol hcross hboot
          (hFTC hsol hcross hboot)
          hrel
          (hClassicalRegularity hsol hcross hboot)
          (hGap hsol hcross hboot)
  let hdyadic :
      _root_.ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals
        p :=
    { boundednessHyp := hbdns
      closedEnergyTrace := hClosedTrace
      integratedMoserDissipation := integratedMoserDissipationCore
      relativeMassGradient := relativeMassGradientCore
      dyadicEndpoint := hDyadicEndpoint }
  exact
    _root_.ShenWork.Paper3.IntervalDomainMassLpSmoothingMoserIntegratedDropDyadicEndpointResiduals.to_integratedDropResiduals
      hdyadic

#print axioms intervalDomain_integratedDropResiduals_of_classical

end

end ShenWork.IntervalDomainExistence.P3MoserAssemblyFiller
