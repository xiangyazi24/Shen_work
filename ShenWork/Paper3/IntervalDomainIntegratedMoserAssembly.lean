import ShenWork.PDE.IntervalDomainMoserLadderAtoms
import ShenWork.PDE.P3MoserLemmaDischarge

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper3

noncomputable section

/-!
Integrated-drop replacement for the old raw pointwise Moser-drop residual.

The current regularity producer API does not derive the integrated first-crossing
regularity package from `IsPaper2ClassicalSolution` alone; it requires the
explicit classical integrated-Moser regularity data.  Consequently the
conversion below keeps this as a separate supplier while replacing the false
`rawMoserDrop` field by the satisfiable integrated dissipation predicate.
-/

/-- Closed-energy Moser residuals with the false pointwise raw drop replaced by
the integrated Moser dissipation estimate.  The relative interpolation field is
still supplied in mass-gradient form and converted by
`P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient`. -/
structure IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        Nonempty
          (P3MoserLemmaDischarge.ClosedEnergyIdentityTraceData T u₀ u)
  integratedMoserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMassGradient :
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
          MoserMassPowerToCurrentLpLowerOrder intervalDomain u T rho p0
  quantitativeEndpoint :
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
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound

namespace IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals

/-- Convert the integrated-drop/mass-gradient residual surface to the reusable
integrated-step residual package.  The explicit regularity supplier is the
honest extra input required by the current `P3MoserRegularityProducer` API. -/
def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p)
    (classicalRegularity :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := ha
  chi_nonneg := le_of_lt hχ0
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact
      P3MoserLemmaDischarge.l2SeedRegularity_of_closedEnergyIdentityTraceData
        (Classical.choice
          (h.closedEnergyTrace u₀ hu₀ T hT u v hsol htrace))
  integratedStep := by
    intro T rho p0 u v hsol hcross hboot
    have hdiss :
        IntegratedMoserDissipationDropBefore
          intervalDomain u T rho p0 :=
      h.integratedMoserDissipation hsol hcross hboot
    have hrel :
        RelativeMoserInterpolationBefore intervalDomain u T rho p0 := by
      rcases h.relativeMassGradient hsol hcross hboot with
        ⟨cGrad, hcGrad, hMG, hgrad, hmassToLp⟩
      exact
        P3MoserLemmaDischarge.relativeMoserInterpolationBefore_of_massGradient
          cGrad hcGrad hMG hgrad hmassToLp
    exact
      intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
        (classicalRegularity hsol hcross hboot)
        hsol
        hdiss
        hrel
        (AbstractLpBootstrapHypothesis.rho_pos hboot)
        (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

def to_routeResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals p)
    (classicalRegularity :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u
          (p.N : ℝ) T rho p0 →
          IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainMassLpSmoothingRouteResiduals p :=
  (h.to_integratedStepResiduals classicalRegularity ha hχ0).to_routeResiduals

end IntervalDomainMassLpSmoothingMoserIntegratedDropResiduals

end

end ShenWork.Paper3
