import ShenWork.PDE.P3MoserEnergyGapRefactor

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence.P3MoserIntegratedDissipationPDEv2
open ShenWork.IntervalDomainExistence.P3MoserEnergyGapRefactor
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.IntervalDomainExistence.P3MoserGapProducerWiring

noncomputable section

/-- Pointwise wrapper for the T22 p-dependent gap producer. -/
theorem intervalDomain_gap_of_classical_pDep_pointwise
    {p : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hp0_gap : gapThresholdPDep p.χ₀ ≤ p0)
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain p T rho u v)
    (hboot : AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0) :
    LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0 :=
  lpBootstrapEnergyInequalityWithGap_of_classical_pDep hp0_gap hsol hcross hboot

/-- Produce the `hGap` function expected by the assembly wiring, provided the
gap threshold is available for each bootstrap instance. -/
theorem intervalDomain_gap_of_classical_pDep
    {p : CM2Params}
    (hp0_gap :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          gapThresholdPDep p.χ₀ ≤ p0) :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        LpBootstrapEnergyInequalityWithGap intervalDomain u T rho p0 := by
  intro T rho p0 u v hsol hcross hboot
  exact
    intervalDomain_gap_of_classical_pDep_pointwise
      (p := p) (T := T) (rho := rho) (p0 := p0) (u := u) (v := v)
      (hp0_gap hsol hcross hboot) hsol hcross hboot

#print axioms intervalDomain_gap_of_classical_pDep_pointwise
#print axioms intervalDomain_gap_of_classical_pDep

end

end ShenWork.IntervalDomainExistence.P3MoserGapProducerWiring
