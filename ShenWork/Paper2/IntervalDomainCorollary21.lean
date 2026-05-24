/-
  ShenWork/Paper2/IntervalDomainCorollary21.lean

  Tier-1 Paper 2 Corollary 2.1 bridge for intervalDomain.

  Intended paper statement:
    On the interval domain, the cross-diffusion bootstrap estimate plus one
    initial L^p bound imply L^p bounds for every p > 1.

  Status:
    This file proves the structural bridge from the Moser iteration lemma
    (`Lemma_2_6 intervalDomain`) and the PDE energy derivation to
    `Corollary_2_1 intervalDomain p`.  It is an honest conditional theorem:
    `Lemma_2_6 intervalDomain` is the Tier-1 H1.2 prerequisite, and the energy
    derivation is the standard test-by-u^{p-1} estimate needed to turn
    `CrossDiffusionBootstrapEstimate` into `LpBootstrapEnergyInequality`.
-/
import ShenWork.Paper2.Statements

open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainCorollary21

/-- **Paper 2 Corollary 2.1 on `intervalDomain`, conditional on the Moser
iteration lemma and the PDE energy derivation.**

Full statement proved here:
if
* `Lemma_2_6 intervalDomain` is available, and
* every classical interval solution satisfying the cross-diffusion bootstrap
  estimate also satisfies the corresponding `LpBootstrapEnergyInequality`,

then the interval-domain form of Paper 2 Corollary 2.1 holds.

This is not the tautological `Corollary_2_1.of_assumed_bound_branch`: the proof
constructs the exact `AbstractLpBootstrapHypothesis` required by `Lemma_2_6`
from the hypotheses appearing in `Corollary_2_1`. -/
theorem Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
    (p : CM2Params)
    (hMoser : Lemma_2_6 intervalDomain)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain p := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0_gt, hp0_bound⟩
  have hN : 0 < (p.N : ℝ) := by
    exact_mod_cast p.hN
  have habs :
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0_gt, hp0_bound⟩
  exact hMoser (p.N : ℝ) hN u T rho p0 habs
    (hEnergyFromCrossDiffusion hsol hcross habs) pExp hpExp

end ShenWork.Paper2.IntervalDomainCorollary21

end
