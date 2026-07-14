/-
  ShenWork/Paper2/IntervalDomainCorollary21.lean

  Tier-1 Paper 2 Corollary 2.1 bridge for intervalDomain.

  Paper statement:
    On the interval domain, the cross-diffusion bootstrap estimate plus one
    uniform L^p seed imply terminal-time L^p bounds for every p > 1.

  The legacy statement-layer `Corollary_2_1` asks for a uniform bound on the
  whole open interval `(0,T)`.  That is stronger than the printed paper
  conclusion `limsup_{t -> T-}` and requires initial high-power control.  The
  theorem `intervalDomain_Corollary_2_1_terminalWindow` below proves the
  paper-faithful terminal-window conclusion unconditionally from the stated
  seed and cross-diffusion hypotheses.
-/
import ShenWork.Paper2.Statements
import ShenWork.PDE.P3MoserAgmonDirectRoute

open ShenWork.Paper2
open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.P3MoserAgmonDirectRoute

noncomputable section

namespace ShenWork.Paper2.IntervalDomainCorollary21

/-- Paper-faithful terminal-time form of Corollary 2.1 on the unit interval.

`LpPowerBoundedOnTerminalWindow` is a concrete uniform bound on some interval
`[s,T)`, hence it implies the printed finite `limsup` conclusion. -/
def Corollary_2_1_TerminalWindow (p : CM2Params) : Prop :=
  ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
    IsPaper2ClassicalSolution intervalDomain p T u v →
      (∃ rho > 0, CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore intervalDomain p0 T u) →
      ∀ pExp > 1,
        LpPowerBoundedOnTerminalWindow intervalDomain pExp T u

/-- Unconditional Paper 2 Corollary 2.1 on the concrete unit interval.

The cross-diffusion estimate produces the tested power-energy inequality.
The fixed seed supplies the low norm in the Agmon/GN absorption, and the
resulting scalar linear damping inequality bounds every higher power from a
positive anchor slice up to `T`. -/
theorem intervalDomain_Corollary_2_1_terminalWindow
    (p : CM2Params) :
    Corollary_2_1_TerminalWindow p := by
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0, hseed⟩
  have hboot : AbstractLpBootstrapHypothesis intervalDomain u
      (p.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0, hseed⟩
  exact intervalDomain_abstractLpBootstrap_terminal
    hsol hboot
      (intervalDomain_LpBootstrapEnergyInequality_of_regularity
        hsol hcross hboot)
    pExp hpExp

/-- **Legacy strengthened all-time wrapper, conditional on the old abstract
`Lemma_2_6` interface and the PDE energy derivation.**

Full statement proved here:
if
* `Lemma_2_6 intervalDomain` is available, and
* every classical interval solution satisfying the cross-diffusion bootstrap
  estimate also satisfies the corresponding `LpBootstrapEnergyInequality`,

then the interval-domain form of Paper 2 Corollary 2.1 holds.

This compatibility theorem is not the paper-faithful close: the raw abstract
`Lemma_2_6` interface is false for arbitrary `BoundedDomainData`, and its
all-time conclusion is stronger than the printed terminal `limsup`.
Use `intervalDomain_Corollary_2_1_terminalWindow` for the genuine result. -/
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

#print axioms intervalDomain_Corollary_2_1_terminalWindow

end ShenWork.Paper2.IntervalDomainCorollary21

end
