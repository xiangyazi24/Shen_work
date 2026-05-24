/-
  ShenWork/Paper2/IntervalDomainTheorem11.lean

  Statement-layer assembly for Paper 2 Theorem 1.1 on intervalDomain.

  This file keeps the remaining analysis as explicit, named hypotheses:
  no new theorem-shaped assumption structure, no axioms, no proof holes.
-/
import ShenWork.Paper2.IntervalDomainChain
import ShenWork.Paper2.IntervalDomainEnergyStep
import ShenWork.Paper2.IntervalDomainLemma41
import ShenWork.Paper2.IntervalDomainCorollary21

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainCorollary21
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem11Composite

/-! ### H1.2/H1.3/H1.4 conditional closures -/

/-- H1.2 front-line closure: the interval-domain Moser lemma follows from the
explicit PDE/frontier hypotheses used by `IntervalDomainEnergyStep`.

The hypotheses are not the conclusion in disguise:
* `hdiss` removes the time derivative plus lower-order term from the energy
  inequality;
* `hMG` is the Paper 2 mass-gradient interpolation estimate;
* `hgrad` is the chain-rule comparison to `∇(u^(p/2))`;
* `hmass`, `hu_nonneg`, and `hpow_int` are standard solution regularity and
  mass/integrability inputs. -/
theorem Lemma_2_6_intervalDomain_of_mass_gradient_frontier
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hdiss :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ A B K L_const,
          (∀ t, 0 < t → t < T →
            (1 / p) * deriv
                (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
              A * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
              B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
            K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
          ∀ t, 0 < t → t < T →
            0 ≤
              (1 / p) * deriv
                  (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
                B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hcGrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → 0 < cGrad u T rho p0 p)
    (hMG :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
          LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x =>
              (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad u T rho p0 p * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
          Ceta * (intervalDomain.integral (u t)) ^ (p + rho) ≤ Cmass)
    (hu_nonneg :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
          IntervalIntegrable
            (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
            MeasureTheory.volume 0 1) :
    Lemma_2_6 intervalDomain := by
  intro N _hN u T rho p0 hboot henergy pExp hpExp
  exact intervalDomain_all_exponents_of_energy_dissipation_mass_gradient
      (cGrad u T rho p0) hboot henergy
      (hdiss hboot henergy)
      (hcGrad hboot henergy)
      (hMG hboot henergy)
      (hgrad hboot henergy)
      (hmass hboot henergy)
      (hu_nonneg hboot henergy)
      (hpow_int hboot henergy)
      pExp hpExp

/-- H1.3 closure from the concrete interval interpolation frontier. -/
theorem Lemma_4_1_intervalDomain_of_GN_frontier
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation) :
    Lemma_4_1 intervalDomain p :=
  IntervalDomainLemma41.Lemma_4_1_intervalDomain_of_interpolation hGN p

/-- H1.4 closure from the Moser/frontier closure and the PDE energy derivation
from the cross-diffusion bootstrap estimate. -/
theorem Corollary_2_1_intervalDomain_of_mass_gradient_frontier
    (p : CM2Params)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hdiss :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ A B K L_const,
          (∀ t, 0 < t → t < T →
            (1 / p) * deriv
                (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
              A * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
              B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
            K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
          ∀ t, 0 < t → t < T →
            0 ≤
              (1 / p) * deriv
                  (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
                B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hcGrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → 0 < cGrad u T rho p0 p)
    (hMG :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
          LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x =>
              (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad u T rho p0 p * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
          Ceta * (intervalDomain.integral (u t)) ^ (p + rho) ≤ Cmass)
    (hu_nonneg :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
          IntervalIntegrable
            (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
            MeasureTheory.volume 0 1)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0) :
    Corollary_2_1 intervalDomain p := by
  have hMoser : Lemma_2_6 intervalDomain :=
    Lemma_2_6_intervalDomain_of_mass_gradient_frontier
      cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
  exact Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hMoser hEnergyFromCrossDiffusion

/-! ### H2.1 conditional Theorem 1.1 assembly -/

private def boundednessExponent (p : CM2Params) : ℝ :=
  max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) + 1

private lemma boundednessExponent_gt_one (p : CM2Params) :
    1 < boundednessExponent p := by
  have hN_nat : 1 ≤ p.N := Nat.succ_le_of_lt p.hN
  have hN : (1 : ℝ) ≤ (p.N : ℝ) := by exact_mod_cast hN_nat
  have hmax : (1 : ℝ) ≤
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) :=
    le_trans hN (le_max_left _ _)
  unfold boundednessExponent
  linarith

private lemma boundednessExponent_above_threshold (p : CM2Params) :
    max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) <
      boundednessExponent p := by
  unfold boundednessExponent
  linarith

/-- Corollary 2.1 plus the repo endpoint `Proposition_2_5` gives a finite
horizon sup-norm bound for the local interval solution. -/
theorem boundedBefore_of_corollary21_and_proposition25
    (p : CM2Params)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hbootstrap :
      ∃ rho > 0, CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
        ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
          LpPowerBoundedBefore intervalDomain p0 T u) :
    IsPaper2BoundedBefore intervalDomain T u := by
  have hLp :
      LpPowerBoundedBefore intervalDomain (boundednessExponent p) T u :=
    hCor21 T hT u v hsol hbootstrap
      (boundednessExponent p) (boundednessExponent_gt_one p)
  exact hProp25 u₀ hu₀ T hT u v hsol htrace
    (boundednessExponent p) (boundednessExponent_above_threshold p) hLp

/-- Paper 2 Theorem 1.1 on `intervalDomain`, conditional on the current honest
frontier:
* local existence and initial sup-norm approach/global extension
  (`IntervalDomainExistence`);
* Corollary 2.1 and `Proposition_2_5`;
* the branch-independent bootstrap seed needed to apply Corollary 2.1.

The actual sup-norm estimates in the theorem are still obtained from the
proved `Lemma_3_1_intervalDomain` via `Theorem_1_1_intervalDomain_conditional`.
The Tier-1 chain is used to provide the boundedness input to the global
extension criterion. -/
theorem Theorem_1_1_intervalDomain_of_corollary21_and_proposition25
    (p : CM2Params)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hbootstrap :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) :
    Theorem_1_1 intervalDomain p := by
  let hexist' : IntervalDomainTheorem11.IntervalDomainExistence p :=
    { localExistence := hexist.localExistence
      initialSupNormApproach := hexist.initialSupNormApproach
      globalExtension := by
        intro u₀ hu₀ Tmax hTmax u v hsol htrace _hbounded hm
        have hbootstrap_t :=
          hbootstrap u₀ hu₀ Tmax hTmax u v hsol htrace
        have hboundedFromTier1 :
            IsPaper2BoundedBefore intervalDomain Tmax u :=
          boundedBefore_of_corollary21_and_proposition25
            p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap_t
        exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
          hboundedFromTier1 hm }
  exact IntervalDomainTheorem11.Theorem_1_1_intervalDomain_conditional
    p hexist'

/-- Direct H1/H2 composition for Paper 2 Theorem 1.1 on `intervalDomain`.

This removes `Corollary_2_1 intervalDomain p` from the theorem input by
constructing it from the explicit mass-gradient Moser frontier plus the
cross-diffusion energy derivation.  The remaining hypotheses are still genuine
frontiers: interval existence/global extension, `Proposition_2_5`, and the
branch-independent bootstrap seed. -/
theorem Theorem_1_1_intervalDomain_of_mass_gradient_frontier_and_proposition25
    (p : CM2Params)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hdiss :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ A B K L_const,
          (∀ t, 0 < t → t < T →
            (1 / p) * deriv
                (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
              A * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2) +
              B * intervalDomain.integral (fun x => (u t x) ^ p) ≤
            K * intervalDomain.integral (fun x => (u t x) ^ (p + rho)) + L_const) →
          ∀ t, 0 < t → t < T →
            0 ≤
              (1 / p) * deriv
                  (fun τ => intervalDomain.integral (fun x => (u τ x) ^ p)) t +
                B * intervalDomain.integral (fun x => (u t x) ^ p))
    (hcGrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → 0 < cGrad u T rho p0 p)
    (hMG :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ eta > 0, ∃ Ceta,
          LpMassGradientInterpolationEstimate intervalDomain (p + rho) eta Ceta T u)
    (hgrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x =>
              (u t x) ^ (p + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad u T rho p0 p * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (hmass :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ p, p0 ≤ p → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
          Ceta * (intervalDomain.integral (u t)) ^ (p + rho) ≤ Cmass)
    (hu_nonneg :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ t, 0 < t → t < T → ∀ x : intervalDomain.Point, 0 ≤ u t x)
    (hpow_int :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp : ℝ, 1 < pExp → ∀ t, 0 < t → t < T →
          IntervalIntegrable
            (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ pExp))
            MeasureTheory.volume 0 1)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hbootstrap :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) :
    Theorem_1_1 intervalDomain p := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    Corollary_2_1_intervalDomain_of_mass_gradient_frontier
      p cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
      hEnergyFromCrossDiffusion
  exact Theorem_1_1_intervalDomain_of_corollary21_and_proposition25
    p hCor21 hProp25 hexist hbootstrap

end ShenWork.Paper2.IntervalDomainTheorem11Composite

end
