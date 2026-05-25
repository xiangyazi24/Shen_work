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
import ShenWork.PDE.IntervalDomainExistence

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainCorollary21
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem11Composite

/-- Build the Paper 2 Theorem 1.1 interval existence package while discharging
the `initialSupNormApproach` field from the concrete interval-domain
`InitialTrace` theorem.

The remaining inputs are genuine Cauchy-theory frontiers: local existence,
boundedness of admissible initial data, and the global-extension criterion. -/
theorem IntervalDomainExistence_of_local_global_bounded_initial
    (p : CM2Params)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v) :
    IntervalDomainTheorem11.IntervalDomainExistence p := by
  refine
    { localExistence := hlocal
      initialSupNormApproach := ?_
      globalExtension := hglobal }
  intro u₀ hu₀ T hT u v hsol htrace ε hε
  exact ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
    p u₀ hu₀ (hboundedInitial u₀ hu₀) hT hsol htrace hε

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

/-- H1.2 front-line closure with the nonnegativity input localized to the
open interval.

This is the version aligned with interval classical solutions: the Moser/Lp
monotonicity step integrates over `[0,1]`, and endpoint values do not affect
the interval integrals.  The remaining hypotheses are the same genuine
mass-gradient, dissipation, chain-rule, mass-control, and integrability
frontiers as in `Lemma_2_6_intervalDomain_of_mass_gradient_frontier`. -/
theorem Lemma_2_6_intervalDomain_of_mass_gradient_frontier_inside_nonneg
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
    (hu_inside_nonneg :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ t, 0 < t → t < T →
          ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
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
  exact intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_inside_nonneg
      (cGrad u T rho p0) hboot henergy
      (hdiss hboot henergy)
      (hcGrad hboot henergy)
      (hMG hboot henergy)
      (hgrad hboot henergy)
      (hmass hboot henergy)
      (hu_inside_nonneg hboot henergy)
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

/-- H1.4 closure from the mass-gradient Moser frontier when solution
nonnegativity is known only on the open interval.

This variant keeps endpoint positivity out of the statement.  It still proves
the full statement-layer `Corollary_2_1 intervalDomain p`; the open analytic
inputs are the same named PDE frontiers plus the interior nonnegativity needed
by finite-interval Lp monotonicity. -/
theorem Corollary_2_1_intervalDomain_of_mass_gradient_frontier_inside_nonneg
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
    (hu_inside_nonneg :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ t, 0 < t → t < T →
          ∀ x : intervalDomain.Point, x ∈ intervalDomain.inside → 0 ≤ u t x)
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
    Lemma_2_6_intervalDomain_of_mass_gradient_frontier_inside_nonneg
      cGrad hdiss hcGrad hMG hgrad hmass hu_inside_nonneg hpow_int
  exact Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hMoser hEnergyFromCrossDiffusion

/-- H1.4 closure where the mass-gradient interpolation estimate is generated
from the concrete interval interpolation frontier and the strict positivity of
the classical solution.

This does not prove the abstract `Lemma_2_6 intervalDomain`: that statement is
quantified over arbitrary bootstrap functions, with no positivity or
regularity data.  It proves the actual Corollary 2.1 use-case, where the
function is a classical interval solution and hence positive on the interior. -/
theorem Corollary_2_1_intervalDomain_of_interpolation_frontier
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation)
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
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0_gt, hp0_bound⟩
  have hN : 0 < (p.N : ℝ) := by
    exact_mod_cast p.hN
  have habs :
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0_gt, hp0_bound⟩
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    hEnergyFromCrossDiffusion hsol hcross habs
  have hMG :
      ∀ q, p0 ≤ q → ∀ eta > 0, ∃ Ceta,
        LpMassGradientInterpolationEstimate intervalDomain (q + rho) eta Ceta T u := by
    intro q hq eta heta
    have hp0_gt_one : 1 < p0 :=
      lt_of_le_of_lt (le_max_left (1 : ℝ) (rho * (p.N : ℝ) / 2)) hp0_gt
    have hq_gt_one : 1 < q := lt_of_lt_of_le hp0_gt_one hq
    have hq_rho_gt_one : 1 < q + rho := by linarith
    obtain ⟨Ceta, _hCeta_pos, hinterp⟩ := hGN eta heta (q + rho) hq_rho_gt_one
    refine ⟨Ceta, ?_⟩
    intro t ht0 htT
    exact hinterp (u t) (fun x hx => hsol.u_pos ht0 htT hx)
  exact intervalDomain_all_exponents_of_energy_dissipation_mass_gradient
    (cGrad u T rho p0) habs henergy
    (hdiss habs henergy)
    (hcGrad habs henergy)
    hMG
    (hgrad habs henergy)
    (hmass habs henergy)
    (hu_nonneg habs henergy)
    (hpow_int habs henergy)
    pExp hpExp

/-- H1.4 closure from the interval interpolation frontier, with the
nonnegativity input discharged from the classical solution positivity on
`intervalDomain.inside`.

Compared with `Corollary_2_1_intervalDomain_of_interpolation_frontier`, this
removes the separate `hu_nonneg` frontier from the actual Paper 2 solution
workflow.  The endpoint issue is handled by the interior-nonnegative
finite-interval Lp monotonicity lemma. -/
theorem Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation)
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
  intro T hT u v hsol hbootstrap pExp hpExp
  rcases hbootstrap with ⟨rho, hrho, hcross, p0, hp0_gt, hp0_bound⟩
  have habs :
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 :=
    ⟨hrho, hT, hp0_gt, hp0_bound⟩
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    hEnergyFromCrossDiffusion hsol hcross habs
  have hMG :
      ∀ q, p0 ≤ q → ∀ eta > 0, ∃ Ceta,
        LpMassGradientInterpolationEstimate intervalDomain (q + rho) eta Ceta T u := by
    intro q hq eta heta
    have hp0_gt_one : 1 < p0 :=
      lt_of_le_of_lt (le_max_left (1 : ℝ) (rho * (p.N : ℝ) / 2)) hp0_gt
    have hq_gt_one : 1 < q := lt_of_lt_of_le hp0_gt_one hq
    have hq_rho_gt_one : 1 < q + rho := by linarith
    obtain ⟨Ceta, _hCeta_pos, hinterp⟩ := hGN eta heta (q + rho) hq_rho_gt_one
    refine ⟨Ceta, ?_⟩
    intro t ht0 htT
    exact hinterp (u t) (fun x hx => hsol.u_pos ht0 htT hx)
  exact intervalDomain_all_exponents_of_energy_dissipation_mass_gradient_inside_nonneg
    (cGrad u T rho p0) habs henergy
    (hdiss habs henergy)
    (hcGrad habs henergy)
    hMG
    (hgrad habs henergy)
    (hmass habs henergy)
    (fun t ht0 htT x hx => le_of_lt (hsol.u_pos ht0 htT hx))
    (hpow_int habs henergy)
    pExp hpExp

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

/-- Branch-sharp Paper 2 Theorem 1.1 assembly.

Compared with `Theorem_1_1_intervalDomain_of_corollary21_and_proposition25`,
this version no longer asks for a branch-independent bootstrap seed.  It only
uses the seed in the two branches that actually occur in Theorem 1.1:
the positive-logistic branch `0 < a, 0 < b` and the minimal branch
`a = 0, b = 0`, both under `χ₀ ≤ 0`.  Outside these branches the auxiliary
global-extension package falls back to the boundedness input it is given, so no
new theorem-shaped assumption is introduced. -/
theorem Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
    (p : CM2Params)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
  intro hχ
  let hexist' : IntervalDomainTheorem11.IntervalDomainExistence p :=
    { localExistence := hexist.localExistence
      initialSupNormApproach := hexist.initialSupNormApproach
      globalExtension := by
        intro u₀ hu₀ Tmax hTmax u v hsol htrace hbounded hm
        by_cases hpos : 0 < p.a ∧ 0 < p.b
        · have hbootstrap :=
            hnonminimalBootstrap hχ hpos.1 hpos.2 u₀ hu₀
              Tmax hTmax u v hsol htrace
          have hboundedFromTier1 :
              IsPaper2BoundedBefore intervalDomain Tmax u :=
            boundedBefore_of_corollary21_and_proposition25
              p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
          exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
            hboundedFromTier1 hm
        · by_cases hzero : p.a = 0 ∧ p.b = 0
          · have hbootstrap :=
              hminimalBootstrap hχ hzero.1 hzero.2 u₀ hu₀
                Tmax hTmax u v hsol htrace
            have hboundedFromTier1 :
                IsPaper2BoundedBefore intervalDomain Tmax u :=
              boundedBefore_of_corollary21_and_proposition25
                p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
            exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
              hboundedFromTier1 hm
          · exact hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
              hbounded hm }
  exact (IntervalDomainTheorem11.Theorem_1_1_intervalDomain_conditional
    p hexist') hχ

/-- Uniform-bootstrap Theorem 1.1 assembly with the interval initial-approach
field discharged from the concrete `InitialTrace` theorem.

This is the bounded-initial-data variant of
`Theorem_1_1_intervalDomain_of_corollary21_and_proposition25`: it preserves the
same `Corollary_2_1`, `Proposition_2_5`, and single bootstrap frontier, while
building the `IntervalDomainExistence` package from local existence, bounded
initial data, and global extension. -/
theorem Theorem_1_1_intervalDomain_of_corollary21_proposition25_uniform_bounded_initial
    (p : CM2Params)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
  exact Theorem_1_1_intervalDomain_of_corollary21_and_proposition25
    p hCor21 hProp25
    (IntervalDomainExistence_of_local_global_bounded_initial
      p hlocal hboundedInitial hglobal)
    hbootstrap

/-- Branch-sharp Theorem 1.1 assembly with the interval initial-approach field
discharged from the concrete `InitialTrace` theorem.

Compared with `Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25`,
this no longer takes the full `IntervalDomainExistence` package.  It asks only
for local existence, bounded admissible initial data, and global extension; the
initial sup-norm approach field is built by
`IntervalDomainExistence_of_local_global_bounded_initial`. -/
theorem Theorem_1_1_intervalDomain_of_corollary21_proposition25_bounded_initial
    (p : CM2Params)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
  exact Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
    p hCor21 hProp25
    (IntervalDomainExistence_of_local_global_bounded_initial
      p hlocal hboundedInitial hglobal)
    hnonminimalBootstrap hminimalBootstrap

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

/-- Direct H1/H2 composition with the interval initial-approach field
discharged from concrete initial traces.

This is the bounded-initial-data counterpart of
`Theorem_1_1_intervalDomain_of_mass_gradient_frontier_and_proposition25`.  It
keeps the same mass-gradient Moser, cross-diffusion energy, `Proposition_2_5`,
and bootstrap frontiers, while replacing the full `IntervalDomainExistence`
package by the three Cauchy-theory inputs actually still needed. -/
theorem Theorem_1_1_intervalDomain_of_mass_gradient_frontier_proposition25_bounded_initial
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
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
  exact Theorem_1_1_intervalDomain_of_mass_gradient_frontier_and_proposition25
    p cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
    hEnergyFromCrossDiffusion hProp25
    (IntervalDomainExistence_of_local_global_bounded_initial
      p hlocal hboundedInitial hglobal)
    hbootstrap

/-- Branch-sharp direct H1/H2 composition for Paper 2 Theorem 1.1.

This combines the mass-gradient Moser frontier and cross-diffusion energy
derivation to obtain `Corollary_2_1`, then applies the branch-sharp bootstrap
assembly above.  The remaining open inputs are genuine analytic frontiers:
the Moser energy/dissipation/mass-gradient hypotheses, `Proposition_2_5`,
interval local/global extension, and the branch-specific bootstrap seeds. -/
theorem Theorem_1_1_intervalDomain_of_branch_mass_gradient_frontier_and_proposition25
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
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
  exact Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
    p hCor21 hProp25 hexist hnonminimalBootstrap hminimalBootstrap

/-- Branch-sharp direct H1/H2 composition with the interval initial-approach
field discharged from concrete initial traces.

This is the bounded-initial-data counterpart of
`Theorem_1_1_intervalDomain_of_branch_mass_gradient_frontier_and_proposition25`.
It keeps the branch-specific bootstrap seeds and all PDE-side Moser frontiers,
while replacing the full `IntervalDomainExistence` package by local existence,
bounded admissible initial data, and the bounded-solution global-extension
criterion. -/
theorem Theorem_1_1_intervalDomain_of_branch_mass_gradient_frontier_proposition25_bounded_initial
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
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
  exact Theorem_1_1_intervalDomain_of_branch_mass_gradient_frontier_and_proposition25
    p cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
    hEnergyFromCrossDiffusion hProp25
    (IntervalDomainExistence_of_local_global_bounded_initial
      p hlocal hboundedInitial hglobal)
    hnonminimalBootstrap hminimalBootstrap

/-- Branch-sharp Theorem 1.1 composition with the mass-gradient interpolation
frontier discharged from `IntervalDomainInterpolation` for each classical
solution.

This is the current sharp H2.1 chain through H1.4: it no longer exposes the
standalone `hMG` hypothesis.  The remaining inputs are the honest PDE-side
energy/dissipation, chain-rule, mass-control, integrability, `Proposition_2_5`,
existence/global-extension, and branch bootstrap frontiers. -/
theorem Theorem_1_1_intervalDomain_of_interpolation_frontier_and_branch_bootstrap
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation)
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
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
    Corollary_2_1_intervalDomain_of_interpolation_frontier
      p hGN cGrad hdiss hcGrad hgrad hmass hu_nonneg hpow_int
      hEnergyFromCrossDiffusion
  exact Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
    p hCor21 hProp25 hexist hnonminimalBootstrap hminimalBootstrap

/-- Branch-sharp Theorem 1.1 composition where the Moser nonnegativity input is
discharged from classical-solution positivity.

This is the theorem-level version of
`Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity`:
it removes the separate `hu_nonneg` frontier from the actual H2.1 route while
leaving the PDE-side energy, chain-rule, mass-control, integrability,
`Proposition_2_5`, existence/global-extension, and branch bootstrap frontiers
explicit. -/
theorem Theorem_1_1_intervalDomain_of_interpolation_frontier_solution_positivity
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation)
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
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
    Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity
      p hGN cGrad hdiss hcGrad hgrad hmass hpow_int hEnergyFromCrossDiffusion
  exact Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
    p hCor21 hProp25 hexist hnonminimalBootstrap hminimalBootstrap

/-- Strongest current H2.1 route with the interval initial-approach field
discharged from the concrete `InitialTrace` theorem.

This combines the interpolation/solution-positivity route with
`IntervalDomainExistence_of_local_global_bounded_initial`, so the full
`IntervalDomainExistence` package is no longer an input.  The remaining
existence hypotheses are the genuine Cauchy frontiers: local existence,
bounded admissible initial data, and global extension from boundedness. -/
theorem Theorem_1_1_intervalDomain_of_interpolation_frontier_solution_positivity_bounded_initial
    (p : CM2Params)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation)
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
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)))
    (hglobal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
        ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v →
          InitialTrace intervalDomain u₀ u →
            IsPaper2BoundedBefore intervalDomain Tmax u →
              1 ≤ p.m →
                IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hnonminimalBootstrap :
      p.χ₀ ≤ 0 → 0 < p.a → 0 < p.b →
        ∀ u₀ : intervalDomain.Point → ℝ,
          PositiveInitialDatum intervalDomain u₀ →
        ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p T u v →
          InitialTrace intervalDomain u₀ u →
            ∃ rho > 0,
              CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
                ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                  LpPowerBoundedBefore intervalDomain p0 T u)
    (hminimalBootstrap :
      p.χ₀ ≤ 0 → p.a = 0 → p.b = 0 →
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
    Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity
      p hGN cGrad hdiss hcGrad hgrad hmass hpow_int hEnergyFromCrossDiffusion
  exact Theorem_1_1_intervalDomain_of_corollary21_proposition25_bounded_initial
    p hCor21 hProp25 hlocal hboundedInitial hglobal
    hnonminimalBootstrap hminimalBootstrap

end ShenWork.Paper2.IntervalDomainTheorem11Composite

end
