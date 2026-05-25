/-
  ShenWork/Paper2/IntervalDomainTierChain.lean

  One-shot conditional assembly of the interval-domain Tier-1 chain feeding
  Paper 2 Theorem 1.1.

  This file introduces no new theorem-shaped assumption structure.  It bundles
  the already proved conditional bridges while keeping every unproved analytic
  input as an explicit named hypothesis.
-/
import ShenWork.Paper2.IntervalDomainTheorem11

open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainTheorem11Composite
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTierChain

/-- Full conditional interval-domain Tier-1/Tier-2 chain for Paper 2
Theorem 1.1.

From the explicit frontiers
* interval GN/mass-gradient interpolation for Lemma 4.1,
* mass-gradient Moser hypotheses for Lemma 2.6,
* cross-diffusion energy derivation for Corollary 2.1,
* `Proposition_2_5`, local existence/global-extension, and the bootstrap seed,

the statement-layer conclusions `Lemma_2_6`, `Lemma_4_1`, `Corollary_2_1`, and
`Theorem_1_1` all follow for `intervalDomain`.  This is playbook state ③:
conditional on named analytic frontiers, not an unconditional close. -/
theorem intervalDomain_tier1_theorem11_chain_of_frontiers
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
    Lemma_2_6 intervalDomain ∧
      Lemma_4_1 intervalDomain p ∧
      Corollary_2_1 intervalDomain p ∧
      Theorem_1_1 intervalDomain p := by
  have hLemma26 : Lemma_2_6 intervalDomain :=
    Lemma_2_6_intervalDomain_of_mass_gradient_frontier
      cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
  have hLemma41 : Lemma_4_1 intervalDomain p :=
    Lemma_4_1_intervalDomain_of_GN_frontier p hGN
  have hCor21 : Corollary_2_1 intervalDomain p :=
    Corollary_2_1_intervalDomain_of_mass_gradient_frontier
      p cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
      hEnergyFromCrossDiffusion
  have hThm11 : Theorem_1_1 intervalDomain p :=
    Theorem_1_1_intervalDomain_of_corollary21_and_proposition25
      p hCor21 hProp25 hexist hbootstrap
  exact ⟨hLemma26, hLemma41, hCor21, hThm11⟩

/-- Sharpened H1.3/H1.4/H2.1 chain for Paper 2 Theorem 1.1.

This is the version to use for the actual interval-domain classical-solution
workflow: `Corollary_2_1` is obtained directly from
`IntervalDomainInterpolation` and solution positivity, so the chain no longer
exposes the standalone mass-gradient interpolation frontier `hMG` or the
abstract `Lemma_2_6 intervalDomain`.  The latter is still a genuine H1.2
frontier for arbitrary bootstrap functions, but it is not needed as an input
for this theorem-level branch. -/
theorem intervalDomain_theorem11_chain_of_interpolation_frontier
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
    Lemma_4_1 intervalDomain p ∧
      Corollary_2_1 intervalDomain p ∧
      Theorem_1_1 intervalDomain p := by
  have hLemma41 : Lemma_4_1 intervalDomain p :=
    Lemma_4_1_intervalDomain_of_GN_frontier p hGN
  have hCor21 : Corollary_2_1 intervalDomain p :=
    Corollary_2_1_intervalDomain_of_interpolation_frontier
      p hGN cGrad hdiss hcGrad hgrad hmass hu_nonneg hpow_int
      hEnergyFromCrossDiffusion
  have hThm11 : Theorem_1_1 intervalDomain p :=
    Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
      p hCor21 hProp25 hexist hnonminimalBootstrap hminimalBootstrap
  exact ⟨hLemma41, hCor21, hThm11⟩

/-- Sharpened Theorem 1.1 chain with solution positivity discharging the
Moser nonnegativity input.

This is the strongest current conditional H1.3/H1.4/H2.1 assembly: the
interval interpolation frontier still supplies the mass-gradient estimate, but
the finite-interval Lp monotonicity uses only `IsPaper2ClassicalSolution.u_pos`
on the open interval. -/
theorem intervalDomain_theorem11_chain_of_interpolation_frontier_from_solution_positivity
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
    Lemma_4_1 intervalDomain p ∧
      Corollary_2_1 intervalDomain p ∧
      Theorem_1_1 intervalDomain p := by
  have hLemma41 : Lemma_4_1 intervalDomain p :=
    Lemma_4_1_intervalDomain_of_GN_frontier p hGN
  have hCor21 : Corollary_2_1 intervalDomain p :=
    Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity
      p hGN cGrad hdiss hcGrad hgrad hmass hpow_int hEnergyFromCrossDiffusion
  have hThm11 : Theorem_1_1 intervalDomain p :=
    Theorem_1_1_intervalDomain_of_branch_bootstrap_and_proposition25
      p hCor21 hProp25 hexist hnonminimalBootstrap hminimalBootstrap
  exact ⟨hLemma41, hCor21, hThm11⟩

end ShenWork.Paper2.IntervalDomainTierChain

end
