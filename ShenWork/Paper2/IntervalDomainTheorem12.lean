/-
  ShenWork/Paper2/IntervalDomainTheorem12.lean

  Statement-layer assembly of Paper 2 Theorem 1.2 on intervalDomain.

  This file does not close the open H0/H1 analysis.  It proves that once the
  Tier-1 interval estimates and the remaining PDE bootstrap/global-boundedness
  bridges are supplied explicitly, the full `Theorem_1_2 intervalDomain p`
  statement follows.
-/
import ShenWork.Paper2.IntervalDomainCorollary21
import ShenWork.Paper2.IntervalDomainChain
import ShenWork.Paper2.IntervalDomainTheorem11

open Filter
open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem12

/-- The exponent used to pass from `Corollary_2_1` to `Proposition_2_5`. -/
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

/-- From Corollary 2.1 plus the repo's Lp-to-sup bridge (`Proposition_2_5`),
a finite-horizon classical interval solution is bounded before the horizon.

This is a structural assembly lemma.  The analytic content remains in
`Corollary_2_1`, the bootstrap seed, and `Proposition_2_5`; none of those is
reproved here. -/
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

/-- Paper 2 Theorem 1.2 on `intervalDomain`, conditional on the honest open
frontier.

Inputs classified by the playbook:
* `hLemma21`, `hLemma26`, `hLemma41`, and `hCor21` are the Tier-1/H0 frontier.
  The current statement-layer proof consumes `hCor21` directly; the other
  Tier-1 lemmas are kept explicit in the theorem signature because the paper
  proof depends on them upstream.
* `hProp25` is the current repo endpoint turning a high-enough Lp bound into
  finite-horizon sup boundedness.
* `hexist` is local existence plus bounded-solution global extension, the same
  honest Cauchy-theory gap used by the interval-domain Theorem 1.1 bridge.
* `hslowBootstrap` and `hcriticalBootstrap` are the branch-specific PDE
  bootstrap seeds.
* `hcriticalGlobalBound` is the remaining long-time uniformity step needed to
  turn global existence plus all finite-horizon bootstrap data into the
  theorem's `IsPaper2Bounded` conclusion.

The conclusion is the full, unweakened repository statement
`Theorem_1_2 intervalDomain p`. -/
theorem Theorem_1_2_intervalDomain
    (p : CM2Params)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (_hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hslowBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      0 < p.m → p.m < 1 →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hcriticalBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hcriticalGlobalBound :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2GlobalClassicalSolution intervalDomain p u v →
        InitialTrace intervalDomain u₀ u →
        (∀ T > 0,
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) →
          IsPaper2Bounded intervalDomain u) :
    Theorem_1_2 intervalDomain p := by
  intro ha_nonneg hb_nonneg hβ
  constructor
  · intro hm_pos hm_lt u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
      hexist.localExistence u₀ hu₀
    have hbootstrap :=
      hslowBootstrap ha_nonneg hb_nonneg hβ hm_pos hm_lt
        u₀ hu₀ Tmax hTmax u v hsol htrace
    have hbounded :=
      boundedBefore_of_corollary21_and_proposition25 p hCor21 hProp25
        hu₀ hTmax hsol htrace hbootstrap
    exact ⟨Tmax, hTmax, u, v, hsol, htrace, hbounded⟩
  · intro hm_eq hχ u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
      hexist.localExistence u₀ hu₀
    have hbootstrap :=
      hcriticalBootstrap ha_nonneg hb_nonneg hβ hm_eq hχ
        u₀ hu₀ Tmax hTmax u v hsol htrace
    have hboundedBefore :=
      boundedBefore_of_corollary21_and_proposition25 p hCor21 hProp25
        hu₀ hTmax hsol htrace hbootstrap
    have hm_ge : 1 ≤ p.m := by rw [hm_eq]
    have hglobal :=
      hexist.globalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
        hboundedBefore hm_ge
    have hbootstrapAll :
        ∀ T > 0,
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u := by
      intro T hT
      exact hcriticalBootstrap ha_nonneg hb_nonneg hβ hm_eq hχ
        u₀ hu₀ T hT u v (hglobal.classical hT) htrace
    have hbounded :=
      hcriticalGlobalBound ha_nonneg hb_nonneg hβ hm_eq hχ
        u₀ hu₀ u v hglobal htrace hbootstrapAll
    exact ⟨u, v, hglobal, htrace, hbounded⟩

/-- Variant of `Theorem_1_2_intervalDomain` that assembles Corollary 2.1 from
`Lemma_2_6 intervalDomain` plus the explicit PDE energy derivation.

This removes `Corollary_2_1 intervalDomain p` as a theorem input while keeping
the genuine H1.2/H0 frontier (`Lemma_2_6` and energy-from-cross-diffusion)
visible. -/
theorem Theorem_1_2_intervalDomain_of_Lemma_2_6_and_energy
    (p : CM2Params)
    (S : SemigroupEstimateData intervalDomain)
    (hLemma21 : Lemma_2_1 intervalDomain p S)
    (hLemma26 : Lemma_2_6 intervalDomain)
    (hLemma41 : Lemma_4_1 intervalDomain p)
    (hEnergyFromCrossDiffusion :
      ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T u v →
        CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
        AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
          LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hslowBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      0 < p.m → p.m < 1 →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hcriticalBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hcriticalGlobalBound :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2GlobalClassicalSolution intervalDomain p u v →
        InitialTrace intervalDomain u₀ u →
        (∀ T > 0,
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) →
          IsPaper2Bounded intervalDomain u) :
    Theorem_1_2 intervalDomain p := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    ShenWork.Paper2.IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hLemma26 hEnergyFromCrossDiffusion
  exact Theorem_1_2_intervalDomain
    p S hLemma21 hLemma26 hLemma41 hCor21 hProp25 hexist
    hslowBootstrap hcriticalBootstrap hcriticalGlobalBound

/-- Full interval-domain Theorem 1.2 assembly from the explicit H1 frontiers.

This pushes the Tier-1 inputs down one layer: `Lemma_2_6`, `Lemma_4_1`, and
`Corollary_2_1` are produced from the interval interpolation, mass-gradient
Moser, and PDE energy frontiers already exposed by the Theorem 1.1 bridge.
The remaining hypotheses are the honest H0/Tier-2 frontier for existence,
`Proposition_2_5`, and the two Theorem 1.2 branch bootstrap/global-boundedness
steps. -/
theorem Theorem_1_2_intervalDomain_of_mass_gradient_frontier
    (p : CM2Params)
    (S : SemigroupEstimateData intervalDomain)
    (hLemma21 : Lemma_2_1 intervalDomain p S)
    (hGN : IntervalDomainLemma41.IntervalDomainInterpolation)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hdiss :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp, p0 ≤ pExp → ∀ A B K L_const,
          (∀ t, 0 < t → t < T →
            (1 / pExp) * deriv
                (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
              A * intervalDomain.integral (fun x =>
                (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2) +
              B * intervalDomain.integral (fun x => (u t x) ^ pExp) ≤
            K * intervalDomain.integral (fun x => (u t x) ^ (pExp + rho)) + L_const) →
          ∀ t, 0 < t → t < T →
            0 ≤
              (1 / pExp) * deriv
                  (fun τ => intervalDomain.integral (fun x => (u τ x) ^ pExp)) t +
                B * intervalDomain.integral (fun x => (u t x) ^ pExp))
    (hcGrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp, p0 ≤ pExp → 0 < cGrad u T rho p0 pExp)
    (hMG :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp, p0 ≤ pExp → ∀ eta > 0, ∃ Ceta,
          LpMassGradientInterpolationEstimate intervalDomain (pExp + rho) eta Ceta T u)
    (hgrad :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp, p0 ≤ pExp → ∀ t, 0 < t → t < T →
          intervalDomain.integral (fun x =>
              (u t x) ^ (pExp + rho - 2) * (intervalDomain.gradNorm (u t) x) ^ 2) ≤
            cGrad u T rho p0 pExp * intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm (fun y => (u t y) ^ (pExp / 2)) x) ^ 2))
    (hmass :
      ∀ {N T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
        AbstractLpBootstrapHypothesis intervalDomain u N T rho p0 →
        LpBootstrapEnergyInequality intervalDomain u T rho p0 →
        ∀ pExp, p0 ≤ pExp → ∀ Ceta, ∃ Cmass, ∀ t, 0 < t → t < T →
          Ceta * (intervalDomain.integral (u t)) ^ (pExp + rho) ≤ Cmass)
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
    (hslowBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      0 < p.m → p.m < 1 →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hcriticalBootstrap :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hcriticalGlobalBound :
      0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
      p.m = 1 → p.χ₀ < chiBeta p →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2GlobalClassicalSolution intervalDomain p u v →
        InitialTrace intervalDomain u₀ u →
        (∀ T > 0,
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) →
          IsPaper2Bounded intervalDomain u) :
    Theorem_1_2 intervalDomain p := by
  have hLemma26 : Lemma_2_6 intervalDomain :=
    IntervalDomainTheorem11Composite.Lemma_2_6_intervalDomain_of_mass_gradient_frontier
      cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
  have hLemma41 : Lemma_4_1 intervalDomain p :=
    IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_GN_frontier p hGN
  have hCor21 : Corollary_2_1 intervalDomain p :=
    IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_mass_gradient_frontier
      p cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
      hEnergyFromCrossDiffusion
  exact Theorem_1_2_intervalDomain
    p S hLemma21 hLemma26 hLemma41 hCor21 hProp25 hexist
    hslowBootstrap hcriticalBootstrap hcriticalGlobalBound

/-- Vacuous interval-domain Theorem 1.2 branch when the top-level
`1 ≤ β` hypothesis fails. -/
theorem Theorem_1_2_intervalDomain_vacuous_when_beta_lt_one
    (p : CM2Params) (hβ : p.β < 1) :
    Theorem_1_2 intervalDomain p := by
  intro _ha _hb hβ'
  exact absurd hβ' (not_le.mpr hβ)

/-- Vacuous interval-domain Theorem 1.2 when `m` is above the theorem's
slow/critical range. -/
theorem Theorem_1_2_intervalDomain_vacuous_when_one_lt_m
    (p : CM2Params) (hm : 1 < p.m) :
    Theorem_1_2 intervalDomain p := by
  intro _ha _hb _hβ
  constructor
  · intro _hm_pos hm_lt _u₀ _hu₀
    exfalso
    exact (not_lt.mpr hm.le) hm_lt
  · intro hm_eq _hχ _u₀ _hu₀
    exfalso
    rw [hm_eq] at hm
    exact (lt_irrefl (1 : ℝ)) hm

/-- Vacuous interval-domain Theorem 1.2 critical branch when `m = 1` but the
critical sensitivity strict inequality fails. -/
theorem Theorem_1_2_intervalDomain_vacuous_when_m_eq_one_and_chiBeta_le_chi
    (p : CM2Params) (hm : p.m = 1) (hχ : chiBeta p ≤ p.χ₀) :
    Theorem_1_2 intervalDomain p := by
  intro _ha _hb _hβ
  constructor
  · intro _hm_pos hm_lt _u₀ _hu₀
    exfalso
    rw [hm] at hm_lt
    exact (lt_irrefl (1 : ℝ)) hm_lt
  · intro _hm_eq hχ_lt _u₀ _hu₀
    exfalso
    exact (not_lt.mpr hχ) hχ_lt

end ShenWork.Paper2.IntervalDomainTheorem12

end
