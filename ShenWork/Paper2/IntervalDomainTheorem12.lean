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

/-- Vacuous interval-domain Theorem 1.2 branch when the top-level
`1 ≤ β` hypothesis fails. -/
theorem Theorem_1_2_intervalDomain_vacuous_when_beta_lt_one
    (p : CM2Params) (hβ : p.β < 1) :
    Theorem_1_2 intervalDomain p := by
  intro _ha _hb hβ'
  exact absurd hβ' (not_le.mpr hβ)

end ShenWork.Paper2.IntervalDomainTheorem12

end
