/-
  ShenWork/Paper2/IntervalDomainTheorem13.lean

  Statement-layer assembly of Paper 2 Theorem 1.3 on intervalDomain.

  The proof composes the Tier-1 interval estimates with explicit strong-logistic
  bootstrap and long-time boundedness bridges.  Open H0/H1 analysis remains as
  named hypotheses; there are no proof holes or theorem-shaped package fields.
-/
import ShenWork.Paper2.IntervalDomainTheorem12

open ShenWork.Paper2
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainTheorem13

/-- Paper 2 Theorem 1.3 on `intervalDomain`, conditional on the honest open
frontier.

The conclusion is the exact repository statement `Theorem_1_3 intervalDomain p C`.
The local branch is obtained by:
local existence → strong-logistic bootstrap seed → Corollary 2.1 →
`Proposition_2_5`.

The global branch additionally uses the bounded-solution global extension
criterion and an explicit long-time uniformity bridge
`hstrongGlobalBound`. -/
theorem Theorem_1_3_intervalDomain
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (_hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongGlobalBound :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      1 ≤ p.m →
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
    Theorem_1_3 intervalDomain p C := by
  intro ha hb hm_pos hstrong
  constructor
  · intro u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
      hexist.localExistence u₀ hu₀
    have hbootstrap :=
      hstrongBootstrap ha hb hm_pos hstrong
        u₀ hu₀ Tmax hTmax u v hsol htrace
    have hbounded :=
      IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
        p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
    exact ⟨Tmax, hTmax, u, v, hsol, htrace, hbounded⟩
  · intro hm_ge u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ :=
      hexist.localExistence u₀ hu₀
    have hbootstrap :=
      hstrongBootstrap ha hb hm_pos hstrong
        u₀ hu₀ Tmax hTmax u v hsol htrace
    have hboundedBefore :=
      IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
        p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
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
      exact hstrongBootstrap ha hb hm_pos hstrong
        u₀ hu₀ T hT u v (hglobal.classical hT) htrace
    have hbounded :=
      hstrongGlobalBound ha hb hm_pos hstrong hm_ge
        u₀ hu₀ u v hglobal htrace hbootstrapAll
    exact ⟨u, v, hglobal, htrace, hbounded⟩

/-- Variant of `Theorem_1_3_intervalDomain` that derives Corollary 2.1 from
`Lemma_2_6 intervalDomain` and the explicit PDE energy derivation before
assembling the full strong-logistic theorem. -/
theorem Theorem_1_3_intervalDomain_of_Lemma_2_6_and_energy
    (p : CM2Params) (C : Paper2Constants p)
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
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongGlobalBound :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      1 ≤ p.m →
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
    Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    ShenWork.Paper2.IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hLemma26 hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain
    p C S hLemma21 hLemma26 hLemma41 hCor21 hProp25 hexist
    hstrongBootstrap hstrongGlobalBound

/-- Full interval-domain Theorem 1.3 assembly from the explicit H1 frontiers.

`Lemma_2_6`, `Lemma_4_1`, and `Corollary_2_1` are derived from the interval
interpolation, mass-gradient Moser, and PDE energy frontiers exposed by the
Theorem 1.1 bridge.  The strong-logistic bootstrap and global-boundedness
inputs remain explicit Tier-2 frontiers. -/
theorem Theorem_1_3_intervalDomain_of_mass_gradient_frontier
    (p : CM2Params) (C : Paper2Constants p)
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
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongGlobalBound :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      1 ≤ p.m →
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
    Theorem_1_3 intervalDomain p C := by
  have hLemma26 : Lemma_2_6 intervalDomain :=
    IntervalDomainTheorem11Composite.Lemma_2_6_intervalDomain_of_mass_gradient_frontier
      cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
  have hLemma41 : Lemma_4_1 intervalDomain p :=
    IntervalDomainTheorem11Composite.Lemma_4_1_intervalDomain_of_GN_frontier p hGN
  have hCor21 : Corollary_2_1 intervalDomain p :=
    IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_mass_gradient_frontier
      p cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
      hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain
    p C S hLemma21 hLemma26 hLemma41 hCor21 hProp25 hexist
    hstrongBootstrap hstrongGlobalBound

/-- Vacuous interval-domain Theorem 1.3 branch when `a = 0`. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_a_zero
    (p : CM2Params) (ha : p.a = 0) (C : Paper2Constants p) :
    Theorem_1_3 intervalDomain p C := by
  intro ha' _hb _hm _hstrong
  exact absurd ha' (by rw [ha]; exact lt_irrefl 0)

/-- Vacuous interval-domain Theorem 1.3 branch when `b = 0`. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_b_zero
    (p : CM2Params) (hb : p.b = 0) (C : Paper2Constants p) :
    Theorem_1_3 intervalDomain p C := by
  intro _ha hb' _hm _hstrong
  exact absurd hb' (by rw [hb]; exact lt_irrefl 0)

/-- Vacuous interval-domain Theorem 1.3 branch when `m ≤ 0`. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_m_le_zero
    (p : CM2Params) (hm : p.m ≤ 0) (C : Paper2Constants p) :
    Theorem_1_3 intervalDomain p C := by
  intro _ha _hb hm' _hstrong
  exact absurd hm' (not_lt.mpr hm)

/-- Vacuous interval-domain Theorem 1.3 branch when the strong-logistic
condition itself is unavailable. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_not_strong_logistic
    (p : CM2Params) (C : Paper2Constants p)
    (hstrong : ¬ StrongLogisticCondition p C) :
    Theorem_1_3 intervalDomain p C := by
  intro _ha _hb _hm hstrong'
  exact False.elim (hstrong hstrong')

end ShenWork.Paper2.IntervalDomainTheorem13

end
