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

/-- Local branch of Paper 2 Theorem 1.3 on `intervalDomain`, conditional on
Corollary 2.1, Proposition 2.5, local existence, and the strong-logistic
bootstrap seed. -/
theorem Theorem_1_3_intervalDomain_local_branch_of_corollary21_and_proposition25
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
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
                LpPowerBoundedBefore intervalDomain p0 T u) :
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
              InitialTrace intervalDomain u₀ u ∧
              IsPaper2BoundedBefore intervalDomain Tmax u := by
  intro ha hb hm_pos hstrong u₀ hu₀
  obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
  have hbootstrap :=
    hstrongBootstrap ha hb hm_pos hstrong
      u₀ hu₀ Tmax hTmax u v hsol htrace
  have hbounded :=
    IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
      p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
  exact ⟨Tmax, hTmax, u, v, hsol, htrace, hbounded⟩

/-- Global branch of Paper 2 Theorem 1.3 on `intervalDomain`, conditional on
Corollary 2.1, Proposition 2.5, local/global extension, the strong-logistic
bootstrap seed, and the long-time boundedness bridge. -/
theorem Theorem_1_3_intervalDomain_global_branch_of_corollary21_and_proposition25
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
      0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
      1 ≤ p.m →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
              InitialTrace intervalDomain u₀ u ∧
              IsPaper2Bounded intervalDomain u := by
  intro ha hb hm_pos hstrong hm_ge u₀ hu₀
  obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
  have hbootstrap :=
    hstrongBootstrap ha hb hm_pos hstrong
      u₀ hu₀ Tmax hTmax u v hsol htrace
  have hboundedBefore :=
    IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
      p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
  have hglobal :=
    hglobalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
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

/-- Paper 2 Theorem 1.3 on `intervalDomain`, with the already-composed
`Corollary_2_1` as the Tier-1 input.

This is the strongest statement-layer form currently closed here: the
remaining hypotheses are exactly interval Cauchy/global extension,
`Proposition_2_5`, the strong-logistic bootstrap seed, and the long-time
uniform boundedness bridge. -/
theorem Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
  exact Theorem_1_3.of_assumed_solutions_branch
    (D := intervalDomain) (p := p) (C := C)
    (Theorem_1_3_intervalDomain_local_branch_of_corollary21_and_proposition25
      p C hCor21 hProp25 hlocal hstrongBootstrap)
    (Theorem_1_3_intervalDomain_global_branch_of_corollary21_and_proposition25
      p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
      hstrongGlobalBound)

/-- Fixed subcritical-`m` regime of Theorem 1.3.

If `m < 1`, the global branch guarded by `1 ≤ m` is vacuous.  The full
`Theorem_1_3 intervalDomain p C` then follows from the local strong-logistic
bootstrap route alone; no global-extension or long-time boundedness frontier
is needed for this wrapper. -/
theorem Theorem_1_3_intervalDomain_m_lt_one_regime_of_corollary21_and_proposition25
    (p : CM2Params) (C : Paper2Constants p)
    (hm_lt : p.m < 1)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
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
                LpPowerBoundedBefore intervalDomain p0 T u) :
    Theorem_1_3 intervalDomain p C := by
  refine Theorem_1_3.of_assumed_solutions_branch
    (D := intervalDomain) (p := p) (C := C)
    (Theorem_1_3_intervalDomain_local_branch_of_corollary21_and_proposition25
      p C hCor21 hProp25 hlocal hstrongBootstrap) ?_
  intro _ha _hb _hm_pos _hstrong hm_ge _u₀ _hu₀
  have hfalse : False := not_lt_of_ge hm_ge hm_lt
  exact False.elim hfalse

/-- Fixed subcritical-`m` regime of Theorem 1.3 with the `m > 0` guard
removed from the strong-logistic bootstrap frontier. -/
theorem Theorem_1_3_intervalDomain_m_lt_one_regime_of_parameter_m_pos_and_corollary21
    (p : CM2Params) (C : Paper2Constants p)
    (hm_lt : p.m < 1)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) :
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_m_lt_one_regime_of_corollary21_and_proposition25
    p C hm_lt hCor21 hProp25 hlocal
    (fun ha hb _hm_pos hstrong =>
      hstrongBootstrap ha hb hstrong)

/-- Fixed subcritical-`m` regime of Theorem 1.3 from `Lemma_2_6` plus the PDE
energy derivation.

Because `m < 1` is fixed, the global branch guarded by `1 ≤ m` is vacuous.
This wrapper does not require global extension or any long-time boundedness
frontier. -/
theorem Theorem_1_3_intervalDomain_m_lt_one_regime_of_Lemma_2_6_energy_parameter_m_pos
    (p : CM2Params) (C : Paper2Constants p)
    (hm_lt : p.m < 1)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
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
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u) :
    Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    ShenWork.Paper2.IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hLemma26 hEnergyFromCrossDiffusion
  exact
    Theorem_1_3_intervalDomain_m_lt_one_regime_of_parameter_m_pos_and_corollary21
      p C hm_lt hCor21 hProp25 hlocal hstrongBootstrap

/-- Corollary-level Theorem 1.3 assembly from the existing interval
`IntervalDomainExistence` package.

This is a compatibility wrapper over
`Theorem_1_3_intervalDomain_of_corollary21_and_proposition25`; the proof uses
only `localExistence` and `globalExtension`, leaving
`initialSupNormApproach` unused. -/
theorem Theorem_1_3_intervalDomain_of_corollary21_proposition25_and_existence
    (p : CM2Params) (C : Paper2Constants p)
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
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
    p C hCor21 hProp25 hexist.localExistence hexist.globalExtension
    hstrongBootstrap hstrongGlobalBound

/-- Corollary-level Theorem 1.3 assembly with the `m > 0` guard removed from
the strong-logistic branch frontiers.

The conclusion remains the full `Theorem_1_3 intervalDomain p C`; the target
statement still introduces `0 < p.m`, and `CM2Params` also carries this field.
This wrapper is for upstream strong-logistic estimates that have already
internalized that parameter fact. -/
theorem Theorem_1_3_intervalDomain_of_parameter_m_pos_and_corollary21
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
    p C hCor21 hProp25 hlocal hglobalExtension
    (fun ha hb _hm hstrong =>
      hstrongBootstrap ha hb hstrong)
    (fun ha hb _hm hstrong hm_ge =>
      hstrongGlobalBound ha hb hstrong hm_ge)

/-- Existence-package variant of
`Theorem_1_3_intervalDomain_of_parameter_m_pos_and_corollary21`.

The strong-logistic frontiers do not expose `0 < p.m`; that guard is supplied
by the theorem target and by the `CM2Params` field. -/
theorem Theorem_1_3_intervalDomain_of_parameter_m_pos_corollary21_proposition25_and_existence
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_of_parameter_m_pos_and_corollary21
    p C hCor21 hProp25 hexist.localExistence hexist.globalExtension
    hstrongBootstrap hstrongGlobalBound

/-- Variant of Theorem 1.3 that assembles `Corollary_2_1` from `Lemma_2_6`
plus the PDE energy derivation, with the `m > 0` branch guard discharged.

The remaining direct long-time frontier is the strong-logistic boundedness
bridge `hstrongGlobalBound`; the eventual-sup version below reduces that
frontier further when an eventual scalar estimate is available. -/
theorem Theorem_1_3_intervalDomain_of_Lemma_2_6_energy_and_parameter_m_pos
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
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
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
  exact Theorem_1_3_intervalDomain_of_parameter_m_pos_and_corollary21
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongGlobalBound

/-- Corollary-level Theorem 1.3 assembly where the long-time frontier is an
eventual scalar sup-norm estimate rather than `IsPaper2Bounded` itself. -/
theorem Theorem_1_3_intervalDomain_of_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
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
    (hstrongEventualSupBound :
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  refine Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
    p C hCor21 hProp25 hexist.localExistence hexist.globalExtension
    hstrongBootstrap ?_
  intro ha hb hm hstrong hm_ge u₀ hu₀ u v hglobal htrace hbootstrapAll
  obtain ⟨T₀, M, hM⟩ :=
    hstrongEventualSupBound ha hb hm hstrong hm_ge u₀ hu₀ u v hglobal htrace
      hbootstrapAll
  exact IsPaper2Bounded.of_forall_ge_supNorm_le
    (D := intervalDomain) (u := u) (T := T₀) (M := M) hM

/-- Corollary-level Theorem 1.3 assembly using only the Cauchy-theory fields
actually needed here: local existence and bounded-solution global extension.

This avoids requiring the `initialSupNormApproach` field from
`IntervalDomainExistence`, which is needed by the Theorem 1.1 sup-norm
argument but not by the H2.3 assembly. -/
theorem Theorem_1_3_intervalDomain_of_local_global_and_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
    (hstrongEventualSupBound :
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  intro ha hb hm_pos hstrong
  constructor
  · intro u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
    have hbootstrap :=
      hstrongBootstrap ha hb hm_pos hstrong
        u₀ hu₀ Tmax hTmax u v hsol htrace
    have hbounded :=
      IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
        p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
    exact ⟨Tmax, hTmax, u, v, hsol, htrace, hbounded⟩
  · intro hm_ge u₀ hu₀
    obtain ⟨Tmax, hTmax, u, v, hsol, htrace⟩ := hlocal u₀ hu₀
    have hbootstrap :=
      hstrongBootstrap ha hb hm_pos hstrong
        u₀ hu₀ Tmax hTmax u v hsol htrace
    have hboundedBefore :=
      IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
        p hCor21 hProp25 hu₀ hTmax hsol htrace hbootstrap
    have hglobal :=
      hglobalExtension u₀ hu₀ Tmax hTmax u v hsol htrace
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
    obtain ⟨T₀, M, hM⟩ :=
      hstrongEventualSupBound ha hb hm_pos hstrong hm_ge
        u₀ hu₀ u v hglobal htrace hbootstrapAll
    have hbounded : IsPaper2Bounded intervalDomain u :=
      IsPaper2Bounded.of_forall_ge_supNorm_le
        (D := intervalDomain) (u := u) (T := T₀) (M := M) hM
    exact ⟨u, v, hglobal, htrace, hbounded⟩

/-- Eventual-sup variant of Theorem 1.3 with the `m > 0` guard removed from
the strong-logistic frontiers.

This is the local/global version: it uses only the two Cauchy-theory fields
needed by H2.3, not the full `IntervalDomainExistence` package. -/
theorem Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongEventualSupBound :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_of_local_global_and_eventual_sup_bound
    p C hCor21 hProp25 hlocal hglobalExtension
    (fun ha hb _hm_pos hstrong =>
      hstrongBootstrap ha hb hstrong)
    (fun ha hb _hm_pos hstrong hm_ge =>
      hstrongEventualSupBound ha hb hstrong hm_ge)

/-- Existence-package variant of
`Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound`.

The proof uses only `localExistence` and `globalExtension`; the remaining
existence-package fields are not part of the H2.3 assembly. -/
theorem Theorem_1_3_intervalDomain_of_parameter_m_pos_eventual_sup_bound_and_existence
    (p : CM2Params) (C : Paper2Constants p)
    (hCor21 : Corollary_2_1 intervalDomain p)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hexist : IntervalDomainTheorem11.IntervalDomainExistence p)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongEventualSupBound :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
    p C hCor21 hProp25 hexist.localExistence hexist.globalExtension
    hstrongBootstrap hstrongEventualSupBound

/-- Theorem 1.3 assembly from `Lemma_2_6` plus the PDE energy derivation,
with the `m > 0` branch guard discharged and long-time boundedness supplied as
an eventual sup-norm estimate.

This removes `Corollary_2_1 intervalDomain p` as an input while keeping the
genuine H1/Tier-2 frontiers explicit. -/
theorem Theorem_1_3_intervalDomain_of_Lemma_2_6_energy_parameter_m_pos_and_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
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
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongEventualSupBound :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    ShenWork.Paper2.IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hLemma26 hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongEventualSupBound

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
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
  exact Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongGlobalBound

/-- Variant of `Theorem_1_3_intervalDomain` that derives Corollary 2.1 from
`Lemma_2_6 intervalDomain` and the explicit PDE energy derivation before
assembling the full strong-logistic theorem. -/
theorem Theorem_1_3_intervalDomain_of_Lemma_2_6_and_energy
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
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
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
  exact Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongGlobalBound

/-- Variant of `Theorem_1_3_intervalDomain` that discharges both composed
frontiers: Corollary 2.1 is obtained from `Lemma_2_6` plus the PDE energy
derivation, and global boundedness is obtained from an eventual sup-norm
estimate. -/
theorem Theorem_1_3_intervalDomain_of_Lemma_2_6_energy_and_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
    (S : SemigroupEstimateData intervalDomain)
    (_hLemma21 : Lemma_2_1 intervalDomain p S)
    (hLemma26 : Lemma_2_6 intervalDomain)
    (_hLemma41 : Lemma_4_1 intervalDomain p)
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
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
    (hstrongEventualSupBound :
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    ShenWork.Paper2.IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hLemma26 hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain_of_local_global_and_eventual_sup_bound
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongEventualSupBound

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
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
    p C S hLemma21 hLemma26 hLemma41 hCor21 hProp25 hlocal hglobalExtension
    hstrongBootstrap hstrongGlobalBound

/-- Full interval-domain Theorem 1.3 assembly from the mass-gradient Moser
frontier plus an eventual sup-norm long-time estimate.

This non-vacuous H2.3 wrapper does not take `Corollary_2_1` or
`IsPaper2Bounded` as inputs.  The remaining explicit frontiers are the
mass-gradient Moser hypotheses, the PDE energy derivation, `Proposition_2_5`,
interval local/global extension, the strong-logistic bootstrap seed, and the
eventual sup-norm estimate. -/
theorem Theorem_1_3_intervalDomain_of_mass_gradient_frontier_and_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
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
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
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
    (hstrongEventualSupBound :
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  have hLemma26 : Lemma_2_6 intervalDomain :=
    IntervalDomainTheorem11Composite.Lemma_2_6_intervalDomain_of_mass_gradient_frontier
      cGrad hdiss hcGrad hMG hgrad hmass hu_nonneg hpow_int
  have hCor21 : Corollary_2_1 intervalDomain p :=
    ShenWork.Paper2.IntervalDomainCorollary21.Corollary_2_1_intervalDomain_of_Lemma_2_6_and_energy
      p hLemma26 hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain_of_local_global_and_eventual_sup_bound
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongEventualSupBound

open ShenWork.Paper2.IntervalDomainTheorem11Composite in
/-- Theorem 1.3 assembly from the mass-gradient frontier with endpoint-free
nonnegativity.

This is the same strong-logistic/eventual-sup route as
`Theorem_1_3_intervalDomain_of_mass_gradient_frontier_and_eventual_sup_bound`,
but the H1.2/H1.4 Moser input only asks for nonnegativity on
`intervalDomain.inside`.  The endpoint values do not enter the interval
integrals used by the finite-interval Lp monotonicity step.  The remaining
inputs are still honest analytic frontiers: dissipation, the chain-rule
gradient comparison, mass control, integrability, Cauchy/global extension,
strong-logistic bootstrap, and eventual sup-norm boundedness. -/
theorem Theorem_1_3_intervalDomain_of_mass_gradient_frontier_inside_nonneg_and_eventual_sup_bound
    (p : CM2Params) (C : Paper2Constants p)
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
          LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hProp25 : Proposition_2_5 intervalDomain p)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongEventualSupBound :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    Corollary_2_1_intervalDomain_of_mass_gradient_frontier_inside_nonneg
      p cGrad hdiss hcGrad hMG hgrad hmass hu_inside_nonneg hpow_int
      hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongEventualSupBound

open ShenWork.Paper2.IntervalDomainTheorem11Composite in
/-- Sharpened Theorem 1.3 assembly from the interpolation frontier and
classical-solution positivity.

Compared with
`Theorem_1_3_intervalDomain_of_mass_gradient_frontier_inside_nonneg_and_eventual_sup_bound`,
this removes the standalone mass-gradient interpolation input and the
nonnegativity frontier. They are discharged by
`Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity`.
The remaining hypotheses are the honest PDE energy/dissipation, chain-rule,
mass-control, integrability, Cauchy/global extension, strong-logistic
bootstrap, and eventual sup-norm frontiers. -/
theorem Theorem_1_3_intervalDomain_of_interpolation_frontier_solution_positivity
    (p : CM2Params) (C : Paper2Constants p)
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
    (hglobalExtension :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ Tmax > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p Tmax u v →
        InitialTrace intervalDomain u₀ u →
          IsPaper2BoundedBefore intervalDomain Tmax u →
            1 ≤ p.m →
              IsPaper2GlobalClassicalSolution intervalDomain p u v)
    (hstrongBootstrap :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∃ rho > 0,
            CrossDiffusionBootstrapEstimate intervalDomain p T rho u v ∧
              ∃ p0 > max 1 (rho * (p.N : ℝ) / 2),
                LpPowerBoundedBefore intervalDomain p0 T u)
    (hstrongEventualSupBound :
      0 < p.a → 0 < p.b → StrongLogisticCondition p C →
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
          ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    Theorem_1_3 intervalDomain p C := by
  have hCor21 : Corollary_2_1 intervalDomain p :=
    Corollary_2_1_intervalDomain_of_interpolation_frontier_from_solution_positivity
      p hGN cGrad hdiss hcGrad hgrad hmass hpow_int hEnergyFromCrossDiffusion
  exact Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
    p C hCor21 hProp25 hlocal hglobalExtension hstrongBootstrap
    hstrongEventualSupBound

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

/-- Vacuous interval-domain Theorem 1.3 branch when the strict `a > 0`
hypothesis is unavailable. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_not_a_pos
    (p : CM2Params) (ha : ¬ 0 < p.a) (C : Paper2Constants p) :
    Theorem_1_3 intervalDomain p C := by
  have ha_zero : p.a = 0 := le_antisymm (not_lt.mp ha) p.ha
  exact Theorem_1_3_intervalDomain_vacuous_when_a_zero p ha_zero C

/-- Vacuous interval-domain Theorem 1.3 branch when the strict `b > 0`
hypothesis is unavailable. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_not_b_pos
    (p : CM2Params) (hb : ¬ 0 < p.b) (C : Paper2Constants p) :
    Theorem_1_3 intervalDomain p C := by
  have hb_zero : p.b = 0 := le_antisymm (not_lt.mp hb) p.hb
  exact Theorem_1_3_intervalDomain_vacuous_when_b_zero p hb_zero C

/-- Vacuous interval-domain Theorem 1.3 branch when the strict `m > 0`
hypothesis is unavailable. -/
theorem Theorem_1_3_intervalDomain_vacuous_when_not_m_pos
    (p : CM2Params) (hm : ¬ 0 < p.m) (C : Paper2Constants p) :
    Theorem_1_3 intervalDomain p C :=
  Theorem_1_3_intervalDomain_vacuous_when_m_le_zero p (not_lt.mp hm) C

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
