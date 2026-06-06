/-
  Bridge: `ThresholdQuantitativeLocalExistence` from the
  threshold-uniform Picard horizon + the abstract restart frontier.

  ## Chain

  `thresholdMildExistenceData_exists` (IntervalMildPicardThreshold)
  gives, for each `(M, c)`, ONE horizon `δ(p, M, c) > 0` and for each
  datum in the threshold class a packaged Picard mild solution with
  `D.T = δ`.  The abstract restart frontier package
  (`GradientMildHalfStepRestartData` + initial approach +
  `GradientMildClassicalFrontierCoreData`) upgrades the mild solution
  to a CLASSICAL solution at the explicit horizon `D.T` via the proved
  regularity bootstrap; restriction gives the threshold factory.

  ## Residual

  `PicardRestartFrontier p` — the restart frontier package for the
  canonical Picard-limit solutions (`gradientMildSolutionData_of_data E`,
  whose `u` is `picardLimit p u₀ E.T` BY CONSTRUCTION).  This is the
  same content as the hMildLocal frontier (F2 / S-construction): the
  S-construction builds the restart source data from the Picard
  ITERATES' convergence, so it applies to the canonical Picard limit at
  any valid horizon — quantifying over `E` (rather than existentially
  choosing it) does not add strength beyond uniformity in the horizon,
  which the iterate estimates carry.

  ## Output

  * `classicalSolution_at_horizon` — horizon-EXPLICIT classical bridge.
  * `thresholdQuantitativeLocalExistence_of_factory` — threshold factory
    from the bundled per-datum data.
  * `thresholdRestartFrontierFactory_of_picardFrontier` — discharges the
    Picard-data half via `thresholdMildExistenceData_exists`.
  * `quantitativeLocalExistence_of_picardFrontier_persistence` — the
    Q-line assembly: hQuant from
    `PicardRestartFrontier` + `ClassicalMinPersistence` + `hlocal`
    (+ regime + α ≥ 1).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainQuantFromThreshold
import ShenWork.Paper2.IntervalMildPicardThreshold
import ShenWork.Paper2.IntervalDomainRestartLocalWiring

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardThreshold
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalMildToLocalExistence
open ShenWork.Paper2
open ShenWork.Paper2.QuantFromThreshold

noncomputable section

namespace ShenWork.Paper2.ThresholdQuantBridge

/-! ## Horizon-explicit classical bridge -/

/-- Classical solution at the EXPLICIT horizon `D.T` from the abstract
restart frontier package.  Horizon-explicit variant of
`localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore`
(which only exposes `∃ Tmax > 0`). -/
theorem classicalSolution_at_horizon
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (R : GradientMildHalfStepRestartData D)
    (hInitialApproach : ∀ ε, 0 < ε →
      ∃ δ > 0, ∀ t, 0 < t → t < δ →
        ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε)
    (hCore : GradientMildClassicalFrontierCoreData p D) :
    ∃ v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p D.T D.u v ∧
      InitialTrace intervalDomain u₀ D.u := by
  have hreg : RegularityBootstrap p D.T u₀ D.u :=
    regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
      p D R hInitialApproach hCore
  obtain ⟨v, hpos, hvnn, hpde_u, hpde_v, hbc, hclassreg, htrace⟩ := hreg
  exact ⟨v,
    IsPaper2ClassicalSolution.of_components D.hT hclassreg hpos hvnn
      hpde_u hpde_v hbc,
    htrace⟩

/-! ## The threshold factory from bundled per-datum data -/

/-- Threshold restart-frontier factory: per `(M, c)` a uniform horizon
`δ` and, per datum in the threshold class, Picard data with `δ ≤ D.T`
PLUS the abstract restart frontier package for that data. -/
def ThresholdRestartFrontierFactory (p : CM2Params) : Prop :=
  ∀ M c : ℝ, 0 < M → 0 < c → ∃ δ : ℝ, 0 < δ ∧
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
      (∀ x, c ≤ u₀ x) →
      ∃ D : GradientMildSolutionData p u₀, δ ≤ D.T ∧
        ∃ _R : GradientMildHalfStepRestartData D,
          (∀ ε, 0 < ε →
            ∃ δ' > 0, ∀ t, 0 < t → t < δ' →
              ∀ x : intervalDomainPoint,
                |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
          GradientMildClassicalFrontierCoreData p D

/-- **ThresholdQuantitativeLocalExistence from the factory.** -/
theorem thresholdQuantitativeLocalExistence_of_factory
    (p : CM2Params)
    (hTF : ThresholdRestartFrontierFactory p) :
    ThresholdQuantitativeLocalExistence p := by
  intro M c hM hc
  obtain ⟨δ, hδ, h⟩ := hTF M c hM hc
  refine ⟨δ, hδ, ?_⟩
  intro w hw hbw hlw
  obtain ⟨D, hδT, R, happroach, hCore⟩ := h w hw hbw hlw
  obtain ⟨v, hsol, htrace⟩ :=
    classicalSolution_at_horizon p D R happroach hCore
  exact ⟨D.u, v, hsol.restrict_horizon hδ hδT, htrace⟩

/-! ## Discharging the Picard-data half -/

/-- **Residual frontier: restart package for the canonical Picard-limit
solutions.**  For `gradientMildSolutionData_of_data E` the solution
field is `picardLimit p u₀ E.T` by construction, so this quantifies the
F2/S-construction target over the admissible Picard horizons. -/
def PicardRestartFrontier (p : CM2Params) : Prop :=
  ∀ (u₀ : intervalDomainPoint → ℝ),
    PositiveInitialDatum intervalDomain u₀ →
  ∀ (E : MildExistenceData p u₀),
    ∃ _R : GradientMildHalfStepRestartData
        (gradientMildSolutionData_of_data E),
      (∀ ε, 0 < ε →
        ∃ δ' > 0, ∀ t, 0 < t → t < δ' →
          ∀ x : intervalDomainPoint,
            |intervalGradientDuhamelMap p u₀
              (gradientMildSolutionData_of_data E).u t x - u₀ x| < ε) ∧
      GradientMildClassicalFrontierCoreData p
        (gradientMildSolutionData_of_data E)

/-- **The factory from the threshold-uniform Picard horizon +
`PicardRestartFrontier`.**  The Picard half is PROVED
(`thresholdMildExistenceData_exists`); only the frontier half remains. -/
theorem thresholdRestartFrontierFactory_of_picardFrontier
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    (hPF : PicardRestartFrontier p) :
    ThresholdRestartFrontierFactory p := by
  intro M c hM hc
  obtain ⟨δ, hδ, h⟩ :=
    thresholdMildExistenceData_exists p hM hc hα_ge hγ_ge
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hu₀ hb hl
  obtain ⟨E, hET⟩ := h u₀ hu₀.admissible.2 hb hl
  obtain ⟨R, happ, hcore⟩ := hPF u₀ hu₀ E
  refine ⟨gradientMildSolutionData_of_data E, ?_, R, happ, hcore⟩
  rw [gradientMildSolutionData_of_data_T, hET]

/-! ## Q-line assembly -/

/-- **ThresholdQuantitativeLocalExistence from
`PicardRestartFrontier`.** -/
theorem thresholdQuantitativeLocalExistence_of_picardFrontier
    (p : CM2Params) (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ)
    (hPF : PicardRestartFrontier p) :
    ThresholdQuantitativeLocalExistence p :=
  thresholdQuantitativeLocalExistence_of_factory p
    (thresholdRestartFrontierFactory_of_picardFrontier p hα_ge hγ_ge hPF)

/-- **hQuant from `PicardRestartFrontier` + `ClassicalMinPersistence` +
`hlocal` (+ regime + α ≥ 1).**

The Q-line assembly: the Picard contraction half of hQuant is proved
(threshold-uniform horizon `δ(M, c)`); the residual is
* `hPF` — restart frontier for the canonical Picard solutions
  (= F2/S-construction, shared with the hMildLocal frontier),
* `hPersist` — quantitative strong minimum principle,
* `hlocal` — per-datum classical local existence (shared frontier). -/
theorem quantitativeLocalExistence_of_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : PicardRestartFrontier p)
    (hPersist : ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u :=
  quantitativeLocalExistence_of_threshold_persistence_seed' p hχ ha hb
    hγ_ge_one
    (thresholdQuantitativeLocalExistence_of_picardFrontier p hα_ge
      hγ_ge_one hPF)
    hPersist hlocal

/-- **Paper 2 Theorem 1.1 from regime + α ≥ 1 +
`PicardRestartFrontier` + `ClassicalMinPersistence` + `hlocal`.**

End-to-end: compared with `paper2_theorem_1_1_from_quant_and_hlocal`,
the hQuant hypothesis is replaced by its proved Picard-contraction core
plus the two genuine residuals (restart frontier for the Picard
solutions; quantitative minimum principle). -/
theorem paper2_theorem_1_1_of_picardFrontier_persistence
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα_ge : 1 ≤ p.α) (hγ_ge_one : 1 ≤ p.γ)
    (hPF : PicardRestartFrontier p)
    (hPersist : ClassicalMinPersistence p)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  RestartLocalWiring.paper2_theorem_1_1_from_quant_and_hlocal
    p hχ ha hb hγ_ge_one
    (quantitativeLocalExistence_of_picardFrontier_persistence
      p hχ ha hb hα_ge hγ_ge_one hPF hPersist hlocal)
    hlocal

end ShenWork.Paper2.ThresholdQuantBridge
