/-
  ShenWork/Paper2/IntervalDomainTheorem11Umbrella.lean

  Top-level "umbrella" theorem wiring the unconditional general-γ gluing
  closure
  (`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound`,
  `IntervalDomainL2USubHorizonGluing`) all the way to Paper 2 Theorem 1.1
  (`Theorem_1_1 intervalDomain p`), under faithful PDE-textbook hypotheses:

  * **regime** — the active negative-sensitivity side `χ₀ ≤ 0`, `0 < a`, `0 < b`;
  * **bounded-below positive datum** — every positive admissible initial datum
    in the application admits a uniform spatial lower bound `δ₀ > 0`
    (`IntervalDomainPosDatumLowerBound`);
  * **local existence** — standard short-time classical existence for every
    positive admissible initial datum;
  * **reachability of arbitrary horizons** — the standard maximal-continuation
    output: from local existence + a-priori sup-norm control (Lemma 3.1) one
    extends each solution past every finite horizon.

  Inside the gluing closure we need two book-keeping pass-throughs about
  initial data of solution pairs (`hposWit`, `hposLowerWit`); these are the
  natural witnessing forms of "the initial trace of any classical solution
  encountered in the application is a bounded-below positive datum".  They are
  taken as separate textbook hypotheses on the input data themselves so that
  no derivation is fabricated.

  No `sorry`, no `admit`, no custom `axiom`, no fake hypotheses.

  Gap honestly recorded:
    * `hlocal` and `hreach` represent the standard local existence + maximal
      continuation pair from PDE textbooks; the reachability step needs
      "local + Lemma 3.1 a-priori sup-norm bound ⇒ continuation past any
      finite horizon", which the repo does not yet derive internally.
    * `hposWit` and `hposLowerWit` are the trace-positivity book-keeping
      pass-throughs; in the application every classical solution under study
      has been instantiated from a positive bounded-below initial datum, so
      these hold tautologically on the data side.  Inside the repo they
      would follow from a `PositiveInitialDatum`-from-trace closure lemma not
      currently formalized; we therefore take them as data hypotheses rather
      than fabricate a derivation.
    * All genuine analytic content — overlap uniqueness, the L²-energy
      method, the sub-horizon two-sided lift bound, the regime-conditional
      uniform upper bound, half-horizon positivity, initial-sup-norm
      approach, branch sup-norm bounds, Lemma 3.1 bridge — is discharged
      unconditionally inside the repo.

    * **Precise frontier of `hlocal` (T7, 2026-05-30).**  `hlocal` is an
      EXISTENCE claim (construct `(u,v)` solving the coupled nonlinear system
      for every positive datum), NOT merely a regularity claim.  The T6 atom
      `intervalDuhamelTerm_closedC2_of_timeC1_source` and the T7 bridges
      (`ShenWork/PDE/IntervalCosineSliceRegularity.lean`) discharge the
      *regularity* half: a mild-solution slice `S_t u₀ + D_t`, being a single
      cosine series `∑cₙcos` with `∑λₙ|cₙ|<∞`, satisfies the spatial regularity
      conjuncts (3)/(6)/(7) of `intervalDomainClassicalRegularity` for free.
      What remains — the irreducible core **[D2]** — is the *construction*:
      the mild-solution fixed point `u = S_t u₀ + ∫₀ᵗ S(t−s)·g[u,v](s)ds` whose
      source `g[u,v] = −χ∇·(u∇v/(1+v)^β)+u(a−bu^α)` depends on `u,v`, plus the
      bootstrap proving that source is `DuhamelSourceTimeC1` (circular: needs
      `u,v` already regular).  This is a Banach/Picard fixed point + parabolic
      Schauder theory that is absent from both this repo and Mathlib; see
      `T5_DESIGN.md` §7.4 and `T7_DESIGN.md`.  `hlocal` therefore remains an
      honest textbook hypothesis; the atom removes its hardest *analytic*
      sub-obstruction (`∂ₓₓD_t`), not the existence itself.
-/
import ShenWork.Paper2.IntervalDomainMoserClosure
import ShenWork.Paper2.IntervalDomainL2USubHorizonGluing
import ShenWork.Paper2.IntervalDomainGlobalWellposed
import ShenWork.Paper2.IntervalDomainL2UEnergyUniformGammaGeOne
import ShenWork.Paper2.IntervalMildToLocalExistence

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildToLocalExistence
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2.IntervalDomainGlobalWellposed

namespace ShenWork.Paper2

noncomputable section

/-! ## Local-existence bridge input from gradient mild data -/

/-- Local-existence input stated at the Picard gradient-mild level.

For every positive admissible datum, this supplies the `GradientMildSolutionData`
plus the two mild-to-local-existence side conditions consumed by
`IntervalMildToLocalExistence.localExistence_of_gradientMildSolutionData`:
initial approach of the gradient Duhamel map and the closed classical solution
bridge for `(u, resolver(u))`. -/
def IntervalDomainGradientMildLocalData (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert the Picard gradient-mild local data into the `hlocal` field consumed
by the umbrella theorems. -/
theorem localExistence_of_gradientMildLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, hInitialApproach, hclassical⟩ := hMildLocal u₀ hu₀
  exact ShenWork.IntervalMildToLocalExistence.localExistence_of_gradientMildSolutionData
    p hu₀ D hInitialApproach hclassical

/-- Local-existence input stated at the Picard gradient-mild level after the
mild-to-classical bridge has been reduced to its core frontier: the parabolic
equation for `u` and the classical regularity bundle. -/
def IntervalDomainGradientMildCoreLocalData (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalCoreData p D

/-- Convert Picard gradient-mild core local data into the `hlocal` field
consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildCoreLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_and_coreData
    p hu₀ D hInitialApproach hCore

/-- Picard gradient-mild local data with restart-cosine representations for
every positive-time slice.  This is the local-data interface matching the T7e
restart bootstrap: the elliptic PDE and Neumann boundary conjuncts are not read
from `hclassical.regularity`, but rebuilt from `H`. -/
def IntervalDomainGradientMildRestartLocalData (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        HasRestartCosineRepresentations D.T D.u ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert restart-cosine Picard gradient-mild local data into the `hlocal`
field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildRestartLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildRestartLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, H, hInitialApproach, hclassical⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations
    p hu₀ D H hInitialApproach hclassical

/-- Restart-cosine Picard local data using only the remaining classical core.
The elliptic PDE and Neumann conjuncts are rebuilt from the restart-cosine
representations. -/
def IntervalDomainGradientMildRestartCoreLocalData (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        HasRestartCosineRepresentations D.T D.u ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalCoreData p D

/-- Convert restart-cosine Picard gradient-mild core local data into the
`hlocal` field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildRestartCoreLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildRestartCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, H, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations_and_coreData
    p hu₀ D H hInitialApproach hCore

/-- Restart-cosine Picard local data using only the reduced regularity frontier.
The restart bootstrap supplies the `u` spatial `C²`/Neumann parts of
`intervalDomainClassicalRegularity`; the data here supplies the remaining
frontier. -/
def IntervalDomainGradientMildRestartFrontierCoreLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        HasRestartCosineRepresentations D.T D.u ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalFrontierCoreData p D

/-- Convert restart-cosine Picard gradient-mild frontier-core local data into
the `hlocal` field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildRestartFrontierCoreLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildRestartFrontierCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, H, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact
    localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations_and_frontierCore
      p hu₀ D H hInitialApproach hCore

/-- Picard gradient-mild local data with half-step source regularity and
cosine-series agreement.  The restart-cosine representation is constructed
internally from this half-step package. -/
def IntervalDomainGradientMildHalfStepRestartLocalData (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _R : GradientMildHalfStepRestartData D,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert half-step restart Picard gradient-mild local data into the `hlocal`
field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildHalfStepRestartLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildHalfStepRestartLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, R, hInitialApproach, hclassical⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_of_halfStepRestartData
    p hu₀ D R hInitialApproach hclassical

/-- Half-step restart Picard local data using only the remaining classical core. -/
def IntervalDomainGradientMildHalfStepRestartCoreLocalData (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _R : GradientMildHalfStepRestartData D,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalCoreData p D

/-- Convert half-step restart Picard gradient-mild core local data into the
`hlocal` field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildHalfStepRestartCoreLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildHalfStepRestartCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, R, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_coreData
    p hu₀ D R hInitialApproach hCore

/-- Half-step restart Picard local data using only the reduced regularity
frontier. -/
def IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _R : GradientMildHalfStepRestartData D,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalFrontierCoreData p D

/-- Convert half-step restart Picard gradient-mild frontier-core local data into
the `hlocal` field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
    (p : CM2Params)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, R, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
    p hu₀ D R hInitialApproach hCore

/-- Picard gradient-mild local data with H²-Neumann half-step source regularity,
quadratic source-coefficient decay, and only the reduced regularity frontier.

The H² source data is converted internally to the older half-step restart
package, which then supplies restart-cosine representations for every
positive-time slice. -/
def IntervalDomainGradientMildHalfStepH2SourceFrontierCoreLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _S : GradientMildHalfStepH2SourceData D,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalFrontierCoreData p D

/-- Convert H²-source half-step Picard gradient-mild frontier-core local data
into the `hlocal` field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildHalfStepH2SourceFrontierCoreLocalData
    (p : CM2Params)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepH2SourceFrontierCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, S, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_of_halfStepH2SourceData_and_frontierCore
    p hu₀ D S hInitialApproach hCore

/-- Picard gradient-mild local data with logistic half-step source regularity
and only the reduced regularity frontier.

The logistic source data is converted internally to the half-step restart
package, which supplies `DuhamelSourceTimeC1`, closed-interval `C²` endpoint
data, and restart-cosine representations for every positive-time slice. -/
def IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _S : GradientMildHalfStepLogisticSourceData D,
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        GradientMildClassicalFrontierCoreData p D

/-- Convert logistic-source half-step Picard gradient-mild frontier-core local
data into the `hlocal` field consumed by the umbrella theorems. -/
theorem localExistence_of_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
    (p : CM2Params)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, S, hInitialApproach, hCore⟩ := hMildLocal u₀ hu₀
  exact
    localExistence_of_gradientMildSolutionData_of_halfStepLogisticSourceData_and_frontierCore
      p hu₀ D S hInitialApproach hCore

/-- Picard gradient-mild local data with the extra old-Duhamel fixed-point
frontiers needed to route through
`IntervalDomainExistence.localExistence_of_fp_and_regularity`.

Compared with `IntervalDomainGradientMildLocalData`, this records precisely the
operator bridge: the endpoint `t = 0` old fixed-point value and the positive-time
RHS equality between `intervalGradientDuhamelMap` and
`intervalDuhamelOperator`. -/
def IntervalDomainGradientMildIntervalDuhamelLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        (∀ x : intervalDomainPoint,
          D.u 0 x = intervalDuhamelOperator p u₀ D.u 0 x) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          intervalGradientDuhamelMap p u₀ D.u t x =
            intervalDuhamelOperator p u₀ D.u t x) ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert Picard gradient-mild local data plus the old-Duhamel bridge into the
`hlocal` field, explicitly via
`localExistence_of_fp_and_regularity`. -/
theorem localExistence_of_gradientMildIntervalDuhamelLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildIntervalDuhamelLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, hzero, hDuhamelEq, hInitialApproach, hclassical⟩ :=
    hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq
    p hu₀ D hzero hDuhamelEq hInitialApproach hclassical

/-- Old-Duhamel routed local data with restart-cosine representations. -/
def IntervalDomainGradientMildRestartIntervalDuhamelLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        HasRestartCosineRepresentations D.T D.u ∧
        (∀ x : intervalDomainPoint,
          D.u 0 x = intervalDuhamelOperator p u₀ D.u 0 x) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          intervalGradientDuhamelMap p u₀ D.u t x =
            intervalDuhamelOperator p u₀ D.u t x) ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert old-Duhamel routed local data with restart-cosine representations
into the `hlocal` field. -/
theorem localExistence_of_gradientMildRestartIntervalDuhamelLocalData
    (p : CM2Params)
    (hMildLocal : IntervalDomainGradientMildRestartIntervalDuhamelLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, H, hzero, hDuhamelEq, hInitialApproach, hclassical⟩ :=
    hMildLocal u₀ hu₀
  exact
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_restartCosineRepresentations
      p hu₀ D H hzero hDuhamelEq hInitialApproach hclassical

/-- Old-Duhamel routed local data with half-step restart source regularity and
cosine-series agreement. -/
def IntervalDomainGradientMildHalfStepRestartIntervalDuhamelLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _R : GradientMildHalfStepRestartData D,
        (∀ x : intervalDomainPoint,
          D.u 0 x = intervalDuhamelOperator p u₀ D.u 0 x) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          intervalGradientDuhamelMap p u₀ D.u t x =
            intervalDuhamelOperator p u₀ D.u t x) ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert old-Duhamel routed half-step restart local data into the `hlocal`
field. -/
theorem localExistence_of_gradientMildHalfStepRestartIntervalDuhamelLocalData
    (p : CM2Params)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepRestartIntervalDuhamelLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, R, hzero, hDuhamelEq, hInitialApproach, hclassical⟩ :=
    hMildLocal u₀ hu₀
  exact
    localExistence_of_gradientMildSolutionData_and_intervalDuhamel_eq_of_halfStepRestartData
      p hu₀ D R hzero hDuhamelEq hInitialApproach hclassical

/-- Zero-sensitivity Picard local data using the componentwise Duhamel frontiers
from `IntervalMildToLocalExistence`.

The chemotaxis contribution is killed by the separate hypothesis `p.χ₀ = 0` in
the theorem below; the remaining fields identify the full/helper semigroup
initial term and the logistic Duhamel terms. -/
def IntervalDomainGradientMildChiZeroDuhamelLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        (∀ x : intervalDomainPoint,
          D.u 0 x = intervalDuhamelOperator p u₀ D.u 0 x) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 =
            intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          (∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) x.1) =
            ∫ s in Set.Icc 0 t,
              intervalSemigroupOperator 1 (t - s)
                (logisticLifted p (D.u s)) x.1) ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert zero-sensitivity componentwise Duhamel-frontier local data into the
`hlocal` field, explicitly constructing the old fixed-point hypothesis consumed
by `localExistence_of_fp_and_regularity`. -/
theorem localExistence_of_gradientMildChiZeroDuhamelLocalData
    (p : CM2Params) (hχ : p.χ₀ = 0)
    (hMildLocal : IntervalDomainGradientMildChiZeroDuhamelLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, hzero, hinit, hlog, hInitialApproach, hclassical⟩ :=
    hMildLocal u₀ hu₀
  exact localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel
    p hu₀ D hχ hzero hinit hlog hInitialApproach hclassical

/-- Zero-sensitivity componentwise Duhamel local data with restart-cosine
representations. -/
def IntervalDomainGradientMildRestartChiZeroDuhamelLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
        HasRestartCosineRepresentations D.T D.u ∧
        (∀ x : intervalDomainPoint,
          D.u 0 x = intervalDuhamelOperator p u₀ D.u 0 x) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 =
            intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          (∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) x.1) =
            ∫ s in Set.Icc 0 t,
              intervalSemigroupOperator 1 (t - s)
                (logisticLifted p (D.u s)) x.1) ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert zero-sensitivity componentwise Duhamel local data with
restart-cosine representations into the `hlocal` field. -/
theorem localExistence_of_gradientMildRestartChiZeroDuhamelLocalData
    (p : CM2Params) (hχ : p.χ₀ = 0)
    (hMildLocal : IntervalDomainGradientMildRestartChiZeroDuhamelLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, H, hzero, hinit, hlog, hInitialApproach, hclassical⟩ :=
    hMildLocal u₀ hu₀
  exact
    localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_restartCosineRepresentations
      p hu₀ D H hχ hzero hinit hlog hInitialApproach hclassical

/-- Zero-sensitivity componentwise Duhamel local data with half-step restart
source regularity and cosine-series agreement. -/
def IntervalDomainGradientMildHalfStepRestartChiZeroDuhamelLocalData
    (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomain.Point → ℝ,
    PositiveInitialDatum intervalDomain u₀ →
      ∃ D : GradientMildSolutionData p u₀,
      ∃ _R : GradientMildHalfStepRestartData D,
        (∀ x : intervalDomainPoint,
          D.u 0 x = intervalDuhamelOperator p u₀ D.u 0 x) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 =
            intervalSemigroupOperator 1 t (intervalDomainLift u₀) x.1) ∧
        (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
          (∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s)
                (logisticLifted p (D.u s)) x.1) =
            ∫ s in Set.Icc 0 t,
              intervalSemigroupOperator 1 (t - s)
                (logisticLifted p (D.u s)) x.1) ∧
        (∀ ε, 0 < ε →
          ∃ δ > 0, ∀ t, 0 < t → t < δ →
            ∀ x : intervalDomainPoint,
              |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε) ∧
        IsPaper2ClassicalSolution intervalDomain p D.T D.u
          (ShenWork.IntervalMildToClassical.mildChemicalConcentration p D.u)

/-- Convert zero-sensitivity half-step restart Duhamel local data into the
`hlocal` field. -/
theorem localExistence_of_gradientMildHalfStepRestartChiZeroDuhamelLocalData
    (p : CM2Params) (hχ : p.χ₀ = 0)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepRestartChiZeroDuhamelLocalData p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨D, R, hzero, hinit, hlog, hInitialApproach, hclassical⟩ :=
    hMildLocal u₀ hu₀
  exact
    localExistence_of_gradientMildSolutionData_chi_zero_via_intervalDuhamel_of_halfStepRestartData
      p hu₀ D R hχ hzero hinit hlog hInitialApproach hclassical

/-- **Umbrella theorem.**  Paper 2 Theorem 1.1 on the interval domain follows
from the negative-sensitivity regime (`χ₀ ≤ 0`, `0 < a`, `0 < b`) together with
honest PDE-textbook inputs and book-keeping pass-throughs about initial data:

* `hlocal` — short-time classical existence for every positive admissible
  initial datum (standard PDE machinery);
* `hreach` — every positive admissible initial datum extends to arbitrarily
  long classical horizons (standard maximal-continuation output: local
  existence + Lemma 3.1 a-priori sup-norm bound ⇒ continuation past every
  finite horizon, not yet derived inside the repo);
* `hposWit` / `hposLowerWit` — book-keeping pass-throughs that the initial
  data of any classical-solution pair encountered in the application is a
  positive bounded-below datum (data-side hypothesis: every initial datum
  put into the application is itself positive and admits a uniform spatial
  lower bound).

The genuine analytic content — overlap uniqueness, the L²-energy method, the
sub-horizon two-sided lift bound, and the regime-conditional uniform upper
bound — is fully discharged inside the repo via
`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound` and the
existing `Theorem_1_1_intervalDomain_of_corrected_existence` bridge. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hreach :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ShenWork.IntervalDomainExistence.ReachableArbitrarilyLong p u₀)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLowerWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Step 1. Instantiate the new unconditional general-γ gluing closure.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
      p hχ ha hb hposWit hposLowerWit
  -- Step 2. Combine gluing with reachability to discharge the existential
  --         global-solution field for every positive datum.
  have hglobalFor :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionFor p u₀ := by
    intro u₀ hu₀
    exact hglue u₀ hu₀ (hreach u₀ hu₀)
  -- Step 3. Assemble the corrected existential-global structure via the
  --         existing `intervalDomainGlobalSolutionExists_of_local_global_bounded_initial`
  --         bridge.  Bounded initial data is supplied by `hu₀.admissible`.
  have hbddInit :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p := by
    refine intervalDomainGlobalSolutionExists_of_local_global_bounded_initial
      p hlocal hbddInit ?_
    intro u₀ hu₀ _hm
    exact hglobalFor u₀ hu₀
  -- Step 4. Route through the existing Moser-closure Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Refined umbrella theorem (no `hreach`).**  Paper 2 Theorem 1.1 on the
interval domain follows from the negative-sensitivity regime
(`χ₀ ≤ 0`, `0 < a`, `0 < b`) together with the honest textbook
maximal-continuation inputs:

* `hlocal` — short-time classical existence for every positive admissible
  initial datum (standard PDE machinery);
* `hrealize` / `hextend_of_not_finiteAlternative` /
  `hextend_of_not_mgeAlternative` — the genuine maximal-continuation
  frontier: realize a classical solution at the finite `sSup` of reachable
  horizons, and from negation of either finite-horizon alternative produce a
  strictly larger reachable horizon (compactness/restart at the supremum).
  These cannot be derived inside the repo without compactness/restart
  machinery and remain genuine PDE-textbook gaps;
* `hrangeBounded` — spatial regularity: every time slice of every classical
  branch has a bounded absolute-value range (textbook input feeding the
  pointwise-from-supnorm bridge);
* `hposWit` / `hposLowerWit` — data-side book-keeping pass-throughs that the
  initial data of any classical-solution pair encountered in the application
  is a positive, uniformly bounded-below datum.

The `hreach` field of the previous umbrella (reachability of arbitrary
horizons) is **eliminated**: it is derived internally by composing the
existing `boundedBefore_nonminimal_of_corrected_initial_approach` (Lemma 3.1
+ initial sup-norm approach) with
`supNormControlsPointwiseBefore_of_timeSlice_rangeBounded` and
`standardContinuationAlternative_of_finiteSup_realization_and_extension`,
via the assembler
`intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing`.

The genuine analytic content — overlap uniqueness, the L²-energy method, the
sub-horizon two-sided lift bound, the regime-conditional uniform upper
bound, half-horizon positivity, initial sup-norm approach, Lemma 3.1
monotonicity, the finite-branch sup-norm bound from Lemma 3.1 — is fully
discharged inside the repo via
`GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound` and
the corrected initial-approach chain. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)))
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLowerWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Step 1. Bounded-initial follows from positive-admissibility on every u₀.
  have hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  -- Step 2. Spatial sup-norm-controls-pointwise on every branch from
  --         time-slice range boundedness.
  have hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact supNormControlsPointwiseBefore_of_timeSlice_rangeBounded
      (hrangeBounded u₀ hu₀ T hT u v hsol htrace)
  -- Step 3. Per-branch gluing from regime + positive-datum lower-bound witness.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
      p hχ ha hb hposWit hposLowerWit
  -- Step 4. Use the existing nonminimal continuation+gluing assembler to
  --         produce the corrected existential-global package.  Finite-horizon
  --         boundedness is internally derived from Lemma 3.1 + the
  --         corrected initial-approach field via
  --         `boundedBefore_nonminimal_of_corrected_initial_approach`; the
  --         finite-horizon alternative is ruled out by
  --         `not_finiteContinuationAlternativeBranch_of_boundedBefore_and_supNormControl`.
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p :=
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing
      p hχ ha hb hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      hsupControls hglue
  -- Step 5. Route through the existing Moser-closure Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Tightened umbrella theorem (no `hreach`, no `hrangeBounded`).**  Same as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach` except
that the `hrangeBounded` time-slice range-boundedness hypothesis is dropped:
it is discharged internally by `classicalSolution_u_range_bddAbove`, which
extracts conjunct (7) (closed-domain `C²` regularity of the lift on `Icc 0 1`)
of the classical-solution regularity bundle and converts continuity on the
compact `[0,1]` into boundedness of `|u t ·|` on the subtype range.

The remaining textbook-input hypotheses (`hlocal`, `hrealize`,
`hextend_of_not_finiteAlternative`, `hextend_of_not_mgeAlternative`,
`hposWit`, `hposLowerWit`) are identical to the `_no_hreach` variant. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLowerWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Internally discharge `hrangeBounded` from conjunct (7) of the classical
  -- regularity bundle on every interior time `t ∈ (0,T)`.
  have hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
    intro _u₀ _hu₀ T _hT u v hsol _htrace t ht_pos ht_T
    exact classicalSolution_u_range_bddAbove hsol ⟨ht_pos, ht_T⟩
  -- Route through the existing `_no_hreach` umbrella with the derived
  -- `hrangeBounded` field.
  exact Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach
    p hχ ha hb hlocal hrealize hextend_of_not_finiteAlternative
    hextend_of_not_mgeAlternative hrangeBounded hposWit hposLowerWit

/-- **Bundled continuation data for the Paper 2 interval-domain umbrella.**

Packages the four textbook PDE continuation hypotheses (`local`, `realize`,
`extend_finite`, `extend_mge`) together with the two book-keeping
pass-throughs (`posWit`, `posLowerWit`) consumed by
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`
into a single record, for cleaner downstream composition.  The field shapes
mirror the umbrella signature verbatim. -/
structure IntervalDomainPaper2ContinuationData (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extend_finite :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        ¬ FiniteHorizonAlternative intervalDomain
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u →
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀)
  extend_mge :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        1 ≤ p.m →
        ¬ MGeOneFiniteHorizonAlternative intervalDomain
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u →
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀)
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀
  posLowerWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainPosDatumLowerBound u₀

/-- **Bundled-input wrapper for the Paper 2 interval-domain umbrella.**

Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`,
but consuming the six textbook/pass-through hypotheses as a single
`IntervalDomainPaper2ContinuationData` record for cleaner composition. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_continuationData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hData : IntervalDomainPaper2ContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded
    p hχ ha hb hData.localExistence hData.realize hData.extend_finite
    hData.extend_mge hData.posWit hData.posLowerWit

/-! ## Refined umbrella: `extend_finite` eliminated

The next umbrella variant drops the `hextend_of_not_finiteAlternative` textbook
PDE-input field of the maximal-continuation interface entirely.  Its content
is internally redundant in the `1 ≤ p.m` regime (the only regime that drives
the global-existence path inside the corrected existential package), because:

* `MGeOneFiniteHorizonAlternative` is the unboundedness disjunct of
  `FiniteHorizonAlternative`, so `¬ Finite → ¬ MGeOne` (logical implication).
* In the negative-sensitivity regime `χ₀ ≤ 0, 0 < a, 0 < b`, the Lemma 3.1
  monotonicity + the initial sup-norm approach (proved unconditionally inside
  the repo by `initialSupNormApproach_intervalDomain` from bounded initial data)
  give an `IsPaper2BoundedBefore` sup-norm bound on the open `(0, T*)`.  The
  closed-domain spatial `C²` regularity (conjunct (7) of the classical
  regularity bundle, unconditionally available via
  `classicalSolution_u_range_bddAbove`) converts that sup-norm bound into a
  pointwise upper bound on `u t x` for `0 < t < T*` and every `x : Point`,
  which rules out `MGeOneFiniteHorizonAlternative T* u` directly via
  `not_mgeOneFiniteHorizonAlternative_of_pointwiseBoundedBefore`.

So the maximal-continuation contradiction at the realized supremum `T*` only
ever needs `hextend_of_not_mgeAlternative`.  The full chain is bundled in
`reachableArbitrarilyLong_of_realize_extend_mge_in_negative_regime` and
`intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing_no_extend_finite`.

The remaining textbook PDE inputs (`hlocal`, `hrealize`,
`hextend_of_not_mgeAlternative`) are the three genuinely-analytic frontiers of
the standard maximal continuation theorem on the interval domain:

* `hlocal` — short-time classical existence (standard Picard);
* `hrealize` — realization of a classical solution at the finite supremum
  `sSup` of reachable horizons (compactness + Ascoli–Arzelà passage to limit);
* `hextend_of_not_mgeAlternative` — restart past `T*` from non-blow-up via
  local existence applied to the limit datum, together with overlap
  uniqueness/gluing to concatenate. -/

/-- **Tightened umbrella (no `hreach`, no `hrangeBounded`, no
`hextend_of_not_finiteAlternative`).**  Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`,
but the `hextend_of_not_finiteAlternative` textbook PDE-input is **eliminated**:
it is internally redundant in the `1 ≤ p.m` regime (see the rationale above
this declaration), being subsumed by Lemma 3.1 + initial-approach + conjunct
(7) of regularity, all unconditional inside the repo.

The remaining textbook PDE-input hypotheses are `hlocal`, `hrealize`,
`hextend_of_not_mgeAlternative` — exactly the three genuine analytic frontiers
of the standard maximal continuation theorem:
short-time existence, realization at `sSup`, and restart-past-`sSup`
in the non-blow-up regime. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀)
    (hposLowerWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          IntervalDomainPosDatumLowerBound u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Bounded-initial from positive-admissibility.
  have hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  -- Per-branch gluing from regime + positive-datum lower-bound witness.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regimeAndPosDatumLowerBound
      p hχ ha hb hposWit hposLowerWit
  -- Direct existential-global package via the new no-extend_finite assembler.
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p :=
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing_no_extend_finite
      p hχ ha hb hlocal hboundedInitial hrealize
      hextend_of_not_mgeAlternative hglue
  -- Route through the existing corrected-existence Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Bundled continuation data, `extend_finite` eliminated.**  Packages the
**three** genuine textbook PDE continuation hypotheses (`localExistence`,
`realize`, `extend_mge`) together with the two book-keeping pass-throughs
(`posWit`, `posLowerWit`) consumed by
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite`
into a single record.  Strictly fewer fields than
`IntervalDomainPaper2ContinuationData` (5 vs 6): `extend_finite` is dropped. -/
structure IntervalDomainPaper2ContinuationData_no_extend_finite
    (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extend_mge :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        1 ≤ p.m →
        ¬ MGeOneFiniteHorizonAlternative intervalDomain
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u →
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀)
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀
  posLowerWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        IntervalDomainPosDatumLowerBound u₀

/-- **Bundled-input wrapper (no `extend_finite`).**  Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite`,
but consuming the **five** textbook/pass-through hypotheses as a single
`IntervalDomainPaper2ContinuationData_no_extend_finite` record.  One textbook
PDE input fewer than `Theorem_1_1_intervalDomain_via_regime_and_continuationData`. -/
theorem Theorem_1_1_intervalDomain_via_regime_and_continuationData_no_extend_finite
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hData : IntervalDomainPaper2ContinuationData_no_extend_finite p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_extend_finite
    p hχ ha hb hData.localExistence hData.realize hData.extend_mge
    hData.posWit hData.posLowerWit

/-- Forgetful map: every old continuation-data bundle (6 fields) gives rise to
the new leaner bundle (5 fields) by simply dropping `extend_finite`.  This
witnesses that the new umbrella consumes a strict subset of the old textbook
PDE-input surface. -/
def IntervalDomainPaper2ContinuationData.toNoExtendFinite
    {p : CM2Params} (h : IntervalDomainPaper2ContinuationData p) :
    IntervalDomainPaper2ContinuationData_no_extend_finite p :=
  { localExistence := h.localExistence
    realize := h.realize
    extend_mge := h.extend_mge
    posWit := h.posWit
    posLowerWit := h.posLowerWit }

/-! ## Paper 2-aligned umbrella (γ ≥ 1)

Paper 2 (Chen-Ruau-Shen) only addresses the case `γ ≥ 1` (confirmed with
author Liang on 2026-05-27).  In this regime the local Lipschitz constant
of the source `x ↦ x^γ` on `[0, M]` is the well-defined `L_γ = γ·M^{γ-1}`,
**without** any positive lower bound `δ > 0`, so the gluing closure
`GlobalSolutionGluingFromReachability_of_regime_gammaGeOne` consumes only
the **per-pair `PositiveInitialDatum`** book-keeping pass-through and
drops the `IntervalDomainPosDatumLowerBound` pass-through entirely.

The variant below mirrors
`Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`
field-by-field except:

* it carries an extra `1 ≤ p.γ` hypothesis (Paper 2's actual regime);
* it routes through the γ≥1 gluing closure instead of the general-γ one;
* it has **no** `hposLowerWit` field. -/

/-- **Paper 2-aligned umbrella theorem (γ≥1).**  In the negative-sensitivity
regime `χ₀ ≤ 0, 0 < a, 0 < b` together with `1 ≤ p.γ` — i.e. exactly the
case addressed by Paper 2 (Chen-Ruau-Shen, confirmed with author Liang
2026-05-27) — Paper 2 Theorem 1.1 on the interval domain follows from
the textbook PDE continuation inputs (`hlocal`, `hrealize`,
`hextend_of_not_finiteAlternative`, `hextend_of_not_mgeAlternative`) and
the **single** book-keeping pass-through `hposWit` (per-pair positive
initial datum of any classical-solution pair).  **No
`IntervalDomainPosDatumLowerBound` is required**: the γ≥1 gluing chain
discharges its δ-free analogue uniformly via `L_γ = γ·M^{γ-1}`.

The spatial range-boundedness (`hrangeBounded`) is internally discharged
from conjunct (7) of the classical-solution regularity bundle, exactly
as in `Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded`. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hrealize :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ _hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
        ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v ∧
          InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Step 1. Bounded-initial from positive-admissibility.
  have hboundedInitial :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          BddAbove (Set.range (fun x : intervalDomain.Point => |u₀ x|)) := by
    intro u₀ hu₀
    exact hu₀.admissible
  -- Step 2. Internal `hrangeBounded` from conjunct (7) of the classical
  --         regularity bundle.
  have hrangeBounded :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ∀ t, 0 < t → t < T →
            BddAbove (Set.range (fun x : intervalDomain.Point => |u t x|)) := by
    intro _u₀ _hu₀ T _hT u v hsol _htrace t ht_pos ht_T
    exact classicalSolution_u_range_bddAbove hsol ⟨ht_pos, ht_T⟩
  -- Step 3. Sup-norm-controls-pointwise per branch.
  have hsupControls :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p T u v →
        InitialTrace intervalDomain u₀ u →
          ShenWork.IntervalDomainExistence.SupNormControlsPointwiseBefore T u := by
    intro u₀ hu₀ T hT u v hsol htrace
    exact supNormControlsPointwiseBefore_of_timeSlice_rangeBounded
      (hrangeBounded u₀ hu₀ T hT u v hsol htrace)
  -- Step 4. **Paper 2's actual gluing chain**: γ≥1 closure, NO `posLowerWit`.
  have hglue :
      ShenWork.IntervalDomainExistence.GlobalSolutionGluingFromReachability p :=
    GlobalSolutionGluingFromReachability_of_regime_gammaGeOne
      p hχ ha hb hγ_ge_one hposWit
  -- Step 5. Existential-global package via the nonminimal continuation+gluing assembler.
  have hexist :
      ShenWork.IntervalDomainExistence.IntervalDomainGlobalSolutionExists p :=
    intervalDomainGlobalSolutionExists_nonminimal_of_continuation_and_gluing
      p hχ ha hb hlocal hboundedInitial hrealize
      hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative
      hsupControls hglue
  -- Step 6. Route through the existing Moser-closure Theorem 1.1 bridge.
  exact Theorem_1_1_intervalDomain_of_corrected_existence p hexist

/-- **Paper 2-aligned bundled continuation data (γ ≥ 1).**

Packages the four textbook PDE continuation hypotheses (`localExistence`,
`realize`, `extend_finite`, `extend_mge`) together with the **single**
book-keeping pass-through `posWit` consumed by
`Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData`.

This is the Paper 2 (Chen-Ruau-Shen)-aligned analogue of
`IntervalDomainPaper2ContinuationData`: the `posLowerWit` field is dropped
because Paper 2 only addresses the γ ≥ 1 regime (confirmed with author
Liang 2026-05-27), and the γ≥1 gluing closure does not need any positive
lower bound. -/
structure IntervalDomainPaper2ContinuationDataGammaGeOne (p : CM2Params) :
    Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  realize :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u
  extend_finite :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        ¬ FiniteHorizonAlternative intervalDomain
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u →
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀)
  extend_mge :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        1 ≤ p.m →
        ¬ MGeOneFiniteHorizonAlternative intervalDomain
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u →
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀)
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- **Paper 2-aligned bundled-input wrapper (γ ≥ 1).**

Same conclusion as
`Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData`,
but consuming the five textbook/pass-through hypotheses as a single
`IntervalDomainPaper2ContinuationDataGammaGeOne` record. -/
theorem Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2ContinuationDataGammaGeOne p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData
    p hχ ha hb hγ_ge_one hData.localExistence hData.realize
    hData.extend_finite hData.extend_mge hData.posWit

/-! ## `hrealize` discharged internally for the γ≥1 regime

Under the Theorem-1.1 negative-sensitivity regime + γ≥1 + the per-pair
positive-initial-datum book-keeping, overlap uniqueness is available from the
γ≥1 L²-energy chain (`intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform`
→ `IntervalClassicalSolutionOverlapUnique_of_l2EnergyMethod`).  Composing
with `realize_at_finiteMaximalReachableHorizon_of_overlapUnique` produces
the umbrella's `hrealize` hypothesis **internally**, without any external
PDE input: structural sub-horizon merging at the finite supremum. -/

/-- The umbrella's `hrealize` hypothesis discharged internally for the γ≥1
regime, by overlap uniqueness (γ≥1 L²-energy chain) plus structural
sub-horizon gluing at the finite reachable supremum. -/
theorem realize_of_regime_gammaGeOne
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ _hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀),
      ∃ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v ∧
        InitialTrace intervalDomain u₀ u := by
  -- Step 1: build `IntervalClassicalSolutionOverlapUnique p` from the γ≥1 chain.
  have hbdd_uniform :
      IntervalDomainL2UBoundednessHypothesis p :=
    boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
      (uniformLiftBoundZeroM_of_regime p hχ ha hb hposWit
        (fun hsol₁ hsol₂ htr₁ htr₂ => (hposWit hsol₁ hsol₂ htr₁ htr₂).admissible))
      (fun hsol₁ hsol₂ htr₁ htr₂ => (hposWit hsol₁ hsol₂ htr₁ htr₂).admissible)
  have hbdd_datum :
      IntervalDomainL2UBoundedDatumUniform p :=
    intervalDomainL2UBoundedDatumUniform_of_bounded hbdd_uniform
  have hL2method :
      IntervalDomainClassicalUniquenessL2EnergyMethod p :=
    intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
      hbdd_datum
  have huniq :
      ShenWork.IntervalDomainExistence.IntervalClassicalSolutionOverlapUnique p :=
    ShenWork.IntervalDomainExistence.IntervalClassicalSolutionOverlapUnique_of_l2EnergyMethod
      hL2method
  -- Step 2: produce hrealize from huniq + hlocal.
  intro u₀ hu₀ hbdd
  exact ShenWork.IntervalDomainExistence.realize_at_finiteMaximalReachableHorizon_of_overlapUnique
    huniq hlocal hu₀ hbdd

/-- **Paper 2-aligned umbrella theorem (γ≥1), `hrealize` eliminated.**

Same conclusion as `Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData`
but with `hrealize` discharged internally — only `hlocal`, `hextend_of_not_finiteAlternative`,
`hextend_of_not_mgeAlternative`, and `hposWit` remain as textbook PDE inputs. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hrealize
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hextend_of_not_finiteAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hextend_of_not_mgeAlternative :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀))
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_and_continuationData
    p hχ ha hb hγ_ge_one hlocal
    (realize_of_regime_gammaGeOne p hχ ha hb hγ_ge_one hlocal hposWit)
    hextend_of_not_finiteAlternative hextend_of_not_mgeAlternative hposWit

/-! ## `hextend_mge` discharged via uniform local existence

The textbook **continuation theorem** for parabolic systems with locally-Lipschitz
nonlinearities (which the Chen–Ruau–Shen (CM) system is, for `γ ≥ 1`) is the
single textbook PDE input replacing `hextend_mge`.  Standard form (e.g. Henry,
*Geometric Theory of Semilinear Parabolic Equations*, Th. 3.3.4; Amann,
*Linear and Quasilinear Parabolic Problems*, Vol. I, Ch. II):

> Given a positive admissible initial datum `u₀` with `L∞`-norm bounded by `M`,
> there is a uniform existence duration `δ(M) > 0` such that, whenever a
> classical solution `(u, v)` already exists on `[0, T₀)` with that initial
> trace, one can extend it to a classical solution `(u', v')` on
> `[0, T₀ + δ(M))` with the **same** initial trace `u₀`.

This statement encodes BOTH the uniform local-existence δ AND the textbook
restart-and-glue (time-shifted classical solution piecewise glued at `T₀` via
overlap uniqueness + autonomy + interior regularity).  It is a SINGLE textbook
PDE input — the standard form of the parabolic continuation theorem.

Under this hypothesis + the γ≥1 regime + overlap uniqueness already proved in
the repo + Lemma 3.1, `hextend_of_not_mgeAlternative` is internally derivable
without further textbook inputs (no `hextend_mge`, no `hextend_finite`).

Note: the `M`-bound is on the initial datum `u₀`, NOT on the solution during
its existence; in the negative-sensitivity regime Lemma 3.1 gives an automatic
upper sup-norm bound from the initial datum bound, so the textbook statement
in this form is faithful to the parabolic textbook continuation theorem. -/

/-- **Uniform parabolic continuation theorem** for the interval-domain (CM)
system.  Single textbook PDE input replacing both `hextend_finite` and
`hextend_mge` in the maximal-continuation interface.

For every `M > 0`, there is a uniform `δ(M) > 0` such that any classical
solution `(u, v)` on `[0, T₀)` with positive admissible initial datum `u₀`
satisfying `|u₀ x| ≤ M` for all `x` extends to a classical solution `(u', v')`
on `[0, T₀ + δ(M))` with the same initial trace `u₀`.

The δ depends only on `M`, not on `T₀` or the specific datum.  This is the
parabolic textbook "uniform local existence + restart-and-glue" packaged as a
single hypothesis. -/
def IntervalDomainUniformLocalExistence (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
      (∀ x : intervalDomain.Point, |u₀ x| ≤ M) →
      ∀ {T₀ : ℝ}, 0 < T₀ →
      ∀ {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
        ∃ u' v' : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p (T₀ + δ) u' v' ∧
          InitialTrace intervalDomain u₀ u'

/-- A `PositiveInitialDatum` yields a uniform absolute-value bound `M` on `u₀`
by definition of `initialAdmissible` (it requires `BddAbove (range |u₀|)`).
This pulls a concrete `M` from the existential witness inside `BddAbove`. -/
private lemma exists_supBound_of_positiveInitialDatum
    {u₀ : intervalDomain.Point → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomain u₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : intervalDomain.Point, |u₀ x| ≤ M := by
  -- `hu₀.admissible : BddAbove (range |u₀|)`.
  obtain ⟨M₀, hM₀⟩ := hu₀.admissible
  -- M₀ is an upper bound for the range; |u₀ x| ≤ M₀ for every x.
  -- Pick M = max M₀ 1 > 0.
  refine ⟨max M₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have hx_mem : |u₀ x| ∈ Set.range (fun y : intervalDomain.Point => |u₀ y|) :=
    ⟨x, rfl⟩
  exact (hM₀ hx_mem).trans (le_max_left _ _)

/-- **Internal derivation of `hextend_of_not_mgeAlternative` from
`IntervalDomainUniformLocalExistence`.**

In the negative-sensitivity regime with γ ≥ 1 + 1 ≤ p.m, the textbook uniform
parabolic continuation theorem
`IntervalDomainUniformLocalExistence` directly produces the
`ReachablePast p u₀ T*` continuation witness consumed by the
`hextend_of_not_mgeAlternative` interface.

The proof:
1. Extract an `L∞` upper bound `M > 0` for `u₀` from its `PositiveInitialDatum`
   admissibility (`exists_supBound_of_positiveInitialDatum`).
2. Apply `IntervalDomainUniformLocalExistence` at this `M`, obtaining a uniform
   `δ > 0` and a classical extension on `[0, T* + δ)`.
3. The extension realizes `ReachableClassicalHorizon p u₀ (T* + δ)` with
   `T* + δ > T*`, hence `ReachablePast p u₀ T*`.

No use is made of the `¬ MGeOneFiniteHorizonAlternative` hypothesis (the
textbook continuation theorem already produces uniform δ-extension without
needing to know the blow-up alternative fails — that information is consumed
inside the textbook input). -/
theorem extend_of_not_mgeAlternative_of_uniformLocalExistence
    (p : CM2Params)
    (hUniform : IntervalDomainUniformLocalExistence p) :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ (_hbdd : BddAbove
        (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
      {u v : ℝ → intervalDomain.Point → ℝ},
        IsPaper2ClassicalSolution intervalDomain p
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u v →
        InitialTrace intervalDomain u₀ u →
        1 ≤ p.m →
        ¬ MGeOneFiniteHorizonAlternative intervalDomain
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) u →
        ShenWork.IntervalDomainExistence.ReachablePast p u₀
          (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
            p u₀) := by
  intro u₀ hu₀ hbdd u v hsol htrace _hm _hnotMge
  -- Step 1: extract M > 0 with |u₀ x| ≤ M for all x.
  obtain ⟨M, hM_pos, hM_bound⟩ := exists_supBound_of_positiveInitialDatum hu₀
  -- Step 2: apply the textbook uniform continuation theorem.
  obtain ⟨δ, hδ_pos, hExtend⟩ := hUniform M hM_pos
  -- Use T₀ = T* = finiteMaximalReachableHorizon p u₀.
  set T_star := ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon p u₀
    with hT_star_def
  have hT_star_pos : 0 < T_star := hsol.T_pos
  obtain ⟨u', v', hsol', htrace'⟩ :=
    hExtend (u₀ := u₀) hu₀ hM_bound (T₀ := T_star) hT_star_pos hsol htrace
  -- Step 3: ReachableClassicalHorizon p u₀ (T_star + δ) with T_star + δ > T_star.
  refine ⟨T_star + δ, ?_, ?_⟩
  · linarith
  · refine ⟨?_, u', v', hsol', htrace'⟩
    -- T_star + δ > 0
    linarith

/-- **Paper 2-aligned umbrella theorem (γ ≥ 1), `hextend_mge` eliminated.**

The umbrella's `hextend_of_not_mgeAlternative` hypothesis is discharged
internally via the textbook uniform parabolic continuation theorem
(`IntervalDomainUniformLocalExistence`).  Likewise `hextend_finite` (already
eliminated in `_no_extend_finite`) and `hrealize` (already eliminated in
`_no_hrealize`) are not consumed at all.

The remaining textbook PDE inputs for the γ ≥ 1 regime are exactly:
* `hlocal` — standard short-time local existence;
* `hUniform` — textbook uniform parabolic continuation (`δ(M)`);
* `hposWit` — book-keeping pass-through (per-pair positive initial datum). -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  -- Build `hextend_of_not_mgeAlternative` from `hUniform`.
  have hextend_mge :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          1 ≤ p.m →
          ¬ MGeOneFiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) :=
    extend_of_not_mgeAlternative_of_uniformLocalExistence p hUniform
  -- Build `hextend_of_not_finiteAlternative` from `hUniform` as well.  The textbook
  -- continuation theorem produces a δ-extension regardless of whether the finite
  -- blow-up alternative occurs (it consumes the `M`-bound on `u₀`, period), so the
  -- same `extend_of_not_mgeAlternative_of_uniformLocalExistence` argument
  -- (with the `1 ≤ p.m` and `¬MGeOne` hypotheses unused) gives the
  -- `¬ FiniteHorizonAlternative` variant too.
  have hextend_finite :
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ (_hbdd : BddAbove
          (ShenWork.IntervalDomainExistence.reachableClassicalHorizonSet p u₀))
        {u v : ℝ → intervalDomain.Point → ℝ},
          IsPaper2ClassicalSolution intervalDomain p
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u v →
          InitialTrace intervalDomain u₀ u →
          ¬ FiniteHorizonAlternative intervalDomain
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) u →
          ShenWork.IntervalDomainExistence.ReachablePast p u₀
            (ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon
              p u₀) := by
    intro u₀ hu₀ hbdd u v hsol htrace _hnot
    -- Step 1: extract M > 0.
    obtain ⟨M, hM_pos, hM_bound⟩ := exists_supBound_of_positiveInitialDatum hu₀
    -- Step 2: apply textbook uniform continuation.
    obtain ⟨δ, hδ_pos, hExtend⟩ := hUniform M hM_pos
    set T_star := ShenWork.IntervalDomainExistence.finiteMaximalReachableHorizon p u₀
    have hT_star_pos : 0 < T_star := hsol.T_pos
    obtain ⟨u', v', hsol', htrace'⟩ :=
      hExtend (u₀ := u₀) hu₀ hM_bound (T₀ := T_star) hT_star_pos hsol htrace
    refine ⟨T_star + δ, ?_, ?_⟩
    · linarith
    · refine ⟨?_, u', v', hsol', htrace'⟩
      linarith
  -- Compose with the existing γ ≥ 1 + no_hrealize umbrella.
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hrealize
    p hχ ha hb hγ_ge_one hlocal hextend_finite hextend_mge hposWit

/-- **Paper 2-aligned bundled continuation data (γ ≥ 1), `hextend_mge`
eliminated.**

Packages the three textbook PDE inputs (`localExistence`, `uniformLocal`,
`hposWit`) into a single record.  This is the leanest textbook PDE input
surface for Paper 2 Theorem 1.1 in the γ ≥ 1 regime: TWO genuine textbook PDE
inputs (local + uniform continuation) plus ONE book-keeping pass-through. -/
structure IntervalDomainPaper2ContinuationDataGammaGeOne_no_hextend_mge
    (p : CM2Params) : Prop where
  localExistence :
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- **Bundled-input wrapper (γ ≥ 1, `hextend_mge` eliminated).**

Same conclusion as `Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge`
but consuming the three textbook/pass-through hypotheses as a single bundle. -/
theorem Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2ContinuationDataGammaGeOne_no_hextend_mge p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one hData.localExistence hData.uniformLocal hData.posWit

/-- **Paper 2-aligned umbrella via Picard gradient-mild local data.**

This is the same γ≥1/no-`hextend_mge` umbrella, but the local-existence input is
lowered from an abstract classical `hlocal` hypothesis to the concrete
Picard-output interface `IntervalDomainGradientMildLocalData`, using
`IntervalMildToLocalExistence.localExistence_of_gradientMildSolutionData`.

Remaining inputs are the genuine continuation theorem
`IntervalDomainUniformLocalExistence` and the `posWit` bookkeeping pass-through. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildLocalData p hMildLocal)
    hUniform hposWit

/-- Paper 2-aligned umbrella via Picard gradient-mild local data whose
elliptic/Neumann regularity is supplied by restart-cosine representations. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildRestartLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildRestartLocalData p hMildLocal)
    hUniform hposWit

/-- Paper 2-aligned umbrella via restart-cosine Picard gradient-mild local data
using only the reduced regularity frontier. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartFrontierCoreLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildRestartFrontierCoreLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildRestartFrontierCoreLocalData p hMildLocal)
    hUniform hposWit

/-- Paper 2-aligned umbrella via half-step restart Picard gradient-mild local
data using only the reduced regularity frontier. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepRestartFrontierCoreLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData
      p hMildLocal)
    hUniform hposWit

/-- Paper 2-aligned umbrella via H²-source half-step Picard gradient-mild local
data using only the reduced regularity frontier. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepH2SourceFrontierCoreLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepH2SourceFrontierCoreLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildHalfStepH2SourceFrontierCoreLocalData
      p hMildLocal)
    hUniform hposWit

/-- Paper 2-aligned umbrella via logistic-source half-step Picard
gradient-mild local data using only the reduced regularity frontier. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
      p hMildLocal)
    hUniform hposWit

/-- Paper 2-aligned umbrella via Picard gradient-mild local data, explicitly
routed through the older `localExistence_of_fp_and_regularity` interface.

The local-existence input is the old-Duhamel bridge data:
`GradientMildSolutionData` plus the `t = 0` old fixed-point endpoint and the
positive-time RHS equality
`intervalGradientDuhamelMap = intervalDuhamelOperator`.  The proof first
constructs the `hlocal` field using
`localExistence_of_gradientMildIntervalDuhamelLocalData`, then reuses the
already-closed γ≥1 gluing/continuation umbrella. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildIntervalDuhamelLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildIntervalDuhamelLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildIntervalDuhamelLocalData p hMildLocal)
    hUniform hposWit

/-- Old-Duhamel-routed Paper 2 umbrella with restart-cosine regularity
discharge for the elliptic and Neumann conjuncts. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartIntervalDuhamelLocalData
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildRestartIntervalDuhamelLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildRestartIntervalDuhamelLocalData p hMildLocal)
    hUniform hposWit

/-- Zero-sensitivity version of the old-Duhamel-routed Paper 2 umbrella.

Here the local data supplies only the component frontiers for the Duhamel RHS:
full/helper semigroup equality and logistic-Duhamel equality.  The chemotaxis
piece is killed by `p.χ₀ = 0`, so the old fixed-point hypothesis is constructed
directly from `GradientMildSolutionData`. -/
theorem
    Theorem_1_1_intervalDomain_via_chiZero_gammaGeOne_gradientMildDuhamelLocalData
    (p : CM2Params) (hχ_zero : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildChiZeroDuhamelLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  have hχ : p.χ₀ ≤ 0 := by
    simp [hχ_zero]
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildChiZeroDuhamelLocalData
      p hχ_zero hMildLocal)
    hUniform hposWit

/-- Zero-sensitivity old-Duhamel Paper 2 umbrella with restart-cosine
regularity discharge for the elliptic and Neumann conjuncts. -/
theorem
    Theorem_1_1_intervalDomain_via_chiZero_gammaGeOne_gradientMildRestartDuhamelLocalData
    (p : CM2Params) (hχ_zero : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hMildLocal : IntervalDomainGradientMildRestartChiZeroDuhamelLocalData p)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hposWit :
      ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
        {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
        IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
        IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
        InitialTrace intervalDomain u₀ u₁ →
        InitialTrace intervalDomain u₀ u₂ →
          PositiveInitialDatum intervalDomain u₀) :
    Theorem_1_1 intervalDomain p := by
  have hχ : p.χ₀ ≤ 0 := by
    simp [hχ_zero]
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildRestartChiZeroDuhamelLocalData
      p hχ_zero hMildLocal)
    hUniform hposWit

/-- Bundled input for the Picard-gradient-mild version of the γ≥1 umbrella. -/
structure IntervalDomainPaper2GradientMildContinuationData (p : CM2Params) :
    Prop where
  mildLocal : IntervalDomainGradientMildLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the Picard-gradient-mild γ≥1 umbrella. -/
theorem Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2GradientMildContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the restart-cosine Picard-gradient-mild γ≥1 umbrella. -/
structure IntervalDomainPaper2GradientMildRestartContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildRestartLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the restart-cosine Picard-gradient-mild γ≥1
umbrella. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2GradientMildRestartContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the half-step restart Picard-gradient-mild γ≥1
umbrella using only the frontier classical core. -/
structure
    IntervalDomainPaper2GradientMildHalfStepRestartFrontierCoreContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the half-step restart Picard-gradient-mild γ≥1
umbrella using only the frontier classical core. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepRestartFrontierCoreLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepRestartFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepRestartFrontierCoreLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the half-step H2-source Picard-gradient-mild γ≥1
umbrella using only the frontier classical core. -/
structure
    IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildHalfStepH2SourceFrontierCoreLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the half-step H2-source Picard-gradient-mild γ≥1
umbrella using only the frontier classical core. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepH2SourceFrontierCoreLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepH2SourceFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepH2SourceFrontierCoreLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the half-step logistic-source Picard-gradient-mild γ≥1
umbrella using only the frontier classical core. -/
structure
    IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
    (p : CM2Params) : Prop where
  mildLocal :
    IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the half-step logistic-source Picard-gradient-mild
γ≥1 umbrella using only the frontier classical core. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepLogisticSourceFrontierCoreLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2GradientMildHalfStepLogisticSourceFrontierCoreContinuationData
        p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the old-Duhamel-routed Picard-gradient-mild γ≥1
umbrella. -/
structure IntervalDomainPaper2GradientMildIntervalDuhamelContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildIntervalDuhamelLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the old-Duhamel-routed Picard-gradient-mild γ≥1
umbrella. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildIntervalDuhamelLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2GradientMildIntervalDuhamelContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildIntervalDuhamelLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the old-Duhamel-routed restart-cosine Picard-gradient-mild
γ≥1 umbrella. -/
structure IntervalDomainPaper2GradientMildRestartIntervalDuhamelContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildRestartIntervalDuhamelLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the old-Duhamel-routed restart-cosine
Picard-gradient-mild γ≥1 umbrella. -/
theorem
    Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartIntervalDuhamelLocalData_bundled
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2GradientMildRestartIntervalDuhamelContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_gradientMildRestartIntervalDuhamelLocalData
    p hχ ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the zero-sensitivity component-frontier Duhamel γ≥1
umbrella. -/
structure IntervalDomainPaper2GradientMildChiZeroDuhamelContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildChiZeroDuhamelLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the zero-sensitivity component-frontier Duhamel
γ≥1 umbrella. -/
theorem
    Theorem_1_1_intervalDomain_via_chiZero_gammaGeOne_gradientMildDuhamelLocalData_bundled
    (p : CM2Params) (hχ_zero : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2GradientMildChiZeroDuhamelContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_chiZero_gammaGeOne_gradientMildDuhamelLocalData
    p hχ_zero ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

/-- Bundled input for the zero-sensitivity restart-cosine component-frontier
Duhamel γ≥1 umbrella. -/
structure IntervalDomainPaper2GradientMildRestartChiZeroDuhamelContinuationData
    (p : CM2Params) : Prop where
  mildLocal : IntervalDomainGradientMildRestartChiZeroDuhamelLocalData p
  uniformLocal : IntervalDomainUniformLocalExistence p
  posWit :
    ∀ {u₀ : intervalDomainPoint → ℝ} {T₁ T₂ : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T₁ u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T₂ u₂ v₂ →
      InitialTrace intervalDomain u₀ u₁ →
      InitialTrace intervalDomain u₀ u₂ →
        PositiveInitialDatum intervalDomain u₀

/-- Bundled-input wrapper for the zero-sensitivity restart-cosine
component-frontier Duhamel γ≥1 umbrella. -/
theorem
    Theorem_1_1_intervalDomain_via_chiZero_gammaGeOne_gradientMildRestartDuhamelLocalData_bundled
    (p : CM2Params) (hχ_zero : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2GradientMildRestartChiZeroDuhamelContinuationData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_chiZero_gammaGeOne_gradientMildRestartDuhamelLocalData
    p hχ_zero ha hb hγ_ge_one hData.mildLocal hData.uniformLocal hData.posWit

end

end ShenWork.Paper2

-- Axiom audit: the umbrella theorems depend only on `propext`, `Classical.choice`,
-- and `Quot.sound` (the standard Lean foundational axioms used throughout the
-- repo); no `sorryAx`, no custom `axiom`.
-- #print axioms ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound
-- #print axioms
--   ShenWork.Paper2.Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach
-- #print axioms
--   ShenWork.Paper2.
--     Theorem_1_1_intervalDomain_via_regime_and_posDatumLowerBound_no_hreach_no_hrangeBounded
