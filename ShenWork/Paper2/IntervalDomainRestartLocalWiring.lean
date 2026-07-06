/-
  Abstract-restart variant of the hMildLocal interface + factored final wiring.

  ## Why this file exists (faithfulness fix, 2026-06-06)

  `IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData`
  requires `GradientMildHalfStepLogisticSourceData`, whose `hagree` field
  represents every mild slice `u(t)` as a restart cosine series whose Duhamel
  source family consists of the cosine coefficients of a *pure logistic*
  source `L(profile t σ)`.  The gradient mild map, however, contains a
  chemotaxis flux term `−χ₀ ∫₀ᵗ ∂ₓ[S(t−s) Q(u s)] ds`.  For `χ₀ ≠ 0` the
  effective restart source contains a flux-divergence component which is in
  general NOT realizable as `L(g)` for any positive C² profile `g` (for
  `α ≥ 1`, `z ↦ z(a − b·z^α)` is bounded above on `z > 0`, while the flux
  component is not bounded in terms of the logistic range).  The logistic-only
  interface is therefore expected to be satisfiable only when the flux term
  vanishes (`χ₀ = 0`).

  The faithful general interface is the ABSTRACT half-step restart package
  `GradientMildHalfStepRestartData` (source family `a t : ℝ → ℕ → ℝ` with
  `DuhamelSourceTimeC1`, no logistic shape constraint), which the regularity
  bootstrap already consumes.  This file:

  1. defines the abstract-restart local-data interface
     `IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData`;
  2. provides the `hlocal` bridge
     `localExistence_of_gradientMildHalfStepRestartFrontierCoreLocalData`;
  3. factors the final wiring through `paper2_theorem_1_1_from_quant` when a
     quantitative local factory is available;
  4. keeps `paper2_theorem_1_1_from_quant_and_hlocal` and
     `paper2_theorem_1_1_from_two_restart` as compatibility wrappers for older
     callers.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalDomainPiecewiseClassical
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainSupNormBridge
import ShenWork.Paper2.IntervalDomainRestartExtension
import ShenWork.Paper2.IntervalDomainFinalWiring

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.IntervalMildToLocalExistence
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.RestartLocalWiring

/-- **Abstract-restart Picard gradient-mild local data** with only the reduced
regularity frontier.  Identical to
`IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData` except
that the half-step source package is the abstract
`GradientMildHalfStepRestartData` (arbitrary `DuhamelSourceTimeC1` source
family), which faithfully accommodates the chemotaxis flux contribution for
`χ₀ ≠ 0`. -/
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

/-- Convert abstract-restart half-step Picard gradient-mild frontier-core local
data into the `hlocal` field consumed by the umbrella theorems. -/
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
  exact
    localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
      p hu₀ D R hInitialApproach hCore

/-- The logistic-source local data implies the abstract-restart local data
(the logistic package is a special case of the abstract restart package). -/
theorem restartLocalData_of_logisticLocalData
    (p : CM2Params)
    (h : IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p := by
  intro u₀ hu₀
  obtain ⟨D, S, hInitialApproach, hCore⟩ := h u₀ hu₀
  exact ⟨D, gradientMildHalfStepRestartData_of_logisticSourceData D S,
    hInitialApproach, hCore⟩

/-- **Factored final wiring: Paper 2 Theorem 1.1 from regime + `hQuant` +
`hlocal`.**  `hPCW` is discharged unconditionally by
`PiecewiseClassical.piecewiseClassicalWorks`; the uniform local existence is
assembled from `hQuant` via the restart-and-glue machinery exactly as in
`FinalWiring.paper2_theorem_1_1_from_three`. -/
theorem paper2_theorem_1_1_from_quant_and_hlocal
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hlocal : ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomain.Point → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p := by
  apply Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
  · exact hlocal
  · -- IntervalDomainUniformLocalExistence
    intro M hM
    set M' := SupNormBridge.regimeBound p M
    have hM' := SupNormBridge.regimeBound_pos p hM
    obtain ⟨δ, hδ, hex⟩ := hQuant M' hM'
    have hRestart : RestartExtension.RestartAndGlueWorks p :=
      GlueExtension.restartAndGlueWorks_of_hypotheses p
        TimeShift.regularityTimeShiftWorks
        (GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
          (intervalDomainClassicalUniquenessL2EnergyMethod_of_boundedDatumUniform p
            (intervalDomainL2UBoundedDatumUniform_of_bounded
              (boundednessHypothesis_of_uniformSupBoundZeroM hγ_ge_one
                (uniformLiftBoundZeroM_of_regime p hχ ha hb)))))
        GlueExtension.timeShiftInitialTraceWorks
        (PiecewiseClassical.piecewiseClassicalWorks p)
    refine ⟨δ / 2, by linarith, ?_⟩
    intro u₀ hu₀ hbound T₀ hT₀ u v hsol htrace
    have hSupBound : ∀ t, 0 < t → t < T₀ → ∀ x : intervalDomainPoint, |u t x| ≤ M' :=
      SupNormBridge.interiorSupNorm_le_regimeBound p hχ ha hb hu₀ hM hbound hT₀ hsol htrace
    have hbound' : ∀ x, |u₀ x| ≤ M' := fun x =>
      le_trans (hbound x) (SupNormBridge.regimeBound_ge_M p M)
    have hfactory : ∀ {w : intervalDomainPoint → ℝ},
        PositiveInitialDatum intervalDomain w → (∀ x, |w x| ≤ M') →
        ∃ uw vw, IsPaper2ClassicalSolution intervalDomain p δ uw vw ∧
          InitialTrace intervalDomain w uw := fun hw hbw => hex hw hbw
    exact hRestart hM' hδ hfactory hu₀ hbound' hT₀ hsol htrace hSupBound

/-- **Paper 2 Theorem 1.1 from one quantitative local factory**, abstract-restart
module alias.

The quantitative factory supplies ordinary local existence and uniform
continuation through `FinalWiring.paper2_theorem_1_1_from_quant`; no separate
abstract-restart local data is needed at this level. -/
theorem paper2_theorem_1_1_from_quant
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u) :
    Theorem_1_1 intervalDomain p :=
  FinalWiring.paper2_theorem_1_1_from_quant
    p hχ ha hb hγ_ge_one hQuant

/-- **Paper 2 Theorem 1.1 from regime + 2 hypotheses, abstract-restart form.**

Compatibility wrapper.  The abstract-restart local data is retained only for
older callers; analytically, the quantitative factory already supplies the
local-existence field consumed by the umbrella. -/
theorem paper2_theorem_1_1_from_two_restart
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (_hMildLocal :
      IntervalDomainGradientMildHalfStepRestartFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_from_quant p hχ ha hb hγ_ge_one hQuant

end ShenWork.Paper2.RestartLocalWiring
