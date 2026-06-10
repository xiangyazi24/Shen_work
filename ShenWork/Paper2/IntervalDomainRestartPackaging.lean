/-
  ShenWork/Paper2/IntervalDomainRestartPackaging.lean

  **Half-step restart packaging from the time-localized subtype ledger.**

  `GradientMildHalfStepRestartData D` (IntervalMildRegularityBootstrap) is the
  per-time-slice restart package: for each `t ∈ (0, D.T)` it carries a restarted
  source `DuhamelSourceTimeC1 (a t)` and the cosine-series agreement `hagree`
  identifying the slice `lift (D.u t)` with the restarted cosine-Duhamel series at
  base `t/2`.  Its STRUCTURE FIELDS ARE PER-`t` (no global `σ` quantifier escapes
  the field binders).

  The existing producer `IntervalPicardLimitSourceData.gradientMildHalfStepRestartData_for_limit`
  (through `gradientMildHalfStepRestartData_of_limit`) demands the FULL (global-`σ`)
  `DuhamelSourceTimeC1` for the genuine limit source family, plus
  `Continuous (intervalDomainLift u₀)` — both unsatisfiable for positive data (the
  zero-extension lift is discontinuous at the Neumann endpoints; the genuine
  source family is regular only on compact time windows of `(0, T)`).

  This file dissolves both, exactly as tonight's `Hu` machinery
  (`TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont`) does for
  `HasTimeNeighborhoodSpectralAgreement`.  For each target time `t` we:

  * pick the CLAMPED, time-shifted source family
      `a t σ k := cosineCoeffs (logisticSourceFun … (lift (D.u (φ c' τ d d' (τ + σ))))) k`
    (`τ = t/2`), whose slice index `φ …` always lands in a compact window
    `[c', d'] ⊂ (0, T)`;
  * supply its `DuhamelSourceTimeC1` via `clampedSource_duhamelSourceTimeC1` from the
    window-restricted ledger data (`src` field);
  * prove `hagree` from `picardLimitRestart_general_of_subtypeCont` at base `τ`,
    horizon `t − τ = t/2`, reconciling the clamped family with the canonical shifted
    family on the integration window via `clampedFamily_eq_on` + `source_family_eq_w`
    (the same reconciliation as the `Hu` route's eventually-nhds tail).

  The hypothesis list is the V2 SUBTYPE ledger shape (`Continuous u₀`,
  `constExtend` slice continuity, time-localized `hbsum/hagree/hpost/hubt`,
  per-compact `hG1t/hG2t/hMdott`, `(0,T)`-localized K1) — identical to
  `Hu_of_restart_localized_of_subtypeCont` — so the producer is directly fed by the
  ledger `LimitRegularityInputs`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitTimeNhdSubtype
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff GradientMildHalfStepRestartData
   gradientMildHalfStepInitialCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.IntervalPicardLimitSourceData
  (restartDuhamelCoeff_eq_localRestartCoeff source_family_eq_w)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalTimeSoftClamp (φ)

noncomputable section

namespace ShenWork.Paper2.RestartPackaging

/-- **`GradientMildHalfStepRestartData D` from the time-localized SUBTYPE ledger.**

The per-`t` restart package is assembled exactly as the `Hu` route
(`TimeNhdSubtype.Hu_of_restart_localized_of_subtypeCont`): for each `t`, the
clamped time-shifted source family (with clamp window `[t/4, (t+3D.T)/4] ⊂ (0,D.T)`,
identity zone `[t/2, (t+D.T)/2]`) supplies a window-only `DuhamelSourceTimeC1` via
`clampedSource_duhamelSourceTimeC1`, and the cosine-series `hagree` follows from
`picardLimitRestart_general_of_subtypeCont` at base `τ = t/2`, reconciled to the
canonical shifted family on the integration window.

Hypotheses are the V2 subtype ledger shapes (cf.
`Hu_of_restart_localized_of_subtypeCont` and `MildLocalChi0.LimitRegularityInputs`). -/
noncomputable def gradientMildHalfStepRestartData_localized_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < D.T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (D.u s) x = intervalGradientDuhamelMap p u₀ D.u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (D.u s)) k) D.T)
    -- K2: per-slice representation and bounds, time-localized
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < D.T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < D.T → Set.EqOn (intervalDomainLift (D.u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (D.u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < D.T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (D.u σ) x ≤ Msup)
    -- K2: gradient/Hessian bounds, PER-COMPACT
    (hG1t : ∀ a' b', 0 < a' → b' < D.T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (D.u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < D.T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (D.u σ))) x| ≤ G2)
    -- K1: UNSHIFTED source-coefficient time-C¹ data on (0,T), per-compact bound
    (adott : ℝ → ℕ → ℝ)
    (hderivt : ∀ σ, 0 < σ → σ < D.T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (D.u r))) k)
      (adott σ k) σ)
    (hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 D.T))
    (hMdott : ∀ a' b', 0 < a' → b' < D.T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adott σ k| ≤ Mdot)
    -- H3 slice continuity — constExtend (subtype) form
    (hLc_ce : ∀ t, 0 < t → t < D.T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (D.u s)))) :
    GradientMildHalfStepRestartData D where
  a := fun t σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
    (intervalDomainLift (D.u (φ (t / 4) (t / 2) ((t + D.T) / 2) ((t + 3 * D.T) / 4)
      (t / 2 + σ))))) k
  src := by
    intro t ht htT
    -- restart base / offset
    set τ : ℝ := t / 2 with hτdef
    have hτpos : 0 < τ := by rw [hτdef]; linarith
    -- clamp window: id-zone [c,d] = [τ, (t+D.T)/2], range window [c',d'] ⊂ (0,D.T)
    set c' : ℝ := t / 4 with hc'def
    set d : ℝ := (t + D.T) / 2 with hddef
    set d' : ℝ := (t + 3 * D.T) / 4 with hd'def
    have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
    have hcd : τ ≤ d := by rw [hddef, hτdef]; linarith
    have hd' : d < d' := by rw [hddef, hd'def]; linarith
    have hc'pos : 0 < c' := by rw [hc'def]; linarith
    have hd'T : d' < D.T := by rw [hd'def]; linarith
    have hwin : ∀ σ ∈ Set.Icc c' d', 0 < σ ∧ σ < D.T := fun σ hσ =>
      ⟨lt_of_lt_of_le hc'pos hσ.1, lt_of_le_of_lt hσ.2 hd'T⟩
    -- per-compact bounds (data target: pick witnesses via `Classical.choose`)
    have hG1 := (hG1t c' d' hc'pos hd'T).choose_spec
    have hG2 := (hG2t c' d' hc'pos hd'T).choose_spec
    have hMdot := (hMdott c' d' hc'pos hd'T).choose_spec
    exact clampedSource_duhamelSourceTimeC1 p D.u hα ha hb hc' hcd hd'
      bc
      (fun σ hσ => hbsum σ (hwin σ hσ).1 (hwin σ hσ).2)
      (fun σ hσ => hagree σ (hwin σ hσ).1 (hwin σ hσ).2)
      (fun σ hσ => hpost σ (hwin σ hσ).1 (hwin σ hσ).2)
      (fun σ hσ => hubt σ (hwin σ hσ).1 (hwin σ hσ).2)
      hG1 hG2 adott
      (fun σ hσ k => hderivt σ (hwin σ hσ).1 (hwin σ hσ).2 k)
      (fun k => (hadotcontt k).mono
        (fun σ hσ => ⟨(hwin σ hσ).1, (hwin σ hσ).2⟩))
      hMdot
  hagree := by
    intro t ht htT
    -- restart base / offset
    set τ : ℝ := t / 2 with hτdef
    have hτpos : 0 < τ := by rw [hτdef]; linarith
    have hτt : τ < t := by rw [hτdef]; linarith
    -- clamp window
    set c' : ℝ := t / 4 with hc'def
    set d : ℝ := (t + D.T) / 2 with hddef
    set d' : ℝ := (t + 3 * D.T) / 4 with hd'def
    have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
    have hd' : d < d' := by rw [hddef, hd'def]; linarith
    have hc'pos : 0 < c' := by rw [hc'def]; linarith
    have hd'T : d' < D.T := by rw [hd'def]; linarith
    -- general restart identity at time t, base τ, horizon t − τ (canonical family)
    have heqon := ShenWork.Paper2.TimeNhdSubtype.picardLimitRestart_general_of_subtypeCont
      p hχ0 u₀ D.u
      (fun r hr hrt => hfix r hr (lt_of_le_of_lt hrt htT))
      hu₀_cont hu₀_bound hsrc0 hτpos hτt htT.le
      (fun s hs hst => hLc_ce t ht htT s hs hst)
    -- `gradientMildHalfStepInitialCoeff D t = cosineCoeffs (lift (D.u (t/2)))`,
    -- which is the restart base coefficient of `heqon` (`τ = t/2`).
    intro x hx
    rw [heqon hx]
    refine tsum_congr (fun k => ?_)
    congr 1
    -- Goal (after `congr 1`): the heqon coefficient (canonical, base `τ`, horizon
    -- `t − τ`) equals the structure-field coefficient (initialCoeff `D t`, clamped
    -- family, horizon `τ = t/2`).  Base coeffs agree definitionally
    -- (`initialCoeff D t = coeffs (lift (D.u τ))`); horizon `t − τ = τ`; bodies
    -- reconciled on the integration window.
    symm
    have hbase : gradientMildHalfStepInitialCoeff D t
        = cosineCoeffs (intervalDomainLift (D.u τ)) := by
      unfold gradientMildHalfStepInitialCoeff; rw [hτdef]
    have hhz : t - τ = τ := by rw [hτdef]; ring
    rw [hbase, hhz]
    rw [restartDuhamelCoeff_eq_localRestartCoeff, restartDuhamelCoeff_eq_localRestartCoeff]
    unfold localRestartCoeff
    congr 1
    -- Duhamel parts: integrands agree on [0, τ] (absolute times in [τ, t] ⊆ [c,d])
    unfold duhamelSpectralCoeff
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [Set.uIcc_of_le (by rw [hτdef]; linarith : (0:ℝ) ≤ τ)] at hσ
    have hmem_cd : τ + σ ∈ Set.Icc τ d := by
      refine ⟨by linarith [hσ.1], ?_⟩
      rw [hddef, hτdef]
      have hσ2 : σ ≤ τ := hσ.2
      rw [hτdef] at hσ2; linarith
    simp only
    -- peel the shared heat factor `exp(-(τ-σ)·λ)`
    congr 1
    rw [clampedFamily_eq_on p D.u hc' hd' hmem_cd k]
    exact (congrFun (congrFun (source_family_eq_w p D.u) (τ + σ)) k).symm

end ShenWork.Paper2.RestartPackaging
