/-
  ShenWork/Paper2/IntervalPicardLimitTimeNhdSubtype.lean

  **Subtype-continuity variant of the time-neighbourhood restart chain.**

  `TimeNhdLocalized.Hu_of_restart_localized` discharges
  `HasTimeNeighborhoodSpectralAgreement` from time-localized ledger data, but it
  routes (via `picardLimitRestart_general` → `limit_lift_eq_cosineSeries_weak`)
  through the hypothesis `hu₀_cont : Continuous (intervalDomainLift u₀)` — the
  zero-extension lift — which is FALSE for positive boundary data (the lift jumps
  to 0 outside `[0,1]`).  The paper works on `C(Ω̄)` (subtype continuity
  `Continuous u₀`).

  The repo already supplies the subtype-continuity adapter for the from-zero
  representation: `limit_lift_eq_cosineSeries_of_subtypeCont`
  (`IntervalPicardLimitRestartWeak`), which replaces the false lift-continuity
  hypothesis by `Continuous u₀` (subtype) plus constExtend slice continuity
  `Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))`,
  routing through `IntervalSpectralSubtypeAdapter`.

  This file lifts that adapter up the whole chain — `cosineCoeffs_halfstep_eq…`,
  `limitCoeff_eq_restartDuhamelCoeff_general`, `picardLimitRestart_general`,
  `Hu_of_restart_localized` — producing the subtype-continuity variant
  `Hu_of_restart_localized_of_subtypeCont`, with which the ledger sweep's
  `Hu_of_reduced` is discharged (the ledger carries `Continuous u₀`, not the false
  lift continuity).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitTimeNhdLocalized

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainConstExtend)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn duhamelSpectralCoeff_general_split_on
    summable_abs_limitCoeff_weak)
-- `limit_lift_eq_cosineSeries_of_subtypeCont` lives at top level (outside the
-- `ShenWork.IntervalPicardLimitRestartWeak` namespace), so it is referenced fully.
open ShenWork.IntervalPicardLimitSourceData
  (restartDuhamelCoeff_eq_localRestartCoeff source_family_eq_w)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
open ShenWork.IntervalPicardIterateRestart (cosineCoeffs_of_l1_cosineSeries)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalTimeSoftClamp (φ)

noncomputable section

namespace ShenWork.Paper2.TimeNhdSubtype

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 1. Coefficient identity at the restart base — subtype variant.

Mirror of `IntervalPicardLimitRestartWeak.cosineCoeffs_halfstep_eq_limitCoeff_weak`,
with the from-zero representation supplied by
`limit_lift_eq_cosineSeries_of_subtypeCont` (subtype `Continuous u₀` + constExtend
slice continuity) instead of `limit_lift_eq_cosineSeries_weak` (false lift
continuity).  Note the adapter representation needs `hfix` only at the single
target time `τ`. -/
theorem cosineCoeffs_halfstep_eq_limitCoeff_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {T τ : ℝ}
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    (hτ : 0 < τ) (hτT : τ ≤ T)
    (hfix_τ : ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u τ) x = intervalGradientDuhamelMap p u₀ u τ ⟨x, hx⟩)
    (hLc_ce : ∀ s, 0 < s → s ≤ τ →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (u τ)) k
      = ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ k := by
  have hrepr : ∀ x ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (u τ) x
        = ∑' j, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ j
            * cosineMode j x := fun x hx =>
    limit_lift_eq_cosineSeries_of_subtypeCont p hχ0 u₀ u hu₀_cont hu₀_bound hsrc0
      hτ hτT hfix_τ hLc_ce hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_limitCoeff_weak p u₀ u hu₀_bound hsrc0 hτ hτT) k

/-! ## 2. General restart coefficient identity — subtype variant.

Mirror of `IntervalPicardLimitTimeNhd.limitCoeff_eq_restartDuhamelCoeff_general`.
The only lift-continuity consumer there was `hbase` (via
`cosineCoeffs_halfstep_eq_limitCoeff_weak`); we feed it deliverable 1 instead.
`hsplit` (`duhamelSpectralCoeff_general_split_on`) needs only `hsrc0.hcont`, no
lift continuity. -/
theorem limitCoeff_eq_restartDuhamelCoeff_general_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {T τ t : ℝ}
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    (hτ : 0 < τ) (hτt : τ < t) (htT : t ≤ T)
    (hfix_τ : ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u τ) x = intervalGradientDuhamelMap p u₀ u τ ⟨x, hx⟩)
    (hLc_ce : ∀ s, 0 < s → s ≤ τ →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    (k : ℕ) :
    ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k
      = restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (u τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k)
          (t - τ) k := by
  -- restart-base coefficient: coeffs u(τ) = limitCoeff τ (subtype variant)
  have hbase : cosineCoeffs (intervalDomainLift (u τ)) k
      = ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ k :=
    cosineCoeffs_halfstep_eq_limitCoeff_of_subtypeCont p hχ0 u₀ u hu₀_cont hu₀_bound
      hsrc0 hτ (le_trans hτt.le htT) hfix_τ hLc_ce k
  unfold restartDuhamelCoeff
  rw [hbase]
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  -- general split of the source Duhamel coefficient at base τ (horizon-bounded)
  have hsplit := duhamelSpectralCoeff_general_split_on (a :=
      fun s k => cosineCoeffs (logisticLifted p (u s)) k) hsrc0.hcont
      hτ.le hτt.le htT k
  -- factor the homogeneous part: e^{−tλ} = e^{−(t−τ)λ}·e^{−τλ}
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-(t - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, hsplit]
  ring

/-! ## 3. General restart representation (EqOn) — subtype variant.

Mirror of `IntervalPicardLimitTimeNhd.picardLimitRestart_general`.  The from-zero
representation at the target `t` is supplied by
`limit_lift_eq_cosineSeries_of_subtypeCont` (needs `hfix` only at `t`); the
coefficient identity is deliverable 2.  We take `hfix` in the same `∀ s, 0 < s →
s ≤ t → …` form as the original and specialize at `t` (for the from-zero rep) and
at `τ` (for deliverable 2). -/
theorem picardLimitRestart_general_of_subtypeCont
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {T τ t : ℝ}
    (hfix : ∀ s, 0 < s → s ≤ t → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    (hτ : 0 < τ) (hτt : τ < t) (htT : t ≤ T)
    (hLc_ce : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))) :
    Set.EqOn (intervalDomainLift (u t))
      (fun x => ∑' k : ℕ,
        restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (u τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k)
          (t - τ) k * cosineMode k x)
      (Set.Icc (0:ℝ) 1) := by
  have ht : 0 < t := lt_trans hτ hτt
  intro x hx
  rw [limit_lift_eq_cosineSeries_of_subtypeCont p hχ0 u₀ u hu₀_cont hu₀_bound hsrc0
        ht htT (fun y hy => hfix t ht le_rfl y hy) hLc_ce hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  exact limitCoeff_eq_restartDuhamelCoeff_general_of_subtypeCont p hχ0 u₀ u
    hu₀_cont hu₀_bound hsrc0 hτ hτt htT
    (fun y hy => hfix τ hτ hτt.le y hy)
    (fun s hs hsτ => hLc_ce s hs (le_of_lt (lt_of_le_of_lt hsτ hτt))) k

/-! ## 4. `Hu` from time-localized data — subtype variant.

Copy of `TimeNhdLocalized.Hu_of_restart_localized` with:
* `hu₀_cont : Continuous (intervalDomainLift u₀)` → `Continuous u₀` (subtype);
* `hLc : … Continuous (logisticLifted p (u s))` → the constExtend form
  `hLc_ce : … Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))`;
* the `picardLimitRestart_general` call → `picardLimitRestart_general_of_subtypeCont`.

The clamped witness package, the M-bound block, and the integral congr are
IDENTICAL — none consumes lift continuity. -/
theorem Hu_of_restart_localized_of_subtypeCont
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hfix : ∀ s, 0 < s → s < T → ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u s) x = intervalGradientDuhamelMap p u₀ u s ⟨x, hx⟩)
    (hsrc0 : DuhamelSourceL1ContOn
      (fun s k => cosineCoeffs (logisticLifted p (u s)) k) T)
    -- K2: per-slice representation and bounds, time-localized
    {Msup : ℝ}
    (bc : ℝ → ℕ → ℝ)
    (hbsum : ∀ σ, 0 < σ → σ < T →
      Summable (fun n => unitIntervalCosineEigenvalue n * |bc σ n|))
    (hagree : ∀ σ, 0 < σ → σ < T → Set.EqOn (intervalDomainLift (u σ))
      (fun x => ∑' n, bc σ n * cosineMode n x) (Set.Icc (0 : ℝ) 1))
    (hpost : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u σ) x)
    (hubt : ∀ σ, 0 < σ → σ < T →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift (u σ) x ≤ Msup)
    -- K2: gradient/Hessian bounds, PER-COMPACT (the satisfiable form)
    (hG1t : ∀ a' b', 0 < a' → b' < T → ∃ G1, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (intervalDomainLift (u σ)) x| ≤ G1)
    (hG2t : ∀ a' b', 0 < a' → b' < T → ∃ G2, ∀ σ ∈ Set.Icc a' b',
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (intervalDomainLift (u σ))) x| ≤ G2)
    -- K1: UNSHIFTED source-coefficient time-C¹ data on (0,T), per-compact bound
    (adott : ℝ → ℕ → ℝ)
    (hderivt : ∀ σ, 0 < σ → σ < T → ∀ k, HasDerivAt
      (fun r => cosineCoeffs
        (logisticSourceFun p.a p.b p.α (intervalDomainLift (u r))) k)
      (adott σ k) σ)
    (hadotcontt : ∀ k, ContinuousOn (fun σ => adott σ k) (Set.Ioo 0 T))
    (hMdott : ∀ a' b', 0 < a' → b' < T → ∃ Mdot, ∀ σ ∈ Set.Icc a' b',
      ∀ k, |adott σ k| ≤ Mdot)
    -- H3 slice continuity — constExtend (subtype) form
    (hLc_ce : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t →
        Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s)))) :
    HasTimeNeighborhoodSpectralAgreement T u := by
  constructor
  intro t₀ ht₀ ht₀T
  -- restart base / offset
  set τ : ℝ := t₀ / 2 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτT : τ < T := by rw [hτdef]; linarith
  -- clamp window: id-zone [c,d] = [τ, (t₀+T)/2], range window [c',d'] ⊂ (0,T)
  set c' : ℝ := t₀ / 4 with hc'def
  set d : ℝ := (t₀ + T) / 2 with hddef
  set d' : ℝ := (t₀ + 3 * T) / 4 with hd'def
  have hc' : c' < τ := by rw [hc'def, hτdef]; linarith
  have hcd : τ ≤ d := by rw [hddef, hτdef]; linarith
  have hd' : d < d' := by rw [hddef, hd'def]; linarith
  have hc'pos : 0 < c' := by rw [hc'def]; linarith
  have hd'T : d' < T := by rw [hd'def]; linarith
  -- window membership facts
  have hwin : ∀ σ ∈ Set.Icc c' d', 0 < σ ∧ σ < T := fun σ hσ =>
    ⟨lt_of_lt_of_le hc'pos hσ.1, lt_of_le_of_lt hσ.2 hd'T⟩
  -- per-compact bounds on the window
  obtain ⟨G1, hG1⟩ := hG1t c' d' hc'pos hd'T
  obtain ⟨G2, hG2⟩ := hG2t c' d' hc'pos hd'T
  obtain ⟨Mdot, hMdot⟩ := hMdott c' d' hc'pos hd'T
  -- the clamped TimeC1 witness package
  have srcC : DuhamelSourceTimeC1
      (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
        (intervalDomainLift (u (φ c' τ d d' (τ + σ))))) k) :=
    clampedSource_duhamelSourceTimeC1 p u hα ha hb hc' hcd hd'
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
  -- the witness tuple
  refine ⟨cosineCoeffs (intervalDomainLift (u τ)), 2 * Msup, ?_, ?_,
    (fun σ k => cosineCoeffs (logisticSourceFun p.a p.b p.α
      (intervalDomainLift (u (φ c' τ d d' (τ + σ))))) k), srcC, τ, ?_, ?_⟩
  · -- 0 ≤ 2·Msup
    have hMnn : 0 ≤ Msup := by
      have h1 := hubt τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
      have h2 := hpost τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
      linarith
    linarith
  · -- |coeffs u(τ) k| ≤ 2·Msup
    have hMnn : 0 ≤ Msup := by
      have h1 := hubt τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
      have h2 := hpost τ hτpos hτT 0 ⟨le_rfl, zero_le_one⟩
      linarith
    intro k
    refine cosineCoeffs_abs_le_of_continuous_bounded
      (((ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
        (hbsum τ hτpos hτT)).continuous.continuousOn).congr
          (hagree τ hτpos hτT)) hMnn ?_ k
    intro x hx
    rw [abs_of_pos (hpost τ hτpos hτT x hx)]
    exact hubt τ hτpos hτT x hx
  · -- 0 < t₀ − offset = τ
    rw [hτdef]; linarith
  · -- eventually-nhds agreement on the open right half-neighbourhood Ioo τ d
    have hmem : t₀ ∈ Set.Ioo τ d := by
      constructor
      · rw [hτdef]; linarith
      · rw [hddef]; linarith
    have hopen : IsOpen (Set.Ioo τ d) := isOpen_Ioo
    filter_upwards [hopen.mem_nhds hmem] with s hs
    -- s ∈ Ioo τ d ⊆ (0, T)
    have hτs : τ < s := hs.1
    have hsd : s < d := hs.2
    have hsT : s < T := lt_trans hsd (lt_trans hd' hd'T)
    have hspos : 0 < s := lt_trans hτpos hτs
    -- general restart identity at time s, base τ, horizon s − τ (canonical family)
    have heqon := picardLimitRestart_general_of_subtypeCont p hχ0 u₀ u
      (fun r hr hrs => hfix r hr (lt_of_le_of_lt hrs hsT))
      hu₀_cont hu₀_bound hsrc0 hτpos hτs hsT.le
      (fun r hr hrs => hLc_ce s hspos hsT r hr hrs)
    intro x
    have hx1 : x.1 ∈ Set.Icc (0:ℝ) 1 := x.2
    have hlift : u s x = intervalDomainLift (u s) x.1 := by
      simp only [intervalDomainLift, hx1, dif_pos, Subtype.eta]
    rw [hlift, heqon hx1]
    refine tsum_congr (fun k => ?_)
    congr 1
    -- restartDuhamelCoeff (canonical shifted) = localRestartCoeff (clamped)
    rw [restartDuhamelCoeff_eq_localRestartCoeff]
    unfold localRestartCoeff
    congr 1
    -- Duhamel parts: integrands agree on [0, s−τ] (absolute times in [τ,s] ⊆ [c,d])
    unfold duhamelSpectralCoeff
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ s - τ)] at hσ
    have hmem_cd : τ + σ ∈ Set.Icc τ d :=
      ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    simp only
    congr 1
    -- canonical: coeffs (logisticLifted p (u (τ+σ))); clamped at φ(τ+σ) = τ+σ
    rw [clampedFamily_eq_on p u hc' hd' hmem_cd k]
    exact congrFun (congrFun (source_family_eq_w p u) (τ + σ)) k

end ShenWork.Paper2.TimeNhdSubtype
