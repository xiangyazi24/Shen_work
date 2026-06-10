/-
  ShenWork/Paper2/IntervalPicardLimitTimeNhdLocalized.lean

  **`Hu_of_restart_localized` — time-neighborhood spectral agreement from
  TIME-LOCALIZED ledger data via soft-clamped witnesses.**

  `Hu_of_restart` (IntervalPicardLimitTimeNhd) demands GLOBAL K2/K1 data:
  slice bounds/representation for ALL σ ∈ ℝ, a single uniform gradient bound
  G1 over all σ, and the t/2-shifted K1 family with global `HasDerivAt`.
  For an arbitrary `GradientMildSolutionData` these are unfillable (D.u is
  unconstrained outside (0,T]) — and the uniform G1 over (0,T) is genuinely
  FALSE for merely-continuous u₀ (parabolic smoothing ~σ^{-1/2} blowup).

  This file dissolves all of that.  `HasTimeNeighborhoodSpectralAgreement`
  quantifies the witness source family EXISTENTIALLY per t₀, so we are free to
  choose it: we take the SOFT-CLAMPED family

      aC σ k = cosineCoeffs (logisticSourceFun … (lift (u (φ (τ+σ))))) k,

  where `φ = IntervalTimeSoftClamp.φ c' c d d'` is C¹, equal to the identity
  on `[c,d] = [τ, (t₀+T)/2]` (⊇ every restart integration range for s near
  t₀), with range inside the compact window `[c',d'] = [t₀/4, (t₀+3T)/4] ⊂
  (0,T)`.  The `DuhamelSourceTimeC1` package for `aC` is produced by
  `clampedSource_duhamelSourceTimeC1` from data required ONLY on the window:

  * K2 slice bounds/representation: time-localized (σ ∈ (0,T)) suffices;
  * gradient/Hessian bounds: PER-COMPACT (∃ G1 per [a,b] ⋐ (0,T)) — the
    satisfiable form;
  * K1: `HasDerivAt`/continuity/bound of the UNSHIFTED `adott` on (0,T) —
    the shifted family is DERIVED by the chain rule (5 ledger fields gone).

  The agreement transfers from `picardLimitRestart_general` because on the
  integration range `[0, s−τ]` the absolute times `τ+σ ∈ [τ,s] ⊆ [c,d]` where
  `φ = id`, so `localRestartCoeff a₀ aC = restartDuhamelCoeff a₀ aS`
  (canonical) by `intervalIntegral.integral_congr`.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitTimeNhd
import ShenWork.Paper2.IntervalDomainClampedSourceRepresentation

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun cosineCoeffs_abs_le_of_continuous_bounded)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)
open ShenWork.IntervalPicardLimitSourceData
  (restartDuhamelCoeff_eq_localRestartCoeff source_family_eq_w)
open ShenWork.IntervalPicardLimitTimeNhd (picardLimitRestart_general)
open ShenWork.Paper2.ClampedSourceRepresentation
  (clampedSource_duhamelSourceTimeC1 clampedFamily_eq_on)
open ShenWork.IntervalTimeSoftClamp (φ)

noncomputable section

namespace ShenWork.Paper2.TimeNhdLocalized

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-- **`Hu` from TIME-LOCALIZED data (soft-clamped witness).**  All K2/K1
hypotheses are required only on `(0,T)` (with gradient/Hessian/derivative
bounds per-compact), matching what a `GradientMildSolutionData` can actually
supply.  No shifted-family data is taken: the witness's derivative data is
derived from the unshifted `adott` by the chain rule through the clamp. -/
theorem Hu_of_restart_localized
    {p : CM2Params} (hχ0 : p.χ₀ = 0)
    {u₀ : intervalDomainPoint → ℝ} (u : ℝ → intervalDomainPoint → ℝ)
    {T : ℝ}
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
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
    -- H3 slice continuity
    (hLc : ∀ t, 0 < t → t < T →
      ∀ s, 0 < s → s ≤ t → Continuous (logisticLifted p (u s))) :
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
    have heqon := picardLimitRestart_general p hχ0 u₀ u
      (fun r hr hrs => hfix r hr (lt_of_le_of_lt hrs hsT))
      hu₀_cont hu₀_bound hsrc0 hτpos hτs hsT.le
      (fun r hr hrs => hLc s hspos hsT r hr hrs)
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

end ShenWork.Paper2.TimeNhdLocalized
