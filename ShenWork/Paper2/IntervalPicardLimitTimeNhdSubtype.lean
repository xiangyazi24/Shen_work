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
import ShenWork.Paper2.IntervalPicardLimitRestartBdd
import ShenWork.Paper2.IntervalPicardLimitBddProducer

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
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn summable_abs_duhamelSpectralCoeff_bdd
    limit_lift_eq_cosineSeries_of_subtypeCont_bdd summable_abs_limitCoeff_bdd
    duhamelSpectral_eq_cosineSeries_bdd)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource patchedSource_eq_of_pos)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalPicardIterateRestart
  (heatValue_eq_cosineSeries intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalDomain (constExtend_eq_lift_on_Icc)

noncomputable section

namespace ShenWork.Paper2.TimeNhdSubtype

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 0. Patched-to-canonical bridge.

The Provider can only build a `DuhamelSourceBddOn` for the PATCHED family
`patchedSource p u₀ u` (the canonical limit-source family is genuinely unbounded
at `s = 0` for merely-continuous `u₀`).  Since `patchedSource = canonical` on
`s > 0` (`patchedSource_eq_of_pos`) and every Duhamel integral runs over `(0, t]`
where the `s = 0` endpoint is measure-null, the per-mode Duhamel coefficients of
the two families coincide for `t > 0`.  This bridge lets the bounded-source
entry points (keyed on the canonical family) be driven by the patched package. -/

/-- For `0 < t` the patched and canonical Duhamel coefficients agree (the families
differ only at the measure-null endpoint `s = 0`). -/
theorem duhamelSpectralCoeff_patched_eq_canonical
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    duhamelSpectralCoeff (patchedSource p u₀ u) t k
      = duhamelSpectralCoeff (fun s k => cosineCoeffs (logisticLifted p (u s)) k) t k := by
  unfold duhamelSpectralCoeff
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le ht.le]
  refine Filter.Eventually.of_forall (fun s hsIoc => ?_)
  rw [patchedSource_eq_of_pos p u₀ u hsIoc.1 k]

/-- The `limitCoeff` of the canonical family equals the same expression with the
patched Duhamel coefficient (for `0 < t`). -/
theorem limitCoeff_eq_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k
      = Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
        + duhamelSpectralCoeff (patchedSource p u₀ u) t k := by
  unfold ShenWork.IntervalPicardLimitRestart.limitCoeff
  rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ u ht k]

/-- **`ℓ¹` summability of `limitCoeff` from the PATCHED bounded package.**
Mirror of `IntervalPicardLimitRestartBdd.summable_abs_limitCoeff_bdd` but driven
by the patched package (the canonical Duhamel part is rewritten to the patched one
through the measure-null endpoint). -/
theorem summable_abs_limitCoeff_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ u) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ) :
    Summable (fun k =>
      |ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k|) := by
  have hhom : Summable (fun k =>
      |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hduh : Summable (fun k => |duhamelSpectralCoeff (patchedSource p u₀ u) t k|) :=
    summable_abs_duhamelSpectralCoeff_bdd src ht htτ
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  rw [limitCoeff_eq_patched p u₀ u ht k]
  exact abs_add_le _ _

/-- **Cosine representation of the Picard limit (subtype-continuity, PATCHED
bounded source).**  Mirror of
`IntervalPicardLimitRestartBdd.limit_lift_eq_cosineSeries_of_subtypeCont_bdd`
driven by the patched package: the Duhamel integral reads the patched family on
`(0, t]` (where it equals the canonical one), the spectral swap and the
final-summability run on the patched package, and the resulting coefficients are
bridged back to `limitCoeff` (canonical) via `limitCoeff_eq_patched`. -/
theorem limit_lift_eq_cosineSeries_of_subtypeCont_patched
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (u : ℝ → intervalDomainPoint → ℝ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ u) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ)
    (hfix_t : ∀ x : ℝ, (hx : x ∈ Set.Icc (0:ℝ) 1) →
      intervalDomainLift (u t) x = intervalGradientDuhamelMap p u₀ u t ⟨x, hx⟩)
    (hL_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalDomainConstExtend (intervalLogisticSource p (u s))))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (u t) x
      = ∑' k, ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u t k * cosineMode k x := by
  -- Subtype continuity of the logistic source from constExtend continuity.
  have hL_subtype : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (u s)) := by
    intro s hs hsT
    have heq : intervalLogisticSource p (u s) =
        (intervalDomainConstExtend (intervalLogisticSource p (u s))) ∘ Subtype.val := by
      funext ⟨y, hy⟩
      simp only [Function.comp]
      rw [constExtend_eq_lift_on_Icc hy]
      simp only [intervalDomainLift]
      split_ifs with h
      · exact congr_arg _ (Subtype.ext rfl)
      · exact absurd hy h
    rw [heq]; exact (hL_cont s hs hsT).comp continuous_subtype_val
  rw [hfix_t x hx,
    intervalGradientDuhamelMap_eq_of_chi0_zero
      p hχ0 u₀ _ t ⟨x, hx⟩]
  have hhom : intervalFullSemigroupOperator t
        (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * unitIntervalCosineEigenvalue k)
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
          ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  -- the Duhamel integrand reads the PATCHED family on (0,t] (= canonical there)
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s)
            (patchedSource p u₀ u s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hsub : Continuous (intervalLogisticSource p (u s)) :=
      hL_subtype s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs (logisticLifted p (u s)) k| ≤ src.M := by
      intro k
      have := src.hM s (le_of_lt hs.1) (le_trans (le_of_lt hs.2) htτ) k
      rwa [patchedSource_eq_of_pos p u₀ u hs.1 k] at this
    have hcanon : unitIntervalCosineHeatValue
          (t - s) (patchedSource p u₀ u s) x
        = unitIntervalCosineHeatValue (t - s)
            (fun k => cosineCoeffs (logisticLifted p (u s)) k) x := by
      congr 1; funext k; exact patchedSource_eq_of_pos p u₀ u hs.1 k
    rw [hcanon]
    show intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalLogisticSource p (u s))) x
        = unitIntervalCosineHeatValue (t - s)
            (fun k => cosineCoeffs (logisticLifted p (u s)) k) x
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        hts hsub hMs hx
  have hduh_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (u s)) x)
      = ∫ s in (0:ℝ)..t,
          unitIntervalCosineHeatValue (t - s)
            (patchedSource p u₀ u s) x := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0:ℝ) t → s ∈ Set.Ioo (0:ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hsmem
      refine ⟨hsmem.1, lt_of_le_of_ne hsmem.2 ?_⟩
      intro hst; exact hs (by simp [hst])
    filter_upwards [hmem] with s hs hsIoc
    exact hduh_integrand s (hs hsIoc)
  rw [hhom, hduh_eq, duhamelSpectral_eq_cosineSeries_bdd src ht htτ]
  have hcosbd : ∀ (c : ℕ → ℝ) (k : ℕ), ‖c k * cosineMode k x‖ ≤ |c k| := by
    intro c k
    rw [Real.norm_eq_abs, abs_mul]
    calc |c k| * |cosineMode k x| ≤ |c k| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          simpa [cosineMode] using Real.abs_cos_le_one ((k : ℝ) * Real.pi * x)
      _ = |c k| := mul_one _
  have hsum_hom : Summable (fun k =>
      (Real.exp (-t * unitIntervalCosineEigenvalue k) * cosineCoeffs (intervalDomainLift u₀) k)
        * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hsum_duh : Summable (fun k =>
      duhamelSpectralCoeff (patchedSource p u₀ u) t k * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    exact summable_abs_duhamelSpectralCoeff_bdd src ht htτ
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  rw [limitCoeff_eq_patched p u₀ u ht k]
  ring

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
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
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
    limit_lift_eq_cosineSeries_of_subtypeCont_patched p hχ0 u₀ u hu₀_cont hu₀_bound hsrc0
      hτ hτT hfix_τ hLc_ce hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_limitCoeff_patched p u₀ u hu₀_bound hsrc0 hτ hτT) k

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
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
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
  have ht : 0 < t := lt_trans hτ hτt
  -- restart-base coefficient: coeffs u(τ) = limitCoeff τ (subtype variant)
  have hbase : cosineCoeffs (intervalDomainLift (u τ)) k
      = ShenWork.IntervalPicardLimitRestart.limitCoeff p u₀ u τ k :=
    cosineCoeffs_halfstep_eq_limitCoeff_of_subtypeCont p hχ0 u₀ u hu₀_cont hu₀_bound
      hsrc0 hτ (le_trans hτt.le htT) hfix_τ hLc_ce k
  unfold restartDuhamelCoeff
  rw [hbase]
  -- express both limitCoeffs (target t, base τ) through the patched Duhamel part
  rw [limitCoeff_eq_patched p u₀ u ht k, limitCoeff_eq_patched p u₀ u hτ k]
  -- general split of the PATCHED source Duhamel coefficient at base τ
  have hsplit := duhamelSpectralCoeff_general_split_on (a := patchedSource p u₀ u)
      hsrc0.hcont hτ.le hτt.le htT k
  -- the shifted patched family equals the canonical shifted one pointwise
  -- (τ + σ ≥ τ > 0), so their Duhamel coefficients agree.
  have hshift : duhamelSpectralCoeff (fun σ k => patchedSource p u₀ u (τ + σ) k) (t - τ) k
      = duhamelSpectralCoeff (fun σ k => cosineCoeffs (logisticLifted p (u (τ + σ))) k)
          (t - τ) k := by
    unfold duhamelSpectralCoeff
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ t - τ)] at hσ
    simp only
    rw [patchedSource_eq_of_pos p u₀ u (by linarith [hτ, hσ.1] : 0 < τ + σ) k]
  -- factor the homogeneous part: e^{−tλ} = e^{−(t−τ)λ}·e^{−τλ}
  have hexp : Real.exp (-t * (λ_ k))
      = Real.exp (-(t - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, hsplit, hshift]
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
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
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
  rw [limit_lift_eq_cosineSeries_of_subtypeCont_patched p hχ0 u₀ u hu₀_cont hu₀_bound hsrc0
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
    (hsrc0 : DuhamelSourceBddOn (patchedSource p u₀ u) T)
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
