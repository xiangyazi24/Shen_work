/-
  ShenWork/Paper2/IntervalPicardIterateBddRepr.lean

  **Iterate from-zero representation against the PATCHED bounded source (K1 wall).**

  The iterate-side mirror of `IntervalPicardLimitTimeNhdSubtype` (the limit side's
  solved pattern).  The original iterate from-zero representation
  (`IntervalPicardSourceSubtypeCont.iterate_lift_eq_cosineSeries_of_sourceSubtypeCont`)
  consumes the FULL canonical `DuhamelSourceTimeC1` package `hsrc0`, whose ℓ¹
  envelope must hold UNIFORMLY down to `s = 0` — the documented unfillable "t→0
  disease" for merely-continuous data.  This file reproves the chain against the
  SATISFIABLE bounded package `DuhamelSourceBddOn (patchedSource p u₀ (picardIter …))`
  (constant `M` on `[0,τ]` + per-window decaying envelopes), producible entirely from
  tower-internal data (`IntervalPicardIterateBddProducer.duhamelSourceBddOn_of_slices`).

  Three deliverables (exact clones of the `SourceSubtypeCont` chain, BddOn-driven):
  * `iterate_lift_eq_cosineSeries_of_sourceBdd`     — from-zero EqOn at `t`;
  * `cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceBdd` — restart-base coeff identity;
  * `picardIterateRestart_general_of_sourceBdd`     — general restart EqOn (the
    `windowAdotLegs_step` consumer).

  The Duhamel integral reads the patched family on `(0,t]` where it equals the
  canonical one (`patchedSource_eq_of_pos`), so the spectral swap / summability run on
  the patched package and the result bridges back to `iterateCoeff` (canonical).

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateBddProducer
import ShenWork.Paper2.IntervalPicardSourceSubtypeCont
import ShenWork.Paper2.IntervalPicardLimitTimeNhd

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (intervalGradientDuhamelMap logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalMildPicardRegularity (logisticSourceFun)
open ShenWork.IntervalPicardIterateRestart
  (iterateCoeff heatValue_eq_cosineSeries cosineCoeffs_of_l1_cosineSeries
   intervalGradientDuhamelMap_eq_of_chi0_zero)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff)
open ShenWork.IntervalPicardIterateRepresentation (iterateReprCoeff)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn summable_abs_duhamelSpectralCoeff_bdd
   duhamelSpectral_eq_cosineSeries_bdd)
open ShenWork.IntervalPicardLimitBddProducer (patchedSource patchedSource_eq_of_pos)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalSemigroupComposition (expEigSummable)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)

noncomputable section

namespace ShenWork.IntervalPicardIterateBddRepr

local notation "λ_" n => unitIntervalCosineEigenvalue n

/-! ## 0. Patched-to-canonical bridge for the iterate source. -/

/-- For `0 < t` the patched and canonical iterate-Duhamel coefficients agree (the
families differ only at the measure-null endpoint `s = 0`). -/
theorem duhamelSpectralCoeff_patched_eq_canonical
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    duhamelSpectralCoeff (patchedSource p u₀ (picardIter p u₀ n)) t k
      = duhamelSpectralCoeff
          (fun s k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) t k := by
  unfold duhamelSpectralCoeff
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le ht.le]
  refine Filter.Eventually.of_forall (fun s hsIoc => ?_)
  rw [patchedSource_eq_of_pos p u₀ (picardIter p u₀ n) hsIoc.1 k]

/-- The `iterateCoeff` of the canonical family equals the same expression with the
patched Duhamel coefficient (for `0 < t`). -/
theorem iterateCoeff_eq_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    iterateCoeff p u₀ n t k
      = Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k
        + duhamelSpectralCoeff (patchedSource p u₀ (picardIter p u₀ n)) t k := by
  unfold iterateCoeff
  rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ n ht k]

/-- **`ℓ¹` summability of `iterateCoeff` from the patched bounded package.** -/
theorem summable_abs_iterateCoeff_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ) :
    Summable (fun k => |iterateCoeff p u₀ n t k|) := by
  have hhom : Summable (fun k =>
      |Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k|) := by
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hduh : Summable (fun k =>
      |duhamelSpectralCoeff (patchedSource p u₀ (picardIter p u₀ n)) t k|) :=
    summable_abs_duhamelSpectralCoeff_bdd src ht htτ
  refine (hhom.add hduh).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
  rw [iterateCoeff_eq_patched p u₀ n ht k]
  exact abs_add_le _ _

/-! ## 1. From-zero representation against the patched bounded source. -/

/-- **Iterate from-zero cosine representation (patched bounded source).**  Mirror of
`IntervalPicardSourceSubtypeCont.iterate_lift_eq_cosineSeries_of_sourceSubtypeCont`,
driven by the patched `DuhamelSourceBddOn` instead of the canonical
`DuhamelSourceTimeC1`. -/
theorem iterate_lift_eq_cosineSeries_of_sourceBdd
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ)
    (hLs_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)))
    {x : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) :
    intervalDomainLift (picardIter p u₀ (n+1) t) x
      = ∑' k, iterateCoeff p u₀ n t k * cosineMode k x := by
  have hlift : intervalDomainLift (picardIter p u₀ (n+1) t) x
      = intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t ⟨x, hx⟩ := by
    show (if hx' : x ∈ Set.Icc (0:ℝ) 1 then
          picardIter p u₀ (n+1) t ⟨x, hx'⟩ else 0) = _
    rw [dif_pos hx]
    rfl
  rw [hlift, intervalGradientDuhamelMap_eq_of_chi0_zero p hχ0 u₀ _ t ⟨x, hx⟩]
  -- homogeneous propagator term — SUBTYPE route.
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      = ∑' k, (Real.exp (-t * (λ_ k))
          * cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
          ht hu₀_cont hu₀_bound hx]
    exact heatValue_eq_cosineSeries t _ x
  -- Duhamel integrand reads the patched family on (0,t] (= canonical there).
  have hduh_integrand : ∀ s ∈ Set.Ioo (0:ℝ) t,
      intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x
        = unitIntervalCosineHeatValue (t - s)
            (patchedSource p u₀ (picardIter p u₀ n) s) x := by
    intro s hs
    have hts : 0 < t - s := by linarith [hs.2]
    have hcont : Continuous (intervalLogisticSource p (picardIter p u₀ n s)) :=
      hLs_cont s hs.1 (le_of_lt hs.2)
    have hMs : ∀ k, |cosineCoeffs
        (intervalDomainLift (intervalLogisticSource p (picardIter p u₀ n s))) k|
        ≤ src.M := by
      intro k
      have := src.hM s (le_of_lt hs.1) (le_trans (le_of_lt hs.2) htτ) k
      rwa [patchedSource_eq_of_pos p u₀ (picardIter p u₀ n) hs.1 k] at this
    have hcanon : unitIntervalCosineHeatValue
          (t - s) (patchedSource p u₀ (picardIter p u₀ n) s) x
        = unitIntervalCosineHeatValue (t - s)
            (fun k => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k) x := by
      congr 1; funext k; exact patchedSource_eq_of_pos p u₀ (picardIter p u₀ n) hs.1 k
    rw [hcanon]
    exact intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      hts hcont hMs hx
  have hduh_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (picardIter p u₀ n s)) x)
      = ∫ s in (0:ℝ)..t,
          unitIntervalCosineHeatValue (t - s)
            (patchedSource p u₀ (picardIter p u₀ n) s) x := by
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
      (Real.exp (-t * (λ_ k)) * cosineCoeffs (intervalDomainLift u₀) k)
        * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((expEigSummable ht).mul_right M₀)
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hu₀_bound k) (Real.exp_pos _).le
  have hsum_duh : Summable (fun k =>
      duhamelSpectralCoeff (patchedSource p u₀ (picardIter p u₀ n)) t k
        * cosineMode k x) := by
    refine Summable.of_norm_bounded ?_ (hcosbd _)
    exact summable_abs_duhamelSpectralCoeff_bdd src ht htτ
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun k => ?_)
  rw [iterateCoeff_eq_patched p u₀ n ht k]
  ring

/-! ## 2. Restart-base coefficient identity. -/

/-- **Restart-base coefficient identity (patched bounded source).** -/
theorem cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceBdd
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {τ : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) τ)
    {t : ℝ} (ht : 0 < t) (htτ : t ≤ τ)
    (hLs_cont : ∀ s, 0 < s → s ≤ t →
      Continuous (intervalLogisticSource p (picardIter p u₀ n s)))
    (k : ℕ) :
    cosineCoeffs (intervalDomainLift (picardIter p u₀ (n+1) t)) k
      = iterateCoeff p u₀ n t k := by
  have hrepr : ∀ x ∈ Set.Icc (0:ℝ) 1,
      intervalDomainLift (picardIter p u₀ (n+1) t) x
        = ∑' j, iterateCoeff p u₀ n t j * cosineMode j x := fun x hx =>
    iterate_lift_eq_cosineSeries_of_sourceBdd p hχ0 u₀ n hu₀_cont hu₀_bound
      src ht htτ hLs_cont hx
  rw [cosineCoeffs_congr_on_Icc hrepr k]
  exact cosineCoeffs_of_l1_cosineSeries
    (summable_abs_iterateCoeff_bdd p u₀ n hu₀_bound src ht htτ) k

/-! ## 3. General restart representation (the `windowAdotLegs_step` consumer). -/

/-- **General-offset iterate restart EqOn (patched bounded source).**  Mirror of
`IntervalPicardWindowAdot.picardIterateRestart_general` driven by the patched bounded
source: from-zero representation at the target `s` + the restart-base coefficient
identity at `τ`, with the general Duhamel split run on the patched family. -/
theorem picardIterateRestart_general_of_sourceBdd
    (p : CM2Params) (hχ0 : p.χ₀ = 0)
    (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    (hu₀_cont : Continuous u₀)
    {M₀ : ℝ} (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {T : ℝ} (src : DuhamelSourceBddOn (patchedSource p u₀ (picardIter p u₀ n)) T)
    {τ s : ℝ} (hτ : 0 < τ) (hτs : τ < s) (hsT : s ≤ T)
    (hLs_cont : ∀ r, 0 < r → r ≤ s →
      Continuous (intervalLogisticSource p (picardIter p u₀ n r))) :
    Set.EqOn (intervalDomainLift (picardIter p u₀ (n + 1) s))
      (fun x => ∑' k,
        localRestartCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)))
          (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (τ + σ))) k)
          (s - τ) k * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  have hs : 0 < s := lt_trans hτ hτs
  intro x hx
  -- from-zero representation of `iter(n+1) s`.
  rw [iterate_lift_eq_cosineSeries_of_sourceBdd p hχ0 u₀ n hu₀_cont hu₀_bound src hs hsT
        hLs_cont hx]
  refine tsum_congr (fun k => ?_)
  congr 1
  unfold localRestartCoeff
  -- base coefficient: coeffs(lift(iter(n+1) τ)) = iterateCoeff p u₀ n τ.
  have hbase : cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) τ)) k
      = iterateCoeff p u₀ n τ k :=
    cosineCoeffs_halfstep_eq_iterateCoeff_of_sourceBdd p hχ0 u₀ n hu₀_cont hu₀_bound
      src hτ (le_trans hτs.le hsT)
      (fun r hr hrτ => hLs_cont r hr (le_trans hrτ hτs.le)) k
  rw [hbase]
  -- express both iterateCoeffs (target s, base τ) through the patched Duhamel part.
  rw [iterateCoeff_eq_patched p u₀ n hs k, iterateCoeff_eq_patched p u₀ n hτ k]
  -- general split of the PATCHED source Duhamel coefficient at base τ.
  have hsplit := ShenWork.IntervalPicardLimitRestartWeak.duhamelSpectralCoeff_general_split_on
    (a := patchedSource p u₀ (picardIter p u₀ n))
    src.hcont hτ.le hτs.le hsT k
  -- the shifted patched family equals the canonical shifted one pointwise
  -- (τ + σ ≥ τ > 0), so their Duhamel coefficients agree.
  have hshift : duhamelSpectralCoeff
        (fun σ k => patchedSource p u₀ (picardIter p u₀ n) (τ + σ) k) (s - τ) k
      = duhamelSpectralCoeff
          (fun σ k => cosineCoeffs (logisticLifted p (picardIter p u₀ n (τ + σ))) k)
          (s - τ) k := by
    unfold duhamelSpectralCoeff
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ s - τ)] at hσ
    simp only
    rw [patchedSource_eq_of_pos p u₀ (picardIter p u₀ n)
      (by linarith [hτ, hσ.1] : 0 < τ + σ) k]
  -- factor the homogeneous part: e^{−sλ} = e^{−(s−τ)λ}·e^{−τλ}.
  have hexp : Real.exp (-s * (λ_ k))
      = Real.exp (-(s - τ) * (λ_ k)) * Real.exp (-τ * (λ_ k)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp, hsplit, hshift]
  ring

end ShenWork.IntervalPicardIterateBddRepr
