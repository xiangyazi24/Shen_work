/-
  Endpoint-safe B-form source coefficients.

  The raw conjugate Picard trajectory is not initialized at `t = 0`, so the
  canonical family `bFormSourceCoeffs p u 0` is not the physical source of the
  initial datum.  This file replaces only the non-positive-time value by the
  physical source of `u₀`.  The replacement is invisible to every positive-time
  Duhamel integral and agrees with the canonical family on every positive
  window.

  All proofs in this file are complete and kernel checked.
-/
import ShenWork.Paper2.IntervalSourceBridgeOpenRepresentativeOn
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.Paper2.IntervalPicardLimitRestartBdd

open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.BFormPatchedSource

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateKernelOperator
   intervalConjugateDuhamelMap)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalPicardLimitRestartWeak
  (DuhamelSourceL1ContOn abs_duhamelSpectralCoeff_le_weak
   duhamelSpectral_eq_cosineSeries_weak)
open ShenWork.IntervalPicardLimitRestartBdd
  (DuhamelSourceBddOn summable_abs_duhamelSpectralCoeff_bdd
   duhamelSpectral_eq_cosineSeries_bdd)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.CosineSpectrum (cosineMode)

/-- The physical B-form source coefficients of the initial datum.  The constant
trajectory is used only to reuse the canonical definitions of the logistic
source, the elliptic resolver, and the chemotaxis divergence. -/
def initialPhysicalBFormSourceCoeffs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ :=
  bFormSourceCoeffs p (fun _ => u₀) 0

/-- The endpoint-safe B-form source: physical initial source for `s ≤ 0`,
canonical conjugate-trajectory source for `s > 0`. -/
def patchedBFormSourceCoeffs
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : ℝ → ℕ → ℝ :=
  fun s n =>
    if s ≤ 0 then initialPhysicalBFormSourceCoeffs p u₀ n
    else bFormSourceCoeffs p u s n

theorem patchedBFormSourceCoeffs_zero
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (n : ℕ) :
    patchedBFormSourceCoeffs p u₀ u 0 n =
      initialPhysicalBFormSourceCoeffs p u₀ n := by
  simp [patchedBFormSourceCoeffs]

/-- Positive times see the canonical B-form source. -/
theorem patchedBFormSourceCoeffs_eq_of_pos
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    patchedBFormSourceCoeffs p u₀ u s n = bFormSourceCoeffs p u s n := by
  simp [patchedBFormSourceCoeffs, not_le.mpr hs]

/-- Exact strength of a weak patched package at the endpoint: it already
implies absolute summability of the physical initial-source coefficients.  In
particular, endpoint patching fixes the trajectory-value mismatch but does not
manufacture this spatial regularity for a merely continuous datum. -/
theorem initialPhysicalBFormSourceCoeffs_abs_summable_of_l1ContOn
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (src : DuhamelSourceL1ContOn (patchedBFormSourceCoeffs p u₀ u) T) :
    Summable (fun n => |initialPhysicalBFormSourceCoeffs p u₀ n|) := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    src.henv_summable
  simpa [patchedBFormSourceCoeffs] using src.henv_bound 0 le_rfl hT n

/-- Replacing the time-zero source does not change a positive-time Duhamel
coefficient. -/
theorem duhamelSpectralCoeff_patched_eq_canonical
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    duhamelSpectralCoeff (patchedBFormSourceCoeffs p u₀ u) t n =
      duhamelSpectralCoeff (bFormSourceCoeffs p u) t n := by
  unfold duhamelSpectralCoeff
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le ht.le]
  exact Filter.Eventually.of_forall (fun s hs => by
    rw [patchedBFormSourceCoeffs_eq_of_pos p u₀ u hs.1 n])

/-- The full heat-series Duhamel integrals are likewise unchanged. -/
theorem duhamelHeatValue_patched_eq_canonical
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (patchedBFormSourceCoeffs p u₀ u s) x) =
      ∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x := by
  refine intervalIntegral.integral_congr_ae ?_
  rw [Set.uIoc_of_le ht.le]
  exact Filter.Eventually.of_forall (fun s hs => by
    congr 1
    funext n
    exact patchedBFormSourceCoeffs_eq_of_pos p u₀ u hs.1 n)

/-- Consequently the from-zero restart coefficients are unchanged at positive
times. -/
theorem localRestartCoeff_patched_eq_canonical
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (a₀ : ℕ → ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    localRestartCoeff a₀ (patchedBFormSourceCoeffs p u₀ u) t n =
      localRestartCoeff a₀ (bFormSourceCoeffs p u) t n := by
  simp only [localRestartCoeff]
  rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ u ht n]

/-- Canonical positive-window `C¹` data transfers to the patched family.  No
regularity at the artificial time-zero value is asserted or used. -/
noncomputable def timeC1OnPatched_of_canonical_positive
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {c d : ℝ} (hc : 0 < c)
    (src : DuhamelSourceTimeC1On (bFormSourceCoeffs p u) c d) :
    DuhamelSourceTimeC1On (patchedBFormSourceCoeffs p u₀ u) c d where
  adot := src.adot
  hderiv := by
    intro s hs n
    exact (src.hderiv s hs n).congr_of_mem
      (fun r hr => patchedBFormSourceCoeffs_eq_of_pos p u₀ u
        (lt_of_lt_of_le hc hr.1) n) hs
  hadotcont := src.hadotcont
  envelope := src.envelope
  henv_summable := src.henv_summable
  henv_bound := by
    intro s hs n
    rw [patchedBFormSourceCoeffs_eq_of_pos p u₀ u
      (lt_of_lt_of_le hc hs.1) n]
    exact src.henv_bound s hs n
  derivBound := src.derivBound
  hderivBound := src.hderivBound

/-- A weak patched source package gives the canonical source-leg cosine
reconstruction, because both the physical integral and every Duhamel
coefficient ignore the changed endpoint. -/
theorem duhamelHeatValue_canonical_eq_cosineSeries_of_patched
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {T t x : ℝ}
    (src : DuhamelSourceL1ContOn (patchedBFormSourceCoeffs p u₀ u) T)
    (ht : 0 < t) (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x) =
      ∑' n, duhamelSpectralCoeff (bFormSourceCoeffs p u) t n *
        cosineMode n x := by
  rw [← duhamelHeatValue_patched_eq_canonical p u₀ u ht x]
  rw [duhamelSpectral_eq_cosineSeries_weak src ht htT]
  refine tsum_congr (fun n => ?_)
  rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ u ht n]

/-- Bounded-source version of the canonical source-leg reconstruction.  This
is the endpoint-safe interface for continuous initial data: it needs only a
uniform mode bound down to zero and summable envelopes on positive compact
windows. -/
theorem duhamelHeatValue_canonical_eq_cosineSeries_of_patched_bdd
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    {T t x : ℝ}
    (src : DuhamelSourceBddOn (patchedBFormSourceCoeffs p u₀ u) T)
    (ht : 0 < t) (htT : t ≤ T) :
    (∫ s in (0 : ℝ)..t,
        unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x) =
      ∑' n, duhamelSpectralCoeff (bFormSourceCoeffs p u) t n *
        cosineMode n x := by
  rw [← duhamelHeatValue_patched_eq_canonical p u₀ u ht x]
  rw [duhamelSpectral_eq_cosineSeries_bdd src ht htT]
  refine tsum_congr (fun n => ?_)
  rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ u ht n]

/-! ## Weak from-zero B-form cosine reconstruction -/

/-- The conjugate Duhamel map has its canonical B-form cosine series from a
weak package for the endpoint-patched source.  Positive-window `C¹` data is not
needed for this from-zero reconstruction; it is consumed later, after a
strictly positive restart. -/
theorem intervalConjugateDuhamelMap_cosineSeries_of_patched
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrc : DuhamelSourceL1ContOn (patchedBFormSourceCoeffs p u₀ u) T)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x := by
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x =
      ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x := by
    rw [
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        ht hu₀_cont hu₀_bound hx]
    simpa using congrFun
      (ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
        t (cosineCoeffs (intervalDomainLift u₀))) x
  have hsource_eq : (-p.χ₀) *
        (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add (hB_int.const_mul (-p.χ₀)) hlog_int]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume,
        s ∈ Set.Ioc (0 : ℝ) t → s ∈ Set.Ioo (0 : ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hst
      exact ⟨hst.1, lt_of_le_of_ne hst.2 (fun heq => hs (by simp [heq]))⟩
    filter_upwards [hmem] with s hs hsIoc
    exact hsource_bridge s (hs hsIoc)
  rw [intervalConjugateDuhamelMap]
  change (intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      + (-p.χ₀) *
          (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      = ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
  rw [hhom, add_assoc, hsource_eq,
    duhamelHeatValue_canonical_eq_cosineSeries_of_patched
      p u₀ u hsrc ht htT]
  have hsum_hom : Summable (fun n : ℕ =>
      (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x) := by
    have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
    refine Summable.of_norm_bounded
      (g := fun n : ℕ =>
        |Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n|) ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hu₀_bound n) (Real.exp_pos _).le
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * |cosineMode n x|
          ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| := by ring
  have hsum_duh_abs_patched : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff (patchedBFormSourceCoeffs p u₀ u) t n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      (hsrc.henv_summable.mul_left t)
    exact abs_duhamelSpectralCoeff_le_weak hsrc ht htT n
  have hsum_duh_abs : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|) := by
    refine hsum_duh_abs_patched.congr (fun n => ?_)
    rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ u ht n]
  have hsum_duh : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (bFormSourceCoeffs p u) t n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|)
      hsum_duh_abs (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * |cosineMode n x|
        ≤ |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * 1 := by
            gcongr
            simpa [cosineMode] using
              Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
      _ = |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| := by ring
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun n => ?_)
  unfold localRestartCoeff
  ring

/-- Bounded-source version of the conjugate Duhamel-map cosine series. -/
theorem intervalConjugateDuhamelMap_cosineSeries_of_patched_bdd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrc : DuhamelSourceBddOn (patchedBFormSourceCoeffs p u₀ u) T)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x := by
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x =
      ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x := by
    rw [
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        ht hu₀_cont hu₀_bound hx]
    simpa using congrFun
      (ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
        t (cosineCoeffs (intervalDomainLift u₀))) x
  have hsource_eq : (-p.χ₀) *
        (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = ∫ s in (0 : ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add (hB_int.const_mul (-p.χ₀)) hlog_int]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume,
        s ∈ Set.Ioc (0 : ℝ) t → s ∈ Set.Ioo (0 : ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hst
      exact ⟨hst.1, lt_of_le_of_ne hst.2 (fun heq => hs (by simp [heq]))⟩
    filter_upwards [hmem] with s hs hsIoc
    exact hsource_bridge s (hs hsIoc)
  rw [intervalConjugateDuhamelMap]
  change (intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      + (-p.χ₀) *
          (∫ s in (0 : ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      = ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
  rw [hhom, add_assoc, hsource_eq,
    duhamelHeatValue_canonical_eq_cosineSeries_of_patched_bdd
      p u₀ u hsrc ht htT]
  have hsum_hom : Summable (fun n : ℕ =>
      (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x) := by
    have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
    refine Summable.of_norm_bounded
      (g := fun n : ℕ =>
        |Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n|) ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hu₀_bound n) (Real.exp_pos _).le
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * |cosineMode n x|
          ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| := by ring
  have hsum_duh_abs_patched : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff (patchedBFormSourceCoeffs p u₀ u) t n|) :=
    summable_abs_duhamelSpectralCoeff_bdd hsrc ht htT
  have hsum_duh_abs : Summable (fun n : ℕ =>
      |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|) := by
    refine hsum_duh_abs_patched.congr (fun n => ?_)
    rw [duhamelSpectralCoeff_patched_eq_canonical p u₀ u ht n]
  have hsum_duh : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (bFormSourceCoeffs p u) t n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|)
      hsum_duh_abs (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * |cosineMode n x|
        ≤ |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * 1 := by
            gcongr
            simpa [cosineMode] using
              Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
      _ = |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| := by ring
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun n => ?_)
  unfold localRestartCoeff
  ring

/-- Fixed-point specialization of
`intervalConjugateDuhamelMap_cosineSeries_of_patched`. -/
theorem conjugatePicardLimit_cosineSeries_of_patched
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrc : DuhamelSourceL1ContOn
      (patchedBFormSourceCoeffs p u₀
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)) T)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        + intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s) x) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  have hpoint := hfix t ht htT ⟨x, hx⟩
  rw [show intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t
          ⟨x, hx⟩ by simp [intervalDomainLift, hx]]
  rw [hpoint]
  exact intervalConjugateDuhamelMap_cosineSeries_of_patched
    (p := p) (u₀ := u₀)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (T := T) (t := t) (x := x) (M₀ := M₀)
    ht htT hx hu₀_cont hu₀_bound hsrc hB_int hlog_int hsource_bridge

/-- Fixed-point specialization of the bounded-source reconstruction. -/
theorem conjugatePicardLimit_cosineSeries_of_patched_bdd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrc : DuhamelSourceBddOn
      (patchedBFormSourceCoeffs p u₀
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)) T)
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        + intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s) x) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  have hpoint := hfix t ht htT ⟨x, hx⟩
  rw [show intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t
          ⟨x, hx⟩ by simp [intervalDomainLift, hx]]
  rw [hpoint]
  exact intervalConjugateDuhamelMap_cosineSeries_of_patched_bdd
    (p := p) (u₀ := u₀)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (T := T) (t := t) (x := x) (M₀ := M₀)
    ht htT hx hu₀_cont hu₀_bound hsrc hB_int hlog_int hsource_bridge

/-- The bank-facing global cosine-reconstruction interface.  Its source
regularity premise is attached to the endpoint-patched family, while its
conclusion uses the canonical B-form coefficients expected by the restart and
PDE consumers. -/
theorem conjugatePicardLimit_hB_global_of_patched
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrc : DuhamelSourceL1ContOn
      (patchedBFormSourceCoeffs p u₀
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)) T)
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hsource_bridge : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        (-p.χ₀) * intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p
              ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
          + intervalFullSemigroupOperator (t - s)
            (logisticLifted p
              ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
          = unitIntervalCosineHeatValue (t - s)
            (bFormSourceCoeffs p
              (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s) x) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn
        (intervalDomainLift
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p
              (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  exact conjugatePicardLimit_cosineSeries_of_patched
    (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
    hfix ht htT hx hu₀_cont hu₀_bound hsrc
    (hB_int t ht htT x hx) (hlog_int t ht htT x hx)
    (hsource_bridge t ht htT x hx)

/-- Bank-facing global cosine reconstruction from the satisfiable bounded
patched source interface. -/
theorem conjugatePicardLimit_hB_global_of_patched_bdd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrc : DuhamelSourceBddOn
      (patchedBFormSourceCoeffs p u₀
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)) T)
    (hB_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hlog_int : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      IntervalIntegrable
        (fun s : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
        volume 0 t)
    (hsource_bridge : ∀ t, 0 < t → t ≤ T → ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        (-p.χ₀) * intervalConjugateKernelOperator (t - s)
            (chemFluxLifted p
              ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
          + intervalFullSemigroupOperator (t - s)
            (logisticLifted p
              ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
          = unitIntervalCosineHeatValue (t - s)
            (bFormSourceCoeffs p
              (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s) x) :
    ∀ t, 0 < t → t ≤ T →
      Set.EqOn
        (intervalDomainLift
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p
              (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  exact conjugatePicardLimit_cosineSeries_of_patched_bdd
    (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
    hfix ht htT hx hu₀_cont hu₀_bound hsrc
    (hB_int t ht htT x hx) (hlog_int t ht htT x hx)
    (hsource_bridge t ht htT x hx)

#print axioms patchedBFormSourceCoeffs_eq_of_pos
#print axioms initialPhysicalBFormSourceCoeffs_abs_summable_of_l1ContOn
#print axioms duhamelSpectralCoeff_patched_eq_canonical
#print axioms duhamelHeatValue_patched_eq_canonical
#print axioms localRestartCoeff_patched_eq_canonical
#print axioms timeC1OnPatched_of_canonical_positive
#print axioms duhamelHeatValue_canonical_eq_cosineSeries_of_patched
#print axioms duhamelHeatValue_canonical_eq_cosineSeries_of_patched_bdd
#print axioms intervalConjugateDuhamelMap_cosineSeries_of_patched
#print axioms intervalConjugateDuhamelMap_cosineSeries_of_patched_bdd
#print axioms conjugatePicardLimit_cosineSeries_of_patched
#print axioms conjugatePicardLimit_cosineSeries_of_patched_bdd
#print axioms conjugatePicardLimit_hB_global_of_patched
#print axioms conjugatePicardLimit_hB_global_of_patched_bdd

end ShenWork.Paper2.BFormPatchedSource
