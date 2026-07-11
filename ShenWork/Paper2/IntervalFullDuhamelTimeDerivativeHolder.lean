/-
  Direct target-time differentiation of a full Neumann Duhamel leg.

  The proof stays in physical space.  A fixed old-history piece is
  differentiated by dominated convergence applied to its time slopes.  The
  remaining short late-history piece is controlled by the cancellative
  Holder Hessian estimate, while its moving endpoint is handled by the
  approximate identity and the uniform source trace.
-/
import ShenWork.Paper2.IntervalFullSemigroupTimeDerivative
import ShenWork.Paper2.IntervalFullDuhamelSpatialC2
import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator weightedHeatHessConst)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_abs_le_of_continuous_bounded)

private def fullDuhamelValueIntegrand
    (H : ℝ → ℝ → ℝ) (r s x : ℝ) : ℝ :=
  intervalFullSemigroupOperator (r - s) (H s) x

private def fullDuhamelHessIntegrand
    (H : ℝ → ℝ → ℝ) (r s x : ℝ) : ℝ :=
  deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalFullSemigroupOperator (r - s) (H s) z) y) x

private theorem source_cosineCoeff_bound
    {CQ : ℝ} (hCQ : 0 ≤ CQ) {H : ℝ → ℝ → ℝ}
    (hH_cont : ∀ s, Continuous (H s))
    (hH_bound : ∀ s y, |H s y| ≤ CQ) :
    ∀ s n, |ShenWork.IntervalNeumannFullKernel.cosineCoeffs (H s) n| ≤ 2 * CQ := by
  intro s n
  exact cosineCoeffs_abs_le_of_continuous_bounded
    (hH_cont s).continuousOn hCQ (fun y _hy => hH_bound s y) n

private theorem fullDuhamelValueIntegrand_hasDerivAt_time
    {CQ : ℝ} (hCQ : 0 ≤ CQ) {H : ℝ → ℝ → ℝ}
    (hH_cont : ∀ s, Continuous (H s))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    {r s x : ℝ} (hsr : s < r) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun q : ℝ => fullDuhamelValueIntegrand H q s x)
      (fullDuhamelHessIntegrand H r s x) r := by
  have hbase := intervalFullSemigroupOperator_hasDerivAt_time_secondDeriv_Icc
    (t := r - s) (x := x) (sub_pos.mpr hsr) (hH_cont s)
    (source_cosineCoeff_bound hCQ hH_cont hH_bound s) hx
  have hshift : HasDerivAt (fun q : ℝ => q - s) 1 r :=
    (hasDerivAt_id r).sub_const s
  simpa [fullDuhamelValueIntegrand, fullDuhamelHessIntegrand] using
    hbase.comp r hshift

/- The old history cut off strictly before the target time has the expected
generator derivative.  This is the nonsingular DCT part of the argument. -/
private theorem fixedOldHistory_hasDerivAt
    {a t CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t) (hCQ : 0 ≤ CQ)
    {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_cont : ∀ s, Continuous (H s))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r : ℝ => ∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H r s x)
      (∫ s in (0 : ℝ)..a, fullDuhamelHessIntegrand H t s x) t := by
  let d : ℝ := (t - a) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  let Cmix : ℝ := 5 * Real.sqrt 2 / 2
  let B : ℝ := Cmix * d ^ (-(1 : ℝ)) * CQ
  have hval_t : IntervalIntegrable
      (fun s : ℝ => fullDuhamelValueIntegrand H t s x) volume 0 a := by
    have ht0 : 0 < t := lt_of_le_of_lt ha0 hat
    have hfull :=
      ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
        ht0 hH_meas hCQ hH_bound x
    exact hfull.mono_set (by
      rw [Set.uIcc_of_le ha0, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc le_rfl hat.le)
  have hslope_tendsto : Tendsto
      (fun r : ℝ => ∫ s in (0 : ℝ)..a,
        slope (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)
      (𝓝[≠] t)
      (𝓝 (∫ s in (0 : ℝ)..a, fullDuhamelHessIntegrand H t s x)) := by
    have hball_ne : ∀ᶠ r in 𝓝[≠] t, r ∈ Metric.ball t d :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds t hd)
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[≠] t) (bound := fun _ : ℝ => B) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hball_ne, self_mem_nhdsWithin] with r hr hrne
      have hra : a < r := by
        rw [Metric.mem_ball, Real.dist_eq] at hr
        dsimp [d] at hr
        have habs := abs_lt.mp hr
        linarith
      have hr0 : 0 < r := lt_of_le_of_lt ha0 hra
      have hval_r_full :=
        ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
          hr0 hH_meas hCQ hH_bound x
      have hval_r : IntervalIntegrable
          (fun s : ℝ => fullDuhamelValueIntegrand H r s x) volume 0 a :=
        hval_r_full.mono_set (by
          rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hr0.le]
          exact Set.Icc_subset_Icc le_rfl hra.le)
      have hsl : IntervalIntegrable
          (fun s : ℝ => slope
            (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)
          volume 0 a := by
        rw [show (fun s : ℝ => slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) =
            fun s : ℝ =>
              (fullDuhamelValueIntegrand H r s x -
                fullDuhamelValueIntegrand H t s x) / (r - t) by
          funext s
          rw [slope_def_field]]
        exact (hval_r.sub hval_t).div_const (r - t)
      simpa [Set.uIoc_of_le ha0] using hsl.aestronglyMeasurable
    · filter_upwards [hball_ne, self_mem_nhdsWithin] with r hr hrne
      filter_upwards with s hsa
      rw [Set.uIoc_of_le ha0] at hsa
      have hsa_le : s ≤ a := hsa.2
      have htball : t ∈ Metric.ball t d := Metric.mem_ball_self hd
      have hdiff : ∀ q ∈ Metric.ball t d,
          DifferentiableAt ℝ (fun w : ℝ => fullDuhamelValueIntegrand H w s x) q := by
        intro q hq
        rw [Metric.mem_ball, Real.dist_eq] at hq
        have habs := abs_lt.mp hq
        have hsq : s < q := by
          dsimp [d] at habs
          linarith [hat, hsa_le]
        exact (fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
          hsq hx).differentiableAt
      have hderiv : ∀ q ∈ Metric.ball t d,
          ‖deriv (fun w : ℝ => fullDuhamelValueIntegrand H w s x) q‖ ≤ B := by
        intro q hq
        rw [Metric.mem_ball, Real.dist_eq] at hq
        have habs := abs_lt.mp hq
        have hlag : 0 < q - s := by
          dsimp [d] at habs
          linarith [hat, hsa_le]
        have hdlag : d ≤ q - s := by
          dsimp [d] at habs ⊢
          linarith [hat, hsa_le]
        have hp : (q - s) ^ (-(1 : ℝ)) ≤ d ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hd hdlag (by norm_num)
        have hraw :=
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
            hlag (hH_int s).aestronglyMeasurable (hH_bound s) x
        rw [(fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
          (sub_pos.mp hlag) hx).deriv, Real.norm_eq_abs]
        exact hraw.trans (by
          dsimp [B, Cmix]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (by positivity)) hCQ)
      have hmv := (convex_ball t d).norm_image_sub_le_of_norm_deriv_le
        hdiff hderiv htball hr
      have hden : 0 < ‖r - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hrne)
      rw [slope_def_field, norm_div]
      exact (div_le_iff₀ hden).2 hmv
    · filter_upwards with s hsa
      rw [Set.uIoc_of_le ha0] at hsa
      exact (fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
        (hsa.2.trans_lt hat) hx).tendsto_slope
  apply hasDerivAt_iff_tendsto_slope.mpr
  refine hslope_tendsto.congr' ?_
  have hball_ne : ∀ᶠ r in 𝓝[≠] t, r ∈ Metric.ball t d :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds t hd)
  filter_upwards [hball_ne, self_mem_nhdsWithin] with r hr hrne
  have hra : a < r := by
    rw [Metric.mem_ball, Real.dist_eq] at hr
    dsimp [d] at hr
    have habs := abs_lt.mp hr
    linarith
  have hr0 : 0 < r := lt_of_le_of_lt ha0 hra
  have hval_r_full :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr0 hH_meas hCQ hH_bound x
  have hval_r : IntervalIntegrable
      (fun s : ℝ => fullDuhamelValueIntegrand H r s x) volume 0 a :=
    hval_r_full.mono_set (by
      rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hr0.le]
      exact Set.Icc_subset_Icc le_rfl hra.le)
  rw [show (fun s : ℝ => slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) =
      fun s : ℝ =>
        (fullDuhamelValueIntegrand H r s x -
          fullDuhamelValueIntegrand H t s x) / (r - t) by
    funext s
    rw [slope_def_field], intervalIntegral.integral_div,
    intervalIntegral.integral_sub hval_r hval_t]
  rw [slope_def_field]

private def clippedSource (H : ℝ → ℝ → ℝ) (s y : ℝ) : ℝ :=
  H s (ShenWork.IntervalMildPicardThreshold.unitClip y).1

private theorem clippedSource_continuous
    {H : ℝ → ℝ → ℝ} (hH_cont : ∀ s, Continuous (H s)) (s : ℝ) :
    Continuous (clippedSource H s) :=
  (hH_cont s).comp
    (continuous_subtype_val.comp ShenWork.IntervalMildPicardThreshold.unitClip_continuous)

private theorem clippedSource_integrable
    {H : ℝ → ℝ → ℝ} (hH_cont : ∀ s, Continuous (H s)) (s : ℝ) :
    Integrable (clippedSource H s) (intervalMeasure 1) := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (clippedSource_continuous hH_cont s).continuousOn.integrableOn_Icc

private theorem clippedSource_bound
    {CQ : ℝ} {H : ℝ → ℝ → ℝ} (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (s y : ℝ) : |clippedSource H s y| ≤ CQ :=
  hH_bound s _

private theorem clippedSource_eq_on_Icc
    {H : ℝ → ℝ → ℝ} (s : ℝ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : clippedSource H s y = H s y := by
  change H s (ShenWork.IntervalMildPicardThreshold.unitClip y).1 = H s y
  rw [ShenWork.IntervalMildPicardThreshold.unitClip_of_mem hy]

/- The new right-hand tail divided by its length converges to the source trace.
Both the time trace and the heat approximate identity are used uniformly on
the physical interval. -/
private theorem rightTailAverage_tendsto_trace
    {t CQ : ℝ} (ht : 0 < t) (hCQ : 0 ≤ CQ)
    {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_cont : ∀ s, Continuous (H s))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_time : TendstoUniformlyOn H (H t) (𝓝 t) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto
      (fun r : ℝ =>
        (∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t))
      (𝓝[>] t) (𝓝 (H t x)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have heps4 : 0 < eps / 4 := by linarith
  rw [Metric.tendstoUniformlyOn_iff] at hH_time
  have hsrc_mem := hH_time (eps / 4) heps4
  obtain ⟨lo, hi, htIoo, hsrc_sub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset.mp hsrc_mem)
  let Htc : ℝ → ℝ := clippedSource H t
  have hHtc_cont : Continuous Htc := clippedSource_continuous hH_cont t
  have hsem := ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
    Htc hHtc_cont
  rw [Metric.tendstoUniformlyOn_iff] at hsem
  have hsem_mem := hsem (eps / 4) heps4
  obtain ⟨delta, hdelta, hsem_sub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset.mp hsem_mem)
  let upper : ℝ := min hi (t + delta)
  have htupper : t < upper := by
    dsimp [upper]
    have htadd : t < t + delta := lt_add_of_pos_right t hdelta
    exact lt_min htIoo.2 htadd
  filter_upwards [Ioo_mem_nhdsGT htupper] with r hr
  have htr : t < r := hr.1
  have hrhi : r < hi := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hrt_delta : r - t < delta := by
    have hru : r < t + delta := lt_of_lt_of_le hr.2 (min_le_right _ _)
    linarith
  have hr0 : 0 < r := ht.trans htr
  have hval_full :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr0 hH_meas hCQ hH_bound x
  have hval : IntervalIntegrable
      (fun s : ℝ => fullDuhamelValueIntegrand H r s x) volume t r :=
    hval_full.mono_set (by
      rw [Set.uIcc_of_le htr.le, Set.uIcc_of_le hr0.le]
      exact Set.Icc_subset_Icc ht.le le_rfl)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpoint : ∀ᵐ s : ℝ ∂volume,
      s ∈ Set.uIoc t r →
        ‖fullDuhamelValueIntegrand H r s x - H t x‖ ≤ eps / 2 := by
    filter_upwards [hne] with s hsr_ne hs
    rw [Set.uIoc_of_le htr.le] at hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hsr_ne
    have hts : t < s := hs.1
    have hs_src : s ∈ Set.Ioo lo hi :=
      ⟨htIoo.1.trans hts, hsr.trans hrhi⟩
    have hlag : 0 < r - s := sub_pos.mpr hsr
    have hlag_delta : r - s < delta := by linarith
    have hsrc : ∀ y ∈ Set.Icc (0 : ℝ) 1, |H s y - H t y| < eps / 4 := by
      intro y hy
      have hd := hsrc_sub hs_src y hy
      simpa [Real.dist_eq, abs_sub_comm] using hd
    have hclipdiff : ∀ y, |clippedSource H s y - clippedSource H t y| ≤ eps / 4 := by
      intro y
      exact (hsrc _ (ShenWork.IntervalMildPicardThreshold.unitClip y).property).le
    have hdiff :=
      ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
        hlag (clippedSource_integrable hH_cont s) (clippedSource_integrable hH_cont t)
        hCQ (clippedSource_bound hH_bound s) hCQ (clippedSource_bound hH_bound t)
        heps4.le hclipdiff x
    have hsem_at := hsem_sub ⟨hlag, hlag_delta⟩ x hx
    have hcongr_s :
        intervalFullSemigroupOperator (r - s) (H s) x =
          intervalFullSemigroupOperator (r - s) (clippedSource H s) x :=
      intervalFullSemigroupOperator_congr_on_Icc
        (fun y hy => (clippedSource_eq_on_Icc s hy).symm) x
    have hcongr_t :
        intervalFullSemigroupOperator (r - s) (H t) x =
          intervalFullSemigroupOperator (r - s) (clippedSource H t) x :=
      intervalFullSemigroupOperator_congr_on_Icc
        (fun y hy => (clippedSource_eq_on_Icc t hy).symm) x
    have hclip_x : Htc x = H t x := clippedSource_eq_on_Icc t hx
    rw [Real.norm_eq_abs]
    dsimp [fullDuhamelValueIntegrand]
    rw [hcongr_s]
    exact le_of_lt (calc
      |intervalFullSemigroupOperator (r - s) (clippedSource H s) x - H t x|
          ≤ |intervalFullSemigroupOperator (r - s) (clippedSource H s) x -
              intervalFullSemigroupOperator (r - s) (clippedSource H t) x| +
            |intervalFullSemigroupOperator (r - s) (clippedSource H t) x - H t x| :=
        abs_sub_le _ _ _
      _ < eps / 4 + eps / 4 := by
        have hsem_abs :
            |intervalFullSemigroupOperator (r - s) (clippedSource H t) x - H t x| < eps / 4 := by
          simpa [Htc, hclip_x, Real.dist_eq, abs_sub_comm] using hsem_at
        exact add_lt_add_of_le_of_lt hdiff hsem_abs
      _ = eps / 2 := by ring)
  have hnum := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := t) (b := r) (C := eps / 2)
    (f := fun s : ℝ => fullDuhamelValueIntegrand H r s x - H t x) hpoint
  have hrewrite :
      (∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) - H t x =
        (∫ s in t..r, fullDuhamelValueIntegrand H r s x - H t x) / (r - t) := by
    rw [intervalIntegral.integral_sub hval intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt (sub_pos.mpr htr)]
  rw [Real.dist_eq, hrewrite, abs_div, abs_of_pos (sub_pos.mpr htr)]
  have hle :
      |∫ s in t..r, fullDuhamelValueIntegrand H r s x - H t x| / (r - t)
        ≤ eps / 2 := by
    rw [← Real.norm_eq_abs] at hnum
    calc
      ‖∫ s in t..r, fullDuhamelValueIntegrand H r s x - H t x‖ / (r - t)
          ≤ ((eps / 2) * |r - t|) / (r - t) :=
        div_le_div_of_nonneg_right hnum (sub_pos.mpr htr).le
      _ = eps / 2 := by
        rw [abs_of_pos (sub_pos.mpr htr)]
        field_simp [ne_of_gt (sub_pos.mpr htr)]
  exact hle.trans_lt (by linarith)

/- The deleted left-hand tail has the same normalized trace limit. -/
private theorem leftDeletedTailAverage_tendsto_trace
    {t CQ : ℝ} (ht : 0 < t) (hCQ : 0 ≤ CQ)
    {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_cont : ∀ s, Continuous (H s))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_time : TendstoUniformlyOn H (H t) (𝓝 t) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto
      (fun r : ℝ =>
        (∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r))
      (𝓝[<] t) (𝓝 (H t x)) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  have heps4 : 0 < eps / 4 := by linarith
  rw [Metric.tendstoUniformlyOn_iff] at hH_time
  have hsrc_mem := hH_time (eps / 4) heps4
  obtain ⟨lo, hi, htIoo, hsrc_sub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset.mp hsrc_mem)
  let Htc : ℝ → ℝ := clippedSource H t
  have hHtc_cont : Continuous Htc := clippedSource_continuous hH_cont t
  have hsem := ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
    Htc hHtc_cont
  rw [Metric.tendstoUniformlyOn_iff] at hsem
  have hsem_mem := hsem (eps / 4) heps4
  obtain ⟨delta, hdelta, hsem_sub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset.mp hsem_mem)
  let lower : ℝ := max (max lo (t - delta)) (t / 2)
  have hlower_t : lower < t := by
    dsimp [lower]
    have hsub : t - delta < t := sub_lt_self t hdelta
    exact max_lt (max_lt htIoo.1 hsub) (by linarith)
  filter_upwards [Ioo_mem_nhdsLT hlower_t] with r hr
  have hlr : lower < r := hr.1
  have hrt : r < t := hr.2
  have hrlo : lo < r :=
    lt_of_le_of_lt (le_max_left lo (t - delta) |>.trans (le_max_left _ (t / 2))) hr.1
  have htr_delta : t - r < delta := by
    have hlow : t - delta ≤ lower :=
      (le_max_right lo (t - delta)).trans (le_max_left _ (t / 2))
    linarith [hlr]
  have hr0 : 0 < r := by
    have hhalf : t / 2 ≤ lower := le_max_right _ _
    linarith [hlr, ht]
  have hval_full :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht hH_meas hCQ hH_bound x
  have hval : IntervalIntegrable
      (fun s : ℝ => fullDuhamelValueIntegrand H t s x) volume r t :=
    hval_full.mono_set (by
      rw [Set.uIcc_of_le hrt.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc hr0.le le_rfl)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpoint : ∀ᵐ s : ℝ ∂volume,
      s ∈ Set.uIoc r t →
        ‖fullDuhamelValueIntegrand H t s x - H t x‖ ≤ eps / 2 := by
    filter_upwards [hne] with s hst_ne hs
    rw [Set.uIoc_of_le hrt.le] at hs
    have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
    have hrs : r < s := hs.1
    have hs_src : s ∈ Set.Ioo lo hi :=
      ⟨hrlo.trans hrs, hst.trans htIoo.2⟩
    have hlag : 0 < t - s := sub_pos.mpr hst
    have hlag_delta : t - s < delta := by linarith
    have hsrc : ∀ y ∈ Set.Icc (0 : ℝ) 1, |H s y - H t y| < eps / 4 := by
      intro y hy
      have hd := hsrc_sub hs_src y hy
      simpa [Real.dist_eq, abs_sub_comm] using hd
    have hclipdiff : ∀ y, |clippedSource H s y - clippedSource H t y| ≤ eps / 4 := by
      intro y
      exact (hsrc _ (ShenWork.IntervalMildPicardThreshold.unitClip y).property).le
    have hdiff :=
      ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
        hlag (clippedSource_integrable hH_cont s) (clippedSource_integrable hH_cont t)
        hCQ (clippedSource_bound hH_bound s) hCQ (clippedSource_bound hH_bound t)
        heps4.le hclipdiff x
    have hsem_at := hsem_sub ⟨hlag, hlag_delta⟩ x hx
    have hcongr_s :
        intervalFullSemigroupOperator (t - s) (H s) x =
          intervalFullSemigroupOperator (t - s) (clippedSource H s) x :=
      intervalFullSemigroupOperator_congr_on_Icc
        (fun y hy => (clippedSource_eq_on_Icc s hy).symm) x
    have hclip_x : Htc x = H t x := clippedSource_eq_on_Icc t hx
    rw [Real.norm_eq_abs]
    dsimp [fullDuhamelValueIntegrand]
    rw [hcongr_s]
    exact le_of_lt (calc
      |intervalFullSemigroupOperator (t - s) (clippedSource H s) x - H t x|
          ≤ |intervalFullSemigroupOperator (t - s) (clippedSource H s) x -
              intervalFullSemigroupOperator (t - s) (clippedSource H t) x| +
            |intervalFullSemigroupOperator (t - s) (clippedSource H t) x - H t x| :=
        abs_sub_le _ _ _
      _ < eps / 4 + eps / 4 := by
        have hsem_abs :
            |intervalFullSemigroupOperator (t - s) (clippedSource H t) x - H t x| < eps / 4 := by
          simpa [Htc, hclip_x, Real.dist_eq, abs_sub_comm] using hsem_at
        exact add_lt_add_of_le_of_lt hdiff hsem_abs
      _ = eps / 2 := by ring)
  have hnum := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (a := r) (b := t) (C := eps / 2)
    (f := fun s : ℝ => fullDuhamelValueIntegrand H t s x - H t x) hpoint
  have hrewrite :
      (∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) - H t x =
        (∫ s in r..t, fullDuhamelValueIntegrand H t s x - H t x) / (t - r) := by
    rw [intervalIntegral.integral_sub hval intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [ne_of_gt (sub_pos.mpr hrt)]
  rw [Real.dist_eq, hrewrite, abs_div, abs_of_pos (sub_pos.mpr hrt)]
  have hle :
      |∫ s in r..t, fullDuhamelValueIntegrand H t s x - H t x| / (t - r)
        ≤ eps / 2 := by
    rw [← Real.norm_eq_abs] at hnum
    calc
      ‖∫ s in r..t, fullDuhamelValueIntegrand H t s x - H t x‖ / (t - r)
          ≤ ((eps / 2) * |t - r|) / (t - r) :=
        div_le_div_of_nonneg_right hnum (sub_pos.mpr hrt).le
      _ = eps / 2 := by
        rw [abs_of_pos (sub_pos.mpr hrt)]
        field_simp [ne_of_gt (sub_pos.mpr hrt)]
  exact hle.trans_lt (by linarith)

private theorem integral_sub_rpow_hessian_from
    {a t theta : ℝ} (hat : a ≤ t) (htheta0 : 0 < theta) :
    (∫ s in a..t, (t - s) ^ (-1 + theta / 2 : ℝ)) =
      (t - a) ^ (theta / 2 : ℝ) / (theta / 2) := by
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun s : ℝ => (t - s) ^ (-1 + theta / 2 : ℝ))
    (a := (0 : ℝ)) (b := t - a) a
  have heq : (fun r : ℝ => (t - (r + a)) ^ (-1 + theta / 2 : ℝ)) =
      fun r : ℝ => ((t - a) - r) ^ (-1 + theta / 2 : ℝ) := by
    funext r
    congr 1
    ring
  have hbase :=
    ShenWork.IntervalNeumannFullKernel.integral_sub_rpow_hessian
      (t := t - a) (sub_nonneg.mpr hat) htheta0
  rw [heq] at hshift
  simpa using hshift.symm.trans hbase

private theorem lateHessIntegral_abs_bound
    {a t theta CQ HQ : ℝ} (hat : a < t) (hta : t / 2 < a)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hHQ : 0 ≤ HQ) {H : ℝ → ℝ → ℝ}
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_holder : ∀ s, t / 2 < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |H s p - H s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |∫ s in a..t, fullDuhamelHessIntegrand H t s x| ≤
      (weightedHeatHessConst theta * HQ) *
        ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
  let Ctheta : ℝ := weightedHeatHessConst theta * HQ
  let g : ℝ → ℝ := fun s => Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ)
  have ht0 : 0 < t := by linarith [hat, hta]
  have ha0 : 0 ≤ a := by linarith [hta, ht0]
  have hg_int : IntervalIntegrable g volume a t := by
    have hbase :=
      (ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Ctheta
    exact hbase.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc ha0 le_rfl)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpt : ∀ᵐ s : ℝ ∂volume, s ∈ Set.Ioc a t →
      ‖fullDuhamelHessIntegrand H t s x‖ ≤ g s := by
    filter_upwards [hne] with s hst_ne hs
    have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
    have hts2 : t / 2 < s := hta.trans hs.1
    have hlag : 0 < t - s := sub_pos.mpr hst
    rw [Real.norm_eq_abs]
    dsimp [fullDuhamelHessIntegrand, g, Ctheta]
    have hraw := intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
      hlag htheta0 htheta1 (hH_int s) (hH_bound s) hHQ
        (hH_holder s hts2 hst) hx
    convert hraw using 1 <;> ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hat.le hpt hg_int
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ s in a..t, fullDuhamelHessIntegrand H t s x|
        ≤ ∫ s in a..t, g s := hnorm
    _ = Ctheta * ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
      rw [show (fun s : ℝ => g s) =
          fun s : ℝ => Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ) by rfl,
        intervalIntegral.integral_const_mul,
        integral_sub_rpow_hessian_from hat.le htheta0]
    _ = (weightedHeatHessConst theta * HQ) *
          ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by rfl

private theorem rightLateHistorySlope_abs_bound
    {a t r theta CQ HQ : ℝ} (hat : a < t) (htr : t < r) (hta : t / 2 < a)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ) {H : ℝ → ℝ → ℝ}
    (hH_cont : ∀ s, Continuous (H s))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_holder : ∀ s, t / 2 < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |H s p - H s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |∫ s in a..t, slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r| ≤
      (weightedHeatHessConst theta * HQ) *
        ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
  let Ctheta : ℝ := weightedHeatHessConst theta * HQ
  let g : ℝ → ℝ := fun s => Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ)
  have ht0 : 0 < t := by linarith [hat, hta]
  have ha0 : 0 ≤ a := by linarith [hta, ht0]
  have hg_int : IntervalIntegrable g volume a t := by
    have hbase :=
      (ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Ctheta
    exact hbase.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc ha0 le_rfl)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpt : ∀ᵐ s : ℝ ∂volume, s ∈ Set.Ioc a t →
      ‖slope (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r‖ ≤ g s := by
    filter_upwards [hne] with s hst_ne hs
    have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
    have hts2 : t / 2 < s := hta.trans hs.1
    have hdiff : ∀ q ∈ Set.Icc t r,
        DifferentiableAt ℝ (fun w : ℝ => fullDuhamelValueIntegrand H w s x) q := by
      intro q hq
      exact (fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
        (hst.trans_le hq.1) hx).differentiableAt
    have hderiv : ∀ q ∈ Set.Icc t r,
        ‖deriv (fun w : ℝ => fullDuhamelValueIntegrand H w s x) q‖ ≤ g s := by
      intro q hq
      have hlag : 0 < q - s := sub_pos.mpr (hst.trans_le hq.1)
      have hbase : t - s ≤ q - s := by linarith [hq.1]
      have hp_nonpos : (-1 + theta / 2 : ℝ) ≤ 0 := by linarith
      have hp := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hst) hbase hp_nonpos
      have hraw := intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
        hlag htheta0 htheta1 (hH_int s) (hH_bound s) hHQ
          (hH_holder s hts2 hst) hx
      rw [(fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
        (sub_pos.mp hlag) hx).deriv, Real.norm_eq_abs]
      exact hraw.trans (by
        dsimp [g, Ctheta]
        have hCnn : 0 ≤ weightedHeatHessConst theta * HQ :=
          mul_nonneg
            (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
        nlinarith)
    have hmv := (convex_Icc t r).norm_image_sub_le_of_norm_deriv_le
      hdiff hderiv (left_mem_Icc.mpr htr.le) (right_mem_Icc.mpr htr.le)
    have hden : 0 < ‖r - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr htr.ne')
    rw [slope_def_field, norm_div]
    exact (div_le_iff₀ hden).2 hmv
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hat.le hpt hg_int
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ s in a..t, slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r|
        ≤ ∫ s in a..t, g s := hnorm
    _ = Ctheta * ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
      rw [show (fun s : ℝ => g s) =
          fun s : ℝ => Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ) by rfl,
        intervalIntegral.integral_const_mul,
        integral_sub_rpow_hessian_from hat.le htheta0]
    _ = (weightedHeatHessConst theta * HQ) *
          ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by rfl

private theorem leftLateHistorySlope_abs_bound
    {a r t theta CQ HQ : ℝ} (har : a < r) (hrt : r < t) (hta : t / 2 < a)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ) {H : ℝ → ℝ → ℝ}
    (hH_cont : ∀ s, Continuous (H s))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_holder : ∀ s, t / 2 < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |H s p - H s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |∫ s in a..r, slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r| ≤
      (weightedHeatHessConst theta * HQ) *
        ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
  let Ctheta : ℝ := weightedHeatHessConst theta * HQ
  let gr : ℝ → ℝ := fun s => Ctheta * (r - s) ^ (-1 + theta / 2 : ℝ)
  have ht0 : 0 < t := by linarith [har, hrt, hta]
  have ha0 : 0 ≤ a := by linarith [hta, ht0]
  have hr0 : 0 < r := lt_of_le_of_lt ha0 har
  have hgr_int : IntervalIntegrable gr volume a r := by
    have hbase :=
      (ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := r) htheta0).const_mul Ctheta
    exact hbase.mono_set (by
      rw [Set.uIcc_of_le har.le, Set.uIcc_of_le hr0.le]
      exact Set.Icc_subset_Icc ha0 le_rfl)
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ r := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hpt : ∀ᵐ s : ℝ ∂volume, s ∈ Set.Ioc a r →
      ‖slope (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r‖ ≤ gr s := by
    filter_upwards [hne] with s hsr_ne hs
    have hsr : s < r := lt_of_le_of_ne hs.2 hsr_ne
    have hst : s < t := hsr.trans hrt
    have hts2 : t / 2 < s := hta.trans hs.1
    have hdiff : ∀ q ∈ Set.Icc r t,
        DifferentiableAt ℝ (fun w : ℝ => fullDuhamelValueIntegrand H w s x) q := by
      intro q hq
      exact (fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
        (hsr.trans_le hq.1) hx).differentiableAt
    have hderiv : ∀ q ∈ Set.Icc r t,
        ‖deriv (fun w : ℝ => fullDuhamelValueIntegrand H w s x) q‖ ≤ gr s := by
      intro q hq
      have hlag : 0 < q - s := sub_pos.mpr (hsr.trans_le hq.1)
      have hbase : r - s ≤ q - s := by linarith [hq.1]
      have hp_nonpos : (-1 + theta / 2 : ℝ) ≤ 0 := by linarith
      have hp := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hsr) hbase hp_nonpos
      have hraw := intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
        hlag htheta0 htheta1 (hH_int s) (hH_bound s) hHQ
          (hH_holder s hts2 hst) hx
      rw [(fullDuhamelValueIntegrand_hasDerivAt_time hCQ hH_cont hH_bound
        (sub_pos.mp hlag) hx).deriv, Real.norm_eq_abs]
      exact hraw.trans (by
        dsimp [gr, Ctheta]
        have hCnn : 0 ≤ weightedHeatHessConst theta * HQ :=
          mul_nonneg
            (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
        nlinarith)
    have hmv := (convex_Icc r t).norm_image_sub_le_of_norm_deriv_le
      hdiff hderiv (right_mem_Icc.mpr hrt.le) (left_mem_Icc.mpr hrt.le)
    have hden : 0 < ‖r - t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hrt.ne)
    rw [slope_def_field, norm_div]
    exact (div_le_iff₀ hden).2 hmv
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le har.le hpt hgr_int
  rw [Real.norm_eq_abs] at hnorm
  have hCnn : 0 ≤ Ctheta := by
    dsimp [Ctheta]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
  have hhalf : 0 < theta / 2 := by linarith
  have hpow : (r - a) ^ (theta / 2 : ℝ) ≤ (t - a) ^ (theta / 2 : ℝ) :=
    Real.rpow_le_rpow (sub_nonneg.mpr har.le) (by linarith) hhalf.le
  calc
    |∫ s in a..r, slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r|
        ≤ ∫ s in a..r, gr s := hnorm
    _ = Ctheta * ((r - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
      rw [show (fun s : ℝ => gr s) =
          fun s : ℝ => Ctheta * (r - s) ^ (-1 + theta / 2 : ℝ) by rfl,
        intervalIntegral.integral_const_mul,
        integral_sub_rpow_hessian_from har.le htheta0]
    _ ≤ Ctheta * ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by
      gcongr
    _ = (weightedHeatHessConst theta * HQ) *
          ((t - a) ^ (theta / 2 : ℝ) / (theta / 2)) := by rfl

private theorem fixedHess_intervalIntegrable
    {a t CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t) (hCQ : 0 ≤ CQ)
    {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    {x : ℝ} :
    IntervalIntegrable (fun s : ℝ => fullDuhamelHessIntegrand H t s x)
      volume 0 a := by
  have ht0 : 0 < t := lt_of_le_of_lt ha0 hat
  have hH_ae : AEStronglyMeasurable (Function.uncurry H)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hH_meas.aestronglyMeasurable
  have hmeas_full :=
    intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht0 hH_ae hH_int hH_bound x
  have hsub : Set.uIoc (0 : ℝ) a ⊆ Set.uIoc (0 : ℝ) t := by
    rw [Set.uIoc_of_le ha0, Set.uIoc_of_le ht0.le]
    exact Set.Ioc_subset_Ioc le_rfl hat.le
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => fullDuhamelHessIntegrand H t s x)
      (volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    have hm := hmeas_full.mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa [fullDuhamelHessIntegrand] using hm
  let Cmix : ℝ := 5 * Real.sqrt 2 / 2
  let B : ℝ := Cmix * (t - a) ^ (-(1 : ℝ)) * CQ
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ => fullDuhamelHessIntegrand H t s x)
    (g := fun _ : ℝ => B) intervalIntegrable_const hmeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  filter_upwards [hne] with s hst_ne hs
  rw [Set.uIoc_of_le ha0] at hs
  have hst : s < t := hs.2.trans_lt hat
  have hlag : 0 < t - s := sub_pos.mpr hst
  have hbase : t - a ≤ t - s := by linarith [hs.2]
  have hp : (t - s) ^ (-(1 : ℝ)) ≤ (t - a) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hat) hbase (by norm_num)
  have hraw :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_secondDeriv_Linfty_pointwise_inv_t
      hlag (hH_int s).aestronglyMeasurable (hH_bound s) x
  rw [Real.norm_eq_abs]
  dsimp [fullDuhamelHessIntegrand, B, Cmix]
  exact hraw.trans (by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity)) hCQ)

private theorem lateHess_intervalIntegrable
    {a t theta CQ HQ : ℝ} (hat : a < t) (hta : t / 2 < a)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hHQ : 0 ≤ HQ) {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_holder : ∀ s, t / 2 < s → s < t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∀ q ∈ Set.Ioo (0 : ℝ) 1,
        |H s p - H s q| ≤ HQ * |p - q| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s : ℝ => fullDuhamelHessIntegrand H t s x)
      volume a t := by
  have ht0 : 0 < t := by linarith [hat, hta]
  have ha0 : 0 ≤ a := by linarith [hta, ht0]
  have hH_ae : AEStronglyMeasurable (Function.uncurry H)
      ((volume.restrict (Set.uIoc (0 : ℝ) t)).prod (intervalMeasure 1)) :=
    hH_meas.aestronglyMeasurable
  have hmeas_full :=
    intervalFullSemigroupOperator_s_dependent_secondDeriv_aestronglyMeasurable_x₀
      ht0 hH_ae hH_int hH_bound x
  have hsub : Set.uIoc a t ⊆ Set.uIoc (0 : ℝ) t := by
    rw [Set.uIoc_of_le hat.le, Set.uIoc_of_le ht0.le]
    exact Set.Ioc_subset_Ioc ha0 le_rfl
  have hmeas : AEStronglyMeasurable
      (fun s : ℝ => fullDuhamelHessIntegrand H t s x)
      (volume.restrict (Set.uIoc a t)) := by
    have hm := hmeas_full.mono_measure (Measure.restrict_mono hsub le_rfl)
    simpa [fullDuhamelHessIntegrand] using hm
  let Ctheta : ℝ := weightedHeatHessConst theta * HQ
  let g : ℝ → ℝ := fun s => Ctheta * (t - s) ^ (-1 + theta / 2 : ℝ)
  have hg_int : IntervalIntegrable g volume a t := by
    have hbase :=
      (ShenWork.IntervalNeumannFullKernel.intervalIntegrable_sub_rpow_hessian
        (t := t) htheta0).const_mul Ctheta
    exact hbase.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht0.le]
      exact Set.Icc_subset_Icc ha0 le_rfl)
  refine IntervalIntegrable.mono_fun'
    (f := fun s : ℝ => fullDuhamelHessIntegrand H t s x)
    (g := g) hg_int hmeas ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  filter_upwards [hne] with s hst_ne hs
  rw [Set.uIoc_of_le hat.le] at hs
  have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
  have hts2 : t / 2 < s := hta.trans hs.1
  have hlag : 0 < t - s := sub_pos.mpr hst
  rw [Real.norm_eq_abs]
  dsimp [fullDuhamelHessIntegrand, g, Ctheta]
  have hraw := intervalFullSemigroupOperator_secondDeriv_abs_le_of_interior_holder_Icc
    hlag htheta0 htheta1 (hH_int s) (hH_bound s) hHQ
      (hH_holder s hts2 hst) hx
  convert hraw using 1 <;> ring

private theorem rightFullDuhamelSlope_decomp
    {a t r CQ : ℝ} (ha0 : 0 ≤ a) (hat : a < t) (htr : t < r)
    (hCQ : 0 ≤ CQ) {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_bound : ∀ s y, |H s y| ≤ CQ) {x : ℝ} :
    slope (fun q : ℝ =>
        ∫ s in (0 : ℝ)..q, fullDuhamelValueIntegrand H q s x) t r =
      slope (fun q : ℝ =>
        ∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H q s x) t r +
      (∫ s in a..t, slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) +
      (∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) := by
  have ht0 : 0 < t := lt_of_le_of_lt ha0 hat
  have hr0 : 0 < r := ht0.trans htr
  have hVr :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr0 hH_meas hCQ hH_bound x
  have hVt :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht0 hH_meas hCQ hH_bound x
  have hVr0a := hVr.mono_set (by
    rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hr0.le]
    exact Set.Icc_subset_Icc le_rfl (hat.le.trans htr.le))
  have hVra_t := hVr.mono_set (by
    rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le hr0.le]
    exact Set.Icc_subset_Icc ha0 htr.le)
  have hVrt_r := hVr.mono_set (by
    rw [Set.uIcc_of_le htr.le, Set.uIcc_of_le hr0.le]
    exact Set.Icc_subset_Icc ht0.le le_rfl)
  have hVra_r := hVr.mono_set (by
    rw [Set.uIcc_of_le (hat.trans htr).le, Set.uIcc_of_le hr0.le]
    exact Set.Icc_subset_Icc ha0 le_rfl)
  have hVt0a := hVt.mono_set (by
    rw [Set.uIcc_of_le ha0, Set.uIcc_of_le ht0.le]
    exact Set.Icc_subset_Icc le_rfl hat.le)
  have hVta_t := hVt.mono_set (by
    rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht0.le]
    exact Set.Icc_subset_Icc ha0 le_rfl)
  have hUr : (∫ s in (0 : ℝ)..r, fullDuhamelValueIntegrand H r s x) =
      (∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H r s x) +
        ∫ s in a..r, fullDuhamelValueIntegrand H r s x :=
    (intervalIntegral.integral_add_adjacent_intervals hVr0a hVra_r).symm
  have hUt : (∫ s in (0 : ℝ)..t, fullDuhamelValueIntegrand H t s x) =
      (∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H t s x) +
        ∫ s in a..t, fullDuhamelValueIntegrand H t s x :=
    (intervalIntegral.integral_add_adjacent_intervals hVt0a hVta_t).symm
  have hBr : (∫ s in a..r, fullDuhamelValueIntegrand H r s x) =
      (∫ s in a..t, fullDuhamelValueIntegrand H r s x) +
        ∫ s in t..r, fullDuhamelValueIntegrand H r s x :=
    (intervalIntegral.integral_add_adjacent_intervals hVra_t hVrt_r).symm
  have hsl : (∫ s in a..t, slope
      (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) =
      ((∫ s in a..t, fullDuhamelValueIntegrand H r s x) -
        ∫ s in a..t, fullDuhamelValueIntegrand H t s x) / (r - t) := by
    rw [show (fun s : ℝ => slope
          (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) =
        fun s : ℝ => (fullDuhamelValueIntegrand H r s x -
          fullDuhamelValueIntegrand H t s x) / (r - t) by
      funext s
      rw [slope_def_field]]
    simp only [fullDuhamelValueIntegrand]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub hVra_t hVta_t]
  rw [slope_def_field, slope_def_field, hUr, hUt, hBr, hsl]
  field_simp [sub_ne_zero.mpr htr.ne']
  ring

private theorem leftFullDuhamelSlope_decomp
    {a r t CQ : ℝ} (ha0 : 0 ≤ a) (har : a < r) (hrt : r < t)
    (hCQ : 0 ≤ CQ) {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_bound : ∀ s y, |H s y| ≤ CQ) {x : ℝ} :
    slope (fun q : ℝ =>
        ∫ s in (0 : ℝ)..q, fullDuhamelValueIntegrand H q s x) t r =
      slope (fun q : ℝ =>
        ∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H q s x) t r +
      (∫ s in a..r, slope
        (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) +
      (∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) := by
  have hr0 : 0 < r := lt_of_le_of_lt ha0 har
  have ht0 : 0 < t := hr0.trans hrt
  have hVr :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hr0 hH_meas hCQ hH_bound x
  have hVt :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht0 hH_meas hCQ hH_bound x
  have hVr0a := hVr.mono_set (by
    rw [Set.uIcc_of_le ha0, Set.uIcc_of_le hr0.le]
    exact Set.Icc_subset_Icc le_rfl har.le)
  have hVra_r := hVr.mono_set (by
    rw [Set.uIcc_of_le har.le, Set.uIcc_of_le hr0.le]
    exact Set.Icc_subset_Icc ha0 le_rfl)
  have hVt0a := hVt.mono_set (by
    rw [Set.uIcc_of_le ha0, Set.uIcc_of_le ht0.le]
    exact Set.Icc_subset_Icc le_rfl (har.le.trans hrt.le))
  have hVta_r := hVt.mono_set (by
    rw [Set.uIcc_of_le har.le, Set.uIcc_of_le ht0.le]
    exact Set.Icc_subset_Icc ha0 hrt.le)
  have hVtr_t := hVt.mono_set (by
    rw [Set.uIcc_of_le hrt.le, Set.uIcc_of_le ht0.le]
    exact Set.Icc_subset_Icc hr0.le le_rfl)
  have hVta_t := hVt.mono_set (by
    rw [Set.uIcc_of_le (har.trans hrt).le, Set.uIcc_of_le ht0.le]
    exact Set.Icc_subset_Icc ha0 le_rfl)
  have hUr : (∫ s in (0 : ℝ)..r, fullDuhamelValueIntegrand H r s x) =
      (∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H r s x) +
        ∫ s in a..r, fullDuhamelValueIntegrand H r s x :=
    (intervalIntegral.integral_add_adjacent_intervals hVr0a hVra_r).symm
  have hUt : (∫ s in (0 : ℝ)..t, fullDuhamelValueIntegrand H t s x) =
      (∫ s in (0 : ℝ)..a, fullDuhamelValueIntegrand H t s x) +
        ∫ s in a..t, fullDuhamelValueIntegrand H t s x :=
    (intervalIntegral.integral_add_adjacent_intervals hVt0a hVta_t).symm
  have hBt : (∫ s in a..t, fullDuhamelValueIntegrand H t s x) =
      (∫ s in a..r, fullDuhamelValueIntegrand H t s x) +
        ∫ s in r..t, fullDuhamelValueIntegrand H t s x :=
    (intervalIntegral.integral_add_adjacent_intervals hVta_r hVtr_t).symm
  have hsl : (∫ s in a..r, slope
      (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) =
      ((∫ s in a..r, fullDuhamelValueIntegrand H r s x) -
        ∫ s in a..r, fullDuhamelValueIntegrand H t s x) / (r - t) := by
    rw [show (fun s : ℝ => slope
          (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) =
        fun s : ℝ => (fullDuhamelValueIntegrand H r s x -
          fullDuhamelValueIntegrand H t s x) / (r - t) by
      funext s
      rw [slope_def_field]]
    simp only [fullDuhamelValueIntegrand]
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub hVra_r hVta_r]
  rw [slope_def_field, slope_def_field, hUr, hUt, hBt, hsl]
  field_simp [sub_ne_zero.mpr hrt.ne, ne_of_gt (sub_pos.mpr hrt)]
  ring

/-- Direct physical-space target-time derivative of the full Neumann Duhamel
leg.  The source needs only a uniform trace at the target time and a spatial
Holder modulus on the preceding late half-window. -/
theorem intervalFullDuhamel_hasDerivAt_time_of_uniform_trace_late_holder
    {t theta CQ HQ : ℝ} (ht : 0 < t)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hCQ : 0 ≤ CQ) (hHQ : 0 ≤ HQ)
    {H : ℝ → ℝ → ℝ}
    (hH_meas : Measurable (Function.uncurry H))
    (hH_cont : ∀ s, Continuous (H s))
    (hH_int : ∀ s, Integrable (H s) (intervalMeasure 1))
    (hH_bound : ∀ s y, |H s y| ≤ CQ)
    (hH_time : TendstoUniformlyOn H (H t) (𝓝 t) (Set.Icc (0 : ℝ) 1))
    (hH_holder : ∀ s, t / 2 < s → s < t →
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ b ∈ Set.Ioo (0 : ℝ) 1,
        |H s a - H s b| ≤ HQ * |a - b| ^ theta)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s) (H s) x)
      ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (H s) z) y) x) +
        H t x) t := by
  let p : ℝ := theta / 2
  let Ctheta : ℝ := weightedHeatHessConst theta * HQ
  let E : ℝ → ℝ := fun a => Ctheta * ((t - a) ^ p / p)
  have hp : 0 < p := by dsimp [p]; linarith
  have hCtheta : 0 ≤ Ctheta := by
    dsimp [Ctheta]
    exact mul_nonneg
      (ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst_nonneg theta) hHQ
  have hE_nonneg : ∀ a, a ≤ t → 0 ≤ E a := by
    intro a hat'
    dsimp [E]
    exact mul_nonneg hCtheta
      (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hat') _) hp.le)
  have hpow_tend : Tendsto (fun a : ℝ => (t - a) ^ p) (𝓝 t) (𝓝 0) := by
    have hc : ContinuousAt (fun a : ℝ => (t - a) ^ p) t :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr hp.le)
    simpa [Real.zero_rpow hp.ne'] using hc.tendsto
  have hE_tend : Tendsto E (𝓝 t) (𝓝 0) := by
    have h := (hpow_tend.div_const p).const_mul Ctheta
    simpa [E] using h
  have hcutoff : ∀ eps > 0, ∃ a : ℝ,
      t / 2 < a ∧ a < t ∧ E a < eps := by
    intro eps heps
    have hleft : Tendsto E (𝓝[<] t) (𝓝 0) :=
      hE_tend.mono_left nhdsWithin_le_nhds
    rw [Metric.tendsto_nhds] at hleft
    have hsmall := hleft eps heps
    have hhalf : Set.Ioo (t / 2) t ∈ 𝓝[<] t :=
      Ioo_mem_nhdsLT (by linarith [ht])
    obtain ⟨a, ha_small, ha⟩ := (hsmall.and hhalf).exists
    refine ⟨a, ha.1, ha.2, ?_⟩
    simpa [Real.dist_eq, abs_of_nonneg (hE_nonneg a ha.2.le)] using ha_small
  let U : ℝ → ℝ := fun tau =>
    ∫ s in (0 : ℝ)..tau, fullDuhamelValueIntegrand H tau s x
  let I : ℝ := ∫ s in (0 : ℝ)..t, fullDuhamelHessIntegrand H t s x
  apply hasDerivAt_iff_tendsto_slope_left_right.mpr
  constructor
  · rw [Metric.tendsto_nhds]
    intro eps heps
    obtain ⟨a, hta, hat, hEa⟩ := hcutoff (eps / 4) (by linarith)
    have ha0 : 0 ≤ a := by linarith [hta, ht]
    let I0 : ℝ := ∫ s in (0 : ℝ)..a, fullDuhamelHessIntegrand H t s x
    let Ia : ℝ := ∫ s in a..t, fullDuhamelHessIntegrand H t s x
    have hI0_int := fixedHess_intervalIntegrable ha0 hat hCQ hH_meas hH_int
      hH_bound (x := x)
    have hIa_int := lateHess_intervalIntegrable hat hta htheta0 htheta1 hHQ
      hH_meas hH_int hH_bound hH_holder hx
    have hsplit : I0 + Ia = I := by
      dsimp [I0, Ia, I]
      exact intervalIntegral.integral_add_adjacent_intervals hI0_int hIa_int
    have hfixed := (fixedOldHistory_hasDerivAt ha0 hat hCQ hH_meas hH_cont
      hH_int hH_bound hx).tendsto_slope.mono_left (nhdsLT_le_nhdsNE t)
    rw [Metric.tendsto_nhds] at hfixed
    have hfixed_evt := hfixed (eps / 4) (by linarith)
    have htail := leftDeletedTailAverage_tendsto_trace ht hCQ hH_meas hH_cont
      hH_int hH_bound hH_time hx
    rw [Metric.tendsto_nhds] at htail
    have htail_evt := htail (eps / 4) (by linarith)
    filter_upwards [hfixed_evt, htail_evt, Ioo_mem_nhdsLT hat] with r hfix htailr hr
    have har : a < r := hr.1
    have hrt : r < t := hr.2
    have hdec := leftFullDuhamelSlope_decomp ha0 har hrt hCQ hH_meas
      hH_bound (x := x)
    have hlate := leftLateHistorySlope_abs_bound har hrt hta htheta0 htheta1
      hCQ hHQ hH_cont hH_int hH_bound hH_holder hx
    have hIa := lateHessIntegral_abs_bound hat hta htheta0 htheta1 hHQ
      hH_int hH_bound hH_holder hx
    have hfix_abs :
        |slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
          fullDuhamelValueIntegrand H q s x) t r - I0| < eps / 4 := by
      simpa [I0, Real.dist_eq] using hfix
    have htail_abs :
        |(∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) - H t x|
          < eps / 4 := by
      simpa [Real.dist_eq] using htailr
    have hlateE :
        |∫ s in a..r, slope
          (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r| ≤ E a := by
      simpa [E, Ctheta, p] using hlate
    have hIaE : |Ia| ≤ E a := by
      simpa [Ia, E, Ctheta, p] using hIa
    rw [show (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
      intervalFullSemigroupOperator (tau - s) (H s) x) = U by
        funext tau; rfl]
    rw [show (∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (H s) z) y) x) = I by rfl]
    rw [Real.dist_eq]
    change |slope U t r - (I + H t x)| < eps
    have hdecU : slope U t r =
        slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
          fullDuhamelValueIntegrand H q s x) t r +
        (∫ s in a..r, slope
          (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) +
        (∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) := by
      simpa [U] using hdec
    rw [hdecU, ← hsplit]
    have htri :
        |(slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
              fullDuhamelValueIntegrand H q s x) t r +
            (∫ s in a..r, slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) +
            (∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r)) -
          ((I0 + Ia) + H t x)| ≤
          |slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
              fullDuhamelValueIntegrand H q s x) t r - I0| +
          |∫ s in a..r, slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r| +
          |(∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) - H t x| +
          |Ia| := by
      calc
        _ = |((slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
                fullDuhamelValueIntegrand H q s x) t r - I0) +
              (∫ s in a..r, slope
                (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)) +
              ((∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) -
                H t x) - Ia| := by ring
        _ ≤ |(slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
                fullDuhamelValueIntegrand H q s x) t r - I0) +
              (∫ s in a..r, slope
                (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)| +
              |((∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) -
                H t x) - Ia| := by
          simpa [sub_eq_add_neg, add_assoc] using
            abs_add_le
              ((slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
                  fullDuhamelValueIntegrand H q s x) t r - I0) +
                (∫ s in a..r, slope
                  (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r))
              (((∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) -
                H t x) - Ia)
        _ ≤ _ := by
          have h1 := abs_add_le
            (slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
              fullDuhamelValueIntegrand H q s x) t r - I0)
            (∫ s in a..r, slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)
          have h2 := abs_sub
            ((∫ s in r..t, fullDuhamelValueIntegrand H t s x) / (t - r) - H t x) Ia
          linarith
    nlinarith [htri]
  · rw [Metric.tendsto_nhds]
    intro eps heps
    obtain ⟨a, hta, hat, hEa⟩ := hcutoff (eps / 4) (by linarith)
    have ha0 : 0 ≤ a := by linarith [hta, ht]
    let I0 : ℝ := ∫ s in (0 : ℝ)..a, fullDuhamelHessIntegrand H t s x
    let Ia : ℝ := ∫ s in a..t, fullDuhamelHessIntegrand H t s x
    have hI0_int := fixedHess_intervalIntegrable ha0 hat hCQ hH_meas hH_int
      hH_bound (x := x)
    have hIa_int := lateHess_intervalIntegrable hat hta htheta0 htheta1 hHQ
      hH_meas hH_int hH_bound hH_holder hx
    have hsplit : I0 + Ia = I := by
      dsimp [I0, Ia, I]
      exact intervalIntegral.integral_add_adjacent_intervals hI0_int hIa_int
    have hfixed := (fixedOldHistory_hasDerivAt ha0 hat hCQ hH_meas hH_cont
      hH_int hH_bound hx).tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)
    rw [Metric.tendsto_nhds] at hfixed
    have hfixed_evt := hfixed (eps / 4) (by linarith)
    have htail := rightTailAverage_tendsto_trace ht hCQ hH_meas hH_cont
      hH_int hH_bound hH_time hx
    rw [Metric.tendsto_nhds] at htail
    have htail_evt := htail (eps / 4) (by linarith)
    filter_upwards [hfixed_evt, htail_evt, self_mem_nhdsWithin] with r hfix htailr hr
    have htr : t < r := hr
    have hdec := rightFullDuhamelSlope_decomp ha0 hat htr hCQ hH_meas
      hH_bound (x := x)
    have hlate := rightLateHistorySlope_abs_bound hat htr hta htheta0 htheta1
      hCQ hHQ hH_cont hH_int hH_bound hH_holder hx
    have hIa := lateHessIntegral_abs_bound hat hta htheta0 htheta1 hHQ
      hH_int hH_bound hH_holder hx
    have hfix_abs :
        |slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
          fullDuhamelValueIntegrand H q s x) t r - I0| < eps / 4 := by
      simpa [I0, Real.dist_eq] using hfix
    have htail_abs :
        |(∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) - H t x|
          < eps / 4 := by
      simpa [Real.dist_eq] using htailr
    have hlateE :
        |∫ s in a..t, slope
          (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r| ≤ E a := by
      simpa [E, Ctheta, p] using hlate
    have hIaE : |Ia| ≤ E a := by
      simpa [Ia, E, Ctheta, p] using hIa
    rw [show (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
      intervalFullSemigroupOperator (tau - s) (H s) x) = U by
        funext tau; rfl]
    rw [show (∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (H s) z) y) x) = I by rfl]
    rw [Real.dist_eq]
    change |slope U t r - (I + H t x)| < eps
    have hdecU : slope U t r =
        slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
          fullDuhamelValueIntegrand H q s x) t r +
        (∫ s in a..t, slope
          (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) +
        (∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) := by
      simpa [U] using hdec
    rw [hdecU, ← hsplit]
    have htri :
        |(slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
              fullDuhamelValueIntegrand H q s x) t r +
            (∫ s in a..t, slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r) +
            (∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t)) -
          ((I0 + Ia) + H t x)| ≤
          |slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
              fullDuhamelValueIntegrand H q s x) t r - I0| +
          |∫ s in a..t, slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r| +
          |(∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) - H t x| +
          |Ia| := by
      calc
        _ = |((slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
                fullDuhamelValueIntegrand H q s x) t r - I0) +
              (∫ s in a..t, slope
                (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)) +
              ((∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) -
                H t x) - Ia| := by ring
        _ ≤ |(slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
                fullDuhamelValueIntegrand H q s x) t r - I0) +
              (∫ s in a..t, slope
                (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)| +
              |((∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) -
                H t x) - Ia| := by
          simpa [sub_eq_add_neg, add_assoc] using
            abs_add_le
              ((slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
                  fullDuhamelValueIntegrand H q s x) t r - I0) +
                (∫ s in a..t, slope
                  (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r))
              (((∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) -
                H t x) - Ia)
        _ ≤ _ := by
          have h1 := abs_add_le
            (slope (fun q : ℝ => ∫ s in (0 : ℝ)..a,
              fullDuhamelValueIntegrand H q s x) t r - I0)
            (∫ s in a..t, slope
              (fun q : ℝ => fullDuhamelValueIntegrand H q s x) t r)
          have h2 := abs_sub
            ((∫ s in t..r, fullDuhamelValueIntegrand H r s x) / (r - t) - H t x) Ia
          linarith
    nlinarith [htri]

section AxiomAudit

#print axioms intervalFullDuhamel_hasDerivAt_time_of_uniform_trace_late_holder

end AxiomAudit

end ShenWork.Paper2
