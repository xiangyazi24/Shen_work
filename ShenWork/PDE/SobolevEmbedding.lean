/-
  ShenWork/PDE/SobolevEmbedding.lean

  One-dimensional Sobolev embedding on an interval.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic

open MeasureTheory Set intervalIntegral
open scoped ENNReal Interval

noncomputable section

namespace ShenWork.Sobolev

/-- On a finite measure space, the `L¹` norm is controlled by the `L²` norm
with the usual factor `μ(univ)^(1/2)`. -/
theorem lpNorm_one_le_rpow_measure_mul_lpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hf_mem : MemLp f (2 : ℝ≥0∞) μ) :
    lpNorm f (1 : ℝ≥0∞) μ ≤
      ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) *
        lpNorm f (2 : ℝ≥0∞) μ := by
  have hle :
      eLpNorm f (1 : ℝ≥0∞) μ ≤
        eLpNorm f (2 : ℝ≥0∞) μ *
          μ Set.univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := by
    exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hf
  have hfinite :
      eLpNorm f (2 : ℝ≥0∞) μ *
          μ Set.univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact hf_mem.eLpNorm_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg
      · norm_num
      · exact measure_ne_top μ Set.univ
  have hreal := ENNReal.toReal_mono hfinite hle
  rw [toReal_eLpNorm hf] at hreal
  rw [ENNReal.toReal_mul, toReal_eLpNorm hf] at hreal
  have hpow :
      (μ Set.univ ^ (1 - (2 : ℝ)⁻¹)).toReal =
        (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.toReal_rpow]
    norm_num
  simpa [hpow, mul_comm, mul_left_comm, mul_assoc] using hreal

/-- Interval version of the finite-measure estimate `L¹ ≤ |I|^(1/2) L²`. -/
theorem interval_integral_abs_le_length_rpow_mul_lpNorm_two
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) L)))
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) :
    (∫ y in (0 : ℝ)..L, |f y|) ≤
      (L ^ (1 / 2 : ℝ)) *
        lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) L)
  have hμ : (μ Set.univ).toReal = L := by
    simp [μ, Real.volume_Ioc, hL.le]
  have hLp := lpNorm_one_le_rpow_measure_mul_lpNorm_two
    (μ := μ) hf hf_mem
  have hLpL :
      lpNorm f (1 : ℝ≥0∞) μ ≤
        (L ^ (1 / 2 : ℝ)) * lpNorm f (2 : ℝ≥0∞) μ := by
    simpa [hμ] using hLp
  have hint :
      (∫ y in (0 : ℝ)..L, |f y|) =
        lpNorm f (1 : ℝ≥0∞) μ := by
    rw [intervalIntegral.integral_of_le hL.le]
    rw [lpNorm_one_eq_integral_norm hf]
    rfl
  simpa [hint, μ] using hLpL

/-- A one-dimensional FTC estimate in `W^{1,1}` form. -/
theorem sobolev_pointwise_bound
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤ (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) +
      (∫ y in (0 : ℝ)..L, |f' y|) := by
  have hne : (Icc (0 : ℝ) L).Nonempty := ⟨0, left_mem_Icc.mpr hL.le⟩
  have habs_cont : ContinuousOn (fun y => |f y|) (Icc 0 L) :=
    continuous_abs.comp_continuousOn hf_cont
  obtain ⟨y₀, hy₀, hmin⟩ := IsCompact.exists_isMinOn isCompact_Icc hne habs_cont
  have hfy₀_mul_L : |f y₀| * L ≤ ∫ y in (0 : ℝ)..L, |f y| := by
    have habs_int : IntervalIntegrable (fun y : ℝ => |f y|) volume 0 L :=
      habs_cont.intervalIntegrable_of_Icc hL.le
    calc |f y₀| * L = ∫ _y in (0 : ℝ)..L, |f y₀| := by
          rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm]
      _ ≤ ∫ y in (0 : ℝ)..L, |f y| :=
          intervalIntegral.integral_mono_on hL.le intervalIntegrable_const
            habs_int (fun y hy => isMinOn_iff.mp hmin y hy)
  have hfy₀_le : |f y₀| ≤ (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) := by
    rw [one_div, le_inv_mul_iff₀ hL]
    simpa [mul_comm] using hfy₀_mul_L
  have huIcc_sub : Set.uIcc y₀ x ⊆ Icc 0 L :=
    Set.uIcc_subset_Icc hy₀ hx
  have hy₀_mem_uIcc : y₀ ∈ Set.uIcc (0 : ℝ) L := Set.Icc_subset_uIcc hy₀
  have hx_mem_uIcc : x ∈ Set.uIcc (0 : ℝ) L := Set.Icc_subset_uIcc hx
  have hftc : ∫ s in y₀..x, f' s = f x - f y₀ := by
    apply integral_eq_sub_of_hasDerivAt
    · exact fun s hs => hf_deriv s (huIcc_sub hs)
    · exact hf'_int.mono
        (Set.uIcc_subset_uIcc hy₀_mem_uIcc hx_mem_uIcc) le_rfl
  have hdiff : |f x - f y₀| ≤ ∫ s in (0 : ℝ)..L, |f' s| := by
    rw [← hftc]
    rcases le_or_gt y₀ x with hle | hgt
    · calc |∫ s in y₀..x, f' s|
          ≤ ∫ s in y₀..x, |f' s| := abs_integral_le_integral_abs hle
        _ ≤ ∫ s in (0 : ℝ)..L, |f' s| :=
            integral_mono_interval hy₀.1 hle hx.2
              (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              hf'_int.norm
    · rw [integral_symm, abs_neg]
      calc |∫ s in x..y₀, f' s|
          ≤ ∫ s in x..y₀, |f' s| := abs_integral_le_integral_abs hgt.le
        _ ≤ ∫ s in (0 : ℝ)..L, |f' s| :=
            integral_mono_interval hx.1 hgt.le hy₀.2
              (Filter.Eventually.of_forall fun _ => abs_nonneg _)
              hf'_int.norm
  have htri : |f x| ≤ |f y₀| + |f x - f y₀| := by
    calc |f x| = |f y₀ + (f x - f y₀)| := by
          congr 1
          ring
      _ ≤ |f y₀| + |f x - f y₀| := abs_add_le _ _
  have hsum :
      |f y₀| + |f x - f y₀| ≤
        (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) +
          (∫ s in (0 : ℝ)..L, |f' s|) :=
    add_le_add hfy₀_le hdiff
  exact htri.trans (by
    change |f y₀| + |f x - f y₀| ≤
      (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) +
        (∫ s in (0 : ℝ)..L, |f' s|)
    exact hsum)

/-- One-dimensional Sobolev embedding on `[0,L]` in pointwise form.

The interval `L²` norms are Mathlib `lpNorm`s for the restricted measure
`volume.restrict (Ioc 0 L)`. Since the representative is continuous, a pointwise
bound on every `x ∈ [0,L]` is the intended `L∞` control. -/
theorem sobolev_H1_Linfty_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤
      (1 / L) *
          ((L ^ (1 / 2 : ℝ)) *
            lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) +
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)) := by
  have hf'_int : IntervalIntegrable f' volume (0 : ℝ) L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
    exact hf'_mem.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  have hpoint := sobolev_pointwise_bound hL hf_cont hf_deriv hf'_int hx
  have hf_l1 :
      (∫ y in (0 : ℝ)..L, |f y|) ≤
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)) :=
    interval_integral_abs_le_length_rpow_mul_lpNorm_two hL
      hf_mem.aestronglyMeasurable hf_mem
  have hf'_l1 :
      (∫ y in (0 : ℝ)..L, |f' y|) ≤
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)) :=
    interval_integral_abs_le_length_rpow_mul_lpNorm_two hL
      hf'_mem.aestronglyMeasurable hf'_mem
  have hcoef_nonneg : 0 ≤ (1 / L : ℝ) := by positivity
  exact hpoint.trans <|
    add_le_add (mul_le_mul_of_nonneg_left hf_l1 hcoef_nonneg) hf'_l1

end ShenWork.Sobolev

end
