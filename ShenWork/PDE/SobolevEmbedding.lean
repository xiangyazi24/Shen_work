/-
  ShenWork/PDE/SobolevEmbedding.lean

  Sobolev embedding H^1([0,L]) -> L^∞([0,L]) in one spatial dimension.
  For f continuous on [0,L] with HasDerivAt on [0,L]:

    |f(x)| ≤ (1/L) ∫₀ᴸ |f(y)| dy + ∫₀ᴸ |f'(y)| dy

  and hence, for f and f' in L²(0,L),

    |f(x)| ≤ (1/L) L^(1/2) ‖f‖₂ + L^(1/2) ‖f'‖₂.
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

theorem sobolev_pointwise_bound
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤ (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) +
      (∫ y in (0 : ℝ)..L, |f' y|) := by
  -- Step 1: find y₀ ∈ [0,L] minimizing |f|
  have hne : (Icc (0 : ℝ) L).Nonempty := ⟨0, left_mem_Icc.mpr hL.le⟩
  have habs_cont : ContinuousOn (fun y => |f y|) (Icc 0 L) :=
    continuous_abs.comp_continuousOn hf_cont
  obtain ⟨y₀, hy₀, hmin⟩ := IsCompact.exists_isMinOn isCompact_Icc hne habs_cont
  -- hmin : IsMinOn (|f ·|) (Icc 0 L) y₀, i.e. ∀ y ∈ Icc 0 L, |f y₀| ≤ |f y|
  -- Step 2: |f y₀| * L ≤ ∫|f|
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
  -- Step 3: FTC gives f(x) - f(y₀) = ∫_{y₀}^x f'
  have huIcc_sub : Set.uIcc y₀ x ⊆ Icc 0 L :=
    Set.uIcc_subset_Icc hy₀ hx
  have hy₀_mem_uIcc : y₀ ∈ Set.uIcc (0 : ℝ) L := Set.Icc_subset_uIcc hy₀
  have hx_mem_uIcc : x ∈ Set.uIcc (0 : ℝ) L := Set.Icc_subset_uIcc hx
  have hftc : ∫ s in y₀..x, f' s = f x - f y₀ := by
    apply integral_eq_sub_of_hasDerivAt
    · exact fun s hs => hf_deriv s (huIcc_sub hs)
    · exact hf'_int.mono
        (Set.uIcc_subset_uIcc hy₀_mem_uIcc hx_mem_uIcc) le_rfl
  -- Step 4: |∫_{y₀}^x f'| ≤ ∫₀ᴸ |f'|
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
  -- Step 5: combine via triangle inequality
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

/-! ### Cauchy-Schwarz step: ∫|f| ≤ √L · √(∫f²) -/

/-- Squared version: (∫₀ᴸ |f|)² ≤ L · ∫₀ᴸ f². This is the algebraic core of
    the interval Cauchy-Schwarz inequality, proved via the variance trick. -/
private lemma sq_integral_abs_le
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L) :
    (∫ y in (0 : ℝ)..L, |f y|) ^ 2 ≤ L * ∫ y in (0 : ℝ)..L, f y ^ 2 := by
  set A := ∫ y in (0 : ℝ)..L, |f y|
  set I := ∫ y in (0 : ℝ)..L, f y ^ 2
  set c := A / L
  -- Integrability facts
  have habs_int : IntervalIntegrable (fun y => |f y|) volume 0 L := hf_int.norm
  -- Variance is nonneg: 0 ≤ ∫₀ᴸ (|f y| - c)²
  have hvar : 0 ≤ ∫ y in (0 : ℝ)..L, (|f y| - c) ^ 2 :=
    integral_nonneg_of_forall hL.le (fun y => sq_nonneg _)
  -- Expand (|f y| - c)² = |f y|² - 2c|f y| + c²
  -- Then use integral linearity:
  -- ∫(|f|-c)² = ∫|f|² - 2c·∫|f| + c²·L = I - 2c·A + c²·L
  -- Expand ∫(|f|-c)² using linearity of the interval integral
  -- We rewrite (|f|-c)² = f² - 2c|f| + c² and use integral linearity
  have h2c_int : IntervalIntegrable (fun y => 2 * c * |f y|) volume 0 L :=
    habs_int.const_mul (2 * c)
  have hexpand : ∫ y in (0 : ℝ)..L, (|f y| - c) ^ 2 = I - 2 * c * A + c ^ 2 * L := by
    -- Split: (|f y| - c)² = f y² - 2c|f y| + c²
    have hrew : ∀ y, (|f y| - c) ^ 2 = f y ^ 2 - 2 * c * |f y| + c ^ 2 := by
      intro y; rw [← sq_abs (f y)]; ring
    simp_rw [hrew]
    -- ∫(a - b + c) = ∫a - ∫b + ∫c  by linearity
    rw [show (fun y => f y ^ 2 - 2 * c * |f y| + c ^ 2) =
        (fun y => (f y ^ 2 - 2 * c * |f y|) + c ^ 2) from by ext y; ring]
    rw [integral_add (hf_sq_int.sub h2c_int) intervalIntegrable_const]
    rw [integral_sub hf_sq_int h2c_int]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]; ring
  rw [hexpand] at hvar
  -- hvar : 0 ≤ I - 2 * c * A + c² * L where c = A/L
  -- Algebraically: I - 2*(A/L)*A + (A/L)²*L = I - A²/L ≥ 0
  -- Hence A² ≤ L * I
  have hcL : c * L = A := div_mul_cancel₀ A hL.ne'
  nlinarith [sq_nonneg c, mul_self_nonneg (c * L)]

private lemma integral_abs_le_sqrt_mul_L2
    {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf_int : IntervalIntegrable f volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L) :
    ∫ y in (0 : ℝ)..L, |f y| ≤
      Real.sqrt L * Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) := by
  have hA_nn : 0 ≤ ∫ y in (0 : ℝ)..L, |f y| :=
    integral_nonneg_of_forall hL.le (fun y => abs_nonneg _)
  have hI_nn : 0 ≤ ∫ y in (0 : ℝ)..L, f y ^ 2 :=
    integral_nonneg_of_forall hL.le (fun y => sq_nonneg _)
  rw [← Real.sqrt_mul hL.le]
  rw [Real.le_sqrt hA_nn (mul_nonneg hL.le hI_nn)]
  exact sq_integral_abs_le hL hf_int hf_sq_int

/-! ### Main L² Sobolev embedding -/

theorem sobolev_H1_Linfty_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf'_int : IntervalIntegrable f' volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun y => f' y ^ 2) volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    |f x| ≤ (1 / Real.sqrt L) * Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) +
      Real.sqrt L * Real.sqrt (∫ y in (0 : ℝ)..L, f' y ^ 2) := by
  -- Step 1: apply sobolev_pointwise_bound
  have hpw := sobolev_pointwise_bound hL hf_cont hf_deriv hf'_int hx
  -- Step 2: integrability of f and f² from continuity
  have hf_int : IntervalIntegrable f volume 0 L :=
    hf_cont.intervalIntegrable_of_Icc hL.le
  have hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L :=
    (hf_cont.pow 2).intervalIntegrable_of_Icc hL.le
  -- Step 3: apply Cauchy-Schwarz
  have hCS_f := integral_abs_le_sqrt_mul_L2 hL hf_int hf_sq_int
  have hCS_f' := integral_abs_le_sqrt_mul_L2 hL hf'_int hf'_sq_int
  -- Step 4: combine
  -- hpw: |f x| ≤ (1/L) * ∫|f| + ∫|f'|
  -- hCS_f: ∫|f| ≤ √L * √(∫f²)
  -- hCS_f': ∫|f'| ≤ √L * √(∫f'²)
  -- So: |f x| ≤ (1/L) * √L * √(∫f²) + √L * √(∫f'²)
  -- And (1/L) * √L = 1/√L
  have h1 : (1 / L) * (∫ y in (0 : ℝ)..L, |f y|) ≤
      (1 / Real.sqrt L) * Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) := by
    calc (1 / L) * (∫ y in (0 : ℝ)..L, |f y|)
        ≤ (1 / L) * (Real.sqrt L * Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2)) :=
          mul_le_mul_of_nonneg_left hCS_f (by positivity)
      _ = (1 / Real.sqrt L) * Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) := by
          rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, one_mul]
          rw [show Real.sqrt L * Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) / L =
              Real.sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) * (Real.sqrt L / L) from by ring]
          rw [show Real.sqrt L / L = 1 / Real.sqrt L from Real.sqrt_div_self']
          ring
  linarith

end ShenWork.Sobolev

end
