/-
  ShenWork/PDE/SobolevEmbedding.lean

  Sobolev embedding H^1([0,L]) → L^∞([0,L]) in one spatial dimension.
  For f continuous on [0,L] with HasDerivAt on [0,L]:

    |f(x)| ≤ (1/L) ∫₀ᴸ |f(y)| dy + ∫₀ᴸ |f'(y)| dy
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic

open MeasureTheory Set intervalIntegral
open scoped Interval

noncomputable section

namespace ShenWork.Sobolev

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

end ShenWork.Sobolev

end
