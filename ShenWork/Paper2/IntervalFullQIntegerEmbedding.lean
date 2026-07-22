import ShenWork.PDE.SobolevEmbedding
import ShenWork.PDE.IntervalDomain

/-!
# Full-exponent integer Sobolev embedding on `[0,1]`

This is the physical `W^{1,p}` endpoint of the Paper-2 embedding scale.  It
does not identify `W^{1,p}` with the fractional Neumann domain, but it records
the full-`p` pointwise and Holder estimates available without any spectral
multiplier theorem.
-/

open MeasureTheory Set Filter
open scoped ENNReal Interval

noncomputable section

namespace ShenWork.Paper2.IntervalFullQIntegerEmbedding

open ShenWork.IntervalDomain
open ShenWork.Sobolev

/-- On the unit interval, `L^p` controls `L^1` for every `1 < p < infinity`.
The proof is direct Holder, with no interpolation theorem. -/
theorem unitInterval_integral_abs_le_lpNorm
    {p r : ℝ} (hrp : r.HolderConjugate p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p)
      (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫ y in (0 : ℝ)..1, |f y|) ≤
      lpNorm f (ENNReal.ofReal p)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ]⟩
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal r) μ := by
    apply MemLp.of_bound aestronglyMeasurable_const 1
    exact Filter.Eventually.of_forall fun _ => by norm_num
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (f := fun _ : ℝ => (1 : ℝ)) (g := f) hrp hone hf
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hlp :
      lpNorm f (ENNReal.ofReal p) μ =
        (∫ y, ‖f y‖ ^ p ∂μ) ^ (1 / p) := by
    dsimp [μ]
    rw [lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  have honepow : (∫ _y, ‖(1 : ℝ)‖ ^ r ∂μ) ^ (1 / r) = 1 := by
    simp [μ]
  calc
    (∫ y in (0 : ℝ)..1, |f y|) =
        ∫ y, ‖(1 : ℝ)‖ * ‖f y‖ ∂μ := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simp [μ, Real.norm_eq_abs]
    _ ≤ (∫ y, ‖(1 : ℝ)‖ ^ r ∂μ) ^ (1 / r) *
        (∫ y, ‖f y‖ ^ p ∂μ) ^ (1 / p) := hholder
    _ = (∫ y, ‖f y‖ ^ p ∂μ) ^ (1 / p) := by
      rw [honepow, one_mul]
    _ = lpNorm f (ENNReal.ofReal p) μ := hlp.symm
    _ = lpNorm f (ENNReal.ofReal p)
        (volume.restrict (Ioc (0 : ℝ) 1)) := rfl

/-- Full-exponent `W^{1,p} -> L^infinity` pointwise embedding on `[0,1]`. -/
theorem sobolev_W1p_Linfty_unitInterval
    {p r : ℝ} (hrp : r.HolderConjugate p)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_deriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (ENNReal.ofReal p)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hf'_mem : MemLp f' (ENNReal.ofReal p)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |f x| ≤
      lpNorm f (ENNReal.ofReal p) (volume.restrict (Ioc (0 : ℝ) 1)) +
        lpNorm f' (ENNReal.ofReal p)
          (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hrp.symm.lt.le
  have hf'_int : IntervalIntegrable f' volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact memLp_one_iff_integrable.mp (hf'_mem.mono_exponent hp_enn)
  have hpoint := sobolev_pointwise_bound
    (L := (1 : ℝ)) one_pos hf_cont hf_deriv hf'_int hx
  have hf_l1 := unitInterval_integral_abs_le_lpNorm hrp hf_mem
  have hf'_l1 := unitInterval_integral_abs_le_lpNorm hrp hf'_mem
  have hsum := add_le_add hf_l1 hf'_l1
  norm_num at hpoint
  exact hpoint.trans hsum

/-- Local interval Holder estimate used in the Morrey endpoint below. -/
theorem interval_integral_abs_le_length_rpow_mul_lpNorm
    {a b p r : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hrp : r.HolderConjugate p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p)
      (volume.restrict (Ioc (0 : ℝ) 1))) :
    (∫ z in a..b, |f z|) ≤
      (b - a) ^ (1 / r) *
        lpNorm f (ENNReal.ofReal p)
          (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let ν := volume.restrict (Ioc a b)
  have hset : Ioc a b ⊆ Ioc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨lt_of_le_of_lt ha hz.1, le_trans hz.2 hb⟩
  have hνμ : ν ≤ μ := Measure.restrict_mono hset le_rfl
  haveI : IsFiniteMeasure ν := ⟨by simp [ν, Real.volume_Ioc]⟩
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal r) ν := by
    apply MemLp.of_bound aestronglyMeasurable_const 1
    exact Filter.Eventually.of_forall fun _ => by norm_num
  have hfν : MemLp f (ENNReal.ofReal p) ν := hf.mono_measure hνμ
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := ν) (f := fun _ : ℝ => (1 : ℝ)) (g := f) hrp hone hfν
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfp_int : Integrable (fun z => ‖f z‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hrp.symm.nonneg] using
      hf.integrable_norm_rpow hp_zero hp_top
  have hlocal_le : (∫ z, ‖f z‖ ^ p ∂ν) ≤ ∫ z, ‖f z‖ ^ p ∂μ :=
    integral_mono_measure hνμ
      (Filter.Eventually.of_forall fun z =>
        Real.rpow_nonneg (norm_nonneg _) p) hfp_int
  have hroot_le :
      (∫ z, ‖f z‖ ^ p ∂ν) ^ (1 / p) ≤
        (∫ z, ‖f z‖ ^ p ∂μ) ^ (1 / p) :=
    Real.rpow_le_rpow
      (integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) p)
      hlocal_le hrp.symm.one_div_nonneg
  have hlp :
      lpNorm f (ENNReal.ofReal p) μ =
        (∫ z, ‖f z‖ ^ p ∂μ) ^ (1 / p) := by
    dsimp [μ]
    rw [lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  have honepow : (∫ _z, ‖(1 : ℝ)‖ ^ r ∂ν) ^ (1 / r) =
      (b - a) ^ (1 / r) := by
    simp [ν, hab]
  calc
    (∫ z in a..b, |f z|) = ∫ z, ‖(1 : ℝ)‖ * ‖f z‖ ∂ν := by
      rw [intervalIntegral.integral_of_le hab]
      simp [ν, Real.norm_eq_abs]
    _ ≤ (∫ z, ‖(1 : ℝ)‖ ^ r ∂ν) ^ (1 / r) *
        (∫ z, ‖f z‖ ^ p ∂ν) ^ (1 / p) := hholder
    _ ≤ (b - a) ^ (1 / r) *
        (∫ z, ‖f z‖ ^ p ∂μ) ^ (1 / p) := by
      rw [honepow]
      exact mul_le_mul_of_nonneg_left hroot_le
        (Real.rpow_nonneg (sub_nonneg.mpr hab) _)
    _ = (b - a) ^ (1 / r) * lpNorm f (ENNReal.ofReal p) μ := by
      rw [hlp]
    _ = (b - a) ^ (1 / r) *
        lpNorm f (ENNReal.ofReal p)
          (volume.restrict (Ioc (0 : ℝ) 1)) := rfl

/-- The ordered-point version of the full-exponent Morrey estimate. -/
theorem sobolev_W1p_holder_unitInterval_of_le
    {p r : ℝ} (hrp : r.HolderConjugate p)
    {f f' : ℝ → ℝ}
    (hf_deriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'_mem : MemLp f' (ENNReal.ofReal p)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    |f x - f y| ≤ |x - y| ^ (1 - 1 / p) *
      lpNorm f' (ENNReal.ofReal p)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hp_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hrp.symm.lt.le
  have hf'_int : IntervalIntegrable f' volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact memLp_one_iff_integrable.mp (hf'_mem.mono_exponent hp_enn)
  have hexp : 1 / r = 1 - 1 / p := by
    have hsum := hrp.inv_add_inv_eq_one
    simpa [one_div] using (eq_sub_of_add_eq hsum)
  have hsub : Set.uIcc x y ⊆ Icc (0 : ℝ) 1 :=
    Set.uIcc_subset_Icc hx hy
  have hftc : ∫ z in x..y, f' z = f y - f x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · exact fun z hz => hf_deriv z (hsub hz)
    · exact hf'_int.mono
        (Set.uIcc_subset_uIcc (Set.Icc_subset_uIcc hx)
          (Set.Icc_subset_uIcc hy)) le_rfl
  have habs := intervalIntegral.abs_integral_le_integral_abs
    (μ := volume) (f := f') hxy
  have hlocal := interval_integral_abs_le_length_rpow_mul_lpNorm
    hx.1 hxy hy.2 hrp hf'_mem
  calc
    |f x - f y| = |∫ z in x..y, f' z| := by
      rw [hftc]
      exact abs_sub_comm _ _
    _ ≤ ∫ z in x..y, |f' z| := habs
    _ ≤ (y - x) ^ (1 / r) *
        lpNorm f' (ENNReal.ofReal p)
          (volume.restrict (Ioc (0 : ℝ) 1)) := hlocal
    _ = |x - y| ^ (1 - 1 / p) *
        lpNorm f' (ENNReal.ofReal p)
          (volume.restrict (Ioc (0 : ℝ) 1)) := by
      rw [hexp, abs_of_nonpos (sub_nonpos.mpr hxy)]
      congr 2
      ring

/-- Full-exponent one-dimensional Morrey estimate:
`W^{1,p}([0,1]) -> C^{0,1-1/p}([0,1])`. -/
theorem sobolev_W1p_holder_unitInterval
    {p r : ℝ} (hrp : r.HolderConjugate p)
    {f f' : ℝ → ℝ}
    (hf_deriv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'_mem : MemLp f' (ENNReal.ofReal p)
      (volume.restrict (Ioc (0 : ℝ) 1)))
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |f x - f y| ≤ |x - y| ^ (1 - 1 / p) *
      lpNorm f' (ENNReal.ofReal p)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
  rcases le_total x y with hxy | hyx
  · exact sobolev_W1p_holder_unitInterval_of_le
      hrp hf_deriv hf'_mem hx hy hxy
  · have h := sobolev_W1p_holder_unitInterval_of_le
      hrp hf_deriv hf'_mem hy hx hyx
    calc
      |f x - f y| = |f y - f x| := abs_sub_comm _ _
      _ ≤ |y - x| ^ (1 - 1 / p) *
          lpNorm f' (ENNReal.ofReal p)
            (volume.restrict (Ioc (0 : ℝ) 1)) := h
      _ = |x - y| ^ (1 - 1 / p) *
          lpNorm f' (ENNReal.ofReal p)
            (volume.restrict (Ioc (0 : ℝ) 1)) := by
        rw [abs_sub_comm y x]

#print axioms unitInterval_integral_abs_le_lpNorm
#print axioms sobolev_W1p_Linfty_unitInterval
#print axioms interval_integral_abs_le_length_rpow_mul_lpNorm
#print axioms sobolev_W1p_holder_unitInterval_of_le
#print axioms sobolev_W1p_holder_unitInterval

end ShenWork.Paper2.IntervalFullQIntegerEmbedding
