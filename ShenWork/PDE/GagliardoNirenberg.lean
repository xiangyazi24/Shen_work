/-
  ShenWork/PDE/GagliardoNirenberg.lean

  One-dimensional Gagliardo--Nirenberg interpolation on an interval.
-/
import ShenWork.PDE.SobolevEmbedding
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Calculus.Deriv.Pow

open MeasureTheory Set intervalIntegral
open scoped ENNReal Interval

noncomputable section

namespace ShenWork.Sobolev

/-- If `f` is essentially bounded by `B`, then the `L⁴` norm is interpolated
between the `L∞` and `L²` norms: `||f||₄² ≤ B ||f||₂`.

The proof is the endpoint Hölder estimate `||f * f||₂ ≤ ||f||∞ ||f||₂`,
written in Mathlib's `lpNorm` API and converted from `eLpNorm`. -/
theorem lpNorm_four_rpow_two_le_bound_mul_lpNorm_two
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f μ)
    (hf_mem : MemLp f (2 : ℝ≥0∞) μ)
    (hB : 0 ≤ B)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ B) :
    (lpNorm f (4 : ℝ≥0∞) μ) ^ (2 : ℝ) ≤
      B * lpNorm f (2 : ℝ≥0∞) μ := by
  have hprod :
      eLpNorm (fun x => f x * f x) (2 : ℝ≥0∞) μ ≤
        (1 : ℝ≥0∞) * eLpNorm f (∞ : ℝ≥0∞) μ *
          eLpNorm f (2 : ℝ≥0∞) μ := by
    refine eLpNorm_le_eLpNorm_top_mul_eLpNorm (p := (2 : ℝ≥0∞))
      (f := f) (g := f) (μ := μ) hf (fun a b : ℝ => a * b) (1 : NNReal) ?_
    filter_upwards with x
    rw [nnnorm_mul]
    simp
  have htop : eLpNorm f (∞ : ℝ≥0∞) μ ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hbound
  have hprod' :
      eLpNorm (fun x => f x * f x) (2 : ℝ≥0∞) μ ≤
        ENNReal.ofReal B * eLpNorm f (2 : ℝ≥0∞) μ := by
    calc
      eLpNorm (fun x => f x * f x) (2 : ℝ≥0∞) μ
          ≤ (1 : ℝ≥0∞) * eLpNorm f (∞ : ℝ≥0∞) μ *
              eLpNorm f (2 : ℝ≥0∞) μ := hprod
      _ = eLpNorm f (∞ : ℝ≥0∞) μ * eLpNorm f (2 : ℝ≥0∞) μ := by
          simp
      _ ≤ ENNReal.ofReal B * eLpNorm f (2 : ℝ≥0∞) μ := by
          exact mul_le_mul_left htop _
  have hshape :
      eLpNorm (fun x => f x * f x) (2 : ℝ≥0∞) μ =
        eLpNorm f (4 : ℝ≥0∞) μ ^ (2 : ℝ) := by
    calc
      eLpNorm (fun x => f x * f x) (2 : ℝ≥0∞) μ =
          eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) (2 : ℝ≥0∞) μ := by
            refine eLpNorm_congr_norm_ae ?_
            filter_upwards with x
            simp [sq, norm_mul]
      _ = eLpNorm f (4 : ℝ≥0∞) μ ^ (2 : ℝ) := by
          have hpow := eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) (μ := μ) f
            (by norm_num : (0 : ℝ) < 2)
          have hfour : (2 : ℝ≥0∞) * ENNReal.ofReal (2 : ℝ) = (4 : ℝ≥0∞) := by
            norm_num
          rw [hfour] at hpow
          simpa using hpow
  have hprod'' :
      eLpNorm f (4 : ℝ≥0∞) μ ^ (2 : ℝ) ≤
        ENNReal.ofReal B * eLpNorm f (2 : ℝ≥0∞) μ := by
    simpa [hshape] using hprod'
  have hfinite :
      ENNReal.ofReal B * eLpNorm f (2 : ℝ≥0∞) μ ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf_mem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hprod''
  rw [← ENNReal.toReal_rpow, toReal_eLpNorm hf] at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB, toReal_eLpNorm hf] at hreal
  exact hreal

/-- One-dimensional Gagliardo--Nirenberg endpoint on `[0,L]`.

This is the `r=4`, `p=q=2`, `theta=1/2` form, squared:
`||f||_4^2 <= (C_L ||f||_2 + C_L ||f'||_2) ||f||_2`. The extra
`L^{-1/2} ||f||_2^2` lower-order contribution is the interval term coming from
`sobolev_H1_Linfty_interval`. -/
theorem gagliardoNirenberg_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (hf_mem : MemLp f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)))
    (hf'_mem : MemLp f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) :
    (lpNorm f (4 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) ^ (2 : ℝ) ≤
      ((1 / L) *
          ((L ^ (1 / 2 : ℝ)) *
            lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) +
        (L ^ (1 / 2 : ℝ)) *
          lpNorm f' (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L))) *
        lpNorm f (2 : ℝ≥0∞) (volume.restrict (Ioc (0 : ℝ) L)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) L)
  let B : ℝ :=
    (1 / L) *
        ((L ^ (1 / 2 : ℝ)) * lpNorm f (2 : ℝ≥0∞) μ) +
      (L ^ (1 / 2 : ℝ)) * lpNorm f' (2 : ℝ≥0∞) μ
  have hB_nonneg : 0 ≤ B := by
    have hsqrt_nonneg : 0 ≤ L ^ (1 / 2 : ℝ) := Real.rpow_nonneg hL.le _
    have hcoef_nonneg : 0 ≤ (1 / L : ℝ) := by positivity
    have hf_nonneg : 0 ≤ lpNorm f (2 : ℝ≥0∞) μ := lpNorm_nonneg
    have hf'_nonneg : 0 ≤ lpNorm f' (2 : ℝ≥0∞) μ := lpNorm_nonneg
    dsimp [B]
    exact add_nonneg
      (mul_nonneg hcoef_nonneg (mul_nonneg hsqrt_nonneg hf_nonneg))
      (mul_nonneg hsqrt_nonneg hf'_nonneg)
  have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ B := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hxIcc : x ∈ Icc (0 : ℝ) L := ⟨le_of_lt hx.1, hx.2⟩
    have hpoint := sobolev_H1_Linfty_interval hL hf_cont hf_deriv hf_mem hf'_mem
      (x := x) hxIcc
    simpa [Real.norm_eq_abs, B, μ] using hpoint
  have hmain := lpNorm_four_rpow_two_le_bound_mul_lpNorm_two
    (μ := μ) (f := f) (B := B) hf_mem.aestronglyMeasurable
    (by simpa [μ] using hf_mem) hB_nonneg hbound
  simpa [B, μ] using hmain

end ShenWork.Sobolev

namespace ShenWork.GagliardoNirenberg

open Real

/-! ### Cauchy–Schwarz for interval integrals -/

private theorem sq_integral_abs_mul_le
    {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℝ}
    (hf_sq : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hg_sq : IntervalIntegrable (fun y => g y ^ 2) volume 0 L)
    (hfg : IntervalIntegrable (fun y => |f y * g y|) volume 0 L) :
    (∫ y in (0 : ℝ)..L, |f y * g y|) ^ 2 ≤
      (∫ y in (0 : ℝ)..L, f y ^ 2) * (∫ y in (0 : ℝ)..L, g y ^ 2) := by
  set A := ∫ y in (0 : ℝ)..L, f y ^ 2 with hA_def
  set B := ∫ y in (0 : ℝ)..L, |f y * g y| with hB_def
  set C := ∫ y in (0 : ℝ)..L, g y ^ 2 with hC_def
  have hA_nn : 0 ≤ A := intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hB_nn : 0 ≤ B := intervalIntegral.integral_nonneg hL.le (fun u _ => abs_nonneg _)
  have hC_nn : 0 ≤ C := intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  -- Discriminant trick: 0 <= ∫(|f| - t|g|)^2 = A - 2tB + t^2C.
  suffices hdisc : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C by
    by_cases hC_pos : 0 < C
    · have h := hdisc (B / C)
      nlinarith [sq_nonneg (B - B / C * C), div_mul_cancel₀ B (ne_of_gt hC_pos)]
    · have hC0 : C = 0 := le_antisymm (not_lt.mp hC_pos) hC_nn
      rw [hC0, mul_zero]
      suffices hB0 : B = 0 by rw [hB0]; simp
      by_contra hBne
      have hBp : 0 < B := hB_nn.lt_of_ne' hBne
      have h := hdisc ((A + 1) / (2 * B))
      have h2B_ne : (2 : ℝ) * B ≠ 0 := by positivity
      nlinarith [div_mul_cancel₀ (A + 1) h2B_ne]
  intro t
  have heq : ∀ y, (|f y| - t * |g y|) ^ 2 =
      f y ^ 2 - 2 * t * (|f y| * |g y|) + t ^ 2 * g y ^ 2 := by
    intro y
    nlinarith [sq_abs (f y), sq_abs (g y), sq_nonneg (|f y| - t * |g y|)]
  have habs_eq : ∀ y, |f y| * |g y| = |f y * g y| := fun y => (abs_mul _ _).symm
  have h_integrand_eq : ∀ y,
      (|f y| - t * |g y|) ^ 2 =
        f y ^ 2 + (-(2 * t) * |f y * g y| + t ^ 2 * g y ^ 2) := by
    intro y
    rw [heq, habs_eq]
    ring
  have h_int_sq : IntervalIntegrable (fun y => (|f y| - t * |g y|) ^ 2) volume 0 L :=
    (hf_sq.add ((hfg.const_mul (-(2 * t))).add (hg_sq.const_mul (t ^ 2)))).congr
      (fun y _ => (h_integrand_eq y).symm)
  have h_nn : (0 : ℝ) ≤ ∫ y in (0 : ℝ)..L, (|f y| - t * |g y|) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg (|f u| - t * |g u|))
  have h_val : ∫ y in (0 : ℝ)..L, (|f y| - t * |g y|) ^ 2 =
      A - 2 * t * B + t ^ 2 * C := by
    have hcongr : ∫ y in (0 : ℝ)..L, (|f y| - t * |g y|) ^ 2 =
        ∫ y in (0 : ℝ)..L,
          (f y ^ 2 + (-(2 * t) * |f y * g y| + t ^ 2 * g y ^ 2)) :=
      intervalIntegral.integral_congr (fun y _ => h_integrand_eq y)
    rw [hcongr, intervalIntegral.integral_add hf_sq
      ((hfg.const_mul (-(2 * t))).add (hg_sq.const_mul (t ^ 2))),
      intervalIntegral.integral_add (hfg.const_mul (-(2 * t))) (hg_sq.const_mul (t ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  linarith

private theorem integral_abs_mul_le_sqrt
    {L : ℝ} (hL : 0 < L)
    {f g : ℝ → ℝ}
    (hf_sq : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hg_sq : IntervalIntegrable (fun y => g y ^ 2) volume 0 L)
    (hfg : IntervalIntegrable (fun y => |f y * g y|) volume 0 L) :
    ∫ y in (0 : ℝ)..L, |f y * g y| ≤
      sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
        sqrt (∫ y in (0 : ℝ)..L, g y ^ 2) := by
  set B := ∫ y in (0 : ℝ)..L, |f y * g y|
  set R := sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
    sqrt (∫ y in (0 : ℝ)..L, g y ^ 2)
  have hB_nn : 0 ≤ B := intervalIntegral.integral_nonneg hL.le (fun u _ => abs_nonneg _)
  have hR_nn : 0 ≤ R := mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
  have hsq := sq_integral_abs_mul_le hL hf_sq hg_sq hfg
  have hR_sq : R ^ 2 =
      (∫ y in (0 : ℝ)..L, f y ^ 2) * (∫ y in (0 : ℝ)..L, g y ^ 2) := by
    simp only [R, mul_pow,
      sq_sqrt (intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _))]
  have : B ^ 2 ≤ R ^ 2 := by linarith
  exact le_of_sq_le_sq this hR_nn

/-! ### Agmon's inequality -/

theorem agmon_inequality_interval
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (_hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Icc 0 L, HasDerivAt f (f' x) x)
    (_hf'_int : IntervalIntegrable f' volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun y => f' y ^ 2) volume 0 L)
    (hff'_int : IntervalIntegrable (fun y => f y * f' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    f x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, f y ^ 2) +
      2 * sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
        sqrt (∫ y in (0 : ℝ)..L, f' y ^ 2) := by
  set If2 := ∫ y in (0 : ℝ)..L, f y ^ 2 with hIf2_def
  set If'2 := ∫ y in (0 : ℝ)..L, f' y ^ 2 with hIf'2_def
  have hIf2_nn : 0 ≤ If2 := intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hfsq_deriv : ∀ s ∈ Icc 0 L,
      HasDerivAt (fun t => f t ^ 2) (2 * f s * f' s) s := by
    intro s hs
    have h := HasDerivAt.fun_pow (hf_deriv s hs) 2
    simp only [Nat.cast_ofNat] at h
    convert h using 1
    ring
  have h2ff'_int : IntervalIntegrable (fun s => 2 * f s * f' s) volume 0 L :=
    (hff'_int.const_mul 2).congr (fun s _ => by ring)
  have habs_ff' : IntervalIntegrable (fun y => |f y * f' y|) volume 0 L := by
    have := hff'_int.norm
    simp only [Real.norm_eq_abs] at this
    exact this
  have hftc : ∀ y₀ ∈ Icc (0 : ℝ) L,
      ∫ s in y₀..x, (2 * f s * f' s) = f x ^ 2 - f y₀ ^ 2 := by
    intro y₀ hy₀
    have hsub : uIcc y₀ x ⊆ Icc 0 L := uIcc_subset_Icc hy₀ hx
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hfsq_deriv s (hsub hs))
      (h2ff'_int.mono (uIcc_subset_uIcc (Icc_subset_uIcc hy₀) (Icc_subset_uIcc hx))
        le_rfl)
  set Iff' := ∫ y in (0 : ℝ)..L, |f y * f' y|
  have hpointwise : ∀ y₀ ∈ Icc (0 : ℝ) L, f x ^ 2 ≤ f y₀ ^ 2 + 2 * Iff' := by
    intro y₀ hy₀
    have hftc_eq := hftc y₀ hy₀
    simp only at hftc_eq
    have : f x ^ 2 = f y₀ ^ 2 + ∫ s in y₀..x, (2 * f s * f' s) := by
      linarith
    rw [this]
    suffices ∫ s in y₀..x, (2 * f s * f' s) ≤ 2 * Iff' by linarith
    calc ∫ s in y₀..x, (2 * f s * f' s)
        ≤ |∫ s in y₀..x, (2 * f s * f' s)| := le_abs_self _
      _ ≤ 2 * Iff' := by
        have habs_eq : (fun s => |2 * f s * f' s|) = fun s => 2 * |f s * f' s| := by
          funext s
          rw [show (2 : ℝ) * f s * f' s = 2 * (f s * f' s) from by ring,
            abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        have h_full_eq : ∫ s in (0 : ℝ)..L, |2 * f s * f' s| = 2 * Iff' := by
          simp_rw [habs_eq]
          exact intervalIntegral.integral_const_mul 2 _
        have h_abs_int : IntervalIntegrable (fun s => |2 * f s * f' s|) volume 0 L := by
          simp_rw [habs_eq]
          exact habs_ff'.const_mul 2
        rcases le_or_gt y₀ x with hle | hgt
        · calc |∫ s in y₀..x, (2 * f s * f' s)|
              ≤ ∫ s in y₀..x, |2 * f s * f' s| :=
                intervalIntegral.abs_integral_le_integral_abs hle
            _ ≤ ∫ s in (0 : ℝ)..L, |2 * f s * f' s| :=
                intervalIntegral.integral_mono_interval hy₀.1 hle hx.2
                  (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_abs_int
            _ = 2 * Iff' := h_full_eq
        · rw [intervalIntegral.integral_symm, abs_neg]
          calc |∫ s in x..y₀, (2 * f s * f' s)|
              ≤ ∫ s in x..y₀, |2 * f s * f' s| :=
                intervalIntegral.abs_integral_le_integral_abs hgt.le
            _ ≤ ∫ s in (0 : ℝ)..L, |2 * f s * f' s| :=
                intervalIntegral.integral_mono_interval hx.1 hgt.le hy₀.2
                  (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_abs_int
            _ = 2 * Iff' := h_full_eq
  have havg : L * f x ^ 2 ≤ If2 + L * (2 * Iff') := by
    have hint_le : ∫ _ in (0 : ℝ)..L, f x ^ 2 ≤
        ∫ y in (0 : ℝ)..L, (f y ^ 2 + 2 * Iff') :=
      intervalIntegral.integral_mono_on hL.le intervalIntegrable_const
        (hf_sq_int.add intervalIntegrable_const) (fun y hy => hpointwise y hy)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at hint_le
    rw [intervalIntegral.integral_add hf_sq_int intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at hint_le
    linarith
  have hcs : Iff' ≤ sqrt If2 * sqrt If'2 :=
    integral_abs_mul_le_sqrt hL hf_sq_int hf'_sq_int habs_ff'
  rw [div_mul_eq_mul_div, ← sub_le_iff_le_add, le_div_iff₀ hL]
  nlinarith [hcs]

/-- Agmon's inequality with only right derivatives on the open interval.

This is the version compatible with zero-extended interval-domain lifts: the
endpoints need not have full `HasDerivAt` data.  The proof is the same as
`agmon_inequality_interval`, using Mathlib's FTC variant for functions
continuous on the closed interval and right-differentiable on the interior. -/
theorem agmon_inequality_interval_rightDeriv
    {L : ℝ} (hL : 0 < L)
    {f f' : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc 0 L))
    (hf_deriv : ∀ x ∈ Ioo (0 : ℝ) L, HasDerivWithinAt f (f' x) (Ioi x) x)
    (_hf'_int : IntervalIntegrable f' volume 0 L)
    (hf_sq_int : IntervalIntegrable (fun y => f y ^ 2) volume 0 L)
    (hf'_sq_int : IntervalIntegrable (fun y => f' y ^ 2) volume 0 L)
    (hff'_int : IntervalIntegrable (fun y => f y * f' y) volume 0 L)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    f x ^ 2 ≤ (2 / L) * (∫ y in (0 : ℝ)..L, f y ^ 2) +
      2 * sqrt (∫ y in (0 : ℝ)..L, f y ^ 2) *
        sqrt (∫ y in (0 : ℝ)..L, f' y ^ 2) := by
  set If2 := ∫ y in (0 : ℝ)..L, f y ^ 2 with hIf2_def
  set If'2 := ∫ y in (0 : ℝ)..L, f' y ^ 2 with hIf'2_def
  have hIf2_nn : 0 ≤ If2 := intervalIntegral.integral_nonneg hL.le (fun u _ => sq_nonneg _)
  have hfsq_deriv : ∀ s ∈ Ioo (0 : ℝ) L,
      HasDerivWithinAt (fun t => f t ^ 2) (2 * f s * f' s) (Ioi s) s := by
    intro s hs
    have h := HasDerivWithinAt.fun_pow (hf_deriv s hs) 2
    simp only [Nat.cast_ofNat] at h
    convert h using 1
    ring
  have hfsq_cont : ContinuousOn (fun t => f t ^ 2) (Icc (0 : ℝ) L) := by
    have hmul : ContinuousOn (fun t => f t * f t) (Icc (0 : ℝ) L) :=
      hf_cont.mul hf_cont
    refine hmul.congr ?_
    intro t ht
    ring
  have h2ff'_int : IntervalIntegrable (fun s => 2 * f s * f' s) volume 0 L :=
    (hff'_int.const_mul 2).congr (fun s _ => by ring)
  have habs_ff' : IntervalIntegrable (fun y => |f y * f' y|) volume 0 L := by
    have := hff'_int.norm
    simp only [Real.norm_eq_abs] at this
    exact this
  have hftc : ∀ y₀ ∈ Icc (0 : ℝ) L,
      ∫ s in y₀..x, (2 * f s * f' s) = f x ^ 2 - f y₀ ^ 2 := by
    intro y₀ hy₀
    have hsub : uIcc y₀ x ⊆ Icc 0 L := uIcc_subset_Icc hy₀ hx
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (hcont := hfsq_cont.mono hsub)
      (hderiv := by
        intro s hs
        have hs_uIoo : s ∈ uIoo y₀ x := by
          simpa [Ioo_min_max] using hs
        exact hfsq_deriv s (uIoo_subset_Ioo hy₀ hx hs_uIoo))
      (hint := h2ff'_int.mono
        (uIcc_subset_uIcc (Icc_subset_uIcc hy₀) (Icc_subset_uIcc hx))
        le_rfl)
  set Iff' := ∫ y in (0 : ℝ)..L, |f y * f' y|
  have hpointwise : ∀ y₀ ∈ Icc (0 : ℝ) L, f x ^ 2 ≤ f y₀ ^ 2 + 2 * Iff' := by
    intro y₀ hy₀
    have hftc_eq := hftc y₀ hy₀
    simp only at hftc_eq
    have : f x ^ 2 = f y₀ ^ 2 + ∫ s in y₀..x, (2 * f s * f' s) := by
      linarith
    rw [this]
    suffices ∫ s in y₀..x, (2 * f s * f' s) ≤ 2 * Iff' by linarith
    calc ∫ s in y₀..x, (2 * f s * f' s)
        ≤ |∫ s in y₀..x, (2 * f s * f' s)| := le_abs_self _
      _ ≤ 2 * Iff' := by
        have habs_eq : (fun s => |2 * f s * f' s|) = fun s => 2 * |f s * f' s| := by
          funext s
          rw [show (2 : ℝ) * f s * f' s = 2 * (f s * f' s) from by ring,
            abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
        have h_full_eq : ∫ s in (0 : ℝ)..L, |2 * f s * f' s| = 2 * Iff' := by
          simp_rw [habs_eq]
          exact intervalIntegral.integral_const_mul 2 _
        have h_abs_int : IntervalIntegrable (fun s => |2 * f s * f' s|) volume 0 L := by
          simp_rw [habs_eq]
          exact habs_ff'.const_mul 2
        rcases le_or_gt y₀ x with hle | hgt
        · calc |∫ s in y₀..x, (2 * f s * f' s)|
              ≤ ∫ s in y₀..x, |2 * f s * f' s| :=
                intervalIntegral.abs_integral_le_integral_abs hle
            _ ≤ ∫ s in (0 : ℝ)..L, |2 * f s * f' s| :=
                intervalIntegral.integral_mono_interval hy₀.1 hle hx.2
                  (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_abs_int
            _ = 2 * Iff' := h_full_eq
        · rw [intervalIntegral.integral_symm, abs_neg]
          calc |∫ s in x..y₀, (2 * f s * f' s)|
              ≤ ∫ s in x..y₀, |2 * f s * f' s| :=
                intervalIntegral.abs_integral_le_integral_abs hgt.le
            _ ≤ ∫ s in (0 : ℝ)..L, |2 * f s * f' s| :=
                intervalIntegral.integral_mono_interval hx.1 hgt.le hy₀.2
                  (Filter.Eventually.of_forall fun _ => abs_nonneg _) h_abs_int
            _ = 2 * Iff' := h_full_eq
  have havg : L * f x ^ 2 ≤ If2 + L * (2 * Iff') := by
    have hint_le : ∫ _ in (0 : ℝ)..L, f x ^ 2 ≤
        ∫ y in (0 : ℝ)..L, (f y ^ 2 + 2 * Iff') :=
      intervalIntegral.integral_mono_on hL.le intervalIntegrable_const
        (hf_sq_int.add intervalIntegrable_const) (fun y hy => hpointwise y hy)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at hint_le
    rw [intervalIntegral.integral_add hf_sq_int intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at hint_le
    linarith
  have hcs : Iff' ≤ sqrt If2 * sqrt If'2 :=
    integral_abs_mul_le_sqrt hL hf_sq_int hf'_sq_int habs_ff'
  rw [div_mul_eq_mul_div, ← sub_le_iff_le_add, le_div_iff₀ hL]
  nlinarith [hcs]

end ShenWork.GagliardoNirenberg

end
