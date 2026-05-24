/-
  ShenWork/PDE/GagliardoNirenberg.lean

  One-dimensional Gagliardo--Nirenberg interpolation on an interval.
-/
import ShenWork.PDE.SobolevEmbedding
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

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

end
