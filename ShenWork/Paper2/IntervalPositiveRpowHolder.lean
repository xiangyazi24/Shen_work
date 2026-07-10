/-
  Elementary one-dimensional Holder estimates used by the faithful
  positive-time bootstrap.  The fractional-power estimate is valid at zero,
  so it does not introduce a positive lower bound on the solution.
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import ShenWork.Paper2.Defs

open scoped Topology

noncomputable section

namespace ShenWork.Paper2

/-- A function with bounded derivative on `(0,1)` is Lipschitz between any two
interior points. -/
theorem abs_sub_le_mul_abs_sub_of_deriv_bound_Ioo
    {f : ℝ → ℝ} {C x y : ℝ}
    (hdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ f z)
    (hbound : ∀ z ∈ Set.Ioo (0 : ℝ) 1, ‖deriv f z‖ ≤ C)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    |f x - f y| ≤ C * |x - y| := by
  have hmv := (convex_Ioo (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := f) hdiff hbound hx hy
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmv

/-- Distances inside the unit interval increase when their exponent is lowered
from `1` to a positive `eta ≤ 1`. -/
theorem unitInterval_abs_sub_le_rpow
    {eta x y : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |x - y| ≤ |x - y| ^ eta := by
  have hdist : |x - y| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  simpa [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_ge'
      (x := |x - y|) (y := 1) (z := eta)
      (abs_nonneg _) hdist heta0.le heta1)

/-- For `0 < gamma ≤ 1`, the nonnegative real power is `gamma`-Holder all the
way down to zero. -/
theorem abs_rpow_sub_rpow_le_abs_sub_rpow
    {a b gamma : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    |a ^ gamma - b ^ gamma| ≤ |a - b| ^ gamma := by
  rcases le_total a b with hab | hba
  · have hpab : a ^ gamma ≤ b ^ gamma :=
      Real.rpow_le_rpow ha hab hgamma0.le
    have hsub : 0 ≤ b - a := sub_nonneg.mpr hab
    have hadd := Real.rpow_add_le_add_rpow ha hsub hgamma0.le hgamma1
    have hrewrite : a + (b - a) = b := by ring
    rw [hrewrite] at hadd
    rw [abs_of_nonpos (sub_nonpos.mpr hpab),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    rw [show -(a - b) = b - a by ring]
    linarith
  · have hpba : b ^ gamma ≤ a ^ gamma :=
      Real.rpow_le_rpow hb hba hgamma0.le
    have hsub : 0 ≤ a - b := sub_nonneg.mpr hba
    have hadd := Real.rpow_add_le_add_rpow hb hsub hgamma0.le hgamma1
    have hrewrite : b + (a - b) = a := by ring
    rw [hrewrite] at hadd
    rw [abs_of_nonneg (sub_nonneg.mpr hpba), abs_of_nonneg hsub]
    linarith

/-- A nonnegative bounded Lipschitz function, raised to an arbitrary positive
power `gamma`, is `eta`-Holder for every `0 < eta ≤ min(1,gamma)`.

The displayed constant covers both cases `gamma ≤ 1` and `1 ≤ gamma`; one of
its two nonnegative summands is unused in each case. -/
theorem rpow_holder_of_nonneg_bounded_lipschitz
    {a b x y gamma eta M C : ℝ}
    (hgamma : 0 < gamma) (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hetagamma : eta ≤ gamma) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (ha : a ∈ Set.Icc (0 : ℝ) M) (hb : b ∈ Set.Icc (0 : ℝ) M)
    (hab : |a - b| ≤ C * |x - y|)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |a ^ gamma - b ^ gamma| ≤
      (C ^ gamma + gamma * M ^ (gamma - 1) * C) * |x - y| ^ eta := by
  have hdist : |x - y| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hpow_eta : |x - y| ^ gamma ≤ |x - y| ^ eta := by
    exact Real.rpow_le_rpow_of_exponent_ge'
      (abs_nonneg _) hdist heta0.le hetagamma
  have hCpow : 0 ≤ C ^ gamma := Real.rpow_nonneg hC _
  have hlinear : 0 ≤ gamma * M ^ (gamma - 1) * C :=
    mul_nonneg (mul_nonneg hgamma.le (Real.rpow_nonneg hM _)) hC
  rcases le_total gamma 1 with hgamma1 | hgamma_ge
  · have hfrac := abs_rpow_sub_rpow_le_abs_sub_rpow
      ha.1 hb.1 hgamma hgamma1
    have habpow : |a - b| ^ gamma ≤ (C * |x - y|) ^ gamma :=
      Real.rpow_le_rpow (abs_nonneg _) hab hgamma.le
    have hmul : (C * |x - y|) ^ gamma =
        C ^ gamma * |x - y| ^ gamma := by
      exact Real.mul_rpow hC (abs_nonneg _)
    calc
      |a ^ gamma - b ^ gamma|
          ≤ |a - b| ^ gamma := hfrac
      _ ≤ (C * |x - y|) ^ gamma := habpow
      _ = C ^ gamma * |x - y| ^ gamma := hmul
      _ ≤ C ^ gamma * |x - y| ^ eta :=
        mul_le_mul_of_nonneg_left hpow_eta hCpow
      _ ≤ (C ^ gamma + gamma * M ^ (gamma - 1) * C) *
            |x - y| ^ eta :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hlinear)
          (Real.rpow_nonneg (abs_nonneg _) _)
  · have hlip : |a ^ gamma - b ^ gamma| ≤
        gamma * M ^ (gamma - 1) * |a - b| := by
      set L : ℝ := gamma * M ^ (gamma - 1) with hL
      have hLnn : 0 ≤ L := by
        rw [hL]
        exact mul_nonneg hgamma.le (Real.rpow_nonneg hM _)
      have hderiv : ∀ z ∈ Set.Icc (0 : ℝ) M,
          HasDerivWithinAt (fun w : ℝ => w ^ gamma)
            (gamma * z ^ (gamma - 1)) (Set.Icc (0 : ℝ) M) z := by
        intro z _
        exact (Real.hasDerivAt_rpow_const (Or.inr hgamma_ge)).hasDerivWithinAt
      have hbound : ∀ z ∈ Set.Icc (0 : ℝ) M,
          ‖gamma * z ^ (gamma - 1)‖ ≤ L := by
        intro z hz
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hgamma.le (Real.rpow_nonneg hz.1 _)), hL]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hz.1 hz.2 (by linarith)) hgamma.le
      have hmv := (convex_Icc (0 : ℝ) M).norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbound hb ha
      simpa [Real.norm_eq_abs, hL, abs_sub_comm] using hmv
    have hcoeff : 0 ≤ gamma * M ^ (gamma - 1) :=
      mul_nonneg hgamma.le (Real.rpow_nonneg hM _)
    have hlinxy :
        gamma * M ^ (gamma - 1) * |a - b| ≤
          (gamma * M ^ (gamma - 1) * C) * |x - y| := by
      calc
        gamma * M ^ (gamma - 1) * |a - b|
            ≤ gamma * M ^ (gamma - 1) * (C * |x - y|) :=
          mul_le_mul_of_nonneg_left hab hcoeff
        _ = (gamma * M ^ (gamma - 1) * C) * |x - y| := by ring
    have hdist_eta := unitInterval_abs_sub_le_rpow heta0 heta1 hx hy
    calc
      |a ^ gamma - b ^ gamma|
          ≤ gamma * M ^ (gamma - 1) * |a - b| := hlip
      _ ≤ (gamma * M ^ (gamma - 1) * C) * |x - y| := hlinxy
      _ ≤ (gamma * M ^ (gamma - 1) * C) * |x - y| ^ eta :=
        mul_le_mul_of_nonneg_left hdist_eta hlinear
      _ ≤ (C ^ gamma + gamma * M ^ (gamma - 1) * C) *
            |x - y| ^ eta :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCpow)
          (Real.rpow_nonneg (abs_nonneg _) _)

/-- Product rule for scalar Holder bounds. -/
theorem abs_mul_sub_mul_le_holder
    {fx fy gx gy Bf Bg Hf Hg d eta : ℝ}
    (hfx : |fx| ≤ Bf) (hgy : |gy| ≤ Bg)
    (hf : |fx - fy| ≤ Hf * d ^ eta)
    (hg : |gx - gy| ≤ Hg * d ^ eta)
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg) (hHf : 0 ≤ Hf) (hHg : 0 ≤ Hg)
    (hd : 0 ≤ d) :
    |fx * gx - fy * gy| ≤ (Hf * Bg + Bf * Hg) * d ^ eta := by
  calc
    |fx * gx - fy * gy|
        = |(fx - fy) * gy + fx * (gx - gy)| := by ring_nf
    _ ≤ |(fx - fy) * gy| + |fx * (gx - gy)| := abs_add_le _ _
    _ = |fx - fy| * |gy| + |fx| * |gx - gy| := by rw [abs_mul, abs_mul]
    _ ≤ (Hf * d ^ eta) * Bg + Bf * (Hg * d ^ eta) := by
      exact add_le_add
        (mul_le_mul hf hgy (abs_nonneg _) (mul_nonneg hHf (Real.rpow_nonneg hd _)))
        (mul_le_mul hfx hg (abs_nonneg _) hBf)
    _ = (Hf * Bg + Bf * Hg) * d ^ eta := by ring

end ShenWork.Paper2
