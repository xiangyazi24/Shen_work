import Mathlib

/-!
# Explicit 1D Neumann elliptic Green kernel on `[0,1]`

This file starts the physical Green-kernel route for `-v'' + μ v = f` with
Neumann boundary conditions.  The main unconditional atom here is strict
positivity of the explicit kernel on the closed unit interval.
-/

noncomputable section

open Set
open scoped Topology

namespace ShenWork.PDE

/-- The explicit Green kernel for `-v'' + μ v = f` on `[0,1]` with Neumann
boundary conditions. -/
def neumannEllipticGreen (μ : ℝ) (x y : ℝ) : ℝ :=
  Real.cosh (Real.sqrt μ * min x y) *
    Real.cosh (Real.sqrt μ * (1 - max x y)) /
      (Real.sqrt μ * Real.sinh (Real.sqrt μ))

/-- The denominator in the positive-mass Neumann Green kernel is positive. -/
lemma neumannEllipticGreen_denom_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < Real.sqrt μ * Real.sinh (Real.sqrt μ) := by
  have hsqrt : 0 < Real.sqrt μ := Real.sqrt_pos_of_pos hμ
  have hsinh : 0 < Real.sinh (Real.sqrt μ) := by
    exact Real.sinh_pos_iff.mpr hsqrt
  exact mul_pos hsqrt hsinh

/-- Strict positivity of the explicit Neumann elliptic Green kernel. -/
theorem neumannEllipticGreen_pos {μ x y : ℝ}
    (hμ : 0 < μ) (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1)
    (_hy0 : 0 ≤ y) (_hy1 : y ≤ 1) :
    0 < neumannEllipticGreen μ x y := by
  have hnum : 0 <
      Real.cosh (Real.sqrt μ * min x y) *
        Real.cosh (Real.sqrt μ * (1 - max x y)) := by
    exact mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  exact div_pos hnum (neumannEllipticGreen_denom_pos hμ)

/-- Nonnegativity corollary of strict positivity. -/
theorem neumannEllipticGreen_nonneg {μ x y : ℝ}
    (hμ : 0 < μ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ neumannEllipticGreen μ x y :=
  (neumannEllipticGreen_pos hμ hx0 hx1 hy0 hy1).le

/-- The classical `x`-derivative of the two smooth pieces of the Green kernel,
with the endpoint value fixed to zero for the Neumann trace.  At `x = y` the
physical kernel has the usual derivative jump. -/
def neumannEllipticGreenDx (μ : ℝ) (x y : ℝ) : ℝ :=
  if x = 0 ∨ x = 1 then
    0
  else if x < y then
    Real.sinh (Real.sqrt μ * x) *
      Real.cosh (Real.sqrt μ * (1 - y)) /
        Real.sinh (Real.sqrt μ)
  else
    - Real.cosh (Real.sqrt μ * y) *
      Real.sinh (Real.sqrt μ * (1 - x)) /
        Real.sinh (Real.sqrt μ)

/-- Neumann boundary trace at the left endpoint, for the packaged derivative
piece. -/
@[simp] theorem neumannEllipticGreenDx_zero_left (μ y : ℝ) :
    neumannEllipticGreenDx μ 0 y = 0 := by
  simp [neumannEllipticGreenDx]

/-- Neumann boundary trace at the right endpoint, for the packaged derivative
piece. -/
@[simp] theorem neumannEllipticGreenDx_zero_right (μ y : ℝ) :
    neumannEllipticGreenDx μ 1 y = 0 := by
  simp [neumannEllipticGreenDx]

/-- Elementary antiderivative for `cosh (α y)`. -/
lemma integral_cosh_mul {α a b : ℝ} (hα : α ≠ 0) :
    ∫ y in a..b, Real.cosh (α * y) =
      Real.sinh (α * b) / α - Real.sinh (α * a) / α := by
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun z : ℝ => Real.sinh (α * z) / α)
        (Real.cosh (α * y)) y := by
    intro y _hy
    have hlin : HasDerivAt (fun z : ℝ => α * z) α y := by
      simpa using ((hasDerivAt_id y).const_mul α)
    convert hlin.sinh.div_const α using 1
    field_simp [hα]
  have hint : IntervalIntegrable (fun y : ℝ => Real.cosh (α * y))
      MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun y : ℝ => Real.cosh (α * y)).intervalIntegrable a b
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Elementary antiderivative for `cosh (α (1-y))`. -/
lemma integral_cosh_one_sub {α a b : ℝ} (hα : α ≠ 0) :
    ∫ y in a..b, Real.cosh (α * (1 - y)) =
      -(Real.sinh (α * (1 - b)) / α) -
        (-(Real.sinh (α * (1 - a)) / α)) := by
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun z : ℝ => -(Real.sinh (α * (1 - z)) / α))
        (Real.cosh (α * (1 - y))) y := by
    intro y _hy
    have hsub : HasDerivAt (fun z : ℝ => (1 : ℝ) - z) (-1) y := by
      simpa using (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)
    have hlin : HasDerivAt (fun z : ℝ => α * (1 - z)) (-α) y := by
      simpa using hsub.const_mul α
    convert hlin.sinh.div_const α |>.neg using 1
    field_simp [hα]
  have hint : IntervalIntegrable (fun y : ℝ => Real.cosh (α * (1 - y)))
      MeasureTheory.volume a b :=
    (by fun_prop : Continuous fun y : ℝ => Real.cosh (α * (1 - y))).intervalIntegrable a b
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

lemma neumannEllipticGreen_continuous_y (μ x : ℝ) :
    Continuous fun y : ℝ => neumannEllipticGreen μ x y := by
  unfold neumannEllipticGreen
  fun_prop

/-- Exact mass of the positive Neumann elliptic Green kernel. -/
theorem neumannEllipticGreen_integral_eq {μ x : ℝ}
    (hμ : 0 < μ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ y in (0 : ℝ)..1, neumannEllipticGreen μ x y = 1 / μ := by
  let α := Real.sqrt μ
  have hαpos : 0 < α := by simpa [α] using Real.sqrt_pos_of_pos hμ
  have hαne : α ≠ 0 := ne_of_gt hαpos
  have hαsq : α ^ 2 = μ := by simpa [α] using Real.sq_sqrt hμ.le
  have hcont := neumannEllipticGreen_continuous_y μ x
  have h0x := hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 x
  have hx1i := hcont.intervalIntegrable (μ := MeasureTheory.volume) x 1
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hx1i
  have hleft : ∫ y in (0 : ℝ)..x, neumannEllipticGreen μ x y =
      (Real.sinh (α * x) / α - Real.sinh (α * 0) / α) *
        (Real.cosh (α * (1 - x)) / (α * Real.sinh α)) := by
    calc
      ∫ y in (0 : ℝ)..x, neumannEllipticGreen μ x y
          = ∫ y in (0 : ℝ)..x, Real.cosh (α * y) *
              (Real.cosh (α * (1 - x)) / (α * Real.sinh α)) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hyI : y ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx0] using hy
            simp only [neumannEllipticGreen, α]
            rw [min_eq_right hyI.2, max_eq_left hyI.2]
            ring_nf
      _ = (∫ y in (0 : ℝ)..x, Real.cosh (α * y)) *
              (Real.cosh (α * (1 - x)) / (α * Real.sinh α)) := by
            rw [← intervalIntegral.integral_mul_const]
      _ = _ := by rw [integral_cosh_mul hαne]
  have hright : ∫ y in x..(1 : ℝ), neumannEllipticGreen μ x y =
      (Real.sinh (α * (1 - x)) / α - Real.sinh (α * (1 - 1)) / α) *
        (Real.cosh (α * x) / (α * Real.sinh α)) := by
    calc
      ∫ y in x..(1 : ℝ), neumannEllipticGreen μ x y
          = ∫ y in x..(1 : ℝ), Real.cosh (α * (1 - y)) *
              (Real.cosh (α * x) / (α * Real.sinh α)) := by
            apply intervalIntegral.integral_congr
            intro y hy
            have hyI : y ∈ Icc x (1 : ℝ) := by simpa [uIcc_of_le hx1] using hy
            simp only [neumannEllipticGreen, α]
            rw [min_eq_left hyI.1, max_eq_right hyI.1]
            ring_nf
      _ = (∫ y in x..(1 : ℝ), Real.cosh (α * (1 - y))) *
              (Real.cosh (α * x) / (α * Real.sinh α)) := by
            rw [← intervalIntegral.integral_mul_const]
      _ = _ := by
            rw [integral_cosh_one_sub hαne]
            ring
  rw [← hadd, hleft, hright]
  have hsinhadd : Real.sinh (α * x) * Real.cosh (α * (1 - x)) +
      Real.sinh (α * (1 - x)) * Real.cosh (α * x) = Real.sinh α := by
    have := Real.sinh_add (α * x) (α * (1 - x))
    rw [show α * x + α * (1 - x) = α by ring] at this
    linarith
  have hsinhne : Real.sinh α ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hαpos)
  have hsinhpos : 0 < Real.sinh α := Real.sinh_pos_iff.mpr hαpos
  simp only [mul_zero, sub_self, Real.sinh_zero, zero_div, sub_zero]
  field_simp [hαne, hsinhne, hαsq]
  nlinarith [hsinhadd, hαsq, hsinhpos]

/-- L¹ value bound: the Green kernel has mass `1/μ`. -/
theorem neumannEllipticGreen_l1_value_le {μ : ℝ} (hμ : 0 < μ) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      ∫ y in (0 : ℝ)..1, |neumannEllipticGreen μ x y| ≤ 1 / μ := by
  intro x hx
  have habs : ∫ y in (0 : ℝ)..1, |neumannEllipticGreen μ x y| =
      ∫ y in (0 : ℝ)..1, neumannEllipticGreen μ x y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hyI : y ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
    exact abs_of_pos (neumannEllipticGreen_pos hμ hx.1 hx.2 hyI.1 hyI.2)
  rw [habs, neumannEllipticGreen_integral_eq hμ hx.1 hx.2]

#print axioms neumannEllipticGreen_pos
#print axioms neumannEllipticGreen_l1_value_le

end ShenWork.PDE
