import ShenWork.Paper1.WholeLineWeightedRegularitySelfVolterra

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

private theorem rpow_three_halves_eq_sqrt_mul {t : ℝ} (ht : 0 < t) :
    t ^ (3 / 2 : ℝ) = Real.sqrt t * t := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add ht, Real.sqrt_eq_rpow]
  simp

/-- Adapter from the constant-plus-gradient mild kernel to the native
single-history Henry closure. -/
theorem volterra_const_invSqrt_profile_bound_of_split
    {h A0 A1 F C0 C1 : ℝ} {x : ℝ → ℝ}
    (hh : 0 < h)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hxcont : ContinuousOn (fun r => Real.sqrt r * x r)
      (Set.Icc (0 : ℝ) h))
    (hx_zero : x 0 ≤ 0)
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) h, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      x r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hsmall : 2 * C0 * h + Real.pi * C1 * Real.sqrt h < 1) :
    ∀ r ∈ Set.Ioc (0 : ℝ) h,
      Real.sqrt r * x r ≤
        (A0 + A1 * Real.sqrt h +
          F * (C0 * h ^ (3 / 2 : ℝ) + 2 * C1 * h)) /
        (1 - (2 * C0 * h + Real.pi * C1 * Real.sqrt h)) := by
  let A : ℝ := A0 + A1 * Real.sqrt h +
    F * (C0 * h ^ (3 / 2 : ℝ) + 2 * C1 * h)
  have hA : 0 ≤ A := by
    have hhpow : 0 ≤ h ^ (3 / 2 : ℝ) := Real.rpow_nonneg hh.le _
    dsimp only [A]
    positivity
  have hq : 2 * C0 * h + C1 * Real.pi * Real.sqrt h < 1 := by
    nlinarith [hsmall]
  have hself : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      x r ≤ A * r ^ (-(1 / 2 : ℝ)) +
        C0 * (∫ s in (0 : ℝ)..r, x s) +
        C1 * (∫ s in (0 : ℝ)..r,
          (r - s) ^ (-(1 / 2 : ℝ)) * x s) := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hrh : r ≤ h := hr.2
    have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hsqrt_le : Real.sqrt r ≤ Real.sqrt h := Real.sqrt_le_sqrt hrh
    have hsqrt_rpow : Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.rpow_neg hrpos.le, ← Real.sqrt_eq_rpow]
      exact mul_inv_cancel₀ (ne_of_gt hsqrt_pos)
    have hsqrt_sq : Real.sqrt r * Real.sqrt r = r :=
      Real.mul_self_sqrt hrpos.le
    have hmul : Real.sqrt r * r ≤ Real.sqrt h * h :=
      mul_le_mul hsqrt_le hrh hrpos.le (Real.sqrt_nonneg h)
    have hforce_scaled :
        Real.sqrt r *
            (A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
              F * (C0 * r + 2 * C1 * Real.sqrt r)) ≤ A := by
      have hraw :
          A0 + A1 * Real.sqrt r +
              F * (C0 * (Real.sqrt r * r) + 2 * C1 * r) ≤
            A0 + A1 * Real.sqrt h +
              F * (C0 * (Real.sqrt h * h) + 2 * C1 * h) := by
        gcongr
      calc
        Real.sqrt r *
            (A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
              F * (C0 * r + 2 * C1 * Real.sqrt r)) =
            A0 + A1 * Real.sqrt r +
              F * (C0 * (Real.sqrt r * r) + 2 * C1 * r) := by
                calc
                  _ = A0 * (Real.sqrt r * r ^ (-(1 / 2 : ℝ))) +
                      A1 * Real.sqrt r +
                      F * (C0 * (Real.sqrt r * r) +
                        2 * C1 * (Real.sqrt r * Real.sqrt r)) := by ring
                  _ = _ := by rw [hsqrt_rpow, hsqrt_sq]; ring
        _ ≤ A0 + A1 * Real.sqrt h +
              F * (C0 * (Real.sqrt h * h) + 2 * C1 * h) := hraw
        _ = A := by
          dsimp only [A]
          rw [← rpow_three_halves_eq_sqrt_mul hh]
    have hforce :
        A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
            F * (C0 * r + 2 * C1 * Real.sqrt r) ≤
          A * r ^ (-(1 / 2 : ℝ)) := by
      apply le_of_mul_le_mul_left (a := Real.sqrt r) ?_ hsqrt_pos
      calc
        Real.sqrt r *
            (A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
              F * (C0 * r + 2 * C1 * Real.sqrt r)) ≤ A := hforce_scaled
        _ = Real.sqrt r * (A * r ^ (-(1 / 2 : ℝ))) := by
          calc
            A = A * (Real.sqrt r * r ^ (-(1 / 2 : ℝ))) := by
              rw [hsqrt_rpow, mul_one]
            _ = _ := by ring
    have hsplit :
        (∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s) =
          C0 * (∫ s in (0 : ℝ)..r, x s) +
          C1 * (∫ s in (0 : ℝ)..r,
            (r - s) ^ (-(1 / 2 : ℝ)) * x s) := by
      have h0 := (hx_int r hr).const_mul C0
      have h1 := (hconv_int r hr).const_mul C1
      rw [show (fun s : ℝ =>
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s) =
          fun s : ℝ => C0 * x s +
            C1 * ((r - s) ^ (-(1 / 2 : ℝ)) * x s) by
              funext s; ring,
        intervalIntegral.integral_add h0 h1,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    calc
      x r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
          F * (C0 * r + 2 * C1 * Real.sqrt r) +
          ∫ s in (0 : ℝ)..r,
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s := hineq r hr
      _ ≤ A * r ^ (-(1 / 2 : ℝ)) +
          C0 * (∫ s in (0 : ℝ)..r, x s) +
          C1 * (∫ s in (0 : ℝ)..r,
            (r - s) ^ (-(1 / 2 : ℝ)) * x s) := by
        rw [hsplit]
        linarith
  have hBddIcc : BddAbove
      ((fun r : ℝ => Real.sqrt r * x r) '' Set.Icc (0 : ℝ) h) :=
    isCompact_Icc.bddAbove_image hxcont
  have hsubset :
      (fun r : ℝ => Real.sqrt r * x r) '' Set.Ioc (0 : ℝ) h ⊆
        (fun r : ℝ => Real.sqrt r * x r) '' Set.Icc (0 : ℝ) h := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, ⟨hr.1.le, hr.2⟩, rfl⟩
  have hBdd : BddAbove
      ((fun r : ℝ => Real.sqrt r * x r) '' Set.Ioc (0 : ℝ) h) :=
    hBddIcc.mono hsubset
  have hbound := henry_invSqrt_bound_of_self_volterra
    (T := h) (A := A) (C0 := C0) (C1 := C1) (r := x)
    hh hA hC0 hC1 hq hx_zero hx_nonneg hx_int hconv_int hself hBdd
  intro r hr
  have hrpos : 0 < r := hr.1
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  have hsqrt_rpow : Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.rpow_neg hrpos.le, ← Real.sqrt_eq_rpow]
    exact mul_inv_cancel₀ (ne_of_gt hsqrt_pos)
  have hscaled := mul_le_mul_of_nonneg_left (hbound r hr) hsqrt_pos.le
  calc
    Real.sqrt r * x r ≤
        Real.sqrt r *
          (A / (1 - (2 * C0 * h + C1 * Real.pi * Real.sqrt h)) *
            r ^ (-(1 / 2 : ℝ))) := hscaled
    _ = A / (1 - (2 * C0 * h + C1 * Real.pi * Real.sqrt h)) := by
      rw [show Real.sqrt r *
          (A / (1 - (2 * C0 * h + C1 * Real.pi * Real.sqrt h)) *
            r ^ (-(1 / 2 : ℝ))) =
          (A / (1 - (2 * C0 * h + C1 * Real.pi * Real.sqrt h))) *
            (Real.sqrt r * r ^ (-(1 / 2 : ℝ))) by ring,
        hsqrt_rpow, mul_one]
    _ = (A0 + A1 * Real.sqrt h +
          F * (C0 * h ^ (3 / 2 : ℝ) + 2 * C1 * h)) /
        (1 - (2 * C0 * h + Real.pi * C1 * Real.sqrt h)) := by
      dsimp only [A]
      congr 2 <;> ring

#print axioms volterra_const_invSqrt_profile_bound_of_split

/-- The PDE-facing form: the history value at the restart endpoint is irrelevant
for interval integrals, so it is reset to zero before applying the native Henry
closure.  Nonnegativity and the two explicit integrability legs are exactly the
properties supplied by a norm-valued weighted history. -/
theorem volterra_const_invSqrt_profile_bound
    {h A0 A1 F C0 C1 : ℝ} {x : ℝ → ℝ}
    (hh : 0 < h)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hxcont : ContinuousOn (fun r => Real.sqrt r * x r)
      (Set.Icc (0 : ℝ) h))
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) h, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      x r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hsmall : 2 * C0 * h + Real.pi * C1 * Real.sqrt h < 1) :
    ∀ r ∈ Set.Ioc (0 : ℝ) h,
      Real.sqrt r * x r ≤
        (A0 + A1 * Real.sqrt h +
          F * (C0 * h ^ (3 / 2 : ℝ) + 2 * C1 * h)) /
        (1 - (2 * C0 * h + Real.pi * C1 * Real.sqrt h)) := by
  let y : ℝ → ℝ := fun r => if r = 0 then 0 else x r
  have hy_scaled :
      (fun r : ℝ => Real.sqrt r * y r) =
        fun r : ℝ => Real.sqrt r * x r := by
    funext r
    by_cases hr : r = 0
    · subst r
      simp [y]
    · simp [y, hr]
  have hycont : ContinuousOn (fun r => Real.sqrt r * y r)
      (Set.Icc (0 : ℝ) h) := by
    rw [hy_scaled]
    exact hxcont
  have hy_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) h, 0 ≤ y r := by
    intro r hr
    simp only [y, if_neg (ne_of_gt hr.1)]
    exact hx_nonneg r hr
  have hy_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      IntervalIntegrable y volume 0 r := by
    intro r hr
    refine IntervalIntegrable.congr ?_ (hx_int r hr)
    intro s hs
    rw [Set.uIoc_of_le hr.1.le] at hs
    simp [y, ne_of_gt hs.1]
  have hyconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * y s) volume 0 r := by
    intro r hr
    refine IntervalIntegrable.congr ?_ (hconv_int r hr)
    intro s hs
    rw [Set.uIoc_of_le hr.1.le] at hs
    simp [y, ne_of_gt hs.1]
  have hint_eq : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      (∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * y s) =
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s := by
    intro r _hr
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with s hs _hmem
    simp [y, hs]
  have hyineq : ∀ r ∈ Set.Ioc (0 : ℝ) h,
      y r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * y s := by
    intro r hr
    rw [show y r = x r by simp [y, ne_of_gt hr.1], hint_eq r hr]
    exact hineq r hr
  have hybound := volterra_const_invSqrt_profile_bound_of_split
    (h := h) (A0 := A0) (A1 := A1) (F := F) (C0 := C0) (C1 := C1)
    (x := y) hh hA0 hA1 hF hC0 hC1 hycont (by simp [y]) hy_nonneg
    hy_int hyconv_int hyineq hsmall
  intro r hr
  simpa [y, ne_of_gt hr.1] using hybound r hr

#print axioms volterra_const_invSqrt_profile_bound

end ShenWork.Paper1
