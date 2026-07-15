import ShenWork.Paper1.WholeLineWeightedRegularitySelfVolterra

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Bounded-profile Henry closure

For a fixed nonzero spatial difference step, the cap-weighted quotient history
has a crude uniform scalar bound, even though its cap-`L²` norm need not be
continuous in time.  This file converts that crude bound into precisely the
`BddAbove` premise of the single-history Henry theorem and exports the
constant-plus-gradient Volterra wrapper without a continuity hypothesis.
-/

/-- A uniform upper bound for a history gives the bounded-above scaled profile
needed by the Henry closure.  No continuity or measurability is used here. -/
theorem bddAbove_sqrt_mul_image_Ioc_of_uniform_upper_bound
    {H K : ℝ} {x : ℝ → ℝ}
    (hK : 0 ≤ K)
    (hx : ∀ r ∈ Set.Ioc (0 : ℝ) H, x r ≤ K) :
    BddAbove
      ((fun r : ℝ => Real.sqrt r * x r) '' Set.Ioc (0 : ℝ) H) := by
  refine ⟨Real.sqrt H * K, ?_⟩
  rintro z ⟨r, hr, rfl⟩
  calc
    Real.sqrt r * x r ≤ Real.sqrt r * K :=
      mul_le_mul_of_nonneg_left (hx r hr) (Real.sqrt_nonneg r)
    _ ≤ Real.sqrt H * K :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr.2) hK

/-- Fixed-step form of
`bddAbove_sqrt_mul_image_Ioc_of_uniform_upper_bound`: a quotient ceiling with
an explicit inverse-step loss is enough for the preliminary boundedness
premise.  The later Henry estimate may remove that loss. -/
theorem bddAbove_sqrt_mul_image_Ioc_of_fixed_step_bound
    {H K₀ K₁ δ : ℝ} {x : ℝ → ℝ}
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hδ : δ ≠ 0)
    (hx : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      x r ≤ K₀ + |δ⁻¹| * K₁) :
    BddAbove
      ((fun r : ℝ => Real.sqrt r * x r) '' Set.Ioc (0 : ℝ) H) := by
  have hδabs : 0 ≤ |δ⁻¹| := (abs_pos.mpr (inv_ne_zero hδ)).le
  apply bddAbove_sqrt_mul_image_Ioc_of_uniform_upper_bound
    (add_nonneg hK₀ (mul_nonneg hδabs hK₁))
  intro r hr
  exact hx r hr

private theorem rpow_three_halves_eq_sqrt_mul_bdd
    {t : ℝ} (ht : 0 < t) :
    t ^ (3 / 2 : ℝ) = Real.sqrt t * t := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.rpow_add ht, Real.sqrt_eq_rpow]
  simp

/-- The constant-plus-gradient Volterra profile bound with the native
bounded-above hypothesis.  This is the PDE-facing Henry wrapper when only a
fixed-step crude bound is available; it deliberately assumes no cap-`L²`
time continuity. -/
theorem volterra_const_invSqrt_profile_bound_of_bddAbove
    {H A0 A1 F C0 C1 : ℝ} {x : ℝ → ℝ}
    (hH : 0 < H)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) H, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      x r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hsmall : 2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1)
    (hBdd : BddAbove
      ((fun r : ℝ => Real.sqrt r * x r) '' Set.Ioc (0 : ℝ) H)) :
    ∀ r ∈ Set.Ioc (0 : ℝ) H,
      Real.sqrt r * x r ≤
        (A0 + A1 * Real.sqrt H +
          F * (C0 * H ^ (3 / 2 : ℝ) + 2 * C1 * H)) /
        (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  let y : ℝ → ℝ := fun r => if r = 0 then 0 else x r
  let A : ℝ := A0 + A1 * Real.sqrt H +
    F * (C0 * H ^ (3 / 2 : ℝ) + 2 * C1 * H)
  have hA : 0 ≤ A := by
    have hHpow : 0 ≤ H ^ (3 / 2 : ℝ) := Real.rpow_nonneg hH.le _
    dsimp only [A]
    positivity
  have hq : 2 * C0 * H + C1 * Real.pi * Real.sqrt H < 1 := by
    nlinarith [hsmall]
  have hy_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) H, 0 ≤ y r := by
    intro r hr
    simp only [y, if_neg (ne_of_gt hr.1)]
    exact hx_nonneg r hr
  have hy_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable y volume 0 r := by
    intro r hr
    refine IntervalIntegrable.congr ?_ (hx_int r hr)
    intro s hs
    rw [Set.uIoc_of_le hr.1.le] at hs
    simp [y, ne_of_gt hs.1]
  have hyconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * y s) volume 0 r := by
    intro r hr
    refine IntervalIntegrable.congr ?_ (hconv_int r hr)
    intro s hs
    rw [Set.uIoc_of_le hr.1.le] at hs
    simp [y, ne_of_gt hs.1]
  have hint_eq : ∀ r ∈ Set.Ioc (0 : ℝ) H,
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
  have hyineq : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      y r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * y s := by
    intro r hr
    rw [show y r = x r by simp [y, ne_of_gt hr.1], hint_eq r hr]
    exact hineq r hr
  have hyself : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      y r ≤ A * r ^ (-(1 / 2 : ℝ)) +
        C0 * (∫ s in (0 : ℝ)..r, y s) +
        C1 * (∫ s in (0 : ℝ)..r,
          (r - s) ^ (-(1 / 2 : ℝ)) * y s) := by
    intro r hr
    have hrpos : 0 < r := hr.1
    have hrH : r ≤ H := hr.2
    have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hsqrt_le : Real.sqrt r ≤ Real.sqrt H := Real.sqrt_le_sqrt hrH
    have hsqrt_rpow : Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.rpow_neg hrpos.le, ← Real.sqrt_eq_rpow]
      exact mul_inv_cancel₀ (ne_of_gt hsqrt_pos)
    have hsqrt_sq : Real.sqrt r * Real.sqrt r = r :=
      Real.mul_self_sqrt hrpos.le
    have hforce_scaled :
        Real.sqrt r *
            (A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
              F * (C0 * r + 2 * C1 * Real.sqrt r)) ≤ A := by
      have hraw :
          A0 + A1 * Real.sqrt r +
              F * (C0 * (Real.sqrt r * r) + 2 * C1 * r) ≤
            A0 + A1 * Real.sqrt H +
              F * (C0 * (Real.sqrt H * H) + 2 * C1 * H) := by
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
        _ ≤ A0 + A1 * Real.sqrt H +
              F * (C0 * (Real.sqrt H * H) + 2 * C1 * H) := hraw
        _ = A := by
          dsimp only [A]
          rw [← rpow_three_halves_eq_sqrt_mul_bdd hH]
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
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * y s) =
          C0 * (∫ s in (0 : ℝ)..r, y s) +
          C1 * (∫ s in (0 : ℝ)..r,
            (r - s) ^ (-(1 / 2 : ℝ)) * y s) := by
      have h0 := (hy_int r hr).const_mul C0
      have h1 := (hyconv_int r hr).const_mul C1
      rw [show (fun s : ℝ =>
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * y s) =
          fun s : ℝ => C0 * y s +
            C1 * ((r - s) ^ (-(1 / 2 : ℝ)) * y s) by
              funext s; ring,
        intervalIntegral.integral_add h0 h1,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    calc
      y r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
          F * (C0 * r + 2 * C1 * Real.sqrt r) +
          ∫ s in (0 : ℝ)..r,
            (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * y s := hyineq r hr
      _ ≤ A * r ^ (-(1 / 2 : ℝ)) +
          C0 * (∫ s in (0 : ℝ)..r, y s) +
          C1 * (∫ s in (0 : ℝ)..r,
            (r - s) ^ (-(1 / 2 : ℝ)) * y s) := by
        rw [hsplit]
        linarith
  have hyBdd : BddAbove
      ((fun r : ℝ => Real.sqrt r * y r) '' Set.Ioc (0 : ℝ) H) := by
    have himage :
        ((fun r : ℝ => Real.sqrt r * y r) '' Set.Ioc (0 : ℝ) H) =
          ((fun r : ℝ => Real.sqrt r * x r) '' Set.Ioc (0 : ℝ) H) := by
      apply Set.image_congr
      intro r hr
      simp [y, ne_of_gt hr.1]
    rw [himage]
    exact hBdd
  have hybound := henry_invSqrt_bound_of_self_volterra
    (T := H) (A := A) (C0 := C0) (C1 := C1) (r := y)
    hH hA hC0 hC1 hq (by simp [y]) hy_nonneg hy_int hyconv_int hyself hyBdd
  intro r hr
  have hrpos : 0 < r := hr.1
  have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  have hsqrt_rpow : Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.rpow_neg hrpos.le, ← Real.sqrt_eq_rpow]
    exact mul_inv_cancel₀ (ne_of_gt hsqrt_pos)
  have hscaled := mul_le_mul_of_nonneg_left (hybound r hr) hsqrt_pos.le
  calc
    Real.sqrt r * x r = Real.sqrt r * y r := by
      simp [y, ne_of_gt hr.1]
    _ ≤ Real.sqrt r *
          (A / (1 - (2 * C0 * H + C1 * Real.pi * Real.sqrt H)) *
            r ^ (-(1 / 2 : ℝ))) := hscaled
    _ = A / (1 - (2 * C0 * H + C1 * Real.pi * Real.sqrt H)) := by
      rw [show Real.sqrt r *
          (A / (1 - (2 * C0 * H + C1 * Real.pi * Real.sqrt H)) *
            r ^ (-(1 / 2 : ℝ))) =
          (A / (1 - (2 * C0 * H + C1 * Real.pi * Real.sqrt H))) *
            (Real.sqrt r * r ^ (-(1 / 2 : ℝ))) by ring,
        hsqrt_rpow, mul_one]
    _ = (A0 + A1 * Real.sqrt H +
          F * (C0 * H ^ (3 / 2 : ℝ) + 2 * C1 * H)) /
        (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
      dsimp only [A]
      congr 2
      ring

/-- Direct fixed-step wrapper: the crude inverse-step ceiling supplies the
bounded-above premise, while the conclusion is the step-independent Henry
bound determined by the Volterra coefficients. -/
theorem volterra_const_invSqrt_profile_bound_of_fixed_step_bound
    {H A0 A1 F C0 C1 K₀ K₁ δ : ℝ} {x : ℝ → ℝ}
    (hH : 0 < H)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hδ : δ ≠ 0)
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) H, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      x r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hsmall : 2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1)
    (hcrude : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      x r ≤ K₀ + |δ⁻¹| * K₁) :
    ∀ r ∈ Set.Ioc (0 : ℝ) H,
      Real.sqrt r * x r ≤
        (A0 + A1 * Real.sqrt H +
          F * (C0 * H ^ (3 / 2 : ℝ) + 2 * C1 * H)) /
        (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  apply volterra_const_invSqrt_profile_bound_of_bddAbove hH hA0 hA1 hF
    hC0 hC1 hx_nonneg hx_int hconv_int hineq hsmall
  exact bddAbove_sqrt_mul_image_Ioc_of_fixed_step_bound hK₀ hK₁ hδ
    hcrude

section AxiomAudit

#print axioms bddAbove_sqrt_mul_image_Ioc_of_uniform_upper_bound
#print axioms bddAbove_sqrt_mul_image_Ioc_of_fixed_step_bound
#print axioms volterra_const_invSqrt_profile_bound_of_bddAbove
#print axioms volterra_const_invSqrt_profile_bound_of_fixed_step_bound

end AxiomAudit

end ShenWork.Paper1
