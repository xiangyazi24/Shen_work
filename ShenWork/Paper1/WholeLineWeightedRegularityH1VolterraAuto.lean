import ShenWork.Paper1.WholeLineWeightedRegularitySelfVolterraBdd

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Automatic short-window Henry closure

The native singular Volterra theorem uses the sharp profile mass
`2 C0 H + pi C1 sqrt H`.  This file chooses a positive window on which that
mass is strictly below one and exposes the form used by the raw spatial
difference quotient: one homogeneous constant multiplying
`1 + t^(-1/2)`.
-/

/-- The sharp Henry profile mass is strictly smaller than one on some
positive subwindow of every prescribed positive horizon. -/
theorem exists_pos_le_henryProfileMass_lt_one
    {H₀ C0 C1 : ℝ}
    (hH₀ : 0 < H₀) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    ∃ H : ℝ, 0 < H ∧ H ≤ H₀ ∧
      2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1 := by
  let mass : ℝ → ℝ := fun H =>
    2 * C0 * H + Real.pi * C1 * Real.sqrt H
  have hcont : ContinuousAt mass 0 := by
    dsimp only [mass]
    fun_prop
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨d, hd, hclose⟩ := hcont 1 (by norm_num)
  let rho : ℝ := min d H₀
  let H : ℝ := rho / 2
  have hrho : 0 < rho := lt_min hd hH₀
  have hH : 0 < H := by
    dsimp only [H]
    linarith
  have hHH₀ : H ≤ H₀ := by
    have hrhoH₀ : rho ≤ H₀ := min_le_right _ _
    dsimp only [H]
    linarith
  have hHd : dist H 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hH]
    have hrhod : rho ≤ d := min_le_left _ _
    dsimp only [H]
    linarith
  have hmass_close := hclose hHd
  have hmass_zero : mass 0 = 0 := by
    simp [mass]
  have hmass_nonneg : 0 ≤ mass H := by
    dsimp only [mass]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC0) hH.le)
      (mul_nonneg
        (mul_nonneg Real.pi_nonneg hC1) (Real.sqrt_nonneg H))
  rw [hmass_zero, Real.dist_eq, sub_zero,
    abs_of_nonneg hmass_nonneg] at hmass_close
  exact ⟨H, hH, hHH₀, by simpa only [mass] using hmass_close⟩

/-- Fixed-window adapter for the PDE inequality
`x(t) <= A (1 + t^(-1/2)) + K*x`.  A crude fixed-step quotient ceiling is
used only to discharge boundedness of the scaled profile; the resulting
Henry bound is independent of that ceiling and of the difference step. -/
theorem volterra_one_add_invSqrt_profile_bound_of_fixed_step_bound
    {H A C0 C1 K₀ K₁ delta : ℝ} {x : ℝ → ℝ}
    (hH : 0 < H) (hA : 0 ≤ A)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hdelta : delta ≠ 0)
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) H, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      x r ≤ A * (1 + r ^ (-(1 / 2 : ℝ))) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hsmall : 2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1)
    (hcrude : ∀ r ∈ Set.Ioc (0 : ℝ) H,
      x r ≤ K₀ + |delta⁻¹| * K₁) :
    ∀ r ∈ Set.Ioc (0 : ℝ) H,
      Real.sqrt r * x r ≤
        A * (1 + Real.sqrt H) /
          (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  have hnative :=
    volterra_const_invSqrt_profile_bound_of_fixed_step_bound
      (H := H) (A0 := A) (A1 := A) (F := 0)
      (C0 := C0) (C1 := C1) (K₀ := K₀) (K₁ := K₁)
      (δ := delta) (x := x)
      hH hA hA (by norm_num) hC0 hC1 hK₀ hK₁ hdelta
      hx_nonneg hx_int hconv_int
      (fun r hr => by
        calc
          x r ≤ A * (1 + r ^ (-(1 / 2 : ℝ))) +
              ∫ s in (0 : ℝ)..r,
                (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s :=
            hineq r hr
          _ = A * r ^ (-(1 / 2 : ℝ)) + A +
              0 * (C0 * r + 2 * C1 * Real.sqrt r) +
                ∫ s in (0 : ℝ)..r,
                  (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s := by
            ring)
      hsmall hcrude
  intro r hr
  have hrbound := hnative r hr
  calc
    Real.sqrt r * x r ≤
        (A + A * Real.sqrt H + 0) /
          (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
      simpa only [zero_mul] using hrbound
    _ = A * (1 + Real.sqrt H) /
          (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
      congr 1
      ring

/-- Complete short-window form.  All analytic hypotheses may be supplied on
an arbitrary positive ambient horizon; the theorem restricts them to a
constructed window where the singular Henry profile closes. -/
theorem exists_shortWindow_volterra_one_add_invSqrt_profile_bound_of_fixed_step
    {H₀ A C0 C1 K₀ K₁ delta : ℝ} {x : ℝ → ℝ}
    (hH₀ : 0 < H₀) (hA : 0 ≤ A)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hdelta : delta ≠ 0)
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) H₀, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      x r ≤ A * (1 + r ^ (-(1 / 2 : ℝ))) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hcrude : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      x r ≤ K₀ + |delta⁻¹| * K₁) :
    ∃ H : ℝ, 0 < H ∧ H ≤ H₀ ∧
      2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1 ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) H,
        Real.sqrt r * x r ≤
          A * (1 + Real.sqrt H) /
            (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  rcases exists_pos_le_henryProfileMass_lt_one hH₀ hC0 hC1 with
    ⟨H, hH, hHH₀, hsmall⟩
  refine ⟨H, hH, hHH₀, hsmall, ?_⟩
  apply volterra_one_add_invSqrt_profile_bound_of_fixed_step_bound
    hH hA hC0 hC1 hK₀ hK₁ hdelta
  · intro r hr
    exact hx_nonneg r ⟨hr.1, hr.2.trans hHH₀⟩
  · intro r hr
    exact hx_int r ⟨hr.1, hr.2.trans hHH₀⟩
  · intro r hr
    exact hconv_int r ⟨hr.1, hr.2.trans hHH₀⟩
  · intro r hr
    exact hineq r ⟨hr.1, hr.2.trans hHH₀⟩
  · exact hsmall
  · intro r hr
    exact hcrude r ⟨hr.1, hr.2.trans hHH₀⟩

end ShenWork.Paper1

#print axioms ShenWork.Paper1.exists_pos_le_henryProfileMass_lt_one
#print axioms
  ShenWork.Paper1.volterra_one_add_invSqrt_profile_bound_of_fixed_step_bound
#print axioms
  ShenWork.Paper1.exists_shortWindow_volterra_one_add_invSqrt_profile_bound_of_fixed_step
