import ShenWork.Paper1.WholeLineWeightedRegularityH1VolterraAuto

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Automatic short-window closure for the raw-DQ Henry inequality

The PDE estimate keeps the homogeneous inverse-square-root term and the
fixed-profile forcing terms separate.  This wrapper chooses a positive
subwindow on which the native Henry mass is strictly smaller than one and
then invokes the fixed-step closure without weakening that structure.
-/

/-- Automatic short-window form of the native constant-plus-gradient
Volterra inequality.  The returned estimate is independent of the crude
inverse-difference-step ceiling. -/
theorem exists_shortWindow_volterra_const_invSqrt_profile_bound_of_fixed_step
    {H₀ A0 A1 F C0 C1 K₀ K₁ delta : ℝ} {x : ℝ → ℝ}
    (hH₀ : 0 < H₀)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hF : 0 ≤ F)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hdelta : delta ≠ 0)
    (hx_nonneg : ∀ r ∈ Set.Ioc (0 : ℝ) H₀, 0 ≤ x r)
    (hx_int : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      IntervalIntegrable x volume 0 r)
    (hconv_int : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      IntervalIntegrable
        (fun s : ℝ => (r - s) ^ (-(1 / 2 : ℝ)) * x s) volume 0 r)
    (hineq : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      x r ≤ A0 * r ^ (-(1 / 2 : ℝ)) + A1 +
        F * (C0 * r + 2 * C1 * Real.sqrt r) +
        ∫ s in (0 : ℝ)..r,
          (C0 + C1 * (r - s) ^ (-(1 / 2 : ℝ))) * x s)
    (hcrude : ∀ r ∈ Set.Ioc (0 : ℝ) H₀,
      x r ≤ K₀ + |delta⁻¹| * K₁) :
    ∃ H : ℝ, 0 < H ∧ H ≤ H₀ ∧
      2 * C0 * H + Real.pi * C1 * Real.sqrt H < 1 ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) H,
        Real.sqrt r * x r ≤
          (A0 + A1 * Real.sqrt H +
            F * (C0 * H ^ (3 / 2 : ℝ) + 2 * C1 * H)) /
          (1 - (2 * C0 * H + Real.pi * C1 * Real.sqrt H)) := by
  rcases exists_pos_le_henryProfileMass_lt_one hH₀ hC0 hC1 with
    ⟨H, hH, hHH₀, hsmall⟩
  refine ⟨H, hH, hHH₀, hsmall, ?_⟩
  apply volterra_const_invSqrt_profile_bound_of_fixed_step_bound
    hH hA0 hA1 hF hC0 hC1 hK₀ hK₁ hdelta
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

#print axioms
  ShenWork.Paper1.exists_shortWindow_volterra_const_invSqrt_profile_bound_of_fixed_step
