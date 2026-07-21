import ShenWork.Paper1.PlateauRpowGap
import ShenWork.Paper1.WholeLineResolverSharpGradient

/-!
# Resolver gradient control from a plateau power gap

This file combines the sharp scalar resolver estimate with the pointwise
power-gap bound.  Its hypotheses concern real functions on one fixed interval;
no time-dependent PDE solution or plateau-invariance assertion is involved.
-/

open MeasureTheory intervalIntegral
open Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper1

/-- If `-v₂ + v = u ^ γ - 1` on an interval and `u` lies in the positive
plateau `[a,b]`, then the sharp resolver estimate transfers the squared
displacement bound to the derivative of `v`.  The source-square and
displacement-square integrability assumptions are stated explicitly.  This is
a static real-analysis bridge; proving that a PDE trajectory stays in the
plateau remains a separate PDE-coupled task. -/
theorem resolver_deriv_sq_le_plateau
    {ℓ r : ℝ} {u v v₁ v₂ : ℝ → ℝ} {γ a b : ℝ}
    (hℓr : ℓ ≤ r)
    (hγ : 1 ≤ γ) (ha : 0 < a) (ha1 : a ≤ 1) (h1b : 1 ≤ b)
    (hplateau : ∀ x ∈ Set.uIcc ℓ r, a ≤ u x ∧ u x ≤ b)
    (hv : ∀ x ∈ Set.uIcc ℓ r, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc ℓ r, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume ℓ r)
    (hsource_sq_int :
      IntervalIntegrable (fun x ↦ (u x ^ γ - 1) ^ 2) volume ℓ r)
    (hdisplacement_sq_int :
      IntervalIntegrable (fun x ↦ (u x - 1) ^ 2) volume ℓ r)
    (hpde : ∀ x ∈ Set.uIcc ℓ r, -v₂ x + v x = u x ^ γ - 1)
    (hboundary : v₁ r * v r - v₁ ℓ * v ℓ ≤ 0) :
    (∫ x in ℓ..r, (v₁ x) ^ 2) ≤
      (γ ^ 2 * b ^ (2 * (γ - 1)) / 4) *
        ∫ x in ℓ..r, (u x - 1) ^ 2 := by
  have hγ0 : 0 ≤ γ := le_trans zero_le_one hγ
  have hb0 : 0 ≤ b := le_trans zero_le_one h1b
  have hγsub : 0 ≤ γ - 1 := sub_nonneg.mpr hγ
  have hbpow0 : 0 ≤ b ^ (γ - 1) := Real.rpow_nonneg hb0 _
  have hbpow_sq : (b ^ (γ - 1)) ^ 2 = b ^ (2 * (γ - 1)) := by
    rw [← Real.rpow_mul_natCast hb0 (γ - 1) 2]
    congr 1
    ring
  have hpoint : ∀ x ∈ Set.uIcc ℓ r,
      (u x ^ γ - 1) ^ 2 ≤
        γ ^ 2 * b ^ (2 * (γ - 1)) * (u x - 1) ^ 2 := by
    intro x hx
    have hgap := plateau_rpow_sub_one_le hγ ha
      (hplateau x hx).1 (hplateau x hx).2 ha1 h1b
    calc
      (u x ^ γ - 1) ^ 2 = |u x ^ γ - 1| ^ 2 := (sq_abs _).symm
      _ ≤ (γ * b ^ (γ - 1) * |u x - 1|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (mul_nonneg hγ0 hbpow0) (abs_nonneg _))).2 hgap
      _ = γ ^ 2 * b ^ (2 * (γ - 1)) * (u x - 1) ^ 2 := by
        rw [mul_pow, mul_pow, hbpow_sq, sq_abs]
  have hsource_le :
      (∫ x in ℓ..r, (u x ^ γ - 1) ^ 2) ≤
        γ ^ 2 * b ^ (2 * (γ - 1)) *
          ∫ x in ℓ..r, (u x - 1) ^ 2 := by
    calc
      (∫ x in ℓ..r, (u x ^ γ - 1) ^ 2) ≤
          ∫ x in ℓ..r,
            γ ^ 2 * b ^ (2 * (γ - 1)) * (u x - 1) ^ 2 :=
        intervalIntegral.integral_mono_on hℓr hsource_sq_int
          (hdisplacement_sq_int.const_mul
            (γ ^ 2 * b ^ (2 * (γ - 1))))
          (fun x hx ↦ hpoint x (by simpa [Set.uIcc_of_le hℓr] using hx))
      _ = γ ^ 2 * b ^ (2 * (γ - 1)) *
          ∫ x in ℓ..r, (u x - 1) ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
  have hsharp := resolver_deriv_sq_le_quarter_source_sq
    (g := fun x ↦ u x ^ γ - 1) hℓr hv hv₁ hv₂_int hsource_sq_int hpde hboundary
  calc
    (∫ x in ℓ..r, (v₁ x) ^ 2) ≤
        (1 / 4 : ℝ) * ∫ x in ℓ..r, (u x ^ γ - 1) ^ 2 := hsharp
    _ ≤ (1 / 4 : ℝ) *
        (γ ^ 2 * b ^ (2 * (γ - 1)) *
          ∫ x in ℓ..r, (u x - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hsource_le (by norm_num)
    _ = (γ ^ 2 * b ^ (2 * (γ - 1)) / 4) *
        ∫ x in ℓ..r, (u x - 1) ^ 2 := by ring

section AxiomAudit

#print axioms resolver_deriv_sq_le_plateau

end AxiomAudit

end ShenWork.Paper1
