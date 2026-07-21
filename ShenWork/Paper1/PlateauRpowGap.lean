import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Power-gap control on a positive plateau

This file records a pointwise real-analysis inequality.  It uses only the
static bounds `a ≤ u ≤ b`; it does not assert plateau invariance in time or
use any PDE solution object.
-/

open scoped Topology

noncomputable section

namespace ShenWork.Paper1

/-- On a positive plateau containing `1`, the real power map has Lipschitz
constant `γ * b ^ (γ - 1)`.  This is a static scalar inequality; establishing
`a ≤ u(t) ≤ b` for a PDE solution remains a separate PDE-coupled task. -/
theorem plateau_rpow_sub_one_le
    {γ a u b : ℝ}
    (hγ : 1 ≤ γ) (ha : 0 < a) (hau : a ≤ u) (hub : u ≤ b)
    (ha1 : a ≤ 1) (h1b : 1 ≤ b) :
    |u ^ γ - 1| ≤ γ * b ^ (γ - 1) * |u - 1| := by
  set L : ℝ := γ * b ^ (γ - 1) with hL
  have hbound : ∀ x ∈ Set.Icc a b, ‖γ * x ^ (γ - 1)‖ ≤ L := by
    intro x hx
    have hx_nonneg : 0 ≤ x := by linarith [hx.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg hx_nonneg _))]
    have hxpow : x ^ (γ - 1) ≤ b ^ (γ - 1) :=
      Real.rpow_le_rpow hx_nonneg hx.2 (by linarith)
    rw [hL]
    exact mul_le_mul_of_nonneg_left hxpow (by linarith)
  have hderiv : ∀ x ∈ Set.Icc a b,
      HasDerivWithinAt (fun y : ℝ ↦ y ^ γ) (γ * x ^ (γ - 1))
        (Set.Icc a b) x := by
    intro x _
    exact (Real.hasDerivAt_rpow_const (Or.inr hγ)).hasDerivWithinAt
  have hmvt := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (show (1 : ℝ) ∈ Set.Icc a b by exact ⟨ha1, h1b⟩)
    (show u ∈ Set.Icc a b by exact ⟨hau, hub⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.one_rpow] at hmvt
  exact hmvt

section AxiomAudit

#print axioms plateau_rpow_sub_one_le

end AxiomAudit

end ShenWork.Paper1
