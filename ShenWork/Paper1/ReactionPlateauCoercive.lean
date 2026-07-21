import ShenWork.Paper1.ReactionRelativeNonpos
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Quantitative reaction coercivity on a positive plateau

This file strengthens the sign-only reaction estimate to a pointwise scalar
lower bound under fixed plateau assumptions.  It does not prove that a PDE
solution remains in the plateau.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- On `a ≤ u ≤ b` with `a > 0` and `a ≤ 1`, the reaction product controls
the squared displacement from `1`.  This is a static scalar inequality;
plateau invariance for a time-dependent PDE solution remains PDE-coupled. -/
theorem reaction_plateau_coercive
    (u α a b : ℝ) (hα : 1 ≤ α) (ha : 0 < a)
    (hau : a ≤ u) (hub : u ≤ b) (ha1 : a ≤ 1) :
    u * (u - 1) * (u ^ α - 1) ≥ α * a ^ α * (u - 1) ^ 2 := by
  have hu : 0 < u := ha.trans_le hau
  have hαsub : 0 ≤ α - 1 := sub_nonneg.mpr hα
  have hapow_pos : 0 < a ^ (α - 1) := Real.rpow_pos_of_pos ha _
  have hapow_nonneg : 0 ≤ a ^ (α - 1) := hapow_pos.le
  have ha_mul_pow : a * a ^ (α - 1) = a ^ α := by
    rw [mul_comm, ← Real.rpow_add_one ha.ne']
    congr 1
    ring
  rcases lt_trichotomy u 1 with hu1 | rfl | h1u
  · obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope (fun x : ℝ ↦ x ^ α) hu1
        (Real.differentiable_rpow_const hα).continuous.continuousOn
        (Real.differentiable_rpow_const hα).differentiableOn
    rw [Real.deriv_rpow_const, Real.one_rpow] at hcderiv
    have hcu : u ≤ c := hc.1.le
    have hac : a ≤ c := hau.trans hcu
    have hpow : a ^ (α - 1) ≤ c ^ (α - 1) :=
      Real.rpow_le_rpow ha.le hac hαsub
    have hgap_pos : 0 < 1 - u := sub_pos.mpr hu1
    have hmul : α * c ^ (α - 1) * (1 - u) = 1 - u ^ α :=
      (eq_div_iff hgap_pos.ne').mp hcderiv
    have hsecant : u ^ α - 1 = α * c ^ (α - 1) * (u - 1) := by
      linarith
    rw [hsecant]
    have hcoef : α * a ^ α ≤ u * (α * c ^ (α - 1)) := by
      rw [← ha_mul_pow]
      calc
        α * (a * a ^ (α - 1)) ≤ α * (u * c ^ (α - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hau hpow hapow_nonneg hu.le)
            (zero_le_one.trans hα)
        _ = u * (α * c ^ (α - 1)) := by ring
    have hsquare : 0 ≤ (u - 1) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hcoef hsquare]
  · simp
  · obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope (fun x : ℝ ↦ x ^ α) h1u
        (Real.differentiable_rpow_const hα).continuous.continuousOn
        (Real.differentiable_rpow_const hα).differentiableOn
    rw [Real.deriv_rpow_const, Real.one_rpow] at hcderiv
    have hcIcc : c ∈ Set.Icc a b := ⟨ha1.trans hc.1.le, hc.2.le.trans hub⟩
    have hpow : a ^ (α - 1) ≤ c ^ (α - 1) :=
      Real.rpow_le_rpow ha.le hcIcc.1 hαsub
    have hgap_pos : 0 < u - 1 := sub_pos.mpr h1u
    have hsecant : u ^ α - 1 = α * c ^ (α - 1) * (u - 1) :=
      ((eq_div_iff hgap_pos.ne').mp hcderiv).symm
    rw [hsecant]
    have hcoef : α * a ^ α ≤ u * (α * c ^ (α - 1)) := by
      rw [← ha_mul_pow]
      calc
        α * (a * a ^ (α - 1)) ≤ α * (u * c ^ (α - 1)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hau hpow hapow_nonneg hu.le)
            (zero_le_one.trans hα)
        _ = u * (α * c ^ (α - 1)) := by ring
    have hsquare : 0 ≤ (u - 1) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hcoef hsquare]

section AxiomAudit

#print axioms reaction_plateau_coercive

end AxiomAudit

end ShenWork.Paper1
