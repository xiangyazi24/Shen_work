import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Testing identities for the one-dimensional elliptic resolver

This file gives an abstract bounded-interval interface for the equation

`-v₂ + v = g`,

where `v₁` and `v₂` are supplied first- and second-derivative witnesses for
`v`.  The interface assumes derivatives directly on `Set.uIcc a b`; this
records the endpoint regularity needed by Mathlib's integration-by-parts
theorem without tying the identities to any PDE solution structure.

The second testing identity explicitly assumes integrability of `v₂²`, which
does not follow from integrability of `v₂`.  For the smoothing estimates, the
boundary flux is assumed nonpositive (in particular, it may vanish).  A direct
interval-integral Cauchy--Schwarz wrapper is not needed: pointwise Young's
inequality `2gv ≤ g² + v²`, followed by monotonicity of the interval integral,
gives both requested multiplier bounds.
-/

open MeasureTheory intervalIntegral
open Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper1

/-- Testing `-v₂ + v = g` against `v` gives the first resolver energy identity,
including the endpoint flux. -/
theorem resolver_testing_identity
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x) :
    (∫ x in a..b, (v₁ x) ^ 2) + (∫ x in a..b, (v x) ^ 2) =
      (∫ x in a..b, g x * v x) +
        (v₁ b * v b - v₁ a * v a) := by
  have hv_cont : ContinuousOn v (Set.uIcc a b) :=
    fun x hx ↦ (hv x hx).continuousAt.continuousWithinAt
  have hv₁_cont : ContinuousOn v₁ (Set.uIcc a b) :=
    fun x hx ↦ (hv₁ x hx).continuousAt.continuousWithinAt
  have hv_int : IntervalIntegrable v volume a b := hv_cont.intervalIntegrable
  have hv₁_int : IntervalIntegrable v₁ volume a b := hv₁_cont.intervalIntegrable
  have hv₁_sq_int : IntervalIntegrable (fun x ↦ (v₁ x) ^ 2) volume a b := by
    simpa [pow_two] using hv₁_int.mul_continuousOn hv₁_cont
  have hv_sq_int : IntervalIntegrable (fun x ↦ (v x) ^ 2) volume a b := by
    simpa [pow_two] using hv_int.mul_continuousOn hv_cont
  have hv₂_mul_v_int : IntervalIntegrable (fun x ↦ v₂ x * v x) volume a b :=
    hv₂_int.mul_continuousOn hv_cont
  have hibp :
      (∫ x in a..b, v x * v₂ x) =
        v b * v₁ b - v a * v₁ a - ∫ x in a..b, v₁ x * v₁ x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := b) (u := v) (v := v₁) (u' := v₁) (v' := v₂)
      hv hv₁ hv₁_int hv₂_int
  have hpde_int :
      (∫ x in a..b, g x * v x) =
        ∫ x in a..b, (-v₂ x + v x) * v x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (fun y : ℝ ↦ y * v x) (hpde x hx).symm
  rw [hpde_int]
  rw [show (fun x ↦ (-v₂ x + v x) * v x) =
      (fun x ↦ v x ^ 2 - v₂ x * v x) by funext x; ring]
  rw [intervalIntegral.integral_sub hv_sq_int hv₂_mul_v_int]
  have hcomm : (∫ x in a..b, v₂ x * v x) = ∫ x in a..b, v x * v₂ x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hcomm, hibp]
  ring

/-- Testing `-v₂ + v = g` against `-v₂` gives control of both derivative
levels, with the same endpoint flux as the first identity. -/
theorem resolver_second_derivative_testing_identity
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hv₂_sq_int : IntervalIntegrable (fun x ↦ (v₂ x) ^ 2) volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x) :
    (∫ x in a..b, (v₂ x) ^ 2) + (∫ x in a..b, (v₁ x) ^ 2) =
      (∫ x in a..b, g x * (-v₂ x)) +
        (v₁ b * v b - v₁ a * v a) := by
  have hv_cont : ContinuousOn v (Set.uIcc a b) :=
    fun x hx ↦ (hv x hx).continuousAt.continuousWithinAt
  have hv₁_cont : ContinuousOn v₁ (Set.uIcc a b) :=
    fun x hx ↦ (hv₁ x hx).continuousAt.continuousWithinAt
  have hv₁_int : IntervalIntegrable v₁ volume a b := hv₁_cont.intervalIntegrable
  have hv_mul_v₂_int : IntervalIntegrable (fun x ↦ v x * v₂ x) volume a b :=
    hv₂_int.continuousOn_mul hv_cont
  have hibp :
      (∫ x in a..b, v x * v₂ x) =
        v b * v₁ b - v a * v₁ a - ∫ x in a..b, v₁ x * v₁ x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := a) (b := b) (u := v) (v := v₁) (u' := v₁) (v' := v₂)
      hv hv₁ hv₁_int hv₂_int
  have hpde_int :
      (∫ x in a..b, g x * (-v₂ x)) =
        ∫ x in a..b, (-v₂ x + v x) * (-v₂ x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (fun y : ℝ ↦ y * (-v₂ x)) (hpde x hx).symm
  rw [hpde_int]
  rw [show (fun x ↦ (-v₂ x + v x) * (-v₂ x)) =
      (fun x ↦ v₂ x ^ 2 - v x * v₂ x) by funext x; ring]
  rw [intervalIntegral.integral_sub hv₂_sq_int hv_mul_v₂_int]
  rw [hibp]
  ring

/-- If the endpoint flux is nonpositive, then testing against `v` and applying
pointwise Young's inequality gives both `L²` smoothing estimates at once. -/
theorem resolver_smoothing_sq_bounds
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hab : a ≤ b)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hg_sq_int : IntervalIntegrable (fun x ↦ (g x) ^ 2) volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x)
    (hboundary : v₁ b * v b - v₁ a * v a ≤ 0) :
    ((∫ x in a..b, (v₁ x) ^ 2) ≤ ∫ x in a..b, (g x) ^ 2) ∧
      ((∫ x in a..b, (v x) ^ 2) ≤ ∫ x in a..b, (g x) ^ 2) := by
  have hv_cont : ContinuousOn v (Set.uIcc a b) :=
    fun x hx ↦ (hv x hx).continuousAt.continuousWithinAt
  have hv₁_cont : ContinuousOn v₁ (Set.uIcc a b) :=
    fun x hx ↦ (hv₁ x hx).continuousAt.continuousWithinAt
  have hv_int : IntervalIntegrable v volume a b := hv_cont.intervalIntegrable
  have hv₁_int : IntervalIntegrable v₁ volume a b := hv₁_cont.intervalIntegrable
  have hv₁_sq_int : IntervalIntegrable (fun x ↦ (v₁ x) ^ 2) volume a b := by
    simpa [pow_two] using hv₁_int.mul_continuousOn hv₁_cont
  have hv_sq_int : IntervalIntegrable (fun x ↦ (v x) ^ 2) volume a b := by
    simpa [pow_two] using hv_int.mul_continuousOn hv_cont
  have hv₂_mul_v_int : IntervalIntegrable (fun x ↦ v₂ x * v x) volume a b :=
    hv₂_int.mul_continuousOn hv_cont
  have hgv_int : IntervalIntegrable (fun x ↦ g x * v x) volume a b := by
    apply (hv_sq_int.sub hv₂_mul_v_int).congr
    intro x hx
    have hx' : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    change v x ^ 2 - v₂ x * v x = g x * v x
    rw [← hpde x hx']
    ring
  have hidentity := resolver_testing_identity hv hv₁ hv₂_int hpde
  have hyoung :
      2 * (∫ x in a..b, g x * v x) ≤
        (∫ x in a..b, (g x) ^ 2) + (∫ x in a..b, (v x) ^ 2) := by
    calc
      2 * (∫ x in a..b, g x * v x) =
          ∫ x in a..b, 2 * (g x * v x) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in a..b, (g x) ^ 2 + (v x) ^ 2 := by
        exact intervalIntegral.integral_mono_on hab
          (hgv_int.const_mul 2) (hg_sq_int.add hv_sq_int)
          (fun x _hx ↦ by nlinarith [sq_nonneg (g x - v x)])
      _ = (∫ x in a..b, (g x) ^ 2) + (∫ x in a..b, (v x) ^ 2) := by
        rw [intervalIntegral.integral_add hg_sq_int hv_sq_int]
  have hv₁_sq_nonneg : 0 ≤ ∫ x in a..b, (v₁ x) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun x _hx ↦ sq_nonneg _)
  have hv_sq_nonneg : 0 ≤ ∫ x in a..b, (v x) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun x _hx ↦ sq_nonneg _)
  constructor <;> nlinarith

/-- The derivative part of the elliptic resolvent is an `L²` contraction on a
bounded interval when its endpoint flux is nonpositive. -/
theorem resolver_deriv_sq_integral_le_source_sq
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hab : a ≤ b)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hg_sq_int : IntervalIntegrable (fun x ↦ (g x) ^ 2) volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x)
    (hboundary : v₁ b * v b - v₁ a * v a ≤ 0) :
    (∫ x in a..b, (v₁ x) ^ 2) ≤ ∫ x in a..b, (g x) ^ 2 :=
  (resolver_smoothing_sq_bounds hab hv hv₁ hv₂_int hg_sq_int hpde hboundary).1

/-- The elliptic resolvent itself is an `L²` contraction on a bounded interval
when its endpoint flux is nonpositive. -/
theorem resolver_sq_integral_le_source_sq
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hab : a ≤ b)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hg_sq_int : IntervalIntegrable (fun x ↦ (g x) ^ 2) volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x)
    (hboundary : v₁ b * v b - v₁ a * v a ≤ 0) :
    (∫ x in a..b, (v x) ^ 2) ≤ ∫ x in a..b, (g x) ^ 2 :=
  (resolver_smoothing_sq_bounds hab hv hv₁ hv₂_int hg_sq_int hpde hboundary).2

section AxiomAudit

#print axioms resolver_testing_identity
#print axioms resolver_second_derivative_testing_identity
#print axioms resolver_smoothing_sq_bounds
#print axioms resolver_deriv_sq_integral_le_source_sq
#print axioms resolver_sq_integral_le_source_sq

end AxiomAudit

end ShenWork.Paper1
