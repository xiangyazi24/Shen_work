import ShenWork.Paper1.WholeLineResolverTestingIdentities

/-!
# Sharp bounded-interval gradient bound for the elliptic resolver

For `-v₂ + v = g`, expanding the square of the source and integrating the
mixed term by parts gives an exact identity with the endpoint flux displayed.
Pointwise Young's inequality then yields the sharp multiplier constant `1 / 4`
when that flux is nonpositive.  Thus the second theorem below supersedes
`resolver_deriv_sq_integral_le_source_sq`, whose constant is `1`.

The factor `1 / 4` is load-bearing in the energy argument because it is the
constant used to absorb the chemotaxis cross-term.  No interval
Cauchy--Schwarz theorem is assumed: the proof integrates the pointwise
inequality `-2 * v * v₂ ≤ v ^ 2 + v₂ ^ 2`.
-/

open MeasureTheory intervalIntegral
open Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper1

/-- Expanding `g = v - v₂` and integrating `v * v₂` by parts gives the exact
source-square decomposition, including twice the endpoint flux. -/
theorem resolver_source_sq_decomposition
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hv₂_sq_int : IntervalIntegrable (fun x ↦ (v₂ x) ^ 2) volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x) :
    (∫ x in a..b, (g x) ^ 2) =
      (∫ x in a..b, (v x) ^ 2) +
        2 * (∫ x in a..b, (v₁ x) ^ 2) +
        (∫ x in a..b, (v₂ x) ^ 2) -
        2 * (v₁ b * v b - v₁ a * v a) := by
  have hv_cont : ContinuousOn v (Set.uIcc a b) :=
    fun x hx ↦ (hv x hx).continuousAt.continuousWithinAt
  have hv₁_cont : ContinuousOn v₁ (Set.uIcc a b) :=
    fun x hx ↦ (hv₁ x hx).continuousAt.continuousWithinAt
  have hv_int : IntervalIntegrable v volume a b := hv_cont.intervalIntegrable
  have hv₁_int : IntervalIntegrable v₁ volume a b := hv₁_cont.intervalIntegrable
  have hv_sq_int : IntervalIntegrable (fun x ↦ (v x) ^ 2) volume a b := by
    simpa [pow_two] using hv_int.mul_continuousOn hv_cont
  have hv_mul_v₂_int : IntervalIntegrable (fun x ↦ v x * v₂ x) volume a b :=
    hv₂_int.continuousOn_mul hv_cont
  have hibp :
      (∫ x in a..b, v x * v₂ x) =
        v b * v₁ b - v a * v₁ a - ∫ x in a..b, (v₁ x) ^ 2 := by
    simpa [pow_two] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := a) (b := b) (u := v) (v := v₁) (u' := v₁) (v' := v₂)
        hv hv₁ hv₁_int hv₂_int)
  have hpde_sq :
      (∫ x in a..b, (g x) ^ 2) =
        ∫ x in a..b, (-v₂ x + v x) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (fun y : ℝ ↦ y ^ 2) (hpde x hx).symm
  rw [hpde_sq]
  rw [show (fun x ↦ (-v₂ x + v x) ^ 2) =
      (fun x ↦ (v x) ^ 2 - 2 * (v x * v₂ x) + (v₂ x) ^ 2) by
        funext x
        ring]
  rw [intervalIntegral.integral_add
    (hv_sq_int.sub (hv_mul_v₂_int.const_mul 2)) hv₂_sq_int]
  rw [intervalIntegral.integral_sub hv_sq_int (hv_mul_v₂_int.const_mul 2)]
  rw [intervalIntegral.integral_const_mul, hibp]
  ring

/-- If the endpoint flux is nonpositive, then the derivative of the resolver
has source-square norm at most `1 / 4` of the source-square norm. -/
theorem resolver_deriv_sq_le_quarter_source_sq
    {a b : ℝ} {v v₁ v₂ g : ℝ → ℝ}
    (hab : a ≤ b)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v₁ x) x)
    (hv₁ : ∀ x ∈ Set.uIcc a b, HasDerivAt v₁ (v₂ x) x)
    (hv₂_int : IntervalIntegrable v₂ volume a b)
    (hg_sq_int : IntervalIntegrable (fun x ↦ (g x) ^ 2) volume a b)
    (hpde : ∀ x ∈ Set.uIcc a b, -v₂ x + v x = g x)
    (hboundary : v₁ b * v b - v₁ a * v a ≤ 0) :
    (∫ x in a..b, (v₁ x) ^ 2) ≤
      (1 / 4 : ℝ) * ∫ x in a..b, (g x) ^ 2 := by
  have hv_cont : ContinuousOn v (Set.uIcc a b) :=
    fun x hx ↦ (hv x hx).continuousAt.continuousWithinAt
  have hv₁_cont : ContinuousOn v₁ (Set.uIcc a b) :=
    fun x hx ↦ (hv₁ x hx).continuousAt.continuousWithinAt
  have hv_int : IntervalIntegrable v volume a b := hv_cont.intervalIntegrable
  have hv₁_int : IntervalIntegrable v₁ volume a b := hv₁_cont.intervalIntegrable
  have hv_sq_int : IntervalIntegrable (fun x ↦ (v x) ^ 2) volume a b := by
    simpa [pow_two] using hv_int.mul_continuousOn hv_cont
  have hv_mul_v₂_int : IntervalIntegrable (fun x ↦ v x * v₂ x) volume a b :=
    hv₂_int.continuousOn_mul hv_cont
  have hgv_int : IntervalIntegrable (fun x ↦ g x * v x) volume a b := by
    apply (hv_sq_int.sub hv_mul_v₂_int).congr
    intro x hx
    have hx' : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    change v x ^ 2 - v x * v₂ x = g x * v x
    rw [← hpde x hx']
    ring
  have hv₂_sq_int : IntervalIntegrable (fun x ↦ (v₂ x) ^ 2) volume a b := by
    apply ((hv_sq_int.sub (hgv_int.const_mul 2)).add hg_sq_int).congr
    intro x hx
    have hx' : x ∈ Set.uIcc a b := Set.uIoc_subset_uIcc hx
    change v x ^ 2 - 2 * (g x * v x) + g x ^ 2 = v₂ x ^ 2
    rw [← hpde x hx']
    ring
  have hibp :
      (∫ x in a..b, v x * v₂ x) =
        v b * v₁ b - v a * v₁ a - ∫ x in a..b, (v₁ x) ^ 2 := by
    simpa [pow_two] using
      (intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (a := a) (b := b) (u := v) (v := v₁) (u' := v₁) (v' := v₂)
        hv hv₁ hv₁_int hv₂_int)
  have hyoung :
      -2 * (∫ x in a..b, v x * v₂ x) ≤
        (∫ x in a..b, (v x) ^ 2) + (∫ x in a..b, (v₂ x) ^ 2) := by
    calc
      -2 * (∫ x in a..b, v x * v₂ x) =
          ∫ x in a..b, -2 * (v x * v₂ x) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ ∫ x in a..b, (v x) ^ 2 + (v₂ x) ^ 2 := by
        exact intervalIntegral.integral_mono_on hab
          (hv_mul_v₂_int.const_mul (-2)) (hv_sq_int.add hv₂_sq_int)
          (fun x _hx ↦ by nlinarith [sq_nonneg (v x + v₂ x)])
      _ = (∫ x in a..b, (v x) ^ 2) +
          (∫ x in a..b, (v₂ x) ^ 2) := by
        rw [intervalIntegral.integral_add hv_sq_int hv₂_sq_int]
  have hderiv_twice :
      2 * (∫ x in a..b, (v₁ x) ^ 2) ≤
        (∫ x in a..b, (v x) ^ 2) + (∫ x in a..b, (v₂ x) ^ 2) := by
    nlinarith [hibp]
  have hdecomp := resolver_source_sq_decomposition hv hv₁ hv₂_int hv₂_sq_int hpde
  nlinarith

section AxiomAudit

#print axioms resolver_source_sq_decomposition
#print axioms resolver_deriv_sq_le_quarter_source_sq

end AxiomAudit

end ShenWork.Paper1
