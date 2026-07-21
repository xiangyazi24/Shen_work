import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The resolver oscillation bound (interface layer)

The crest gradient route (`crest_gradient_bound`) needs the non-circular
oscillation bounds `|v − u|(z) ≤ b − a`, where `v` is the resolver of `u` for
`-v_zz + v = u`.  The Green representation `v = ½ e^{-|·|} ∗ u` (a unit-mass
average) makes this elementary:

`(v − u)(z) = ∫ K(z−y)(u(y) − u(z)) dy`,  `K(s) = ½ e^{-|s|}`, `∫ K = 1`,

so `|v − u|(z) ≤ (b − a) ∫ K = b − a`.

This file proves that inequality at the INTERFACE level: the Green representation
`hrep`, the kernel unit-mass `hmass`, and the integrability `hint` are carried as
hypotheses (their discharge — proving the convolution solves the elliptic
equation, and computing `∫ ½e^{-|s|} = 1` from `integral_exp_neg_Ioi_zero` — is
the deferred analytic construction).  Given them, the oscillation bound is a
clean consequence of `norm_integral_le_integral_norm` + `integral_mono`.
-/

open MeasureTheory Real

noncomputable section

namespace ShenWork.Paper1

variable {u v : ℝ → ℝ} {z a b : ℝ}

/-- **Resolver oscillation bound.**  If `v z` is the kernel average of `u` with a
unit-mass nonnegative kernel `K` and `a ≤ u ≤ b`, then `|v z − u z| ≤ b − a`. -/
theorem resolver_oscillation_bound
    {K : ℝ → ℝ}
    (hKnonneg : ∀ y, 0 ≤ K y)
    (hmass : ∫ y, K y = 1)
    (hint : Integrable (fun y => K y * u y))
    (hintK : Integrable K)
    (hrep : v z = ∫ y, K y * u y)
    (hu_lo : ∀ y, a ≤ u y) (hu_hi : ∀ y, u y ≤ b) :
    |v z - u z| ≤ b - a := by
  -- `v z - u z = ∫ K y * (u y - u z)` (kernel has unit mass)
  have hsub : v z - u z = ∫ y, K y * (u y - u z) := by
    have h2 : (∫ y, K y * (u y - u z)) = (∫ y, K y * u y) - (∫ y, K y * u z) := by
      simp_rw [mul_sub]
      exact MeasureTheory.integral_sub hint (hintK.mul_const (u z))
    rw [h2, ← hrep, MeasureTheory.integral_mul_const, hmass, one_mul]
  rw [hsub]
  -- `|∫ K (u - u z)| ≤ ∫ |K (u - u z)| ≤ ∫ K (b - a) = b - a`
  have hintsub : Integrable (fun y => K y * (u y - u z)) := by
    have := hint.sub (hintK.mul_const (u z))
    simpa [mul_sub] using this
  rw [← Real.norm_eq_abs]
  calc ‖∫ y, K y * (u y - u z)‖
      ≤ ∫ y, ‖K y * (u y - u z)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y, K y * (b - a) := by
        simp_rw [Real.norm_eq_abs]
        apply MeasureTheory.integral_mono hintsub.abs (hintK.mul_const (b - a))
        intro y
        dsimp only
        rw [abs_mul, abs_of_nonneg (hKnonneg y)]
        apply mul_le_mul_of_nonneg_left _ (hKnonneg y)
        rw [abs_le]
        constructor
        · have := hu_lo y; have := hu_hi z; linarith
        · have := hu_hi y; have := hu_lo z; linarith
    _ = b - a := by rw [MeasureTheory.integral_mul_const, hmass, one_mul]

section AxiomAudit

#print axioms resolver_oscillation_bound

end AxiomAudit

end ShenWork.Paper1
