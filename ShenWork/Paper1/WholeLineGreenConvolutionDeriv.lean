import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Derivatives of the Green half-line integrals

For bounded continuous `u`, the Green representation
`v = ½ e^{-|·|} ∗ u = V₋ + V₊` with
`V₋(z) = ½ e^{-z} I₋(z)`, `I₋(z) = ∫_{Iic z} e^{y} u(y) dy`, and symmetrically
`V₊`.  This file proves the two moving-endpoint FTC facts that everything else
(the ODE `v'' = v − u`) reduces to, per Fable R2's route (2026-07-21):

`d/dz I₋(z) = e^{z} u(z)`  (Q2, the `I₋` half).

The improper endpoint is handled WITHOUT limits: `I₋(z) − I₋(z₀) = ∫_{z₀..z}`
(`integral_Iic_sub_Iic`), and the interval integral's moving-endpoint derivative is
`e^{z} u(z)` (`integral_hasDerivAt_right`).  Integrability on `Iic w` comes from the
dominator `M e^{y}` (`integrableOn_exp_Iic`).
-/

open MeasureTheory Set Real intervalIntegral

noncomputable section

namespace ShenWork.Paper1

variable {u : ℝ → ℝ}

/-- `y ↦ e^{y} u(y)` is integrable on every left ray `Iic w` (dominated by `M e^y`). -/
theorem expMul_integrableOn_Iic (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (w : ℝ) : IntegrableOn (fun y => Real.exp y * u y) (Iic w) := by
  apply Integrable.mono' ((integrableOn_exp_Iic w).const_mul M)
  · exact (Real.continuous_exp.mul hu).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with y _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos y)]
    nlinarith [mul_le_mul_of_nonneg_left (hM y) (Real.exp_pos y).le]

/-- **The `I₋` FTC.**  `d/dz ∫_{Iic z} e^{y} u(y) dy = e^{z} u(z)`. -/
theorem Iminus_hasDerivAt (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (z : ℝ) :
    HasDerivAt (fun z => ∫ y in Iic z, Real.exp y * u y)
      (Real.exp z * u z) z := by
  set f : ℝ → ℝ := fun y => Real.exp y * u y with hf
  have hcont : Continuous f := Real.continuous_exp.mul hu
  have hint : ∀ w, IntegrableOn f (Iic w) :=
    fun w => expMul_integrableOn_Iic hu hM w
  -- rewrite `∫_{Iic ·}` as a constant plus the interval integral from a fixed anchor `z`
  have hrw : (fun w => ∫ y in Iic w, f y)
      = (fun w => (∫ y in Iic z, f y) + ∫ y in z..w, f y) := by
    funext w
    rw [← integral_Iic_sub_Iic (hint z) (hint w)]
    ring
  rw [hrw]
  -- derivative of the interval integral at the moving upper endpoint
  have hFTC : HasDerivAt (fun w => ∫ y in z..w, f y) (f z) z := by
    apply integral_hasDerivAt_right
    · exact (hcont.intervalIntegrable z z)
    · exact hcont.stronglyMeasurableAtFilter _ _
    · exact hcont.continuousAt
  exact hFTC.const_add (∫ y in Iic z, f y)

/-- **The `I₊` FTC.**  `d/dz ∫_{Ioi z} e^{-y} u(y) dy = −e^{-z} u(z)`.
Uses `I₊(z) = (∫_ℝ) − ∫_{Iic z}` and the `Iminus` result with `u` replaced by
`e^{-2y} u(y)`. -/
theorem Iplus_hasDerivAt (hu : Continuous u)
    (hInt : Integrable (fun y => Real.exp (-y) * u y))
    (z : ℝ) :
    HasDerivAt (fun z => ∫ y in Ioi z, Real.exp (-y) * u y)
      (-(Real.exp (-z) * u z)) z := by
  have hcont : Continuous (fun y => Real.exp (-y) * u y) :=
    (Real.continuous_exp.comp continuous_neg).mul hu
  have hintIic : ∀ w, IntegrableOn (fun y => Real.exp (-y) * u y) (Iic w) :=
    fun w => hInt.integrableOn
  -- `∫_{Ioi z} g = (∫ g) − ∫_{Iic z} g`
  have hrw : (fun w => ∫ y in Ioi w, Real.exp (-y) * u y)
      = (fun w => (∫ y, Real.exp (-y) * u y) - ∫ y in Iic w, Real.exp (-y) * u y) := by
    funext w
    have hsplit := integral_add_compl (s := Iic w) (μ := volume) measurableSet_Iic hInt
    rw [compl_Iic] at hsplit
    linarith [hsplit]
  rw [hrw]
  -- derivative of `∫_{Iic z} e^{-y}u` at the endpoint = `e^{-z} u z`
  have hFTC : HasDerivAt (fun w => ∫ y in Iic w, Real.exp (-y) * u y)
      (Real.exp (-z) * u z) z := by
    have hrw2 : (fun w => ∫ y in Iic w, Real.exp (-y) * u y)
        = (fun w => (∫ y in Iic z, Real.exp (-y) * u y)
            + ∫ y in z..w, Real.exp (-y) * u y) := by
      funext w
      rw [← integral_Iic_sub_Iic (hintIic z) (hintIic w)]; ring
    rw [hrw2]
    have hF : HasDerivAt (fun w => ∫ y in z..w, Real.exp (-y) * u y)
        (Real.exp (-z) * u z) z := by
      apply integral_hasDerivAt_right
      · exact hcont.intervalIntegrable z z
      · exact hcont.stronglyMeasurableAtFilter _ _
      · exact hcont.continuousAt
    exact hF.const_add (∫ y in Iic z, Real.exp (-y) * u y)
  simpa using ((hasDerivAt_const z (∫ y, Real.exp (-y) * u y)).sub hFTC)

section AxiomAudit

#print axioms Iminus_hasDerivAt
#print axioms Iplus_hasDerivAt

end AxiomAudit

end ShenWork.Paper1
