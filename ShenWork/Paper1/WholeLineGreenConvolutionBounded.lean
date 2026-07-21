import ShenWork.Paper1.WholeLineGreenConvolutionODE

/-!
# The Green convolution is bounded by `M`

The final glue for the Green-representation discharge: `|vConv u z| ≤ M` when
`|u| ≤ M`.  Indeed `|V₋(z)| = ½ e^{-z} |∫_{Iic z} e^y u| ≤ ½ e^{-z} ∫_{Iic z} e^y M
= ½ e^{-z} · M · e^z = M/2` (using `∫_{Iic z} e^y = e^z`), and symmetrically
`|V₊(z)| ≤ M/2`, so `|vConv| ≤ M`.

With `vConv_secondDeriv` (the convolution solves `v'' = v − u`) and the uniqueness
keystone `bounded_solution_wzz_eq_w_is_zero`, this makes `vConv` THE bounded
resolver: any bounded `C²` solution of the resolver equation equals `vConv`.
-/

open MeasureTheory Set Real

noncomputable section

namespace ShenWork.Paper1

variable {u : ℝ → ℝ}

/-- `|V₋(z)| ≤ M/2`. -/
theorem Vminus_abs_le (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (z : ℝ) : |Vminus u z| ≤ M / 2 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM z)
  have hintU : IntegrableOn (fun y => Real.exp y * u y) (Iic z) :=
    expMul_integrableOn_Iic hu hM z
  have hintM : IntegrableOn (fun y => Real.exp y * M) (Iic z) :=
    (integrableOn_exp_Iic z).mul_const M
  -- `|∫ e^y u| ≤ ∫ e^y M = M e^z`
  have hbound : |∫ y in Iic z, Real.exp y * u y| ≤ M * Real.exp z := by
    calc |∫ y in Iic z, Real.exp y * u y|
        ≤ ∫ y in Iic z, |Real.exp y * u y| := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume.restrict (Iic z))
              (fun y => Real.exp y * u y))
      _ ≤ ∫ y in Iic z, Real.exp y * M := by
          apply integral_mono hintU.abs hintM
          intro y
          dsimp only
          rw [abs_mul, abs_of_pos (Real.exp_pos y)]
          exact mul_le_mul_of_nonneg_left (hM y) (Real.exp_pos y).le
      _ = M * Real.exp z := by
          rw [show (fun y => Real.exp y * M) = (fun y => M * Real.exp y) by
            funext y; ring, integral_const_mul, integral_exp_Iic]
  -- assemble
  unfold Vminus
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/2),
    abs_of_pos (Real.exp_pos (-z))]
  have hexp : (0:ℝ) < Real.exp (-z) := Real.exp_pos _
  calc (1 / 2) * Real.exp (-z) * |∫ y in Iic z, Real.exp y * u y|
      ≤ (1 / 2) * Real.exp (-z) * (M * Real.exp z) := by
        apply mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = M / 2 := by
        have hc : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
        linear_combination (M / 2) * hc

/-- `|V₊(z)| ≤ M/2`. -/
theorem Vplus_abs_le (_hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (hInt : Integrable (fun y => Real.exp (-y) * u y)) (z : ℝ) :
    |Vplus u z| ≤ M / 2 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM z)
  have hintU : IntegrableOn (fun y => Real.exp (-y) * u y) (Ioi z) := hInt.integrableOn
  have hintM : IntegrableOn (fun y => Real.exp (-y) * M) (Ioi z) :=
    (integrableOn_exp_neg_Ioi z).mul_const M
  have hbound : |∫ y in Ioi z, Real.exp (-y) * u y| ≤ M * Real.exp (-z) := by
    calc |∫ y in Ioi z, Real.exp (-y) * u y|
        ≤ ∫ y in Ioi z, |Real.exp (-y) * u y| := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume.restrict (Ioi z))
              (fun y => Real.exp (-y) * u y))
      _ ≤ ∫ y in Ioi z, Real.exp (-y) * M := by
          apply integral_mono hintU.abs hintM
          intro y
          dsimp only
          rw [abs_mul, abs_of_pos (Real.exp_pos (-y))]
          exact mul_le_mul_of_nonneg_left (hM y) (Real.exp_pos (-y)).le
      _ = M * Real.exp (-z) := by
          rw [show (fun y => Real.exp (-y) * M) = (fun y => M * Real.exp (-y)) by
            funext y; ring, integral_const_mul, integral_exp_neg_Ioi]
  unfold Vplus
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/2),
    abs_of_pos (Real.exp_pos z)]
  calc (1 / 2) * Real.exp z * |∫ y in Ioi z, Real.exp (-y) * u y|
      ≤ (1 / 2) * Real.exp z * (M * Real.exp (-z)) := by
        apply mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = M / 2 := by
        have hc : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
        linear_combination (M / 2) * hc

/-- **`vConv` is bounded by `M`.** -/
theorem vConv_abs_le (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (hInt : Integrable (fun y => Real.exp (-y) * u y)) (z : ℝ) :
    |vConv u z| ≤ M := by
  unfold vConv
  calc |Vminus u z + Vplus u z|
      ≤ |Vminus u z| + |Vplus u z| := abs_add_le _ _
    _ ≤ M / 2 + M / 2 := add_le_add (Vminus_abs_le hu hM z) (Vplus_abs_le hu hM hInt z)
    _ = M := by ring

section AxiomAudit

#print axioms vConv_abs_le

end AxiomAudit

end ShenWork.Paper1
