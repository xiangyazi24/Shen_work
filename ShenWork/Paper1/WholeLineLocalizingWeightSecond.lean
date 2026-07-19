import ShenWork.Paper1.WholeLineLocalizingWeight

/-!
# Second-derivative domination for the localizing weight

The weighted local energy estimate integrates by parts twice, so besides
`|ψ'| ≤ κ ψ` it needs `|ψ''| ≤ κ' ψ` with an explicit `κ'`.

Writing `s x = x / regDist x` for the derivative of the regularized distance,
`ψ' = -κ s ψ` gives

  `ψ'' = (-κ s' + κ² s²) ψ`,

and `s' = 1 / (regDist x) ^ 3 ∈ (0, 1]` while `|s| ≤ 1`, so `κ' = κ + κ²`
works.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- Derivative of the regularized-distance slope `x / regDist x`. -/
theorem hasDerivAt_regDistSlope (x : ℝ) :
    HasDerivAt (fun y : ℝ => y / regDist y)
      (1 / (regDist x) ^ 3) x := by
  have hpos : 0 < regDist x := regDist_pos x
  have hne : regDist x ≠ 0 := ne_of_gt hpos
  have hsq : (regDist x) ^ 2 = 1 + x ^ 2 := regDist_sq x
  have hcube : (regDist x) ^ 3 = (1 + x ^ 2) * regDist x := by
    rw [pow_succ, hsq]
  have h := (hasDerivAt_id x).div (hasDerivAt_regDist x) (ne_of_gt hpos)
  convert h using 1
  simp only [id_eq]
  have hnum : (1 : ℝ) * regDist x - x * (x / regDist x) = 1 / regDist x := by
    field_simp
    nlinarith [hsq]
  rw [hnum, div_div]
  congr 1
  rw [pow_succ]
  ring

theorem regDistSlope_deriv_pos (x : ℝ) : 0 < 1 / (regDist x) ^ 3 := by
  have hpos : 0 < regDist x := regDist_pos x
  positivity

theorem regDistSlope_deriv_le_one (x : ℝ) : 1 / (regDist x) ^ 3 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ regDist x := one_le_regDist x
  have hpos : 0 < regDist x := regDist_pos x
  have hcube : (1 : ℝ) ≤ (regDist x) ^ 3 := by
    nlinarith [h1, hpos.le, sq_nonneg (regDist x - 1)]
  rw [div_le_one (by nlinarith [hcube])]
  exact hcube

/-- The weight is twice differentiable, with
`ψ'' = (-κ · s' + κ² · s²) ψ` where `s x = x / regDist x`. -/
theorem hasDerivAt_deriv_localizingWeight (κ x : ℝ) :
    HasDerivAt (fun y : ℝ => -κ * (y / regDist y) * localizingWeight κ y)
      ((-κ * (1 / (regDist x) ^ 3)
        + κ ^ 2 * (x / regDist x) ^ 2) * localizingWeight κ x) x := by
  have hs := hasDerivAt_regDistSlope x
  have hw := hasDerivAt_localizingWeight κ x
  have h := ((hs.const_mul (-κ)).mul hw)
  convert h using 1
  ring

/-- Second-derivative domination with the explicit constant `κ + κ ^ 2`. -/
theorem abs_second_deriv_localizingWeight_le {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    |((-κ * (1 / (regDist x) ^ 3)
        + κ ^ 2 * (x / regDist x) ^ 2) * localizingWeight κ x)| ≤
      (κ + κ ^ 2) * localizingWeight κ x := by
  have hw : 0 < localizingWeight κ x := localizingWeight_pos κ x
  have hslope : |x / regDist x| ≤ 1 := abs_deriv_regDist_le_one x
  have hsq : (x / regDist x) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (x / regDist x), hslope, abs_nonneg (x / regDist x)]
  have hd0 : 0 < 1 / (regDist x) ^ 3 := regDistSlope_deriv_pos x
  have hd1 : 1 / (regDist x) ^ 3 ≤ 1 := regDistSlope_deriv_le_one x
  rw [abs_mul, abs_of_pos hw]
  have hfactor :
      |(-κ * (1 / (regDist x) ^ 3) + κ ^ 2 * (x / regDist x) ^ 2)| ≤
        κ + κ ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hd0.le, hd1, hsq, sq_nonneg (x / regDist x), hκ,
      mul_nonneg hκ hd0.le, sq_nonneg κ]
  nlinarith [hfactor, hw.le, abs_nonneg
    (-κ * (1 / (regDist x) ^ 3) + κ ^ 2 * (x / regDist x) ^ 2)]

section AxiomAudit

#print axioms hasDerivAt_regDistSlope
#print axioms hasDerivAt_deriv_localizingWeight
#print axioms abs_second_deriv_localizingWeight_le

end AxiomAudit

end ShenWork.Paper1
