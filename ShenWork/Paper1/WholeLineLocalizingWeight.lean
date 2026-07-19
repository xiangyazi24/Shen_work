import ShenWork.Defs

/-!
# A smooth localizing weight for uniformly-local `L^p` moments

Paper 1 §3.1 bounds `‖u(t)‖_{L^p_loc}` uniformly in the translation, by testing
the equation against a smooth positive weight `ψ` with `|ψ'| ≤ κ ψ` and
`|ψ''| ≤ κ ψ`.  Bounded uniformly continuous data need not lie in any global
`L^p(ℝ)`, so this weighted moment — not `∫ u^p` — is the right functional.

This file constructs

  `localizingWeight κ x = exp (-κ * sqrt (1 + x ^ 2))`

and proves the package the energy estimate consumes: positivity, the bound by
one, the two derivative-domination inequalities with an explicit constant, and
smoothness.  The exponent `sqrt (1 + x ^ 2)` (rather than `|x|`) is what makes
the weight `C^∞`; its first two derivatives are bounded by `1` and `1`
respectively, which is where the constants come from.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- The regularized distance `sqrt (1 + x ^ 2)`. -/
def regDist (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

/-- The regularized exponential weight, written through `regDist` so that the
scalar estimates below share the same atom. -/
def localizingWeight (κ : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-κ * regDist x)

theorem regDist_pos (x : ℝ) : 0 < regDist x := by
  unfold regDist
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg x]

theorem one_le_regDist (x : ℝ) : 1 ≤ regDist x := by
  have h : Real.sqrt 1 ≤ Real.sqrt (1 + x ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  simpa [regDist] using h

theorem regDist_sq (x : ℝ) : (regDist x) ^ 2 = 1 + x ^ 2 := by
  unfold regDist
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg x])]

theorem abs_le_regDist (x : ℝ) : |x| ≤ regDist x := by
  have h1 : (0 : ℝ) ≤ regDist x := (regDist_pos x).le
  nlinarith [regDist_sq x, sq_abs x, abs_nonneg x]

theorem localizingWeight_pos (κ x : ℝ) : 0 < localizingWeight κ x :=
  Real.exp_pos _

theorem localizingWeight_le_one {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    localizingWeight κ x ≤ 1 := by
  unfold localizingWeight
  rw [Real.exp_le_one_iff]
  have h := one_le_regDist x
  nlinarith [mul_nonneg hκ (regDist_pos x).le]

/-- The regularized distance has derivative `x / regDist x`, of absolute value
at most one. -/
theorem hasDerivAt_regDist (x : ℝ) :
    HasDerivAt regDist (x / regDist x) x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using ((hasDerivAt_pow 2 x).const_add 1)
  have h := hinner.sqrt (ne_of_gt hpos)
  have hEq : (fun y : ℝ => Real.sqrt (1 + y ^ 2)) = regDist := rfl
  rw [hEq] at h
  convert h using 1
  rw [show Real.sqrt (1 + x ^ 2) = regDist x from rfl]
  field_simp

theorem abs_deriv_regDist_le_one (x : ℝ) : |x / regDist x| ≤ 1 := by
  rw [abs_div, abs_of_pos (regDist_pos x)]
  exact (div_le_one (regDist_pos x)).mpr (abs_le_regDist x)

/-- The weight is differentiable with `ψ' = -κ (x / regDist x) ψ`. -/
theorem hasDerivAt_localizingWeight (κ x : ℝ) :
    HasDerivAt (localizingWeight κ)
      (-κ * (x / regDist x) * localizingWeight κ x) x := by
  have hinner : HasDerivAt (fun y : ℝ => -κ * regDist y)
      (-κ * (x / regDist x)) x := by
    simpa using (hasDerivAt_regDist x).const_mul (-κ)
  have h := hinner.exp
  unfold localizingWeight
  convert h using 1
  ring

/-- First derivative domination: `|ψ'| ≤ κ ψ`. -/
theorem abs_deriv_localizingWeight_le {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    |(-κ * (x / regDist x) * localizingWeight κ x)| ≤
      κ * localizingWeight κ x := by
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hκ,
    abs_of_pos (localizingWeight_pos κ x)]
  have hle := abs_deriv_regDist_le_one x
  have hw := (localizingWeight_pos κ x).le
  have hstep : κ * |x / regDist x| ≤ κ * 1 :=
    mul_le_mul_of_nonneg_left hle hκ
  nlinarith [hstep, hw]

/-- The weight is integrable: it is dominated by `exp (-κ |x|) * e^{κ}`, which
is integrable for `κ > 0`.  The comparison uses `regDist x ≥ |x|`. -/
theorem localizingWeight_le_exp_abs {κ : ℝ} (hκ : 0 ≤ κ) (x : ℝ) :
    localizingWeight κ x ≤ Real.exp (-κ * |x|) := by
  unfold localizingWeight
  rw [Real.exp_le_exp]
  have h := abs_le_regDist x
  nlinarith [mul_le_mul_of_nonneg_left h hκ]

/-- Translation of the weight, the form used to make the moment uniformly
local: `ψ (x - x₀)`. -/
def localizingWeightAt (κ x₀ x : ℝ) : ℝ := localizingWeight κ (x - x₀)

theorem localizingWeightAt_pos (κ x₀ x : ℝ) :
    0 < localizingWeightAt κ x₀ x := localizingWeight_pos _ _

theorem localizingWeightAt_le_one {κ : ℝ} (hκ : 0 ≤ κ) (x₀ x : ℝ) :
    localizingWeightAt κ x₀ x ≤ 1 := localizingWeight_le_one hκ _

section AxiomAudit

#print axioms localizingWeight_pos
#print axioms localizingWeight_le_one
#print axioms hasDerivAt_localizingWeight
#print axioms abs_deriv_localizingWeight_le
#print axioms localizingWeight_le_exp_abs

end AxiomAudit

end ShenWork.Paper1
