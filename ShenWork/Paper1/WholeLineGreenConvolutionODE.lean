import ShenWork.Paper1.WholeLineGreenConvolutionDeriv

/-!
# The Green convolution solves `v'' = v − u`

Building on the two FTC facts (`Iminus_hasDerivAt`, `Iplus_hasDerivAt`), this file
assembles the resolver ODE for the convolution
`v_conv = V₋ + V₊`, `V₋(z) = ½ e^{-z} I₋(z)`, `V₊(z) = ½ e^{z} I₊(z)`:

`V₋' = −V₋ + u/2`,  `V₊' = V₊ − u/2`,

so with `w := V₊ − V₋`, `v_conv' = w` (the `u/2` terms cancel) and
`v_conv'' = w' = v_conv − u` (they add to `−u`).  With the uniqueness keystone
`bounded_solution_wzz_eq_w_is_zero`, this identifies the repo's `pde_v` solution
with `v_conv`, discharging the representation hypothesis of
`resolver_oscillation_bound`.
-/

open MeasureTheory Set Real intervalIntegral

noncomputable section

namespace ShenWork.Paper1

variable {u : ℝ → ℝ}

/-- `Vminus z = ½ e^{-z} ∫_{Iic z} e^{y} u`. -/
def Vminus (u : ℝ → ℝ) (z : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-z) * ∫ y in Iic z, Real.exp y * u y

/-- `Vplus z = ½ e^{z} ∫_{Ioi z} e^{-y} u`. -/
def Vplus (u : ℝ → ℝ) (z : ℝ) : ℝ :=
  (1 / 2) * Real.exp z * ∫ y in Ioi z, Real.exp (-y) * u y

/-- `V₋' = −V₋ + u/2`. -/
theorem Vminus_hasDerivAt (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (z : ℝ) :
    HasDerivAt (Vminus u) (-(Vminus u z) + u z / 2) z := by
  have hI := Iminus_hasDerivAt hu hM z
  have hexp : HasDerivAt (fun z : ℝ => (1 / 2) * Real.exp (-z))
      ((1 / 2) * (-Real.exp (-z))) z := by
    have h := (((hasDerivAt_id z).neg).exp).const_mul (1 / 2 : ℝ)
    simpa using h
  have hprod := hexp.mul hI
  have hcancel : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  have hval : (1 / 2) * (-Real.exp (-z)) * (∫ y in Iic z, Real.exp y * u y)
      + (1 / 2) * Real.exp (-z) * (Real.exp z * u z)
      = -(Vminus u z) + u z / 2 := by
    unfold Vminus
    linear_combination (u z / 2) * hcancel
  rw [hval] at hprod
  exact hprod

/-- `V₊' = V₊ − u/2`. -/
theorem Vplus_hasDerivAt (hu : Continuous u)
    (hInt : Integrable (fun y => Real.exp (-y) * u y)) (z : ℝ) :
    HasDerivAt (Vplus u) (Vplus u z - u z / 2) z := by
  have hI := Iplus_hasDerivAt hu hInt z
  have hexp : HasDerivAt (fun z : ℝ => (1 / 2) * Real.exp z)
      ((1 / 2) * Real.exp z) z := by
    have h := ((hasDerivAt_id z).exp).const_mul (1 / 2 : ℝ)
    simpa using h
  have hprod := hexp.mul hI
  have hcancel : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
  have hval : (1 / 2) * Real.exp z * (∫ y in Ioi z, Real.exp (-y) * u y)
      + (1 / 2) * Real.exp z * (-(Real.exp (-z) * u z))
      = Vplus u z - u z / 2 := by
    unfold Vplus
    linear_combination (-(u z) / 2) * hcancel
  rw [hval] at hprod
  exact hprod

/-- The convolution resolver `v_conv = V₋ + V₊`. -/
def vConv (u : ℝ → ℝ) (z : ℝ) : ℝ := Vminus u z + Vplus u z

/-- First derivative: `v_conv' = V₊ − V₋` (the `u/2` terms cancel). -/
theorem vConv_hasDerivAt (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (hInt : Integrable (fun y => Real.exp (-y) * u y)) (z : ℝ) :
    HasDerivAt (vConv u) (Vplus u z - Vminus u z) z := by
  have h := (Vminus_hasDerivAt hu hM z).add (Vplus_hasDerivAt hu hInt z)
  have hval : -(Vminus u z) + u z / 2 + (Vplus u z - u z / 2)
      = Vplus u z - Vminus u z := by ring
  rw [hval] at h
  exact h

/-- **The convolution solves the resolver ODE `v_conv'' = v_conv − u`.** -/
theorem vConv_secondDeriv (hu : Continuous u) {M : ℝ} (hM : ∀ y, |u y| ≤ M)
    (hInt : Integrable (fun y => Real.exp (-y) * u y)) (z : ℝ) :
    HasDerivAt (fun z => Vplus u z - Vminus u z) (vConv u z - u z) z := by
  have h := (Vplus_hasDerivAt hu hInt z).sub (Vminus_hasDerivAt hu hM z)
  have hval : (Vplus u z - u z / 2) - (-(Vminus u z) + u z / 2)
      = vConv u z - u z := by
    unfold vConv; ring
  rw [hval] at h
  exact h

section AxiomAudit

#print axioms Vminus_hasDerivAt
#print axioms Vplus_hasDerivAt
#print axioms vConv_hasDerivAt
#print axioms vConv_secondDeriv

end AxiomAudit

end ShenWork.Paper1
