import ShenWork.Paper1.WholeLineWeightedRegularityL2History

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Strong `L²` continuity under bounded time-dependent coefficients

The weighted generator forcing is a finite sum of bounded coefficient
fields multiplying weighted population and resolver fields.  This file
records the scalar `L²` closure needed to pass from strong continuity of
those fields and uniform convergence of the coefficients to strong
continuity of each product.  No stronger exponential weight or pointwise
spatial dominator is used.
-/

/-- Pointwise square estimate for a varying bounded coefficient multiplying
a varying scalar field. -/
theorem mul_sub_mul_sq_le_of_abs_le
    {a b u v B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ha : |a| ≤ B) (hab : |a - b| ≤ D) :
    (a * u - b * v) ^ 2 ≤
      2 * B ^ 2 * (u - v) ^ 2 + 2 * D ^ 2 * v ^ 2 := by
  have hsplit : a * u - b * v = a * (u - v) + (a - b) * v := by ring
  rw [hsplit]
  have hsum : (a * (u - v) + (a - b) * v) ^ 2 ≤
      2 * (a * (u - v)) ^ 2 + 2 * ((a - b) * v) ^ 2 := by
    nlinarith [sq_nonneg (a * (u - v) - (a - b) * v)]
  have ha_sq : a ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg a) hB).2 ha
  have hab_sq : (a - b) ^ 2 ≤ D ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a - b)) hD).2 hab
  calc
    (a * (u - v) + (a - b) * v) ^ 2 ≤
        2 * (a * (u - v)) ^ 2 + 2 * ((a - b) * v) ^ 2 := hsum
    _ = 2 * a ^ 2 * (u - v) ^ 2 +
        2 * (a - b) ^ 2 * v ^ 2 := by ring
    _ ≤ 2 * B ^ 2 * (u - v) ^ 2 + 2 * D ^ 2 * v ^ 2 := by
      gcongr

/-- Integrable-data form of the bounded-coefficient product estimate. -/
theorem integral_mul_sub_mul_sq_data
    {a b u v : ℝ → ℝ} {B D : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ha : ∀ x, |a x| ≤ B) (hab : ∀ x, |a x - b x| ≤ D)
    (hout_meas : AEStronglyMeasurable
      (fun x => a x * u x - b x * v x) volume)
    (huv : Integrable (fun x => (u x - v x) ^ 2) volume)
    (hv : Integrable (fun x => v x ^ 2) volume) :
    Integrable (fun x => (a x * u x - b x * v x) ^ 2) volume ∧
      (∫ x : ℝ, (a x * u x - b x * v x) ^ 2) ≤
        2 * B ^ 2 * (∫ x : ℝ, (u x - v x) ^ 2) +
          2 * D ^ 2 * (∫ x : ℝ, v x ^ 2) := by
  let major : ℝ → ℝ := fun x =>
    2 * B ^ 2 * (u x - v x) ^ 2 + 2 * D ^ 2 * v x ^ 2
  have hmajor : Integrable major volume :=
    (huv.const_mul (2 * B ^ 2)).add (hv.const_mul (2 * D ^ 2))
  have hpoint : ∀ x,
      (a x * u x - b x * v x) ^ 2 ≤ major x := by
    intro x
    exact mul_sub_mul_sq_le_of_abs_le hB hD (ha x) (hab x)
  have hout : Integrable
      (fun x => (a x * u x - b x * v x) ^ 2) volume := by
    refine hmajor.mono' (hout_meas.pow 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ, (a x * u x - b x * v x) ^ 2) ≤
        ∫ x : ℝ, major x := integral_mono hout hmajor hpoint
    _ = 2 * B ^ 2 * (∫ x : ℝ, (u x - v x) ^ 2) +
          2 * D ^ 2 * (∫ x : ℝ, v x ^ 2) := by
      dsimp only [major]
      rw [integral_add, integral_const_mul, integral_const_mul]
      · exact huv.const_mul _
      · exact hv.const_mul _

/-- Uniform coefficient convergence and strong scalar `L²` convergence of a
field imply strong `L²` convergence of their product.  The coefficient
modulus is explicit, which is the form produced by the canonical BUC time
regularity estimates. -/
theorem tendsto_integral_mul_sub_mul_sq_zero
    {a u : ℝ → ℝ → ℝ} {t B : ℝ} {D : ℝ → ℝ}
    (hB : 0 ≤ B)
    (hD_nonneg : ∀ᶠ s in 𝓝 t, 0 ≤ D s)
    (hD : Tendsto D (𝓝 t) (𝓝 0))
    (ha : ∀ᶠ s in 𝓝 t, ∀ x, |a s x| ≤ B)
    (hadiff : ∀ᶠ s in 𝓝 t, ∀ x,
      |a s x - a t x| ≤ D s)
    (hout_meas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x => a s x * u s x - a t x * u t x) volume)
    (hut : Integrable (fun x => u t x ^ 2) volume)
    (hudiff : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (u s x - u t x) ^ 2) volume)
    (hudiff_zero : Tendsto
      (fun s => ∫ x : ℝ, (u s x - u t x) ^ 2)
      (𝓝 t) (𝓝 0)) :
    Tendsto
      (fun s => ∫ x : ℝ,
        (a s x * u s x - a t x * u t x) ^ 2)
      (𝓝 t) (𝓝 0) := by
  let upper : ℝ → ℝ := fun s =>
    2 * B ^ 2 * (∫ x : ℝ, (u s x - u t x) ^ 2) +
      2 * D s ^ 2 * (∫ x : ℝ, u t x ^ 2)
  have hupper_zero : Tendsto upper (𝓝 t) (𝓝 0) := by
    have hfirst := hudiff_zero.const_mul (2 * B ^ 2)
    have hsecond := (hD.pow 2).const_mul
      (2 * (∫ x : ℝ, u t x ^ 2))
    convert hfirst.add hsecond using 1
    · funext s
      dsimp only [upper]
      ring_nf
    · ring_nf
  have hupper : ∀ᶠ s in 𝓝 t,
      (∫ x : ℝ,
        (a s x * u s x - a t x * u t x) ^ 2) ≤ upper s := by
    filter_upwards [hD_nonneg, ha, hadiff, hout_meas, hudiff]
      with s hsD hsa hsad hsmeas hsint
    have hdata := integral_mul_sub_mul_sq_data hB hsD hsa hsad
      hsmeas hsint hut
    simpa only [upper] using hdata.2
  exact squeeze_zero'
    (Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _)
    hupper hupper_zero

/-- Integrable-data closure for a sum of four strongly `L²` varying scalar
fields. -/
theorem integral_four_sum_sub_sq_data
    {f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ : ℝ → ℝ}
    (hout_meas : AEStronglyMeasurable (fun x =>
      (f₁ x + f₂ x + f₃ x + f₄ x) -
        (g₁ x + g₂ x + g₃ x + g₄ x)) volume)
    (h₁ : Integrable (fun x => (f₁ x - g₁ x) ^ 2) volume)
    (h₂ : Integrable (fun x => (f₂ x - g₂ x) ^ 2) volume)
    (h₃ : Integrable (fun x => (f₃ x - g₃ x) ^ 2) volume)
    (h₄ : Integrable (fun x => (f₄ x - g₄ x) ^ 2) volume) :
    Integrable (fun x =>
      ((f₁ x + f₂ x + f₃ x + f₄ x) -
        (g₁ x + g₂ x + g₃ x + g₄ x)) ^ 2) volume ∧
      (∫ x : ℝ,
        ((f₁ x + f₂ x + f₃ x + f₄ x) -
          (g₁ x + g₂ x + g₃ x + g₄ x)) ^ 2) ≤
        4 * ((∫ x : ℝ, (f₁ x - g₁ x) ^ 2) +
          (∫ x : ℝ, (f₂ x - g₂ x) ^ 2) +
          (∫ x : ℝ, (f₃ x - g₃ x) ^ 2) +
          (∫ x : ℝ, (f₄ x - g₄ x) ^ 2)) := by
  let major : ℝ → ℝ := fun x => 4 *
    ((f₁ x - g₁ x) ^ 2 + (f₂ x - g₂ x) ^ 2 +
      (f₃ x - g₃ x) ^ 2 + (f₄ x - g₄ x) ^ 2)
  have hmajor : Integrable major volume :=
    (((h₁.add h₂).add h₃).add h₄).const_mul 4
  have h₁₂ : Integrable (fun x =>
      (f₁ x - g₁ x) ^ 2 + (f₂ x - g₂ x) ^ 2) volume := by
    simpa only [Pi.add_apply] using h₁.add h₂
  have h₁₂₃ : Integrable (fun x =>
      (f₁ x - g₁ x) ^ 2 + (f₂ x - g₂ x) ^ 2 +
        (f₃ x - g₃ x) ^ 2) volume := by
    simpa only [Pi.add_apply] using h₁₂.add h₃
  have hpoint : ∀ x,
      ((f₁ x + f₂ x + f₃ x + f₄ x) -
        (g₁ x + g₂ x + g₃ x + g₄ x)) ^ 2 ≤ major x := by
    intro x
    let d₁ := f₁ x - g₁ x
    let d₂ := f₂ x - g₂ x
    let d₃ := f₃ x - g₃ x
    let d₄ := f₄ x - g₄ x
    have hs : (d₁ + d₂ + d₃ + d₄) ^ 2 ≤
        4 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2 + d₄ ^ 2) := by
      nlinarith [sq_nonneg (d₁ - d₂), sq_nonneg (d₁ - d₃),
        sq_nonneg (d₁ - d₄), sq_nonneg (d₂ - d₃),
        sq_nonneg (d₂ - d₄), sq_nonneg (d₃ - d₄)]
    dsimp only [major]
    dsimp only [d₁, d₂, d₃, d₄] at hs
    convert hs using 1
    all_goals ring_nf
  have hout : Integrable (fun x =>
      ((f₁ x + f₂ x + f₃ x + f₄ x) -
        (g₁ x + g₂ x + g₃ x + g₄ x)) ^ 2) volume := by
    refine hmajor.mono' (hout_meas.pow 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hout, ?_⟩
  calc
    (∫ x : ℝ,
        ((f₁ x + f₂ x + f₃ x + f₄ x) -
          (g₁ x + g₂ x + g₃ x + g₄ x)) ^ 2) ≤
        ∫ x : ℝ, major x := integral_mono hout hmajor hpoint
    _ = 4 * ((∫ x : ℝ, (f₁ x - g₁ x) ^ 2) +
          (∫ x : ℝ, (f₂ x - g₂ x) ^ 2) +
          (∫ x : ℝ, (f₃ x - g₃ x) ^ 2) +
          (∫ x : ℝ, (f₄ x - g₄ x) ^ 2)) := by
      dsimp only [major]
      rw [integral_const_mul]
      congr 1
      rw [integral_add h₁₂₃ h₄,
        integral_add h₁₂ h₃,
        integral_add h₁ h₂]

/-- Four convergent scalar `L²` trajectories may be added without any
pointwise common dominator. -/
theorem tendsto_integral_four_sum_sub_sq_zero
    {f₁ f₂ f₃ f₄ : ℝ → ℝ → ℝ} {t : ℝ}
    (hout_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x =>
      (f₁ s x + f₂ s x + f₃ s x + f₄ s x) -
        (f₁ t x + f₂ t x + f₃ t x + f₄ t x)) volume)
    (h₁int : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (f₁ s x - f₁ t x) ^ 2) volume)
    (h₂int : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (f₂ s x - f₂ t x) ^ 2) volume)
    (h₃int : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (f₃ s x - f₃ t x) ^ 2) volume)
    (h₄int : ∀ᶠ s in 𝓝 t,
      Integrable (fun x => (f₄ s x - f₄ t x) ^ 2) volume)
    (h₁ : Tendsto (fun s => ∫ x : ℝ, (f₁ s x - f₁ t x) ^ 2)
      (𝓝 t) (𝓝 0))
    (h₂ : Tendsto (fun s => ∫ x : ℝ, (f₂ s x - f₂ t x) ^ 2)
      (𝓝 t) (𝓝 0))
    (h₃ : Tendsto (fun s => ∫ x : ℝ, (f₃ s x - f₃ t x) ^ 2)
      (𝓝 t) (𝓝 0))
    (h₄ : Tendsto (fun s => ∫ x : ℝ, (f₄ s x - f₄ t x) ^ 2)
      (𝓝 t) (𝓝 0)) :
    Tendsto (fun s => ∫ x : ℝ,
      ((f₁ s x + f₂ s x + f₃ s x + f₄ s x) -
        (f₁ t x + f₂ t x + f₃ t x + f₄ t x)) ^ 2)
      (𝓝 t) (𝓝 0) := by
  let upper : ℝ → ℝ := fun s => 4 *
    ((∫ x : ℝ, (f₁ s x - f₁ t x) ^ 2) +
      (∫ x : ℝ, (f₂ s x - f₂ t x) ^ 2) +
      (∫ x : ℝ, (f₃ s x - f₃ t x) ^ 2) +
      (∫ x : ℝ, (f₄ s x - f₄ t x) ^ 2))
  have hupper_zero : Tendsto upper (𝓝 t) (𝓝 0) := by
    have hsum := ((h₁.add h₂).add h₃).add h₄
    simpa only [upper, zero_add, mul_zero] using hsum.const_mul 4
  have hupper : ∀ᶠ s in 𝓝 t,
      (∫ x : ℝ,
        ((f₁ s x + f₂ s x + f₃ s x + f₄ s x) -
          (f₁ t x + f₂ t x + f₃ t x + f₄ t x)) ^ 2) ≤
        upper s := by
    filter_upwards [hout_meas, h₁int, h₂int, h₃int, h₄int]
      with s hsmeas hs₁ hs₂ hs₃ hs₄
    simpa only [upper] using
      (integral_four_sum_sub_sq_data hsmeas hs₁ hs₂ hs₃ hs₄).2
  exact squeeze_zero'
    (Eventually.of_forall fun s => integral_nonneg fun x => sq_nonneg _)
    hupper hupper_zero

section AxiomAudit

#print axioms mul_sub_mul_sq_le_of_abs_le
#print axioms integral_mul_sub_mul_sq_data
#print axioms tendsto_integral_mul_sub_mul_sq_zero
#print axioms integral_four_sum_sub_sq_data
#print axioms tendsto_integral_four_sum_sub_sq_zero

end AxiomAudit

end ShenWork.Paper1
