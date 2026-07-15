import ShenWork.Paper1.Theorem12WeightedEnergy

open MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# The weighted lower-order source

The corrected weighted perturbation equation consists of the constant
coefficient principal part

`W_t = W_xx + (c - 2 * eta) W_x + source`.

This file names the complete lower-order source and records its elementary
`L^2` estimate.  The estimate keeps all four coefficient bounds explicit.
Measurability of the source is also stated explicitly: domination by an
integrable function alone does not imply measurability.
-/

/-- The complete nondivergence-form lower-order source in the corrected
weighted perturbation equation. -/
def paper5WeightedLowerOrderSource
    (p : CMParams) (eta c : ℝ)
    (u v : ℝ → ℝ → ℝ) (U : ℝ → ℝ)
    (W Wx Z Zx : ℝ → ℝ) (t x : ℝ) : ℝ :=
  paper5CorrectedJ2Coefficient p eta c u v U t x * W x -
    p.χ * paper5B1 p u v t x * Wx x -
    p.χ * paper5B3 p U x * Zx x +
    p.χ * (eta * paper5B3 p U x - paper5B4 p U x) * Z x

/-- For a classical solution, the named lower-order source is exactly the
material derivative minus the diffusion and constant drift terms. -/
theorem paper5WeightedLowerOrderSource_eq_material_sub_principal_of_classical
    (p : CMParams) {T eta c t x : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V) :
    paper5WeightedLowerOrderSource p eta c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t x =
      paper5WeightedPopulationT eta (paper5CoMovingMaterialTime c u) t x -
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x -
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x := by
  have heq := paper5WeightedPerturbationEquation_corrected_of_classical
    p (η := eta) hsol ht0 htT hTW hu hu1 hv2 hU1 hV2
  unfold paper5WeightedLowerOrderSource
  rw [heq]
  ring

/-- The four-term Cauchy--Schwarz inequality in the scalar form used for the
source estimate. -/
theorem paper5_four_term_sq_le_four_sum_sq (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

/-- Pointwise square bound for the complete lower-order source.  The last
coefficient is bounded by `|chi| * (|eta| * KB3 + KB4)`. -/
theorem paper5WeightedLowerOrderSource_sq_le
    (p : CMParams) {eta c t x KJ2 KB1 KB3 KB4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx : ℝ → ℝ}
    (hJ2 : |paper5CorrectedJ2Coefficient p eta c u v U t x| ≤ KJ2)
    (hB1 : |paper5B1 p u v t x| ≤ KB1)
    (hB3 : |paper5B3 p U x| ≤ KB3)
    (hB4 : |paper5B4 p U x| ≤ KB4) :
    paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2 ≤
      4 *
        (KJ2 ^ 2 * W x ^ 2 +
          (|p.χ| * KB1) ^ 2 * Wx x ^ 2 +
          (|p.χ| * KB3) ^ 2 * Zx x ^ 2 +
          (|p.χ| * (|eta| * KB3 + KB4)) ^ 2 * Z x ^ 2) := by
  have hKJ2 : 0 ≤ KJ2 := (abs_nonneg _).trans hJ2
  have hKB1 : 0 ≤ KB1 := (abs_nonneg _).trans hB1
  have hKB3 : 0 ≤ KB3 := (abs_nonneg _).trans hB3
  have hKB4 : 0 ≤ KB4 := (abs_nonneg _).trans hB4
  let q1 : ℝ :=
    paper5CorrectedJ2Coefficient p eta c u v U t x * W x
  let q2 : ℝ := -p.χ * paper5B1 p u v t x * Wx x
  let q3 : ℝ := -p.χ * paper5B3 p U x * Zx x
  let q4 : ℝ :=
    p.χ * (eta * paper5B3 p U x - paper5B4 p U x) * Z x
  have hq1_abs : |q1| ≤ KJ2 * |W x| := by
    dsimp [q1]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hJ2 (abs_nonneg _)
  have hq2_abs : |q2| ≤ (|p.χ| * KB1) * |Wx x| := by
    dsimp [q2]
    rw [abs_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)) (abs_nonneg _)
  have hq3_abs : |q3| ≤ (|p.χ| * KB3) * |Zx x| := by
    dsimp [q3]
    rw [abs_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB3 (abs_nonneg _)) (abs_nonneg _)
  have hinner_abs :
      |eta * paper5B3 p U x - paper5B4 p U x| ≤
        |eta| * KB3 + KB4 := by
    calc
      |eta * paper5B3 p U x - paper5B4 p U x| ≤
          |eta * paper5B3 p U x| + |paper5B4 p U x| := abs_sub _ _
      _ = |eta| * |paper5B3 p U x| + |paper5B4 p U x| := by
        rw [abs_mul]
      _ ≤ |eta| * KB3 + KB4 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hB3 (abs_nonneg _)) hB4
  have hq4_abs :
      |q4| ≤ (|p.χ| * (|eta| * KB3 + KB4)) * |Z x| := by
    dsimp [q4]
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinner_abs (abs_nonneg _)) (abs_nonneg _)
  have hq1_sq : q1 ^ 2 ≤ KJ2 ^ 2 * W x ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg q1)
      (mul_nonneg hKJ2 (abs_nonneg (W x)))).2 hq1_abs
    simpa only [sq_abs, mul_pow] using hsq
  have hq2_sq : q2 ^ 2 ≤ (|p.χ| * KB1) ^ 2 * Wx x ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg q2)
      (mul_nonneg (mul_nonneg (abs_nonneg _) hKB1) (abs_nonneg (Wx x)))).2
        hq2_abs
    simpa only [sq_abs, mul_pow] using hsq
  have hq3_sq : q3 ^ 2 ≤ (|p.χ| * KB3) ^ 2 * Zx x ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg q3)
      (mul_nonneg (mul_nonneg (abs_nonneg _) hKB3) (abs_nonneg (Zx x)))).2
        hq3_abs
    simpa only [sq_abs, mul_pow] using hsq
  have hq4_sq :
      q4 ^ 2 ≤ (|p.χ| * (|eta| * KB3 + KB4)) ^ 2 * Z x ^ 2 := by
    have hcoeff : 0 ≤ |p.χ| * (|eta| * KB3 + KB4) := by positivity
    have hsq := (sq_le_sq₀ (abs_nonneg q4)
      (mul_nonneg hcoeff (abs_nonneg (Z x)))).2 hq4_abs
    simpa only [sq_abs, mul_pow] using hsq
  calc
    paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2 =
        (q1 + q2 + q3 + q4) ^ 2 := by
      dsimp [q1, q2, q3, q4, paper5WeightedLowerOrderSource]
      ring
    _ ≤ 4 * (q1 ^ 2 + q2 ^ 2 + q3 ^ 2 + q4 ^ 2) :=
      paper5_four_term_sq_le_four_sum_sq q1 q2 q3 q4
    _ ≤ 4 *
        (KJ2 ^ 2 * W x ^ 2 +
          (|p.χ| * KB1) ^ 2 * Wx x ^ 2 +
          (|p.χ| * KB3) ^ 2 * Zx x ^ 2 +
          (|p.χ| * (|eta| * KB3 + KB4)) ^ 2 * Z x ^ 2) := by
      nlinarith

/-- The complete lower-order source is square-integrable, with the explicit
four-square integral bound.  `hsource_meas` is the unavoidable measurability
input; in applications it is supplied by the positive-time regularity of the
classical solution. -/
theorem paper5WeightedLowerOrderSource_sq_integrable_and_integral_le
    (p : CMParams) {eta c t KJ2 KB1 KB3 KB4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx : ℝ → ℝ}
    (hsource_meas : AEStronglyMeasurable
      (paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t))
    (hJ2 : ∀ x,
      |paper5CorrectedJ2Coefficient p eta c u v U t x| ≤ KJ2)
    (hB1 : ∀ x, |paper5B1 p u v t x| ≤ KB1)
    (hB3 : ∀ x, |paper5B3 p U x| ≤ KB3)
    (hB4 : ∀ x, |paper5B4 p U x| ≤ KB4)
    (hW2 : Integrable (fun x : ℝ => W x ^ 2))
    (hWx2 : Integrable (fun x : ℝ => Wx x ^ 2))
    (hZ2 : Integrable (fun x : ℝ => Z x ^ 2))
    (hZx2 : Integrable (fun x : ℝ => Zx x ^ 2)) :
    Integrable (fun x : ℝ =>
        paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2) ∧
      (∫ x : ℝ,
          paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2) ≤
        4 *
          (KJ2 ^ 2 * (∫ x : ℝ, W x ^ 2) +
            (|p.χ| * KB1) ^ 2 * (∫ x : ℝ, Wx x ^ 2) +
            (|p.χ| * KB3) ^ 2 * (∫ x : ℝ, Zx x ^ 2) +
            (|p.χ| * (|eta| * KB3 + KB4)) ^ 2 *
              (∫ x : ℝ, Z x ^ 2)) := by
  let f1 : ℝ → ℝ := fun x => KJ2 ^ 2 * W x ^ 2
  let f2 : ℝ → ℝ := fun x => (|p.χ| * KB1) ^ 2 * Wx x ^ 2
  let f3 : ℝ → ℝ := fun x => (|p.χ| * KB3) ^ 2 * Zx x ^ 2
  let f4 : ℝ → ℝ := fun x =>
    (|p.χ| * (|eta| * KB3 + KB4)) ^ 2 * Z x ^ 2
  let majorant : ℝ → ℝ := fun x =>
    4 * (f1 x + f2 x + f3 x + f4 x)
  have hf1 : Integrable f1 := by
    simpa only [f1] using hW2.const_mul (KJ2 ^ 2)
  have hf2 : Integrable f2 := by
    simpa only [f2] using hWx2.const_mul ((|p.χ| * KB1) ^ 2)
  have hf3 : Integrable f3 := by
    simpa only [f3] using hZx2.const_mul ((|p.χ| * KB3) ^ 2)
  have hf4 : Integrable f4 := by
    simpa only [f4] using
      hZ2.const_mul ((|p.χ| * (|eta| * KB3 + KB4)) ^ 2)
  have hf12 : Integrable (fun x => f1 x + f2 x) := hf1.add hf2
  have hf123 : Integrable (fun x => f1 x + f2 x + f3 x) :=
    hf12.add hf3
  have hsum : Integrable (fun x => f1 x + f2 x + f3 x + f4 x) :=
    hf123.add hf4
  have hmajorant : Integrable majorant := by
    simpa only [majorant] using hsum.const_mul 4
  have hpoint : ∀ x,
      paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2 ≤
        majorant x := by
    intro x
    simpa only [majorant, f1, f2, f3, f4] using
      paper5WeightedLowerOrderSource_sq_le p
        (hJ2 x) (hB1 x) (hB3 x) (hB4 x)
  have hsource_sq : Integrable (fun x : ℝ =>
      paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2) := by
    refine Integrable.mono' hmajorant (hsource_meas.pow 2) ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hsource_sq, ?_⟩
  calc
    (∫ x : ℝ,
        paper5WeightedLowerOrderSource p eta c u v U W Wx Z Zx t x ^ 2) ≤
        ∫ x : ℝ, majorant x :=
      integral_mono hsource_sq hmajorant hpoint
    _ = 4 *
          (KJ2 ^ 2 * (∫ x : ℝ, W x ^ 2) +
            (|p.χ| * KB1) ^ 2 * (∫ x : ℝ, Wx x ^ 2) +
            (|p.χ| * KB3) ^ 2 * (∫ x : ℝ, Zx x ^ 2) +
            (|p.χ| * (|eta| * KB3 + KB4)) ^ 2 *
              (∫ x : ℝ, Z x ^ 2)) := by
      rw [show majorant = fun x => 4 * (f1 x + f2 x + f3 x + f4 x) by rfl,
        integral_const_mul,
        integral_add hf123 hf4,
        integral_add hf12 hf3,
        integral_add hf1 hf2]
      simp only [f1, f2, f3, f4, integral_const_mul]

end ShenWork.Paper1

#print axioms ShenWork.Paper1.paper5WeightedLowerOrderSource_eq_material_sub_principal_of_classical
#print axioms ShenWork.Paper1.paper5_four_term_sq_le_four_sum_sq
#print axioms ShenWork.Paper1.paper5WeightedLowerOrderSource_sq_le
#print axioms ShenWork.Paper1.paper5WeightedLowerOrderSource_sq_integrable_and_integral_le
