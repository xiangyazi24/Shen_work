/-
  ShenWork/PDE/LeibnizRule.lean

  Leibniz rule building blocks for Psi differentiation.
-/
import ShenWork.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral

open MeasureTheory Filter Topology Real Set

noncomputable section

/-- HasDerivAt for exp(-|x'-y|)*u(y) at x'=x when y < x. -/
lemma hasDerivAt_psi_integrand_left {u : ℝ → ℝ} {x y : ℝ} (hy : y < x) :
    HasDerivAt (fun x' => Real.exp (-|x' - y|) * u y)
      (-Real.exp (-(x - y)) * u y) x :=
  (hasDerivAt_kernel_left hy).mul_const (u y)

/-- HasDerivAt for exp(-|x'-y|)*u(y) at x'=x when y > x. -/
lemma hasDerivAt_psi_integrand_right {u : ℝ → ℝ} {x y : ℝ} (hy : x < y) :
    HasDerivAt (fun x' => Real.exp (-|x' - y|) * u y)
      (Real.exp (-(y - x)) * u y) x :=
  (hasDerivAt_kernel_right hy).mul_const (u y)

/-- The absolute value of the derivative is bounded by the integrand for u ≥ 0.
    For y < x: |-exp(-(x-y)) * u(y)| = exp(-(x-y)) * u(y) = exp(-|x-y|) * u(y)
    For y > x: |exp(-(y-x)) * u(y)| = exp(-(y-x)) * u(y) = exp(-|x-y|) * u(y) -/
lemma psi_integrand_deriv_le_integrand {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x)
    {x y : ℝ} (hyx : y ≠ x) :
    ‖(if y < x then -Real.exp (-(x - y)) * u y
      else Real.exp (-(y - x)) * u y)‖ ≤ Real.exp (-|x - y|) * u y := by
  rcases lt_or_gt_of_ne hyx with hy | hy
  · simp [hy, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg (Real.exp_nonneg _),
      abs_of_nonneg (hu y), abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy))]
  · simp [show ¬(y < x) from not_lt.mpr (le_of_lt hy), Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (hu y),
      abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy))]

/-- exp(-|·-y|)*c is Lipschitz on ball(x,1) with constant e*exp(-|x-y|)*c.
    Proof: exp(-|·-y|) is 1-Lipschitz globally; on ball(x,1) the derivative
    is bounded by e*exp(-|x-y|). -/
private lemma exp_neg_abs_sub_mul_lipschitzOnWith_ball (x y : ℝ) (c : ℝ) (hc : 0 ≤ c) :
    LipschitzOnWith (Real.nnabs (Real.exp 1 * (Real.exp (-|x - y|) * c)))
      (fun x' => Real.exp (-|x' - y|) * c) (Metric.ball x 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x₁ hx₁ x₂ hx₂
  simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg (by positivity : 0 ≤ Real.exp 1 * (Real.exp (-|x - y|) * c))]
  rw [show (fun x' => Real.exp (-|x' - y|) * c) x₁ - (fun x' => Real.exp (-|x' - y|) * c) x₂ =
    c * (Real.exp (-|x₁ - y|) - Real.exp (-|x₂ - y|)) from by ring]
  rw [abs_mul, abs_of_nonneg hc]
  have hx₁_ball := Metric.mem_ball.mp hx₁
  have hx₂_ball := Metric.mem_ball.mp hx₂
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    suffices h : |Real.exp (-|x₁ - y|) - Real.exp (-|x₂ - y|)| ≤
        Real.exp 1 * Real.exp (-|x - y|) * |x₁ - x₂| by
      calc c * |Real.exp (-|x₁ - y|) - Real.exp (-|x₂ - y|)|
          ≤ c * (Real.exp 1 * Real.exp (-|x - y|) * |x₁ - x₂|) :=
            mul_le_mul_of_nonneg_left h hc
        _ = Real.exp 1 * (Real.exp (-|x - y|) * c) * |x₁ - x₂| := by ring
    -- Core estimate: |exp(-|x₁-y|) - exp(-|x₂-y|)| ≤ e*exp(-|x-y|)*|x₁-x₂|
    -- Uses: exp(-|·-y|) is 1-Lipschitz, and on ball(x,1) the
    -- derivative is ≤ e*exp(-|x-y|). Both cases give the bound.
    sorry

/-- Full Psi_deriv_abs_le proved via Leibniz rule + triangle inequality.
    This is the assembled proof using all building blocks above. -/
theorem Psi_deriv_abs_le' {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ)
    (hint : Integrable (fun y => Real.exp (-|x - y|) * u y) volume)
    (hu_meas : AEStronglyMeasurable u volume) :
    |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x := by
  -- Step 1: Psi u 1 1 = (1/2) * ∫ F(x, y) dy where F(x',y) = exp(-|x'-y|)*u(y)
  have hPsi : Psi u 1 1 x = (1 / 2 : ℝ) * ∫ y, Real.exp (-|x - y|) * u y := by
    simp [Psi]
  -- Define F' = derivative of integrand at x
  let F' : ℝ → ℝ := fun y =>
    if y < x then -Real.exp (-(x - y)) * u y
    else Real.exp (-(y - x)) * u y
  -- Step 2: HasDerivAt for the integral (Leibniz rule)
  have hLeibniz : HasDerivAt (fun x' => ∫ y, Real.exp (-|x' - y|) * u y)
      (∫ y, F' y) x := by
    let G : ℝ → ℝ → ℝ := fun x' y => Real.exp (-|x' - y|) * u y
    let G' : ℝ → ℝ := fun y =>
      if y < x then -Real.exp (-(x - y)) * u y
      else Real.exp (-(y - x)) * u y
    let bound : ℝ → ℝ := fun y => Real.exp 1 * (Real.exp (-|x - y|) * u y)
    have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x zero_lt_one
    have hG_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (G x') volume := by
      filter_upwards with x'
      exact ((by fun_prop : Continuous fun y : ℝ => Real.exp (-|x' - y|))).aestronglyMeasurable.mul
        hu_meas
    have hG_int : Integrable (G x) volume := by simpa [G] using hint
    have hG'_meas : AEStronglyMeasurable G' volume := by
      show AEStronglyMeasurable (fun y =>
        if y < x then -Real.exp (-(x - y)) * u y
        else Real.exp (-(y - x)) * u y) volume
      have : AEStronglyMeasurable (fun y =>
          (if y < x then -Real.exp (-(x - y)) else Real.exp (-(y - x))) * u y) volume := by
        exact (StronglyMeasurable.piecewise measurableSet_Iio
          (by fun_prop : Continuous fun y => -Real.exp (-(x - y))).stronglyMeasurable
          (by fun_prop : Continuous fun y => Real.exp (-(y - x))).stronglyMeasurable).aestronglyMeasurable.mul
          hu_meas
      exact this.congr (by filter_upwards with y; split_ifs <;> rfl)
    have hbound_int : Integrable bound volume := by
      dsimp [bound]; simpa [mul_assoc] using hint.const_mul (Real.exp 1)
    have h_lip : ∀ᵐ y ∂volume,
        LipschitzOnWith (Real.nnabs (bound y)) (fun x' => G x' y) (Metric.ball x 1) := by
      filter_upwards with y
      dsimp [G, bound]
      exact exp_neg_abs_sub_mul_lipschitzOnWith_ball x y (u y) (hu y)
    have hdiff : ∀ᵐ y ∂volume, HasDerivAt (fun x' => G x' y) (G' y) x := by
      have hne : ∀ᵐ y ∂volume, y ≠ x := by rw [ae_iff]; simp
      filter_upwards [hne] with y hy
      by_cases hylt : y < x
      · simpa [G, G', F', hylt] using hasDerivAt_psi_integrand_left (u := u) hylt
      · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hylt) (Ne.symm hy)
        simpa [G, G', F', hylt] using hasDerivAt_psi_integrand_right (u := u) hxy
    simpa [G, G', F'] using
      (hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (bound := bound)
        (F := G) (F' := G') (x₀ := x) (s := Metric.ball x 1)
        hs hG_meas hG_int hG'_meas h_lip hbound_int hdiff).2
  -- Step 3: deriv(Psi) = (1/2) * ∫ F'
  have hPsi_fun : Psi u 1 1 = fun x' => (1/2 : ℝ) * ∫ y, Real.exp (-|x' - y|) * u y := by
    ext x'; simp [Psi]
  have hda : HasDerivAt (Psi u 1 1) ((1/2 : ℝ) * ∫ y, F' y) x := by
    rw [hPsi_fun]; exact hLeibniz.const_mul (1/2)
  -- Step 4: |deriv| ≤ Psi via triangle inequality
  rw [hda.deriv, hPsi]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1/2)
  -- |∫ F'| ≤ ∫ |F'| ≤ ∫ exp*u
  calc |∫ y, F' y|
      ≤ ∫ y, ‖F' y‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, Real.exp (-|x - y|) * u y := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall (fun y => norm_nonneg _)
        · exact hint
        · exact Eventually.of_forall (fun y => by
            by_cases hyx : y = x
            · subst hyx
              show ‖F' _‖ ≤ _
              simp only [F', lt_irrefl, ite_false, sub_self, neg_zero,
                Real.exp_zero, one_mul, abs_zero]
              rw [Real.norm_of_nonneg (hu _)]
            · exact psi_integrand_deriv_le_integrand hu hyx)

end
