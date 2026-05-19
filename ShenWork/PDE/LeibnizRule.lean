/-
  ShenWork/PDE/LeibnizRule.lean

  Leibniz rule building blocks for Psi differentiation.
-/
import ShenWork.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue

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

/-- HasDerivAt for exp(-a*|x'-y|)*u(y) at x'=x when y < x. -/
lemma hasDerivAt_psi_integrand_left_general {u : ℝ → ℝ} {a x y : ℝ}
    (hy : y < x) :
    HasDerivAt (fun x' => Real.exp (-a * |x' - y|) * u y)
      (-a * Real.exp (-a * (x - y)) * u y) x := by
  have hev : (fun x' => Real.exp (-a * |x' - y|) * u y) =ᶠ[𝓝 x]
      (fun x' => Real.exp (-a * (x' - y)) * u y) := by
    filter_upwards [Ioi_mem_nhds hy] with x' hx'
    congr 2
    rw [abs_of_pos (sub_pos.mpr hx')]
  have hder :=
    (((((hasDerivAt_id x).sub_const y).const_mul (-a)).exp).mul_const (u y))
  have hder0 := hev.hasDerivAt_iff.mpr hder
  change HasDerivAt (fun x' => Real.exp (-a * |x' - y|) * u y)
    (Real.exp (-a * (x - y)) * (-a * 1) * u y) x at hder0
  convert hder0 using 1
  ring_nf

/-- HasDerivAt for exp(-a*|x'-y|)*u(y) at x'=x when y > x. -/
lemma hasDerivAt_psi_integrand_right_general {u : ℝ → ℝ} {a x y : ℝ}
    (hy : x < y) :
    HasDerivAt (fun x' => Real.exp (-a * |x' - y|) * u y)
      (a * Real.exp (-a * (y - x)) * u y) x := by
  have hev : (fun x' => Real.exp (-a * |x' - y|) * u y) =ᶠ[𝓝 x]
      (fun x' => Real.exp (a * (x' - y)) * u y) := by
    filter_upwards [Iio_mem_nhds hy] with x' hx'
    show Real.exp (-a * |x' - y|) * u y = Real.exp (a * (x' - y)) * u y
    congr 2
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hx'))]
    ring
  have hder :
      HasDerivAt (fun x' => Real.exp (a * (x' - y)) * u y)
        (Real.exp (a * (x - y)) * (a * 1) * u y) x :=
    (((hasDerivAt_id x).sub_const y).const_mul a).exp.mul_const (u y)
  convert hev.hasDerivAt_iff.mpr hder using 2 <;> ring_nf

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

/-- |exp(-a) - exp(-b)| ≤ exp(-min a b) * |a - b| for a, b ≥ 0. -/
private lemma exp_neg_abs_sub_le (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-min a b) * |a - b| := by
  have hderiv_any : ∀ (s : Set ℝ) (x' : ℝ),
      HasDerivWithinAt (fun t => Real.exp (-t)) (-Real.exp (-x')) s x' := by
    intro s x'; simpa [mul_comm] using ((hasDerivAt_id' x').neg.exp).hasDerivWithinAt (s := s)
  have hordered : ∀ {u v : ℝ}, u ≤ v →
      |Real.exp (-u) - Real.exp (-v)| ≤ Real.exp (-u) * |u - v| := by
    intro u v huv
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t => Real.exp (-t)) (f' := fun t => -Real.exp (-t))
      (a := u) (b := v) (C := Real.exp (-u))
      (fun x' _hx' => hderiv_any _ x')
      (fun x' hx' => by
        simp only [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (neg_le_neg hx'.1))
      v ⟨huv, le_rfl⟩
    calc |Real.exp (-u) - Real.exp (-v)|
        = ‖(fun t => Real.exp (-t)) v - (fun t => Real.exp (-t)) u‖ := by
          simp [Real.norm_eq_abs, abs_sub_comm]
      _ ≤ Real.exp (-u) * (v - u) := hseg
      _ = Real.exp (-u) * |u - v| := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv)]
  by_cases hab : a ≤ b
  · calc |Real.exp (-a) - Real.exp (-b)| ≤ Real.exp (-a) * |a - b| := hordered hab
      _ = Real.exp (-min a b) * |a - b| := by rw [min_eq_left hab]
  · push_neg at hab
    calc |Real.exp (-a) - Real.exp (-b)| = |Real.exp (-b) - Real.exp (-a)| := abs_sub_comm _ _
      _ ≤ Real.exp (-b) * |b - a| := hordered (le_of_lt hab)
      _ = Real.exp (-min a b) * |a - b| := by rw [min_eq_right (le_of_lt hab), abs_sub_comm]

/-- exp(-|·-y|)*c is Lipschitz on ball(x,1) with constant e*exp(-|x-y|)*c. -/
private lemma exp_neg_abs_sub_mul_lipschitzOnWith_ball (x y : ℝ) (c : ℝ) (hc : 0 ≤ c) :
    LipschitzOnWith (Real.nnabs (Real.exp 1 * (Real.exp (-|x - y|) * c)))
      (fun x' => Real.exp (-|x' - y|) * c) (Metric.ball x 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x₁ hx₁ x₂ hx₂
  simp only [Real.dist_eq, NNReal.coe_mk, Real.coe_nnabs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp 1 * (Real.exp (-|x - y|) * c))]
  rw [show (fun x' => Real.exp (-|x' - y|) * c) x₁ - (fun x' => Real.exp (-|x' - y|) * c) x₂ =
    c * (Real.exp (-|x₁ - y|) - Real.exp (-|x₂ - y|)) from by ring]
  rw [abs_mul, abs_of_nonneg hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hx₁b : |x₁ - x| < 1 := Real.dist_eq x₁ x ▸ Metric.mem_ball.mp hx₁
    have hx₂b : |x₂ - x| < 1 := Real.dist_eq x₂ x ▸ Metric.mem_ball.mp hx₂
    have hmin_ge : |x - y| - 1 ≤ min (|x₁ - y|) (|x₂ - y|) := by
      apply le_min
      · have h := (le_abs_self (|x - y| - |x₁ - y|)).trans
            (abs_abs_sub_abs_le_abs_sub (x - y) (x₁ - y))
        rw [show (x - y) - (x₁ - y) = -(x₁ - x) from by ring, abs_neg] at h; linarith
      · have h := (le_abs_self (|x - y| - |x₂ - y|)).trans
            (abs_abs_sub_abs_le_abs_sub (x - y) (x₂ - y))
        rw [show (x - y) - (x₂ - y) = -(x₂ - x) from by ring, abs_neg] at h; linarith
    have h_rev : abs (|x₁ - y| - |x₂ - y|) ≤ |x₁ - x₂| := by
      calc abs (|x₁ - y| - |x₂ - y|)
          ≤ |(x₁ - y) - (x₂ - y)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |x₁ - x₂| := by congr 1; ring
    have h_exp := exp_neg_abs_sub_le (|x₁ - y|) (|x₂ - y|) (abs_nonneg _) (abs_nonneg _)
    calc c * |Real.exp (-|x₁ - y|) - Real.exp (-|x₂ - y|)|
        ≤ c * (Real.exp (-min (|x₁ - y|) (|x₂ - y|)) * abs (|x₁ - y| - |x₂ - y|)) :=
          mul_le_mul_of_nonneg_left h_exp hc
      _ ≤ c * (Real.exp (-(|x - y| - 1)) * |x₁ - x₂|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul
            (Real.exp_le_exp.mpr (neg_le_neg hmin_ge)) h_rev (abs_nonneg _) (Real.exp_pos _).le) hc
      _ = Real.exp 1 * (Real.exp (-|x - y|) * c) * |x₁ - x₂| := by
          rw [show -(|x - y| - 1) = 1 + (-|x - y|) from by ring, Real.exp_add]; ring

/-- `exp(-a*|·-y|)*c` is locally Lipschitz, with an integrable bound after
multiplication by a bounded nonnegative profile. -/
private lemma exp_neg_mul_abs_sub_mul_lipschitzOnWith_ball
    {a : ℝ} (ha : 0 < a) (x y : ℝ) (c : ℝ) (hc : 0 ≤ c) :
    LipschitzOnWith
      (Real.nnabs (a * Real.exp a * (Real.exp (-a * |x - y|) * c)))
      (fun x' => Real.exp (-a * |x' - y|) * c) (Metric.ball x 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x₁ hx₁ x₂ hx₂
  have hcoef_nonneg :
      0 ≤ a * Real.exp a * (Real.exp (-a * |x - y|) * c) := by
    exact mul_nonneg (mul_nonneg ha.le (Real.exp_pos a).le)
      (mul_nonneg (Real.exp_pos (-a * |x - y|)).le hc)
  simp only [Real.dist_eq, NNReal.coe_mk, Real.coe_nnabs]
  rw [abs_of_nonneg hcoef_nonneg]
  rw [show (fun x' => Real.exp (-a * |x' - y|) * c) x₁ -
      (fun x' => Real.exp (-a * |x' - y|) * c) x₂ =
        c * (Real.exp (-a * |x₁ - y|) - Real.exp (-a * |x₂ - y|)) from by ring]
  rw [abs_mul, abs_of_nonneg hc]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hx₁b : |x₁ - x| < 1 := Real.dist_eq x₁ x ▸ Metric.mem_ball.mp hx₁
    have hx₂b : |x₂ - x| < 1 := Real.dist_eq x₂ x ▸ Metric.mem_ball.mp hx₂
    have hmin_ge : a * |x - y| - a ≤ min (a * |x₁ - y|) (a * |x₂ - y|) := by
      apply le_min
      · have h := (le_abs_self (|x - y| - |x₁ - y|)).trans
            (abs_abs_sub_abs_le_abs_sub (x - y) (x₁ - y))
        rw [show (x - y) - (x₁ - y) = -(x₁ - x) from by ring, abs_neg] at h
        nlinarith
      · have h := (le_abs_self (|x - y| - |x₂ - y|)).trans
            (abs_abs_sub_abs_le_abs_sub (x - y) (x₂ - y))
        rw [show (x - y) - (x₂ - y) = -(x₂ - x) from by ring, abs_neg] at h
        nlinarith
    have h_absdist : abs (|x₁ - y| - |x₂ - y|) ≤ |x₁ - x₂| := by
      calc abs (|x₁ - y| - |x₂ - y|)
          ≤ |(x₁ - y) - (x₂ - y)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |x₁ - x₂| := by congr 1; ring
    have h_exp :=
      exp_neg_abs_sub_le (a * |x₁ - y|) (a * |x₂ - y|)
        (mul_nonneg ha.le (abs_nonneg _))
        (mul_nonneg ha.le (abs_nonneg _))
    have h_exp' :
        |Real.exp (-a * |x₁ - y|) - Real.exp (-a * |x₂ - y|)| ≤
          Real.exp (-min (a * |x₁ - y|) (a * |x₂ - y|)) *
            |a * (|x₁ - y|) - a * (|x₂ - y|)| := by
      simpa using h_exp
    have h_arg :
        |a * (|x₁ - y|) - a * (|x₂ - y|)| ≤ a * |x₁ - x₂| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ha.le]
      exact mul_le_mul_of_nonneg_left h_absdist ha.le
    calc
      c * |Real.exp (-a * |x₁ - y|) - Real.exp (-a * |x₂ - y|)|
          ≤ c * (Real.exp (-min (a * |x₁ - y|) (a * |x₂ - y|)) *
              |a * (|x₁ - y|) - a * (|x₂ - y|)|) :=
            mul_le_mul_of_nonneg_left h_exp' hc
      _ ≤ c * (Real.exp (-(a * |x - y| - a)) * (a * |x₁ - x₂|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hmin_ge)) h_arg
                (abs_nonneg _) (Real.exp_pos _).le) hc
      _ = a * Real.exp a * (Real.exp (-a * |x - y|) * c) * |x₁ - x₂| := by
            rw [show -(a * |x - y| - a) = a + (-a * |x - y|) by ring,
              Real.exp_add]
            ring

/-- Arbitrary-sign version of the local Lipschitz bound, controlled by `|c|`. -/
private lemma exp_neg_mul_abs_sub_mul_lipschitzOnWith_ball_abs
    {a : ℝ} (ha : 0 < a) (x y c : ℝ) :
    LipschitzOnWith
      (Real.nnabs (a * Real.exp a * (Real.exp (-a * |x - y|) * |c|)))
      (fun x' => Real.exp (-a * |x' - y|) * c) (Metric.ball x 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x₁ hx₁ x₂ hx₂
  have hcoef_nonneg :
      0 ≤ a * Real.exp a * (Real.exp (-a * |x - y|) * |c|) := by
    exact mul_nonneg (mul_nonneg ha.le (Real.exp_pos a).le)
      (mul_nonneg (Real.exp_pos (-a * |x - y|)).le (abs_nonneg c))
  simp only [Real.dist_eq, NNReal.coe_mk, Real.coe_nnabs]
  rw [abs_of_nonneg hcoef_nonneg]
  rw [show (fun x' => Real.exp (-a * |x' - y|) * c) x₁ -
      (fun x' => Real.exp (-a * |x' - y|) * c) x₂ =
        c * (Real.exp (-a * |x₁ - y|) - Real.exp (-a * |x₂ - y|)) from by ring]
  rw [abs_mul]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hx₁b : |x₁ - x| < 1 := Real.dist_eq x₁ x ▸ Metric.mem_ball.mp hx₁
    have hx₂b : |x₂ - x| < 1 := Real.dist_eq x₂ x ▸ Metric.mem_ball.mp hx₂
    have hmin_ge : a * |x - y| - a ≤ min (a * |x₁ - y|) (a * |x₂ - y|) := by
      apply le_min
      · have h := (le_abs_self (|x - y| - |x₁ - y|)).trans
            (abs_abs_sub_abs_le_abs_sub (x - y) (x₁ - y))
        rw [show (x - y) - (x₁ - y) = -(x₁ - x) from by ring, abs_neg] at h
        nlinarith
      · have h := (le_abs_self (|x - y| - |x₂ - y|)).trans
            (abs_abs_sub_abs_le_abs_sub (x - y) (x₂ - y))
        rw [show (x - y) - (x₂ - y) = -(x₂ - x) from by ring, abs_neg] at h
        nlinarith
    have h_absdist : abs (|x₁ - y| - |x₂ - y|) ≤ |x₁ - x₂| := by
      calc abs (|x₁ - y| - |x₂ - y|)
          ≤ |(x₁ - y) - (x₂ - y)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |x₁ - x₂| := by congr 1; ring
    have h_exp :=
      exp_neg_abs_sub_le (a * |x₁ - y|) (a * |x₂ - y|)
        (mul_nonneg ha.le (abs_nonneg _))
        (mul_nonneg ha.le (abs_nonneg _))
    have h_exp' :
        |Real.exp (-a * |x₁ - y|) - Real.exp (-a * |x₂ - y|)| ≤
          Real.exp (-min (a * |x₁ - y|) (a * |x₂ - y|)) *
            |a * (|x₁ - y|) - a * (|x₂ - y|)| := by
      simpa using h_exp
    have h_arg :
        |a * (|x₁ - y|) - a * (|x₂ - y|)| ≤ a * |x₁ - x₂| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ha.le]
      exact mul_le_mul_of_nonneg_left h_absdist ha.le
    calc
      |c| * |Real.exp (-a * |x₁ - y|) - Real.exp (-a * |x₂ - y|)|
          ≤ |c| * (Real.exp (-min (a * |x₁ - y|) (a * |x₂ - y|)) *
              |a * (|x₁ - y|) - a * (|x₂ - y|)|) :=
            mul_le_mul_of_nonneg_left h_exp' (abs_nonneg c)
      _ ≤ |c| * (Real.exp (-(a * |x - y| - a)) * (a * |x₁ - x₂|)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.exp_le_exp.mpr (neg_le_neg hmin_ge)) h_arg
                (abs_nonneg _) (Real.exp_pos _).le) (abs_nonneg c)
      _ = a * Real.exp a * (Real.exp (-a * |x - y|) * |c|) *
            |x₁ - x₂| := by
            rw [show -(a * |x - y| - a) = a + (-a * |x - y|) by ring,
              Real.exp_add]
            ring

private lemma psi_integral_deriv_measurable_general
    {u : ℝ → ℝ} {a x : ℝ} (hu_meas : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable
      (fun y : ℝ =>
        if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
        else a * Real.exp (-a * (y - x)) * u y) volume := by
  have : AEStronglyMeasurable (fun y =>
      (if y ≤ x then -a * Real.exp (-a * (x - y))
        else a * Real.exp (-a * (y - x))) * u y) volume := by
    exact (StronglyMeasurable.piecewise measurableSet_Iic
      (by fun_prop : Continuous fun y => -a * Real.exp (-a * (x - y))).stronglyMeasurable
      (by fun_prop : Continuous fun y => a * Real.exp (-a * (y - x))).stronglyMeasurable
      ).aestronglyMeasurable.mul hu_meas
  exact this.congr (by filter_upwards with y; split_ifs <;> ring)

private lemma kernel_exp_neg_mul_abs_integrable_local {a : ℝ} (ha : 0 < a) (x : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => Real.exp (-a * |x - y|)) := by
  let f : ℝ → ℝ := fun y => Real.exp (-a * |x - y|)
  have hleft_eq :
      Set.EqOn (fun y : ℝ => Real.exp (-a * x) * Real.exp (a * y))
        f (Set.Iic x) := by
    intro y hy
    have hyx : y ≤ x := by simpa using hy
    simp only [f]
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), ← Real.exp_add]
    congr 1
    ring
  have hright_eq :
      Set.EqOn (fun y : ℝ => Real.exp (a * x) * Real.exp ((-a) * y))
        f (Set.Ioi x) := by
    intro y hy
    have hxy : x < y := by simpa using hy
    simp only [f]
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy)), ← Real.exp_add]
    congr 1
    ring
  have hleft : MeasureTheory.IntegrableOn f (Set.Iic x) := by
    have h1 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (a * y)) (Set.Iic x) :=
      integrableOn_exp_mul_Iic ha x
    have h2 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (-a * x) * Real.exp (a * y)) (Set.Iic x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp (-a * x))
    exact h2.congr_fun hleft_eq measurableSet_Iic
  have hright : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    have h1 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp ((-a) * y)) (Set.Ioi x) :=
      integrableOn_exp_mul_Ioi (by linarith : -a < (0 : ℝ)) x
    have h2 :
        MeasureTheory.IntegrableOn
          (fun y : ℝ => Real.exp (a * x) * Real.exp ((-a) * y)) (Set.Ioi x) :=
      MeasureTheory.Integrable.const_mul h1 (Real.exp (a * x))
    exact h2.congr_fun hright_eq measurableSet_Ioi
  have hcover : Set.Iic x ∪ Set.Ioi x = (Set.univ : Set ℝ) := by
    ext y
    by_cases hy : y ≤ x <;> simp [hy, lt_of_not_ge]
  rw [← MeasureTheory.integrableOn_univ, ← hcover]
  exact hleft.union hright

private lemma kernel_mul_bounded_integrable_of_pos_local
    {u : ℝ → ℝ} {a M : ℝ} (ha : 0 < a) (_hM : 0 ≤ M)
    (hu : ∀ y, |u y| ≤ M) (x : ℝ)
    (hu_meas : AEStronglyMeasurable u MeasureTheory.volume) :
    MeasureTheory.Integrable (fun y => Real.exp (-a * |x - y|) * u y) :=
  (kernel_exp_neg_mul_abs_integrable_local ha x).mul_bdd hu_meas
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hu y)

private lemma psi_kernel_mul_bounded_integrable_local
    {u : ℝ → ℝ} {l M : ℝ} (hl : 0 < l) (hM : 0 ≤ M)
    (hu : ∀ y, |u y| ≤ M) (x : ℝ)
    (hu_meas : AEStronglyMeasurable u MeasureTheory.volume) :
    MeasureTheory.Integrable
      (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y) :=
  kernel_mul_bounded_integrable_of_pos_local (Real.sqrt_pos.mpr hl) hM hu x hu_meas

private lemma psi_integral_deriv_integrable_general
    {u : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hu : IsCUnifBdd u) (x : ℝ) :
    Integrable
      (fun y : ℝ =>
        if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
        else a * Real.exp (-a * (y - x)) * u y) volume := by
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hbound :
      Integrable
        (fun y : ℝ => a * (Real.exp (-a * |x - y|) * |u y|)) volume := by
    exact (kernel_mul_bounded_integrable_of_pos_local ha hM_nonneg
      (fun y => by
        rw [abs_abs]
        exact hM y)
      x (hu.1.abs.aestronglyMeasurable)).const_mul a
  refine hbound.mono' (psi_integral_deriv_measurable_general hu.1.aestronglyMeasurable) ?_
  exact Eventually.of_forall (fun y => by
    by_cases hy : y ≤ x
    · calc
        ‖(if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
            else a * Real.exp (-a * (y - x)) * u y)‖
            = a * Real.exp (-a * (x - y)) * |u y| := by
              simp only [hy, ite_true]
              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
                abs_of_nonneg ha.le, abs_of_nonneg (Real.exp_nonneg _)]
          _ ≤ a * (Real.exp (-a * |x - y|) * |u y|) := by
              rw [abs_of_nonneg (sub_nonneg.mpr hy)]
              simpa [mul_assoc, mul_left_comm, mul_comm]
    · have hxy : x < y := lt_of_not_ge hy
      calc
        ‖(if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
            else a * Real.exp (-a * (y - x)) * u y)‖
            = a * Real.exp (-a * (y - x)) * |u y| := by
              simp only [hy, ite_false]
              rw [Real.norm_eq_abs, abs_mul, abs_mul,
                abs_of_nonneg ha.le, abs_of_nonneg (Real.exp_nonneg _)]
          _ ≤ a * (Real.exp (-a * |x - y|) * |u y|) := by
              rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy))]
              simpa [mul_assoc, mul_left_comm, mul_comm])

theorem hasDerivAt_integral_exp_neg_mul_abs_sub_general
    {u : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hu : IsCUnifBdd u) (x : ℝ) :
    HasDerivAt
      (fun x' => ∫ y, Real.exp (-a * |x' - y|) * u y)
      (∫ y,
        if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
        else a * Real.exp (-a * (y - x)) * u y) x := by
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  let G : ℝ → ℝ → ℝ := fun x' y => Real.exp (-a * |x' - y|) * u y
  let G' : ℝ → ℝ := fun y =>
    if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
    else a * Real.exp (-a * (y - x)) * u y
  let bound : ℝ → ℝ := fun y => a * Real.exp a *
    (Real.exp (-a * |x - y|) * |u y|)
  have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x zero_lt_one
  have hG_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (G x') volume := by
    filter_upwards with x'
    exact ((by fun_prop : Continuous fun y : ℝ =>
      Real.exp (-a * |x' - y|))).aestronglyMeasurable.mul
        hu.1.aestronglyMeasurable
  have hG_int : Integrable (G x) volume := by
    exact kernel_mul_bounded_integrable_of_pos_local ha hM_nonneg hM x
      hu.1.aestronglyMeasurable
  have hG'_meas : AEStronglyMeasurable G' volume := by
    exact psi_integral_deriv_measurable_general hu.1.aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    dsimp [bound]
    exact ((kernel_mul_bounded_integrable_of_pos_local ha hM_nonneg
      (fun y => by
        rw [abs_abs]
        exact hM y)
      x hu.1.abs.aestronglyMeasurable).const_mul (a * Real.exp a))
  have h_lip : ∀ᵐ y ∂volume,
      LipschitzOnWith (Real.nnabs (bound y)) (fun x' => G x' y)
        (Metric.ball x 1) := by
    filter_upwards with y
    dsimp [G, bound]
    exact exp_neg_mul_abs_sub_mul_lipschitzOnWith_ball_abs ha x y (u y)
  have hdiff : ∀ᵐ y ∂volume, HasDerivAt (fun x' => G x' y) (G' y) x := by
    have hne : ∀ᵐ y ∂volume, y ≠ x := by rw [ae_iff]; simp
    filter_upwards [hne] with y hy
    by_cases hylt : y < x
    · have hyle : y ≤ x := le_of_lt hylt
      simpa [G, G', hyle] using
        hasDerivAt_psi_integrand_left_general (u := u) (a := a) hylt
    · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hylt) (Ne.symm hy)
      have hnle : ¬y ≤ x := not_le.mpr hxy
      simpa [G, G', hnle] using
        hasDerivAt_psi_integrand_right_general (u := u) (a := a) hxy
  simpa [G, G'] using
    (hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (bound := bound)
      (F := G) (F' := G') (x₀ := x) (s := Metric.ball x 1)
      hs hG_meas hG_int hG'_meas h_lip hbound_int hdiff).2

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

/-- General-parameter derivative estimate for the one-dimensional elliptic
resolvent kernel. This proves Paper1 Lemma 2.3 without needing the explicit
Leibniz endpoint formula from Lemma 2.2. -/
theorem Psi_deriv_abs_le_general {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u)
    (hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    |deriv (fun z => Psi u l mu z) x| ≤ Real.sqrt l * Psi u l mu x := by
  let a : ℝ := Real.sqrt l
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr hl
  rcases hu.2 with ⟨M, hM⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (u 0)) (hM 0)
  have hint :
      Integrable (fun y : ℝ => Real.exp (-a * |x - y|) * u y) := by
    dsimp [a]
    exact psi_kernel_mul_bounded_integrable_local hl hM_nonneg hM x
      hu.1.aestronglyMeasurable
  let F' : ℝ → ℝ := fun y =>
    if y < x then -a * Real.exp (-a * (x - y)) * u y
    else a * Real.exp (-a * (y - x)) * u y
  have hLeibniz :
      HasDerivAt
        (fun x' => ∫ y, Real.exp (-a * |x' - y|) * u y)
        (∫ y, F' y) x := by
    let G : ℝ → ℝ → ℝ := fun x' y => Real.exp (-a * |x' - y|) * u y
    let G' : ℝ → ℝ := fun y =>
      if y < x then -a * Real.exp (-a * (x - y)) * u y
      else a * Real.exp (-a * (y - x)) * u y
    let bound : ℝ → ℝ := fun y => a * Real.exp a *
      (Real.exp (-a * |x - y|) * u y)
    have hs : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x zero_lt_one
    have hG_meas : ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (G x') volume := by
      filter_upwards with x'
      exact ((by fun_prop : Continuous fun y : ℝ =>
        Real.exp (-a * |x' - y|))).aestronglyMeasurable.mul
          hu.1.aestronglyMeasurable
    have hG_int : Integrable (G x) volume := by
      simpa [G] using hint
    have hG'_meas : AEStronglyMeasurable G' volume := by
      show AEStronglyMeasurable (fun y =>
        if y < x then -a * Real.exp (-a * (x - y)) * u y
        else a * Real.exp (-a * (y - x)) * u y) volume
      have : AEStronglyMeasurable (fun y =>
          (if y < x then -a * Real.exp (-a * (x - y))
            else a * Real.exp (-a * (y - x))) * u y) volume := by
        exact (StronglyMeasurable.piecewise measurableSet_Iio
          (by fun_prop : Continuous fun y =>
            -a * Real.exp (-a * (x - y))).stronglyMeasurable
          (by fun_prop : Continuous fun y =>
            a * Real.exp (-a * (y - x))).stronglyMeasurable).aestronglyMeasurable.mul
          hu.1.aestronglyMeasurable
      exact this.congr (by filter_upwards with y; split_ifs <;> ring)
    have hbound_int : Integrable bound volume := by
      dsimp [bound]
      exact hint.const_mul (a * Real.exp a)
    have h_lip : ∀ᵐ y ∂volume,
        LipschitzOnWith (Real.nnabs (bound y)) (fun x' => G x' y)
          (Metric.ball x 1) := by
      filter_upwards with y
      dsimp [G, bound]
      exact exp_neg_mul_abs_sub_mul_lipschitzOnWith_ball ha x y (u y)
        (hu_nonneg y)
    have hdiff : ∀ᵐ y ∂volume, HasDerivAt (fun x' => G x' y) (G' y) x := by
      have hne : ∀ᵐ y ∂volume, y ≠ x := by rw [ae_iff]; simp
      filter_upwards [hne] with y hy
      by_cases hylt : y < x
      · simpa [G, G', F', hylt] using
          hasDerivAt_psi_integrand_left_general (u := u) (a := a) hylt
      · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hylt) (Ne.symm hy)
        simpa [G, G', F', hylt] using
          hasDerivAt_psi_integrand_right_general (u := u) (a := a) hxy
    simpa [G, G', F'] using
      (hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (bound := bound)
        (F := G) (F' := G') (x₀ := x) (s := Metric.ball x 1)
        hs hG_meas hG_int hG'_meas h_lip hbound_int hdiff).2
  have hPsi_fun :
      (fun z => Psi u l mu z) =
        fun x' => mu / (2 * a) *
          ∫ y, Real.exp (-a * |x' - y|) * u y := by
    ext x'
    simp [Psi, a]
  have hda :
      HasDerivAt (fun z => Psi u l mu z)
        (mu / (2 * a) * ∫ y, F' y) x := by
    rw [hPsi_fun]
    exact hLeibniz.const_mul (mu / (2 * a))
  have hF'_bound :
      ∫ y, ‖F' y‖ ≤ ∫ y, a * (Real.exp (-a * |x - y|) * u y) := by
    have hint_rhs :
        Integrable (fun y : ℝ => a * (Real.exp (-a * |x - y|) * u y)) :=
      hint.const_mul a
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall (fun y => norm_nonneg _)
    · exact hint_rhs
    · exact Eventually.of_forall (fun y => by
        by_cases hyx : y = x
        · subst hyx
          simp only [F', lt_irrefl, ite_false, sub_self, neg_zero, mul_zero,
            Real.exp_zero, mul_one]
          rw [Real.norm_of_nonneg (mul_nonneg ha.le (hu_nonneg _))]
          simp
        · rcases lt_or_gt_of_ne hyx with hy | hy
          · calc
              ‖F' y‖ = a * Real.exp (-a * (x - y)) * u y := by
                simp only [F', hy, ite_true]
                rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
                  abs_of_nonneg ha.le, abs_of_nonneg (Real.exp_nonneg _),
                  abs_of_nonneg (hu_nonneg y)]
              _ ≤ a * (Real.exp (-a * |x - y|) * u y) := by
                rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy))]
                simpa [mul_assoc, mul_left_comm, mul_comm]
          · calc
              ‖F' y‖ = a * Real.exp (-a * (y - x)) * u y := by
                simp only [F', show ¬ y < x from not_lt.mpr (le_of_lt hy),
                  ite_false]
                rw [Real.norm_eq_abs, abs_mul, abs_mul,
                  abs_of_nonneg ha.le, abs_of_nonneg (Real.exp_nonneg _),
                  abs_of_nonneg (hu_nonneg y)]
              _ ≤ a * (Real.exp (-a * |x - y|) * u y) := by
                rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy))]
                simpa [mul_assoc, mul_left_comm, mul_comm])
  have hInt_bound :
      |∫ y, F' y| ≤ a * ∫ y, Real.exp (-a * |x - y|) * u y := by
    calc
      |∫ y, F' y| ≤ ∫ y, ‖F' y‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
      _ ≤ ∫ y, a * (Real.exp (-a * |x - y|) * u y) := hF'_bound
      _ = a * ∫ y, Real.exp (-a * |x - y|) * u y := by
        exact MeasureTheory.integral_const_mul _ _
  have hcoeff_nonneg : 0 ≤ mu / (2 * a) := by positivity
  rw [hda.deriv]
  calc
    |mu / (2 * a) * ∫ y, F' y|
        = (mu / (2 * a)) * |∫ y, F' y| := by
          rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
    _ ≤ (mu / (2 * a)) *
          (a * ∫ y, Real.exp (-a * |x - y|) * u y) :=
          mul_le_mul_of_nonneg_left hInt_bound hcoeff_nonneg
    _ = Real.sqrt l * Psi u l mu x := by
          simp [Psi, a]
          field_simp [ne_of_gt ha]

theorem Psi_derivative_formula_general {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (_hmu : 0 < mu) (hu : IsCUnifBdd u) :
    ∀ x,
      deriv (fun z => Psi u l mu z) x =
        (-(mu / 2) * Real.exp (-Real.sqrt l * x) *
            (∫ y in Set.Iic x, Real.exp (Real.sqrt l * y) * u y))
          + ((mu / 2) * Real.exp (Real.sqrt l * x) *
            (∫ y in Set.Ioi x, Real.exp (-Real.sqrt l * y) * u y)) := by
  intro x
  let a : ℝ := Real.sqrt l
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr hl
  let F' : ℝ → ℝ := fun y =>
    if y ≤ x then -a * Real.exp (-a * (x - y)) * u y
    else a * Real.exp (-a * (y - x)) * u y
  have hLeibniz :
      HasDerivAt
        (fun x' => ∫ y, Real.exp (-a * |x' - y|) * u y)
        (∫ y, F' y) x := by
    simpa [F'] using
      hasDerivAt_integral_exp_neg_mul_abs_sub_general
        (u := u) (a := a) ha hu x
  have hPsi_fun :
      (fun z => Psi u l mu z) =
        fun x' => mu / (2 * a) *
          ∫ y, Real.exp (-a * |x' - y|) * u y := by
    ext x'
    simp [Psi, a]
  have hda :
      HasDerivAt (fun z => Psi u l mu z)
        (mu / (2 * a) * ∫ y, F' y) x := by
    rw [hPsi_fun]
    exact hLeibniz.const_mul (mu / (2 * a))
  have hF'_int : Integrable F' volume := by
    simpa [F'] using psi_integral_deriv_integrable_general
      (u := u) (a := a) ha hu x
  have hsplit :=
    MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hF'_int
  simp only [Set.compl_Iic] at hsplit
  have hleft :
      ∫ y in Set.Iic x, F' y =
        (-a * Real.exp (-a * x)) *
          ∫ y in Set.Iic x, Real.exp (a * y) * u y := by
    have hleft_eq :
        Set.EqOn F'
          (fun y : ℝ => (-a * Real.exp (-a * x)) *
            (Real.exp (a * y) * u y))
          (Set.Iic x) := by
      intro y hy
      have hyx : y ≤ x := by simpa using hy
      change F' y =
        (-a * Real.exp (-a * x)) * (Real.exp (a * y) * u y)
      simp only [F', hyx, ite_true]
      rw [show -a * (x - y) = -a * x + a * y by ring, Real.exp_add]
      ring
    calc
      ∫ y in Set.Iic x, F' y
          = ∫ y in Set.Iic x,
              (-a * Real.exp (-a * x)) * (Real.exp (a * y) * u y) := by
            exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq
      _ = (-a * Real.exp (-a * x)) *
            ∫ y in Set.Iic x, Real.exp (a * y) * u y := by
            exact MeasureTheory.integral_const_mul _ _
  have hright :
      ∫ y in Set.Ioi x, F' y =
        (a * Real.exp (a * x)) *
          ∫ y in Set.Ioi x, Real.exp (-a * y) * u y := by
    have hright_eq :
        Set.EqOn F'
          (fun y : ℝ => (a * Real.exp (a * x)) *
            (Real.exp (-a * y) * u y))
          (Set.Ioi x) := by
      intro y hy
      have hxy : x < y := by simpa using hy
      have hnle : ¬y ≤ x := not_le.mpr hxy
      change F' y =
        (a * Real.exp (a * x)) * (Real.exp (-a * y) * u y)
      simp only [F', hnle, ite_false]
      rw [show -a * (y - x) = a * x + -a * y by ring, Real.exp_add]
      ring
    calc
      ∫ y in Set.Ioi x, F' y
          = ∫ y in Set.Ioi x,
              (a * Real.exp (a * x)) * (Real.exp (-a * y) * u y) := by
            exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq
      _ = (a * Real.exp (a * x)) *
            ∫ y in Set.Ioi x, Real.exp (-a * y) * u y := by
            exact MeasureTheory.integral_const_mul _ _
  have hInt :
      ∫ y, F' y =
        (-a * Real.exp (-a * x)) *
            (∫ y in Set.Iic x, Real.exp (a * y) * u y)
          + (a * Real.exp (a * x)) *
            (∫ y in Set.Ioi x, Real.exp (-a * y) * u y) := by
    calc
      ∫ y, F' y =
          (∫ y in Set.Iic x, F' y) + (∫ y in Set.Ioi x, F' y) :=
            hsplit.symm
      _ = (-a * Real.exp (-a * x)) *
              (∫ y in Set.Iic x, Real.exp (a * y) * u y)
            + (a * Real.exp (a * x)) *
              (∫ y in Set.Ioi x, Real.exp (-a * y) * u y) := by
            rw [hleft, hright]
  let L : ℝ := ∫ y in Set.Iic x, Real.exp (a * y) * u y
  let R : ℝ := ∫ y in Set.Ioi x, Real.exp (-a * y) * u y
  have hIntLR :
      ∫ y, F' y =
        (-a * Real.exp (-a * x)) * L + (a * Real.exp (a * x)) * R := by
    simpa [L, R] using hInt
  calc
    deriv (fun z => Psi u l mu z) x
        = mu / (2 * a) * ∫ y, F' y := hda.deriv
    _ = mu / (2 * a) *
          ((-a * Real.exp (-a * x)) * L + (a * Real.exp (a * x)) * R) := by
          rw [hIntLR]
    _ = -(mu / 2) * Real.exp (-a * x) * L +
          (mu / 2) * Real.exp (a * x) * R := by
          field_simp [ne_of_gt ha]
    _ = (-(mu / 2) * Real.exp (-Real.sqrt l * x) *
            (∫ y in Set.Iic x, Real.exp (Real.sqrt l * y) * u y))
          + ((mu / 2) * Real.exp (Real.sqrt l * x) *
            (∫ y in Set.Ioi x, Real.exp (-Real.sqrt l * y) * u y)) := by
          simp [L, R, a]

/-! ## Psi elliptic ODE identity

The resolvent `v(x) = Ψ(x; f, λ, μ)` satisfies `v'' - λv + μf = 0`. -/

private theorem hasDerivAt_setIntegral_Iic_of_continuous
    {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_int : ∀ b : ℝ, IntegrableOn g (Set.Iic b)) (x : ℝ) :
    HasDerivAt (fun x' => ∫ y in Set.Iic x', g y) (g x) x := by
  set x₀ := x - 1
  have hx₀x : x₀ ≤ x := by linarith
  have hsplit : ∀ᶠ x' in 𝓝 x,
      ∫ y in Set.Iic x', g y =
        (∫ y in Set.Iic x₀, g y) + ∫ y in x₀..x', g y := by
    filter_upwards [Ioi_mem_nhds (show x₀ < x by linarith)] with x' hx'
    have hle : x₀ ≤ x' := le_of_lt hx'
    rw [← Set.Iic_union_Ioc_eq_Iic hle]
    rw [MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioc le_rfl)
      measurableSet_Ioc (hg_int x₀)
      ((hg_int x').mono_set Set.Ioc_subset_Iic_self)]
    rw [intervalIntegral.integral_of_le hle]
  have hFTC : HasDerivAt (fun x' => ∫ y in x₀..x', g y) (g x) x := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hg_cont.intervalIntegrable x₀ x)
      hg_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg_cont.continuousAt
  have hconst : HasDerivAt (fun _ : ℝ => ∫ y in Set.Iic x₀, g y) 0 x :=
    hasDerivAt_const x _
  have hsum : HasDerivAt
      (fun x' => (∫ y in Set.Iic x₀, g y) + ∫ y in x₀..x', g y) (g x) x := by
    have h := hconst.add hFTC
    rw [zero_add] at h
    exact h.congr_deriv rfl
  exact hsum.congr_of_eventuallyEq hsplit

private theorem hasDerivAt_setIntegral_Ioi_of_continuous
    {g : ℝ → ℝ} (hg_cont : Continuous g)
    (hg_int : ∀ b : ℝ, IntegrableOn g (Set.Ioi b)) (x : ℝ) :
    HasDerivAt (fun x' => ∫ y in Set.Ioi x', g y) (-g x) x := by
  set x₁ := x + 1
  have hxx₁ : x < x₁ := by linarith
  have hsplit :
      (fun x' => ∫ y in Set.Ioi x', g y) =ᶠ[𝓝 x]
        ((fun x' => ∫ y in x'..x₁, g y) +
          fun _ : ℝ => ∫ y in Set.Ioi x₁, g y) := by
    filter_upwards [Iio_mem_nhds hxx₁] with x' hx'
    change ∫ y in Set.Ioi x', g y =
      (∫ y in x'..x₁, g y) + ∫ y in Set.Ioi x₁, g y
    simpa using (intervalIntegral.integral_interval_add_Ioi'
      (hg_cont.intervalIntegrable x' x₁) (hg_int x₁)).symm
  have hFTC : HasDerivAt (fun x' => ∫ y in x'..x₁, g y) (-g x) x := by
    exact intervalIntegral.integral_hasDerivAt_left
      (hg_cont.intervalIntegrable x x₁)
      hg_cont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg_cont.continuousAt
  have hconst : HasDerivAt (fun _ : ℝ => ∫ y in Set.Ioi x₁, g y) 0 x :=
    hasDerivAt_const x _
  have hsum := hFTC.add hconst
  rw [add_zero] at hsum
  exact hsum.congr_of_eventuallyEq hsplit

private lemma integrableOn_exp_mul_u_Iic
    {u : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hu : IsCUnifBdd u) (b : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (a * y) * u y) (Set.Iic b) := by
  rcases hu.2 with ⟨M, hM⟩
  exact (integrableOn_exp_mul_Iic ha b).mul_bdd
    (hu.1.continuousOn.aestronglyMeasurable measurableSet_Iic)
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hM y)

private lemma integrableOn_exp_neg_mul_u_Ioi
    {u : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hu : IsCUnifBdd u) (b : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-a * y) * u y) (Set.Ioi b) := by
  rcases hu.2 with ⟨M, hM⟩
  exact (integrableOn_exp_mul_Ioi (by linarith : -a < (0 : ℝ)) b).mul_bdd
    (hu.1.continuousOn.aestronglyMeasurable measurableSet_Ioi)
    (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hM y)

theorem Psi_elliptic_ode {u : ℝ → ℝ} {l mu : ℝ}
    (hl : 0 < l) (hmu : 0 < mu) (hu : IsCUnifBdd u)
    (_hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    iteratedDeriv 2 (fun z => Psi u l mu z) x -
      l * Psi u l mu x + mu * u x = 0 := by
  let a : ℝ := Real.sqrt l
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr hl
  have ha_sq : a ^ 2 = l := by
    dsimp [a]
    exact Real.sq_sqrt (le_of_lt hl)
  let L : ℝ → ℝ := fun z => ∫ y in Set.Iic z, Real.exp (a * y) * u y
  let R : ℝ → ℝ := fun z => ∫ y in Set.Ioi z, Real.exp (-a * y) * u y
  let D : ℝ → ℝ := fun z =>
    (-(mu / 2) * Real.exp (-a * z) * L z) +
      ((mu / 2) * Real.exp (a * z) * R z)
  have hderiv_fun :
      (fun z => deriv (fun w => Psi u l mu w) z) = D := by
    funext z
    simpa [D, L, R, a] using Psi_derivative_formula_general hl hmu hu z
  have hL_cont : Continuous (fun y : ℝ => Real.exp (a * y) * u y) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hu.1
  have hR_cont : Continuous (fun y : ℝ => Real.exp (-a * y) * u y) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hu.1
  have hL_deriv : HasDerivAt L (Real.exp (a * x) * u x) x := by
    simpa [L] using
      hasDerivAt_setIntegral_Iic_of_continuous hL_cont
        (integrableOn_exp_mul_u_Iic ha hu) x
  have hR_deriv : HasDerivAt R (-(Real.exp (-a * x) * u x)) x := by
    simpa [R] using
      hasDerivAt_setIntegral_Ioi_of_continuous hR_cont
        (integrableOn_exp_neg_mul_u_Ioi ha hu) x
  have hExp_neg : HasDerivAt (fun z : ℝ => Real.exp (-a * z))
      (-a * Real.exp (-a * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul (-a)).exp)
  have hExp_pos : HasDerivAt (fun z : ℝ => Real.exp (a * z))
      (a * Real.exp (a * x)) x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul a).exp)
  let d : ℝ :=
    ((-(mu / 2) * (-a * Real.exp (-a * x))) * L x +
      (-(mu / 2) * Real.exp (-a * x)) * (Real.exp (a * x) * u x)) +
    (((mu / 2) * (a * Real.exp (a * x))) * R x +
      ((mu / 2) * Real.exp (a * x)) * (-(Real.exp (-a * x) * u x)))
  have hD_deriv : HasDerivAt D d x := by
    have hleft :
        HasDerivAt (fun z : ℝ => (-(mu / 2) * Real.exp (-a * z)) * L z)
          ((-(mu / 2) * (-a * Real.exp (-a * x))) * L x +
            (-(mu / 2) * Real.exp (-a * x)) * (Real.exp (a * x) * u x)) x := by
      exact (hExp_neg.const_mul (-(mu / 2))).mul hL_deriv
    have hright :
        HasDerivAt (fun z : ℝ => ((mu / 2) * Real.exp (a * z)) * R z)
          (((mu / 2) * (a * Real.exp (a * x))) * R x +
            ((mu / 2) * Real.exp (a * x)) * (-(Real.exp (-a * x) * u x))) x := by
      exact (hExp_pos.const_mul (mu / 2)).mul hR_deriv
    simpa [D, d, mul_assoc] using hleft.add hright
  have hsecond :
      iteratedDeriv 2 (fun z => Psi u l mu z) x = d := by
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
    exact (hderiv_fun ▸ hD_deriv).deriv
  have hkernel_split :
      ∫ y : ℝ, Real.exp (-a * |x - y|) * u y =
        Real.exp (-a * x) * L x + Real.exp (a * x) * R x := by
    have hiu : Integrable (fun y : ℝ => Real.exp (-a * |x - y|) * u y) :=
      kernel_mul_bounded_integrable_of_pos_local ha
        (le_trans (abs_nonneg (u 0)) (Classical.choose_spec hu.2 0))
        (Classical.choose_spec hu.2) x hu.1.aestronglyMeasurable
    have hsplit :=
      MeasureTheory.integral_add_compl (s := Set.Iic x) measurableSet_Iic hiu
    simp only [Set.compl_Iic] at hsplit
    have hleft :
        ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y =
          Real.exp (-a * x) * L x := by
      have hleft_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-a * |x - y|) * u y)
            (fun y : ℝ => Real.exp (-a * x) * (Real.exp (a * y) * u y))
            (Set.Iic x) := by
        intro y hy
        have hyx : y ≤ x := by simpa using hy
        change
          Real.exp (-a * |x - y|) * u y =
            Real.exp (-a * x) * (Real.exp (a * y) * u y)
        rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
        rw [show -a * (x - y) = -a * x + a * y by ring, Real.exp_add]
        ring
      calc
        ∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y
            = ∫ y in Set.Iic x,
                Real.exp (-a * x) * (Real.exp (a * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Iic hleft_eq
        _ = Real.exp (-a * x) * L x := by
              simp [L, MeasureTheory.integral_const_mul]
    have hright :
        ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y =
          Real.exp (a * x) * R x := by
      have hright_eq :
          Set.EqOn
            (fun y : ℝ => Real.exp (-a * |x - y|) * u y)
            (fun y : ℝ => Real.exp (a * x) * (Real.exp (-a * y) * u y))
            (Set.Ioi x) := by
        intro y hy
        have hxy : x < y := by simpa using hy
        change
          Real.exp (-a * |x - y|) * u y =
            Real.exp (a * x) * (Real.exp (-a * y) * u y)
        rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy))]
        rw [show -a * -(x - y) = a * x + -a * y by ring, Real.exp_add]
        ring
      calc
        ∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y
            = ∫ y in Set.Ioi x,
                Real.exp (a * x) * (Real.exp (-a * y) * u y) := by
              exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hright_eq
        _ = Real.exp (a * x) * R x := by
              simp [R, MeasureTheory.integral_const_mul]
    calc
      ∫ y : ℝ, Real.exp (-a * |x - y|) * u y
          = (∫ y in Set.Iic x, Real.exp (-a * |x - y|) * u y) +
              (∫ y in Set.Ioi x, Real.exp (-a * |x - y|) * u y) := hsplit.symm
      _ = Real.exp (-a * x) * L x + Real.exp (a * x) * R x := by
            rw [hleft, hright]
  have hPsi :
      Psi u l mu x =
        mu / (2 * a) * (Real.exp (-a * x) * L x + Real.exp (a * x) * R x) := by
    unfold Psi
    rw [show Real.sqrt l = a by rfl]
    rw [hkernel_split]
  have hcancel₁ : Real.exp (-a * x) * Real.exp (a * x) = 1 := by
    rw [← Real.exp_add]
    have hzero : -a * x + a * x = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hcancel₂ : Real.exp (a * x) * Real.exp (-a * x) = 1 := by
    rw [← Real.exp_add]
    have hzero : a * x + -a * x = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hcancel₁' : Real.exp (-(a * x)) * Real.exp (a * x) = 1 := by
    rw [← Real.exp_add]
    have hzero : -(a * x) + a * x = 0 := by ring
    rw [hzero, Real.exp_zero]
  have hprod :
      mu * Real.exp (-(a * x)) * Real.exp (a * x) * u x * 2 = mu * u x * 2 := by
    calc
      mu * Real.exp (-(a * x)) * Real.exp (a * x) * u x * 2
          = mu * (Real.exp (-(a * x)) * Real.exp (a * x)) * u x * 2 := by ring
      _ = mu * u x * 2 := by rw [hcancel₁']; ring
  rw [hsecond, hPsi]
  rw [← ha_sq]
  dsimp [d]
  field_simp [ne_of_gt ha]
  ring_nf
  rw [hprod]
  ring

end
