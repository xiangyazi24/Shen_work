/-
  ShenWork/PDE/HeatSemigroup.lean

  The heat semigroup e^{tΔ} on ℝ and its basic properties.
  This is the fundamental tool for studying parabolic equations.

  The heat kernel: G(t,x) = (4πt)^{-1/2} exp(-x²/(4t))
  The semigroup: (e^{tΔ} f)(x) = ∫ G(t,x-y) f(y) dy

  Properties needed:
  1. ∫ G(t,x) dx = 1 (conservation of mass)
  2. e^{tΔ} maps C^b_unif to itself
  3. L^p → L^q smoothing estimates (Lemma 2.1)
  4. Gradient estimates
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Filter Topology Real

noncomputable section

/-- The heat kernel on ℝ at time t > 0. -/
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))

/-- The heat semigroup acting on a function f. -/
def heatSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, heatKernel t (x - y) * f y

/-- The modified semigroup e^{(Δ-I)t} = e^{-t} e^{tΔ} used in the paper. -/
def modifiedSemigroup (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-t) * heatSemigroup t f x

/-! ## Basic properties of the heat kernel -/

/-- The heat kernel is nonneg for t > 0. -/
lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ heatKernel t x := by
  unfold heatKernel
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact Real.sqrt_nonneg _
  · exact Real.exp_nonneg _

/-- The heat kernel integrates to 1: ∫ G(t,x) dx = 1 for t > 0.
    This is the Gaussian integral. -/
theorem heatKernel_integral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, heatKernel t x = 1 := by
  unfold heatKernel
  rw [show (fun x : ℝ => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))) =
    (fun x => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(1/(4*t)) * x ^ 2)) from by
      ext x; congr 1; ring]
  rw [MeasureTheory.integral_const_mul, integral_gaussian (1/(4*t))]
  have h4pt : 0 < 4 * Real.pi * t := by positivity
  have hsqrt_ne : Real.sqrt (4 * Real.pi * t) ≠ 0 := Real.sqrt_ne_zero'.mpr h4pt
  field_simp [hsqrt_ne]

/-- The heat kernel is even: G(t, -x) = G(t, x). -/
lemma heatKernel_neg (t x : ℝ) : heatKernel t (-x) = heatKernel t x := by
  unfold heatKernel; congr 1; congr 1; ring

/-- The heat kernel integrates to 1 after translation: ∫ G(t, x-y) dy = 1. -/
theorem heatKernel_integral_translated {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y : ℝ, heatKernel t (x - y) = 1 := by
  have key : (fun y : ℝ => heatKernel t (x - y)) =
      (fun y => (fun z => heatKernel t z) (y + (-x))) := by
    ext y; simp only; rw [show x - y = -(y + (-x)) from by ring, heatKernel_neg]
  rw [key, integral_add_right_eq_self, heatKernel_integral_eq_one ht]

/-- The heat kernel is integrable. -/
lemma heatKernel_integrable {t : ℝ} (ht : 0 < t) :
    MeasureTheory.Integrable (fun x => heatKernel t x) := by
  unfold heatKernel
  have hb : 0 < 1 / (4 * t) := by positivity
  rw [show (fun x : ℝ => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x ^ 2 / (4 * t))) =
    (fun x => 1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-(1/(4*t)) * x ^ 2)) from by
      ext x; congr 1; ring]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

/-- The translated heat kernel is integrable. -/
lemma heatKernel_translated_integrable {t : ℝ} (ht : 0 < t) (x : ℝ) :
    MeasureTheory.Integrable (fun y => heatKernel t (x - y)) := by
  have h := heatKernel_integrable ht
  have key : (fun y : ℝ => heatKernel t (x - y)) =
      (fun y => (fun z => heatKernel t z) (-(y + (-x)))) := by
    ext y; congr 1; ring
  rw [key, show (fun y : ℝ => (fun z => heatKernel t z) (-(y + -x))) =
    (fun y => (fun z => heatKernel t (-z)) (y + (-x))) from rfl]
  simp_rw [heatKernel_neg]
  rw [show (fun y : ℝ => heatKernel t (y + -x)) =
    (fun y => (fun z => heatKernel t z) (y + (-x))) from rfl]
  exact h.comp_add_right (-x)

/-- The heat kernel (translated) times a bounded function is integrable. -/
lemma heatKernel_mul_bounded_integrable {t : ℝ} (ht : 0 < t) (x : ℝ)
    {f : ℝ → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y) :=
  (heatKernel_translated_integrable ht x).mul_bdd hf_meas
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hf y)

/-! ## Semigroup estimates (Lemma 2.1 of the paper) -/

/-- The comparison principle for the heat equation:
    If f ≤ g pointwise, then e^{tΔ} f ≤ e^{tΔ} g. -/
theorem heatSemigroup_mono {f g : ℝ → ℝ} (hfg : ∀ x, f x ≤ g x)
    {t : ℝ} (ht : 0 < t)
    (hf_int : MeasureTheory.Integrable (fun y => heatKernel t (x₀ - y) * f y))
    (hg_int : MeasureTheory.Integrable (fun y => heatKernel t (x₀ - y) * g y)) :
    heatSemigroup t f x₀ ≤ heatSemigroup t g x₀ := by
  unfold heatSemigroup
  exact MeasureTheory.integral_mono hf_int hg_int
    (fun y => mul_le_mul_of_nonneg_left (hfg y) (heatKernel_nonneg ht _))

/-- If f ≥ 0 and f ≤ M, then e^{tΔ} f ≤ M (conservation + positivity). -/
theorem heatSemigroup_upper_bound {f : ℝ → ℝ} {M : ℝ}
    (_hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ M)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ M := by
  intro x
  unfold heatSemigroup
  calc ∫ y, heatKernel t (x - y) * f y
      ≤ ∫ y, heatKernel t (x - y) * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y =>
            mul_nonneg (heatKernel_nonneg ht _) (_hf_nn y))
        · exact (heatKernel_translated_integrable ht x).mul_const M
        · exact Filter.Eventually.of_forall (fun y =>
            mul_le_mul_of_nonneg_left (hf_le y) (heatKernel_nonneg ht _))
    _ = M * ∫ y, heatKernel t (x - y) := by
        rw [show (fun y => heatKernel t (x - y) * M) = (fun y => M * heatKernel t (x - y)) from by
          ext y; ring]
        exact MeasureTheory.integral_const_mul _ _
    _ = M * 1 := by rw [heatKernel_integral_translated ht x]
    _ = M := by ring

/-- L^∞ bound: ‖e^{(Δ-I)t} f‖_∞ ≤ e^{-t} ‖f‖_∞. -/
theorem heatSemigroup_abs_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    ∀ x, |heatSemigroup t f x| ≤ M := by
  intro x; unfold heatSemigroup
  calc |∫ y, heatKernel t (x - y) * f y|
      ≤ ∫ y, ‖heatKernel t (x - y) * f y‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = ∫ y, heatKernel t (x - y) * |f y| := by
        congr 1; ext y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht _)]
    _ ≤ ∫ y, heatKernel t (x - y) * M := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y =>
            mul_nonneg (heatKernel_nonneg ht _) (abs_nonneg _))
        · exact (heatKernel_translated_integrable ht x).mul_const M
        · exact Filter.Eventually.of_forall (fun y =>
            mul_le_mul_of_nonneg_left (hf y) (heatKernel_nonneg ht _))
    _ = M := by
        rw [show (fun y => heatKernel t (x - y) * M) = (fun y => M * heatKernel t (x - y)) from by
          ext y; ring]
        rw [MeasureTheory.integral_const_mul, heatKernel_integral_translated ht x, mul_one]

theorem modifiedSemigroup_Linfty_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) (hM : 0 ≤ M)
    (hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    ∀ x, |modifiedSemigroup t f x| ≤ Real.exp (-t) * M := by
  intro x; unfold modifiedSemigroup
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left (heatSemigroup_abs_bound hf ht hM hf_meas x) (Real.exp_nonneg _)

lemma heatKernel_zero (x : ℝ) : heatKernel 0 x = 0 := by
  unfold heatKernel
  simp [mul_zero, Real.sqrt_zero, div_zero]

lemma heatSemigroup_zero (f : ℝ → ℝ) (x : ℝ) : heatSemigroup 0 f x = 0 := by
  unfold heatSemigroup
  simp [heatKernel_zero, zero_mul]

theorem heatSemigroup_sub {f g : ℝ → ℝ} {t : ℝ} (x : ℝ)
    (hf : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * f y))
    (hg : MeasureTheory.Integrable (fun y => heatKernel t (x - y) * g y)) :
    heatSemigroup t (fun y => f y - g y) x =
    heatSemigroup t f x - heatSemigroup t g x := by
  simpa [heatSemigroup, mul_sub] using MeasureTheory.integral_sub hf hg

end
