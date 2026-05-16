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

/-! ## Semigroup estimates (Lemma 2.1 of the paper) -/

/-- L^∞ bound: ‖e^{(Δ-I)t} f‖_∞ ≤ e^{-t} ‖f‖_∞.
    The heat semigroup is a contraction on L^∞. -/
theorem modifiedSemigroup_Linfty_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) {t : ℝ} (ht : 0 < t) :
    ∀ x, |modifiedSemigroup t f x| ≤ Real.exp (-t) * M := by
  sorry

/-- The comparison principle for the heat equation:
    If f ≤ g pointwise, then e^{tΔ} f ≤ e^{tΔ} g. -/
theorem heatSemigroup_mono {f g : ℝ → ℝ} (hfg : ∀ x, f x ≤ g x)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ heatSemigroup t g x := by
  intro x
  unfold heatSemigroup
  sorry -- needs integrability + monotonicity of integral with nonneg kernel

/-- If f ≥ 0 and f ≤ M, then e^{tΔ} f ≤ M (conservation + positivity). -/
theorem heatSemigroup_upper_bound {f : ℝ → ℝ} {M : ℝ}
    (_hf_nn : ∀ x, 0 ≤ f x) (hf_le : ∀ x, f x ≤ M)
    {t : ℝ} (ht : 0 < t) :
    ∀ x, heatSemigroup t f x ≤ M := by
  intro x
  unfold heatSemigroup
  calc ∫ y, heatKernel t (x - y) * f y
      ≤ ∫ y, heatKernel t (x - y) * M := by
        sorry -- integral_mono with integrability
    _ = M * ∫ y, heatKernel t (x - y) := by
        rw [show (fun y => heatKernel t (x - y) * M) = (fun y => M * heatKernel t (x - y)) from by
          ext y; ring]
        rw [MeasureTheory.integral_const_mul]
    _ = M := by
        sorry -- ∫ G(t, x-y) dy = 1 by translation

end
