/-
  ShenWork/PsiDef.lean

  Definition of Ψ (elliptic Green's function) and proofs of its properties.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Convolution

open Filter Topology MeasureTheory Real Set

noncomputable section

/-- Ψ(x; u, l, μ) = (μ / (2√l)) ∫ e^{-√l |x-y|} u(y) dy -/
def Psi (u : ℝ → ℝ) (l mu : ℝ) (x : ℝ) : ℝ :=
  mu / (2 * Real.sqrt l) * ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y

lemma kernel_nonneg (a x y : ℝ) : 0 ≤ Real.exp (-a * |x - y|) :=
  Real.exp_nonneg _

lemma prefactor_nonneg {l mu : ℝ} (hmu : 0 ≤ mu) (_hl : 0 < l) :
    0 ≤ mu / (2 * Real.sqrt l) :=
  div_nonneg hmu (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg l))

theorem Psi_nonneg {u : ℝ → ℝ} {l mu : ℝ} (_hl : 0 < l) (hmu : 0 < mu)
    (hu : ∀ x, 0 ≤ u x) (x : ℝ) : 0 ≤ Psi u l mu x := by
  unfold Psi
  apply mul_nonneg
  · exact div_nonneg (le_of_lt hmu) (mul_nonneg (by norm_num) (Real.sqrt_nonneg l))
  · exact integral_nonneg (fun y => mul_nonneg (kernel_nonneg _ x y) (hu y))

theorem Psi_mono {u v : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (huv : ∀ x, u x ≤ v x) (x : ℝ)
    (hiu : Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y))
    (hiv : Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * v y)) :
    Psi u l mu x ≤ Psi v l mu x := by
  unfold Psi
  apply mul_le_mul_of_nonneg_left
  · exact integral_mono hiu hiv (fun y =>
      mul_le_mul_of_nonneg_left (huv y) (kernel_nonneg _ x y))
  · exact prefactor_nonneg (le_of_lt hmu) hl

/-! ## Key integral identity: ∫ e^{-|t|} dt = 2 -/

lemma integral_exp_neg_abs : ∫ x : ℝ, Real.exp (-|x|) = 2 := by
  have h := @integral_comp_abs (fun t => Real.exp (-t))
  simp only [Function.comp] at h
  -- h : ∫ x, exp (-|x|) = 2 * ∫ x in Ioi 0, exp (-x)
  linarith [integral_exp_neg_Ioi_zero]

/-! ## Psi_const: Ψ of a constant -/

lemma integral_exp_neg_abs_sub (x : ℝ) :
    ∫ y : ℝ, Real.exp (-|x - y|) = 2 := by
  have h : (fun y : ℝ => Real.exp (-|x - y|)) = (fun y => Real.exp (-|y + (-x)|)) := by
    ext y; congr 2; rw [abs_sub_comm]; ring_nf
  rw [h, integral_add_right_eq_self (fun z => Real.exp (-|z|)) (-x), integral_exp_neg_abs]

theorem Psi_const {c : ℝ} (_hc : 0 ≤ c) (x : ℝ) :
    Psi (fun _ : ℝ => c) 1 1 x = c := by
  simp only [Psi, Real.sqrt_one, mul_one]
  rw [show (fun y : ℝ => Real.exp (-1 * |x - y|) * c) =
    (fun y => c * Real.exp (-|x - y|)) from by ext y; ring]
  rw [MeasureTheory.integral_const_mul, integral_exp_neg_abs_sub x]
  ring

/-! ## Psi_exp: Ψ of an exponential -/

theorem Psi_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x =
      1 / (1 - k ^ 2) * Real.exp (-k * x) := by
  sorry

/-! ## Gradient bound -/

theorem Psi_deriv_abs_le {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x := by
  sorry

end
