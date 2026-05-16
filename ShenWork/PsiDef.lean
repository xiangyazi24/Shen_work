/-
  ShenWork/PsiDef.lean

  Definition of Ψ (elliptic Green's function) and proofs of its properties.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Basic

open Filter Topology MeasureTheory Real

noncomputable section

/-- The elliptic Green's function:
    Ψ(x; u, l, μ) = (μ / (2√l)) ∫ e^{-√l |x-y|} u(y) dy -/
def Psi (u : ℝ → ℝ) (l mu : ℝ) (x : ℝ) : ℝ :=
  mu / (2 * Real.sqrt l) * ∫ y : ℝ, Real.exp (-Real.sqrt l * |x - y|) * u y

/-- The kernel e^{-a|t|} is nonneg for any a and t. -/
lemma kernel_nonneg (a x y : ℝ) : 0 ≤ Real.exp (-a * |x - y|) :=
  Real.exp_nonneg _

/-- The prefactor mu/(2√l) is nonneg when mu ≥ 0 and l > 0. -/
lemma prefactor_nonneg {l mu : ℝ} (hmu : 0 ≤ mu) (hl : 0 < l) :
    0 ≤ mu / (2 * Real.sqrt l) :=
  div_nonneg hmu (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg l))

/-- Psi is nonneg when u ≥ 0, l > 0, mu > 0. -/
theorem Psi_nonneg {u : ℝ → ℝ} {l mu : ℝ} (_hl : 0 < l) (hmu : 0 < mu)
    (hu : ∀ x, 0 ≤ u x) (x : ℝ) : 0 ≤ Psi u l mu x := by
  unfold Psi
  apply mul_nonneg
  · exact div_nonneg (le_of_lt hmu) (mul_nonneg (by norm_num) (Real.sqrt_nonneg l))
  · exact integral_nonneg (fun y => mul_nonneg (kernel_nonneg _ x y) (hu y))

/-- Psi is monotone: u ≤ v pointwise implies Psi u ≤ Psi v (when integrable). -/
theorem Psi_mono {u v : ℝ → ℝ} {l mu : ℝ} (hl : 0 < l) (hmu : 0 < mu)
    (huv : ∀ x, u x ≤ v x) (x : ℝ)
    (hiu : Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * u y))
    (hiv : Integrable (fun y => Real.exp (-Real.sqrt l * |x - y|) * v y)) :
    Psi u l mu x ≤ Psi v l mu x := by
  unfold Psi
  apply mul_le_mul_of_nonneg_left
  · exact integral_mono hiu hiv (fun y => by
      apply mul_le_mul_of_nonneg_left (huv y) (kernel_nonneg _ x y))
  · exact prefactor_nonneg (le_of_lt hmu) hl

/-- Psi of a constant: Psi (fun _ => c) 1 1 x = c when c ≥ 0.
    Requires ∫ (1/2) e^{-|x-y|} dy = 1 (Laplace density integrates to 1). -/
theorem Psi_const {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Psi (fun _ : ℝ => c) 1 1 x = c := by
  sorry

/-- Psi of exponential: Psi (fun y => e^{-ky}) 1 1 x = e^{-kx}/(1-k²). -/
theorem Psi_exp {k : ℝ} (hk : 0 < k) (hk1 : k < 1) (x : ℝ) :
    Psi (fun y : ℝ => Real.exp (-k * y)) 1 1 x =
      1 / (1 - k ^ 2) * Real.exp (-k * x) := by
  sorry

/-- |Ψ'(x)| ≤ √l · Ψ(x) for nonneg u. Specialized to l=1. -/
theorem Psi_deriv_abs_le {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ u x) (x : ℝ) :
    |deriv (Psi u 1 1) x| ≤ Psi u 1 1 x := by
  sorry

end
