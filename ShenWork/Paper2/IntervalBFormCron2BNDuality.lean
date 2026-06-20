/-
  Kernel symmetry and the regular B_N adjoint identity for the cron2 route.

  This file proves the concrete regular B_N Fubini identity under the explicit
  hypotheses that make the Bochner integrals and the derivative of `S_N(τ)ψ`
  available.
-/
import ShenWork.Paper2.IntervalBFormNegativePartCron2

open MeasureTheory
open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

/-- Symmetry of the full periodised Neumann kernel. -/
theorem intervalNeumannFullKernel_symm {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalNeumannFullKernel t x y = intervalNeumannFullKernel t y x := by
  unfold intervalNeumannFullKernel
  have hleft :
      (∑' k : ℤ, heatKernel t (x - y + 2 * (k : ℝ)))
        = ∑' k : ℤ, heatKernel t (y - x + 2 * (k : ℝ)) := by
    rw [← (Equiv.neg ℤ).tsum_eq
      (fun k : ℤ => heatKernel t (y - x + 2 * (k : ℝ)))]
    refine tsum_congr (fun k => ?_)
    rw [← heatKernel_neg t (y - x + 2 * ((Equiv.neg ℤ k : ℤ) : ℝ))]
    congr 1
    simp only [Equiv.neg_apply]
    push_cast
    ring
  have hright :
      (∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ)))
        = ∑' k : ℤ, heatKernel t (y + x + 2 * (k : ℝ)) := by
    refine tsum_congr (fun k => ?_)
    congr 1
    ring
  rw [Summable.tsum_add, Summable.tsum_add, hleft, hright]
  · exact (latticeGaussianSummable ht (y - x))
  · exact (latticeGaussianSummable ht (y + x))
  · exact (latticeGaussianSummable ht (x - y))
  · exact (latticeGaussianSummable ht (x + y))

/-- The second-variable derivative of `K_N(t,x,y)` is the first-variable
derivative of the swapped kernel. -/
theorem deriv_intervalNeumannFullKernel_snd_eq_fst_swap
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y
      = deriv (fun z : ℝ => intervalNeumannFullKernel t z x) y := by
  have hfun :
      (fun y' : ℝ => intervalNeumannFullKernel t x y')
        = fun z : ℝ => intervalNeumannFullKernel t z x := by
    funext z
    exact intervalNeumannFullKernel_symm ht x z
  rw [hfun]

end ShenWork.IntervalNeumannFullKernel

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalNeumannFullKernel

/-- Regular-function version of the B-form adjoint identity:

`∫ B_N(τ)g · ψ = -∫ g · ∂x(S_N(τ)ψ)`.

The two analytic hypotheses are exactly the Fubini product integrability and
the derivative-under-the-integral representation for `S_N(τ)ψ`. -/
theorem bN_duality_regular
    {τ : ℝ} (hτ : 0 < τ) (g ψ : ℝ → ℝ)
    (hF_int : Integrable
      (fun p : ℝ × ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ p.1 y') p.2
          * g p.2 * ψ p.1)
      ((intervalMeasure 1).prod (intervalMeasure 1)))
    (hS_deriv : ∀ y : ℝ,
      deriv (fun z : ℝ => intervalFullSemigroupOperator τ ψ z) y
        =
      ∫ x,
        deriv (fun z : ℝ => intervalNeumannFullKernel τ z x) y * ψ x
        ∂ intervalMeasure 1) :
    (∫ x, intervalConjugateKernelOperator τ g x * ψ x ∂ intervalMeasure 1)
      =
    -(∫ y, g y *
        deriv (fun z : ℝ => intervalFullSemigroupOperator τ ψ z) y
        ∂ intervalMeasure 1) := by
  let μ := intervalMeasure 1
  have hinner :
      (fun x : ℝ =>
        intervalConjugateKernelOperator τ g x * ψ x)
        =
      fun x : ℝ =>
        -(∫ y,
          deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
            * g y * ψ x ∂ μ) := by
    funext x
    unfold intervalConjugateKernelOperator
    rw [neg_mul]
    congr 1
    rw [MeasureTheory.integral_mul_const]
  rw [hinner]
  rw [MeasureTheory.integral_neg]
  have hswap :
      (∫ x, ∫ y,
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
          * g y * ψ x ∂ μ ∂ μ)
        =
      ∫ y, ∫ x,
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
          * g y * ψ x ∂ μ ∂ μ := by
    simpa [μ, Function.uncurry] using
      (MeasureTheory.integral_integral_swap (μ := μ) (ν := μ)
        (f := fun x y : ℝ =>
          deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
            * g y * ψ x) hF_int)
  rw [hswap]
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (∫ x,
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
          * g y * ψ x ∂ μ)
      = g y * deriv (fun z : ℝ => intervalFullSemigroupOperator τ ψ z) y
    rw [hS_deriv y]
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change deriv (fun y' : ℝ => intervalNeumannFullKernel τ x y') y
          * g y * ψ x
        = g y * (deriv (fun z : ℝ => intervalNeumannFullKernel τ z x) y * ψ x)
      rw [deriv_intervalNeumannFullKernel_snd_eq_fst_swap hτ x y]
      ring

/-- B-form adjoint identity with the semigroup derivative representation
discharged from the existing full-kernel differentiation theorem.  The remaining
explicit hypothesis is the Fubini product integrability of the displayed
kernel-gradient integrand. -/
theorem bN_duality_of_bounded_test
    {τ : ℝ} (hτ : 0 < τ) (g ψ : ℝ → ℝ)
    (hF_int : Integrable
      (fun p : ℝ × ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ p.1 y') p.2
          * g p.2 * ψ p.1)
      ((intervalMeasure 1).prod (intervalMeasure 1)))
    (hψ_meas : AEStronglyMeasurable ψ (intervalMeasure 1))
    {Cψ : ℝ} (hψ_bound : ∀ x, |ψ x| ≤ Cψ) :
    (∫ x, intervalConjugateKernelOperator τ g x * ψ x ∂ intervalMeasure 1)
      =
    -(∫ y, g y *
        deriv (fun z : ℝ => intervalFullSemigroupOperator τ ψ z) y
        ∂ intervalMeasure 1) :=
  bN_duality_regular hτ g ψ hF_int
    (fun y =>
      (intervalFullSemigroupOperator_hasDerivAt_fst hτ hψ_meas hψ_bound y).deriv)

end ShenWork.Paper2.BFormPositiveDatumNegPart
