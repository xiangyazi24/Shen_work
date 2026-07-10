/-
  Operator-level integration by parts for the Neumann conjugate kernel.

  B_N(t)Q(x) = -∫₀¹ ∂_y K_N(t,x,y) Q(y) dy
             = ∫₀¹ K_N(t,x,y) Q'(y) dy      when Q(0)=Q(1)=0 and Q∈W^{1,1}
             = S_N(t)(Q')(x)

  This eliminates the 1/(t-s) singularity in the gradient estimate of the
  chemotaxis Duhamel leg, reducing it to the integrable √(t-s) singularity.
-/

import ShenWork.Paper2.IntervalConjugateDuhamelMap

open MeasureTheory intervalIntegral Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalConjugateKernelIBP

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalMeasure intervalSet)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator
   continuousOn_intervalNeumannFullKernel_snd
   hasDerivAt_intervalNeumannFullKernel_snd
   intervalIntegrable_deriv_intervalNeumannFullKernel_snd)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)

lemma intervalMeasure_one_integral_eq_intervalIntegral (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  unfold intervalMeasure intervalSet
  change (∫ y in Icc (0 : ℝ) 1, f y ∂ volume) = ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem intervalConjugateKernelOperator_eq_semigroup_deriv
    {t x : ℝ} (ht : 0 < t) {Q : ℝ → ℝ}
    (hQ_cont : ContinuousOn Q (uIcc (0 : ℝ) 1))
    (hQ_deriv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt Q (deriv Q y) y)
    (hQ_deriv_int :
      IntervalIntegrable (fun y : ℝ => deriv Q y) volume 0 1)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0) :
    intervalConjugateKernelOperator t Q x =
      intervalFullSemigroupOperator t (deriv Q) x := by
  classical
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  set K : ℝ → ℝ := fun y : ℝ => intervalNeumannFullKernel t x y with hK
  set K' : ℝ → ℝ :=
    fun y : ℝ => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y with hK'
  have hK_cont : ContinuousOn K (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le h01]
    simpa [K] using continuousOn_intervalNeumannFullKernel_snd ht x
  have hK_deriv :
      ∀ y ∈ Ioo (min (0 : ℝ) 1) (max 0 1), HasDerivAt K (K' y) y := by
    intro y _hy
    have h := hasDerivAt_intervalNeumannFullKernel_snd ht x y
    simpa [K, K', h.deriv] using h
  have hQ_deriv_minmax :
      ∀ y ∈ Ioo (min (0 : ℝ) 1) (max 0 1), HasDerivAt Q (deriv Q y) y := by
    intro y hy
    have hy' : y ∈ Ioo (0 : ℝ) 1 := by
      simpa [min_eq_left h01, max_eq_right h01] using hy
    exact hQ_deriv y hy'
  have hK'_int : IntervalIntegrable K' volume 0 1 := by
    simpa [K'] using intervalIntegrable_deriv_intervalNeumannFullKernel_snd ht x
  have hIBP :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        K 1 * Q 1 - K 0 * Q 0 - ∫ y in (0 : ℝ)..1, K' y * Q y :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hK_cont hQ_cont hK_deriv hQ_deriv_minmax hK'_int hQ_deriv_int
  have hIBP_zero :
      (∫ y in (0 : ℝ)..1, K y * deriv Q y) =
        - ∫ y in (0 : ℝ)..1, K' y * Q y := by
    simpa [hQ0, hQ1] using hIBP
  unfold intervalConjugateKernelOperator intervalFullSemigroupOperator
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ =>
      deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * Q y)]
  rw [intervalMeasure_one_integral_eq_intervalIntegral
    (f := fun y : ℝ => intervalNeumannFullKernel t x y * deriv Q y)]
  simpa [K, K'] using hIBP_zero.symm

end ShenWork.Paper2.IntervalConjugateKernelIBP
