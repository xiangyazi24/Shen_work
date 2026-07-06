import ShenWork.PDE.IntervalFullKernelSourceIBP

/-!
# Reflected half-kernel for conjugate-kernel mass defects

This file starts the non-circular mass-defect route for the conjugate/Dirichlet
approximate identity.  The key algebraic observation is that `-Ktilde` is the
full Neumann kernel minus twice the reflected image half.
-/

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

noncomputable section

/-- The reflected image half of the full Neumann image kernel. -/
def intervalNeumannReflectedKernelPart (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ))

/-- Summability of the reflected half-kernel lattice. -/
theorem reflectedKernelPart_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun k : ℤ => heatKernel t (x + y + 2 * (k : ℝ))) :=
  latticeGaussianSummable ht (x + y)

/-- The reflected half-kernel is nonnegative. -/
theorem reflectedKernelPart_nonneg {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    0 ≤ intervalNeumannReflectedKernelPart t x y := by
  rw [intervalNeumannReflectedKernelPart]
  exact tsum_nonneg (fun k => heatKernel_nonneg ht _)

/-- Continuity in the integration variable of the reflected half-kernel. -/
theorem continuousOn_reflectedKernelPart_snd {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (fun y : ℝ => intervalNeumannReflectedKernelPart t x y) (Set.Icc 0 1) := by
  have hh : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  have hsum : Summable (fun k : ℤ => heatKernelWindowBound t x 1 k) :=
    summable_heatKernelWindowBound ht x 1
  change ContinuousOn (fun y : ℝ => ∑' k : ℤ,
    heatKernel t (x + y + 2 * (k : ℝ))) (Set.Icc 0 1)
  refine continuousOn_tsum (fun k => (hh.comp (by fun_prop)).continuousOn) hsum
    (fun k y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht _)]
  exact heatKernel_le_windowShift ht x 1 k
    (by
      rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
      exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)

/-- Pointwise algebra: `-Ktilde = Kfull - 2 * reflectedHalf`. -/
theorem neg_conjugateKernel_eq_full_sub_two_reflected
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    -intervalNeumannConjugateKernel t x y =
      intervalNeumannFullKernel t x y - 2 * intervalNeumannReflectedKernelPart t x y := by
  have hA : Summable (fun k : ℤ => heatKernel t (x - y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x - y)
  have hB : Summable (fun k : ℤ => heatKernel t (x + y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x + y)
  rw [intervalNeumannConjugateKernel, intervalNeumannFullKernel,
    intervalNeumannReflectedKernelPart]
  rw [Summable.tsum_add hA.neg hB, Summable.tsum_add hA hB, tsum_neg]
  ring

/-- Algebraic mass-defect identity for the conjugate kernel. -/
theorem conjugateKernel_massDefect_eq_neg_two_reflectedMass
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (-(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) - 1)
      = -2 * (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hK_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannConjugateKernel t x y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_conjugateKernel_snd ht x
  have hF_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannFullKernel t x y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_intervalNeumannFullKernel_snd ht x
  have hR_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannReflectedKernelPart t x y) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_reflectedKernelPart_snd ht x
  have hneg :
      (∫ y in (0 : ℝ)..1, -intervalNeumannConjugateKernel t x y)
        = -(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) := by
    rw [intervalIntegral.integral_neg]
  have hcongr :
      (∫ y in (0 : ℝ)..1, -intervalNeumannConjugateKernel t x y)
        = ∫ y in (0 : ℝ)..1,
          intervalNeumannFullKernel t x y - 2 * intervalNeumannReflectedKernelPart t x y := by
    apply intervalIntegral.integral_congr
    intro y _
    exact neg_conjugateKernel_eq_full_sub_two_reflected ht x y
  calc
    (-(∫ y in (0 : ℝ)..1, intervalNeumannConjugateKernel t x y) - 1)
        = (∫ y in (0 : ℝ)..1, -intervalNeumannConjugateKernel t x y) - 1 := by
      rw [hneg]
    _ = (∫ y in (0 : ℝ)..1,
          intervalNeumannFullKernel t x y - 2 * intervalNeumannReflectedKernelPart t x y) - 1 := by
      rw [hcongr]
    _ = (∫ y in (0 : ℝ)..1, intervalNeumannFullKernel t x y)
          - 2 * (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) - 1 := by
      rw [intervalIntegral.integral_sub hF_int (hR_int.const_mul 2),
        intervalIntegral.integral_const_mul]
    _ = -2 * (∫ y in (0 : ℝ)..1, intervalNeumannReflectedKernelPart t x y) := by
      rw [intervalNeumannFullKernel_integral_eq_one ht x]
      ring

end

end ShenWork.IntervalNeumannFullKernel
