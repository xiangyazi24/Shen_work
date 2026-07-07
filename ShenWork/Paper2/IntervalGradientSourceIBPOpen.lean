import ShenWork.PDE.IntervalFullKernelSourceIBP
import ShenWork.Paper2.IntervalSourceBridgeOpen

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

noncomputable section

/-- Endpoint-safe/open version of the full-kernel source IBP identity.

The closed theorem
`deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral`
requires an ambient `HasDerivAt` hypothesis on `uIcc 0 1`, including the
endpoints.  This variant uses the same kernel identity and boundary
cancellations, but its source derivative hypothesis is only a right derivative
on the open interval `(0,1)`, matching the zero-extended flux regularity used in
`IntervalSourceBridgeOpen`.

No PDE/classical-solution information is used here; this is purely a kernel
IBP bridge for the gradient Duhamel leg. -/
theorem deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral_open
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQcont : ContinuousOn Q (Set.Icc (0 : ℝ) 1))
    (hQderiv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt Q (Q' y) (Set.Ioi y) y)
    (hQ'_int : IntervalIntegrable Q' MeasureTheory.volume 0 1)
    (x : ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
      -(∫ y in (0 : ℝ)..1,
        Q' y * intervalNeumannConjugateKernel t x y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [(intervalFullSemigroupOperator_hasDerivAt_fst ht hQ_meas hQ_bound x).deriv]
  have hμconv :
      (∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x * Q y
        ∂(intervalMeasure 1))
        = ∫ y in (0 : ℝ)..1,
            Q y * deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x := by
    simp only [intervalMeasure, intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h01]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  rw [hμconv]
  have hKcont : ContinuousOn
      (fun y : ℝ => intervalNeumannConjugateKernel t x y)
      (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le h01]
    exact continuousOn_conjugateKernel_snd ht x
  have hQcont' : ContinuousOn Q (Set.uIcc (0 : ℝ) 1) := by
    rwa [Set.uIcc_of_le h01]
  have hQderiv' :
      ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivWithinAt Q (Q' y) (Set.Ioi y) y := by
    intro y hy
    rw [min_eq_left h01, max_eq_right h01] at hy
    exact hQderiv y hy
  have hKderiv :
      ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
        HasDerivWithinAt
          (fun y : ℝ => intervalNeumannConjugateKernel t x y)
          (deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x)
          (Set.Ioi y) y := by
    intro y _hy
    have h := hasDerivAt_conjugateKernel_snd ht x y
    have h' :
        HasDerivAt
          (fun y : ℝ => intervalNeumannConjugateKernel t x y)
          (deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x) y := by
      rwa [← (hasDerivAt_intervalNeumannFullKernel_fst ht x y).deriv] at h
    exact h'.hasDerivWithinAt (s := Set.Ioi y)
  have hDii : IntervalIntegrable
      (fun y : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x)
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_deriv_intervalNeumannFullKernel_fst ht x
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hQcont' hKcont hQderiv' hKderiv hQ'_int hDii
  rw [hibp]
  simp [conjugateKernel_at_one ht x, conjugateKernel_at_zero]

end

end ShenWork.IntervalNeumannFullKernel
