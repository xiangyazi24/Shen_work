/-
  B-form Picard maps-to (ball) bound that uses the banked conjugate-kernel √T
  bound — the sup-norm twin of `intervalConjugateDuhamelMap_diff_bound_of_banked`
  in `IntervalConjugatePicardBounds.lean`.

  The chemotaxis leg is estimated through `conjugateDuhamel_sup_bound` (banked
  √T conjugate-kernel bound, NOT the divergence-form gradient Duhamel estimate);
  the homogeneous leg `S(t)u₀` through the full-semigroup L∞ contraction; the
  logistic leg through `valueDuhamel_sup_bound`.  Assembling these three legs is
  the analytic core of the `hmapsTo` field of `ConjugateMildExistenceCore`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalConjugatePicardBounds

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel
   intervalFullSemigroupOperator_Linfty_bound)
open ShenWork.IntervalGradDuhamelBound (valueDuhamel_sup_bound)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)

noncomputable section

namespace ShenWork.IntervalConjugatePicardBounds

/-- **B-form map maps-to (ball) bound.**  For a ball element `w` whose
chemotaxis flux is sup-bounded by `Cq` and whose logistic source is sup-bounded
by `Cl`, with `u₀` sup-bounded by `M₀`, the B-form Picard image is bounded by
`M₀ + |χ₀|·Cg·(2√T)·Cq + T·Cl` at every interior point.

This is the sup-norm analogue of `intervalConjugateDuhamelMap_diff_bound_of_banked`:
the chemotaxis leg goes through the banked `conjugateDuhamel_sup_bound`, the
homogeneous leg through the full-semigroup L∞ contraction, and the logistic leg
through `valueDuhamel_sup_bound`. -/
theorem intervalConjugateDuhamelMap_sup_bound_of_banked
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {w : ℝ → intervalDomainPoint → ℝ}
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    {M₀ Cq Cl : ℝ} (hM₀ : 0 ≤ M₀) (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ M₀)
    (hq_int : ∀ s, Integrable (chemFluxLifted p (w s)) (intervalMeasure 1))
    (hq_sup : ∀ s y, |chemFluxLifted p (w s) y| ≤ Cq)
    (hl_sup : ∀ s y, |logisticLifted p (w s) y| ≤ Cl)
    (hB_int : IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
      volume 0 t)
    (hL_int : IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
      volume 0 t) :
    |intervalConjugateDuhamelMap p u₀ w t x|
      ≤ M₀
        + |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq)
        + T * Cl := by
  set Hleg := intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 with hHleg
  set Gleg := ∫ s in (0:ℝ)..t,
    intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1 with hGleg
  set Lleg := ∫ s in (0:ℝ)..t,
    intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1 with hLleg
  -- Homogeneous leg: full-semigroup L∞ contraction.
  have hH : |Hleg| ≤ M₀ :=
    intervalFullSemigroupOperator_Linfty_bound ht hM₀ hu₀_bound x.1
  -- Chemotaxis leg: banked conjugate-kernel √T bound.
  have hG : |(-p.χ₀) * Gleg|
      ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq) := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (conjugateDuhamel_sup_bound ht htT hq_int hCq hq_sup x.1 hB_int)
      (abs_nonneg p.χ₀)
  -- Logistic leg: value-Duhamel sup bound.
  have hL : |Lleg| ≤ T * Cl :=
    valueDuhamel_sup_bound ht htT hCl hl_sup x.1 hL_int
  -- Triangle assembly.
  have hsplit : intervalConjugateDuhamelMap p u₀ w t x
      = Hleg + (-p.χ₀) * Gleg + Lleg := by
    simp only [intervalConjugateDuhamelMap, hHleg, hGleg, hLleg]
  rw [hsplit]
  calc |Hleg + (-p.χ₀) * Gleg + Lleg|
      ≤ |Hleg + (-p.χ₀) * Gleg| + |Lleg| := abs_add_le _ _
    _ ≤ (|Hleg| + |(-p.χ₀) * Gleg|) + |Lleg| := by
        gcongr; exact abs_add_le _ _
    _ ≤ (M₀ + |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq))
          + T * Cl := by
        gcongr

#print axioms intervalConjugateDuhamelMap_sup_bound_of_banked

end ShenWork.IntervalConjugatePicardBounds
