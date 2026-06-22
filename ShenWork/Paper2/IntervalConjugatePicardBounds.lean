/-
  B-form Picard estimates that use the banked conjugate-kernel √T bound.

  The key point is that the chemotaxis leg is estimated through
  `conjugateDuhamel_diff_sup_bound`, not by silently reverting to the
  divergence-form gradient Duhamel estimate.
-/
import ShenWork.Paper2.IntervalConjugateDuhamelMap

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)

noncomputable section

namespace ShenWork.IntervalConjugatePicardBounds

/-- Chemotaxis-leg difference bound for the B-form map, directly from the
banked conjugate-kernel `√T` estimate. -/
theorem conjugateChemotaxisDuhamel_diff_sup_bound
    (p : CM2Params) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {q₁ q₂ : ℝ → ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hq_diff : ∀ s, 0 < s → s ≤ T → ∀ y, |q₁ s y - q₂ s y| ≤ D)
    (hq_int_diff : ∀ s, 0 < s → s ≤ T → Integrable (fun y => q₁ s y - q₂ s y)
      (intervalMeasure 1))
    (x : ℝ)
    (hKq₁ : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x y') y
          * q₁ s y)
      (intervalMeasure 1))
    (hKq₂ : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x y') y
          * q₂ s y)
      (intervalMeasure 1))
    (hB_int : IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (fun y => q₁ s y - q₂ s y) x)
      volume 0 t) :
    |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
        (intervalConjugateKernelOperator (t - s) (q₁ s) x
          - intervalConjugateKernelOperator (t - s) (q₂ s) x))|
      ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * D) := by
  rw [abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left
    (conjugateDuhamel_diff_sup_bound ht htT hD hq_diff hq_int_diff x hKq₁ hKq₂ hB_int)
    (abs_nonneg p.χ₀)

/-- The same bound specialized to the B-form chemotaxis flux
`chemFluxLifted p (u s)`. -/
theorem conjugateChemFluxDuhamel_diff_sup_bound
    (p : CM2Params) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    {u w : ℝ → intervalDomainPoint → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hq_diff : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxLifted p (u s) y - chemFluxLifted p (w s) y| ≤ D)
    (hq_int_diff : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y)
      (intervalMeasure 1))
    (x : ℝ)
    (hKq_u : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x y') y
          * chemFluxLifted p (u s) y)
      (intervalMeasure 1))
    (hKq_w : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) x y') y
          * chemFluxLifted p (w s) y)
      (intervalMeasure 1))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y) x)
      volume 0 t) :
    |(-p.χ₀) * (∫ s in (0 : ℝ)..t,
        (intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x
          - intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x))|
      ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * D) :=
  conjugateChemotaxisDuhamel_diff_sup_bound p ht htT hD hq_diff hq_int_diff x
    hKq_u hKq_w hB_int

/-- Componentwise B-form map difference bound.  The chemotaxis component is
estimated by the banked conjugate-kernel bound; the value/logistic component is
left as its own named bound, matching the existing Picard architecture. -/
theorem intervalConjugateDuhamelMap_diff_bound_of_banked
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {u w : ℝ → intervalDomainPoint → ℝ}
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    {Dq Cv : ℝ} (hDq : 0 ≤ Dq)
    (hq_diff : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxLifted p (u s) y - chemFluxLifted p (w s) y| ≤ Dq)
    (hq_int_diff : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y)
      (intervalMeasure 1))
    (hKq_u : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) (x.1) y') y
          * chemFluxLifted p (u s) y)
      (intervalMeasure 1))
    (hKq_w : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel (t - s) (x.1) y') y
          * chemFluxLifted p (w s) y)
      (intervalMeasure 1))
    (hB_u_int : IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x.1)
      volume 0 t)
    (hB_w_int : IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
      volume 0 t)
    (hB_diff_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxLifted p (u s) y - chemFluxLifted p (w s) y) x.1)
      volume 0 t)
    (hV :
      |((∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1)
        - (∫ s in (0 : ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1))|
      ≤ Cv) :
    |intervalConjugateDuhamelMap p u₀ u t x
      - intervalConjugateDuhamelMap p u₀ w t x|
      ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Dq)
        + Cv := by
  set Gu := ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x.1
  set Gw := ∫ s in (0 : ℝ)..t,
    intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1
  set Vu := ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1
  set Vw := ∫ s in (0 : ℝ)..t,
    intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1
  have hchem_raw :
      |(-p.χ₀) * (Gu - Gw)|
        ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Dq) := by
    dsimp only [Gu, Gw]
    rw [← intervalIntegral.integral_sub hB_u_int hB_w_int]
    exact conjugateChemFluxDuhamel_diff_sup_bound p ht htT hDq hq_diff hq_int_diff
      x.1 hKq_u hKq_w hB_diff_int
  have hcancel :
      (intervalConjugateDuhamelMap p u₀ u t x
        - intervalConjugateDuhamelMap p u₀ w t x)
        = (-p.χ₀) * (Gu - Gw) + (Vu - Vw) := by
    simp only [intervalConjugateDuhamelMap, Gu, Gw, Vu, Vw]
    ring
  rw [hcancel]
  calc |(-p.χ₀) * (Gu - Gw) + (Vu - Vw)|
      ≤ |(-p.χ₀) * (Gu - Gw)| + |Vu - Vw| := abs_add_le _ _
    _ ≤ |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Dq)
        + Cv := add_le_add hchem_raw hV

#print axioms conjugateChemFluxDuhamel_diff_sup_bound
#print axioms intervalConjugateDuhamelMap_diff_bound_of_banked

end ShenWork.IntervalConjugatePicardBounds
