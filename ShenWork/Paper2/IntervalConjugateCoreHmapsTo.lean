/-
  Core `hmapsTo` assembly: from the new sup-norm brick
  `intervalConjugateDuhamelMap_sup_bound_of_banked` plus the per-trajectory
  flux/logistic sup bounds (via the ball lemmas, concrete `Cq = M·C_RG`,
  `Cl = M(a+bMᵅ)`) and the integrability witnesses, conclude the ball
  maps-to bound `|Φᴮ(w) t x| ≤ M` under the smallness condition
  `M₀ + |χ₀|·Cg·(2√T)·Cq + T·Cl ≤ M`.

  This is the `hmapsTo` field shape of `ConjugateMildExistenceCore`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalConjugatePicardSupBound

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)

noncomputable section

namespace ShenWork.IntervalConjugatePicardBounds

/-- **Core `hmapsTo` assembly.**  Given the smallness budget
`M₀ + |χ₀|·Cg·(2√T)·Cq + T·Cl ≤ M`, the sup-norm brick yields the ball
maps-to bound `|Φᴮ(w) t x| ≤ M` for every interior `(t,x)`. -/
theorem intervalConjugateDuhamelMap_mapsTo_of_banked
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {w : ℝ → intervalDomainPoint → ℝ}
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint)
    {M M₀ Cq Cl : ℝ} (hM₀ : 0 ≤ M₀) (hCq : 0 ≤ Cq) (hCl : 0 ≤ Cl)
    (hbudget :
      M₀ + |p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq)
        + T * Cl ≤ M)
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
    |intervalConjugateDuhamelMap p u₀ w t x| ≤ M :=
  le_trans
    (intervalConjugateDuhamelMap_sup_bound_of_banked
      p ht htT x hM₀ hCq hCl hu₀_bound hq_int hq_sup hl_sup hB_int hL_int)
    hbudget

#print axioms intervalConjugateDuhamelMap_mapsTo_of_banked

end ShenWork.IntervalConjugatePicardBounds
