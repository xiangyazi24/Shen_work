import ShenWork.Paper1.WholeLineWeightedRegularityFluxDerivative
import ShenWork.Paper1.WholeLineWeightedRegularityCap

open Filter MeasureTheory

noncomputable section

namespace ShenWork.Paper1

/-!
# Cap-conjugated chemotactic-flux derivative

The corrected flux-derivative expansion is linear in its four weighted
fields.  Consequently any scalar exhaustion multiplier can be distributed
through the expansion.  This file records the resulting static `L²` estimate
without assuming exponential integrability of the population derivative.
-/

/-- A scalar multiplier distributes through the corrected four-field flux
derivative expansion. -/
theorem paper5WeightedFluxDerivativeExpanded_mul_fields
    (p : CMParams) (eta : ℝ)
    (u v : ℝ → ℝ → ℝ) (U W Wx Z Zx a : ℝ → ℝ)
    (t x : ℝ) :
    paper5WeightedFluxDerivativeExpanded p eta u v U
        (fun y => a y * W y) (fun y => a y * Wx y)
        (fun y => a y * Z y) (fun y => a y * Zx y) t x =
      a x * paper5WeightedFluxDerivativeExpanded p eta u v U
        W Wx Z Zx t x := by
  unfold paper5WeightedFluxDerivativeExpanded
  ring

/-- Static cap/exhaustion version of the corrected flux-derivative estimate.
Only the four multiplier-conjugated fields need to lie in `L²`; the theorem
does not presuppose the exact exponential derivative budget. -/
theorem multipliedFluxDerivativeExpanded_sq_integrable_and_integral_le
    (p : CMParams) {eta t B1 B2 B0 B3 B4 : ℝ}
    {u v : ℝ → ℝ → ℝ} {U W Wx Z Zx a : ℝ → ℝ}
    (hsource_meas : AEStronglyMeasurable (fun x =>
      a x * paper5WeightedFluxDerivativeExpanded p eta
        u v U W Wx Z Zx t x))
    (hb1 : ∀ x, |paper5B1 p u v t x| ≤ B1)
    (hb2 : ∀ x, |paper5B2 p u v U t x| ≤ B2)
    (hb0 : ∀ x,
      |paper5CorrectedChemZeroCoefficient p u v U t x| ≤ B0)
    (hb3 : ∀ x, |paper5B3 p U x| ≤ B3)
    (hb4 : ∀ x, |paper5B4 p U x| ≤ B4)
    (hW2 : Integrable (fun x => (a x * W x) ^ 2))
    (hWx2 : Integrable (fun x => (a x * Wx x) ^ 2))
    (hZ2 : Integrable (fun x => (a x * Z x) ^ 2))
    (hZx2 : Integrable (fun x => (a x * Zx x) ^ 2)) :
    Integrable (fun x =>
        (a x * paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x) ^ 2) ∧
      (∫ x : ℝ,
        (a x * paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x) ^ 2) ≤
        4 *
          (B1 ^ 2 * (∫ x : ℝ, (a x * Wx x) ^ 2) +
            (B2 + B0 + |eta| * B1) ^ 2 *
              (∫ x : ℝ, (a x * W x) ^ 2) +
            B3 ^ 2 * (∫ x : ℝ, (a x * Zx x) ^ 2) +
            (B4 + |eta| * B3) ^ 2 *
              (∫ x : ℝ, (a x * Z x) ^ 2)) := by
  let Wc : ℝ → ℝ := fun x => a x * W x
  let Wxc : ℝ → ℝ := fun x => a x * Wx x
  let Zc : ℝ → ℝ := fun x => a x * Z x
  let Zxc : ℝ → ℝ := fun x => a x * Zx x
  have hpoint : ∀ x,
      paper5WeightedFluxDerivativeExpanded p eta u v U
          Wc Wxc Zc Zxc t x =
        a x * paper5WeightedFluxDerivativeExpanded p eta
          u v U W Wx Z Zx t x := by
    intro x
    exact paper5WeightedFluxDerivativeExpanded_mul_fields
      p eta u v U W Wx Z Zx a t x
  have hmeas : AEStronglyMeasurable
      (paper5WeightedFluxDerivativeExpanded p eta
        u v U Wc Wxc Zc Zxc t) := by
    refine hsource_meas.congr ?_
    exact Eventually.of_forall fun x => (hpoint x).symm
  have hbase :=
    paper5WeightedFluxDerivativeExpanded_sq_integrable_and_integral_le
      p hmeas hb1 hb2 hb0 hb3 hb4
        (by simpa only [Wc] using hW2)
        (by simpa only [Wxc] using hWx2)
        (by simpa only [Zc] using hZ2)
        (by simpa only [Zxc] using hZx2)
  simpa only [hpoint, Wc, Wxc, Zc, Zxc] using hbase

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5WeightedFluxDerivativeExpanded_mul_fields
#print axioms
  ShenWork.Paper1.multipliedFluxDerivativeExpanded_sq_integrable_and_integral_le
