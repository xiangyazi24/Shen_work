import ShenWork.Paper1.WholeLineCauchyFluxC1Bootstrap

open Filter Topology MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive-time C2 bootstrap for the whole-line Cauchy solution

The first structural step integrates one spatial derivative off the Gaussian
and onto the now-`C1` physical flux.  The boundary term at both infinities is
handled by Mathlib's whole-line integration-by-parts theorem in its integrable
form; Gaussian derivative integrability and boundedness of the source provide
all three required products.
-/

/-- Whole-line Gaussian integration by parts for the modified heat Hessian:
for a bounded `C1` source with bounded continuous derivative, one derivative
can be transferred from the kernel to the source. -/
theorem wholeLineCauchyHeatHessOp_eq_gradOp_deriv
    {f : ℝ → ℝ} {t x C D : ℝ}
    (ht : 0 < t)
    (hf : ∀ y, |f y| ≤ C)
    (hfd : ∀ y, |deriv f y| ≤ D)
    (hfderiv : ∀ y, HasDerivAt f (deriv f y) y)
    (hfdcont : Continuous (deriv f)) :
    wholeLineCauchyHeatHessOp t f x =
      wholeLineCauchyHeatGradOp t (deriv f) x := by
  let k : ℝ → ℝ := fun y =>
    deriv (fun z : ℝ => heatKernel t z) (x - y)
  let k' : ℝ → ℝ := fun y =>
    -deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u) (x - y)
  have hkderiv : ∀ y, HasDerivAt k (k' y) y := by
    intro y
    have hinner : HasDerivAt (fun q : ℝ => x - q) (-1) y := by
      simpa using (hasDerivAt_const y x).sub (hasDerivAt_id y)
    have hcomp :=
      (ShenWork.IntervalNeumannFullKernel.heatKernel_secondDeriv_hasDerivAt
        ht (x - y)).comp y hinner
    change HasDerivAt
      (fun q : ℝ => deriv (fun z : ℝ => heatKernel t z) (x - q))
      (-deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
        (x - y)) y
    convert hcomp using 1
    rw [ShenWork.IntervalNeumannFullKernel.deriv_deriv_heatKernel ht]
    ring
  have hkfd : Integrable (fun y => k y * deriv f y) := by
    have hbase := heatKernel_deriv_mul_bounded_integrable ht x hfd
      hfdcont.aestronglyMeasurable
    exact hbase.congr (Filter.Eventually.of_forall fun y => by
      dsimp [k]
      rw [deriv_heatKernel_translated_left ht, deriv_heatKernel ht])
  have hk'f : Integrable (fun y => k' y * f y) := by
    have hbase :=
      ShenWork.PaperOne.ConvLeibniz.secondDeriv_heatKernel_mul_bounded_integrable
        ht x hf (continuous_iff_continuousAt.2
          (fun y => (hfderiv y).continuousAt)).aestronglyMeasurable
    simpa [k'] using hbase.neg
  have hkf : Integrable (fun y => k y * f y) := by
    have hbase := heatKernel_deriv_mul_bounded_integrable ht x hf
      (continuous_iff_continuousAt.2
        (fun y => (hfderiv y).continuousAt)).aestronglyMeasurable
    exact hbase.congr (Filter.Eventually.of_forall fun y => by
      dsimp [k]
      rw [deriv_heatKernel_translated_left ht, deriv_heatKernel ht])
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := k) (v := f) (u' := k') (v' := deriv f)
    (fun y _ => hkderiv y) (fun y _ => hfderiv y) hkfd hk'f hkf
  have hbase :
      (∫ y : ℝ, k y * deriv f y) =
        ∫ y : ℝ,
          deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
            (x - y) * f y := by
    rw [hibp]
    rw [show (fun y : ℝ => k' y * f y) = fun y =>
        -(deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (x - y) * f y) by
      funext y
      dsimp [k']
      ring]
    rw [integral_neg, neg_neg]
  unfold wholeLineCauchyHeatHessOp wholeLineCauchyHeatGradOp
  have hgrad : (∫ y : ℝ, Real.exp (-t) *
      (deriv (fun z : ℝ => heatKernel t (z - y)) x * deriv f y)) =
      Real.exp (-t) * ∫ y : ℝ, k y * deriv f y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    rw [deriv_heatKernel_translated_left ht]
    dsimp [k]
    rw [deriv_heatKernel ht]
  rw [hgrad, hbase]

section WholeLineCauchyC2BootstrapAxiomAudit

#print axioms wholeLineCauchyHeatHessOp_eq_gradOp_deriv

end WholeLineCauchyC2BootstrapAxiomAudit

end ShenWork.Paper1
