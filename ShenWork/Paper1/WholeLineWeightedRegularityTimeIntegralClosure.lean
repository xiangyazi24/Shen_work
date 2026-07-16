import ShenWork.Paper1.WholeLineWeightedRegularityTimeClosure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter MeasureTheory Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Time differentiation from a concrete `L²` increment identity

The canonical weighted trajectory need not be differentiated by a spatial
pointwise dominator.  Once its increments are represented as a Bochner
integral of a continuous `L²` velocity, the Banach-valued fundamental theorem
of calculus gives its derivative directly.
-/

/-- A local Bochner increment identity against a continuous velocity gives
the strong derivative of the trajectory. -/
theorem hasDerivAt_of_eventually_eq_intervalIntegral_increment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {Z G : ℝ → E} {t : ℝ}
    (hG : Continuous G)
    (hinc : Z =ᶠ[𝓝 t]
      fun s => Z t + ∫ r in t..s, G r) :
    HasDerivAt Z (G t) t := by
  have hprim : HasDerivAt (fun s => ∫ r in t..s, G r) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hG.intervalIntegrable t t)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter
      hG.continuousAt
  have hrhs : HasDerivAt (fun s => Z t + ∫ r in t..s, G r) (G t) t := by
    convert (hasDerivAt_const t (Z t)).add hprim using 1 <;> simp only [Pi.add_apply, zero_add]
  exact hinc.hasDerivAt_iff.mpr hrhs

/-- The same closure with the velocity identified only at the target time. -/
theorem hasDerivAt_of_eventually_eq_intervalIntegral_increment_of_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {Z G : ℝ → E} {Zt : E} {t : ℝ}
    (hG : Continuous G)
    (hinc : Z =ᶠ[𝓝 t]
      fun s => Z t + ∫ r in t..s, G r)
    (hGt : G t = Zt) :
    HasDerivAt Z Zt t := by
  simpa only [hGt] using
    hasDerivAt_of_eventually_eq_intervalIntegral_increment hG hinc

/-- Concrete `hhalf` endpoint from a continuous canonical `L²` material
velocity and its local Bochner increment identity.  This replaces the
pointwise-in-space common dominator by the natural Hilbert trajectory. -/
theorem paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_increment
    (p : CMParams) {T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu : ∀ x, 0 ≤ coMovingPath c u t x)
    (hu1 : ContDiff ℝ 1 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU1 : ContDiff ℝ 1 U) (hV2 : ContDiff ℝ 2 V)
    (hW_meas : ∀ᶠ s in nhds t,
      AEStronglyMeasurable
        (paper5WeightedPopulation eta (coMovingPath c u) U s) volume)
    (hclose : ∀ᶠ s in nhds t, Integrable (fun x : ℝ =>
      Real.exp (2 * eta * x) *
        |coMovingPath c u s x - U x| ^ 2) volume)
    (hWt_meas : AEStronglyMeasurable
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t) volume)
    (hgenerator_sq : Integrable (fun x : ℝ =>
      (paper5WeightedPopulationXX eta (coMovingPath c u) U t x +
        (c - 2 * eta) *
          paper5WeightedPopulationX eta (coMovingPath c u) U t x +
        (eta ^ 2 - c * eta) *
          paper5WeightedPopulation eta (coMovingPath c u) U t x) ^ 2)
      volume)
    (hforcing_sq : Integrable (fun x : ℝ =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V t x ^ 2) volume)
    {G : ℝ → WholeLineRealL2}
    (hG : Continuous G)
    (hinc :
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s)) =ᶠ[𝓝 t]
      fun s =>
        wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U t) +
          ∫ r in t..s, G r)
    (hGt : G t = wholeLineRealL2Total
      (paper5WeightedPopulationT eta
        (paper5CoMovingMaterialTime c u) t)) :
    HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x : ℝ,
        paper5WeightedPopulation eta (coMovingPath c u) U t x *
          paper5WeightedPopulationT eta
            (paper5CoMovingMaterialTime c u) t x) t := by
  have hZ : HasDerivAt
      (fun s => wholeLineRealL2Total
        (paper5WeightedPopulation eta (coMovingPath c u) U s))
      (wholeLineRealL2Total
        (paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t)) t :=
    hasDerivAt_of_eventually_eq_intervalIntegral_increment_of_eq
      hG hinc hGt
  exact
    paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_canonicalL2
      p hsol ht0 htT hTW hu hu1 hv2 hU1 hV2 hW_meas hclose
        hWt_meas hgenerator_sq hforcing_sq hZ

section AxiomAudit

#print axioms hasDerivAt_of_eventually_eq_intervalIntegral_increment
#print axioms hasDerivAt_of_eventually_eq_intervalIntegral_increment_of_eq
#print axioms
  paper5WeightedHalfEnergy_hasDerivAt_of_generatorForcing_and_increment

end AxiomAudit

end ShenWork.Paper1
