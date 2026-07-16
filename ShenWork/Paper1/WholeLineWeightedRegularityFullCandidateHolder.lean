import ShenWork.Paper1.WholeLineWeightedRegularityDuhamelHolder

open Filter MeasureTheory Set Topology
open scoped RealInnerProductSpace Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Interior time modulus for the full weighted mild candidate

The homogeneous datum is already a positive heat lag on an interior window,
so it is Lipschitz.  The Duhamel history has the square-root modulus proved by
the near/far split.  Combining the two gives the exact state modulus consumed
by the quantitative nonlinear-forcing closure.
-/

/-- The complete full-generator mild candidate is square-root Hölder on an
interior window under a uniform exact-weight forcing budget and measurable
heat histories. -/
theorem weightedMovingHeatFullGeneratorCandidate_sub_norm_le_sqrt_of_history_measurable
    {eta c a R s t delta K : ℝ}
    (hdelta : 0 < delta) (hK : 0 ≤ K)
    (hsInterior : a + delta ≤ s) (hst : s ≤ t) (htR : t ≤ R)
    (hstep : 0 < t - s)
    (hsmall : t - s ≤ min (delta / 2) 1)
    {F : ℝ → WholeLineRealL2} (Z₀ : WholeLineRealL2)
    (hF : ∀ q ∈ Set.Icc a R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ r : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      (volume.restrict (Set.Icc a R))) :
    ‖weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t -
        weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F s‖ ≤
      (weightedMovingHeatGeneratorHorizonConst eta c (R - a) * delta⁻¹ *
          ‖Z₀‖ +
        3 * Real.exp (|eta ^ 2 - c * eta| * (R - a)) * K +
        2 * weightedMovingHeatGeneratorHorizonConst eta c (R - a) * K *
          Real.sqrt (R - a)) * Real.sqrt (t - s) := by
  have has : a ≤ s := by linarith
  have hat : a ≤ t := has.trans hst
  have haR : a < R := by linarith
  have hsR : s ≤ R := hst.trans htR
  have hr : 0 < s - a := by linarith
  have hh0 : 0 ≤ t - s := hstep.le
  have hrhR : (s - a) + (t - s) ≤ R - a := by linarith
  have hhom0 := weightedMovingHeatL2Semigroup_sub_norm_le_of_positive_lag
    (eta := eta) (c := c) hr hh0 hrhR Z₀
  have hinv : (s - a)⁻¹ ≤ delta⁻¹ := by
    have hdsa : delta ≤ s - a := by linarith
    simpa only [one_div] using one_div_le_one_div_of_le hdelta hdsa
  have hCg0 :
      0 ≤ weightedMovingHeatGeneratorHorizonConst eta c (R - a) :=
    weightedMovingHeatGeneratorHorizonConst_nonneg (sub_nonneg.mpr haR.le)
  have hcoef0 :
      0 ≤ weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
        delta⁻¹ * ‖Z₀‖ := by positivity
  have hhom :
      ‖weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
          weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ ≤
        (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
          delta⁻¹ * ‖Z₀‖) * (t - s) := by
    calc
      ‖weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
          weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ =
          ‖weightedMovingHeatL2Semigroup eta c
              ((s - a) + (t - s)) Z₀ -
            weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ := by
        congr 3
        ring
      _ ≤ (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
            (s - a)⁻¹ * ‖Z₀‖) * (t - s) := hhom0
      _ ≤ (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
            delta⁻¹ * ‖Z₀‖) * (t - s) := by
        gcongr
  have hstep_one : t - s ≤ 1 := hsmall.trans (min_le_right _ _)
  have hle_sqrt : t - s ≤ Real.sqrt (t - s) := by
    rw [Real.le_sqrt' hstep]
    nlinarith
  have hhom_sqrt :
      ‖weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
          weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ ≤
        (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
          delta⁻¹ * ‖Z₀‖) * Real.sqrt (t - s) :=
    hhom.trans (mul_le_mul_of_nonneg_left hle_sqrt hcoef0)
  have hduh :=
    weightedMovingHeatL2Semigroup_duhamel_sub_norm_le_sqrt_of_history_measurable
      (eta := eta) (c := c) hdelta hK hsInterior hst htR hstep hsmall
      hF hhist_meas
  unfold weightedMovingHeatFullGeneratorCandidate
  calc
    ‖(weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
          ∫ q in a..t,
            weightedMovingHeatL2Semigroup eta c (t - q) (F q)) -
        (weightedMovingHeatL2Semigroup eta c (s - a) Z₀ +
          ∫ q in a..s,
            weightedMovingHeatL2Semigroup eta c (s - q) (F q))‖ ≤
        ‖weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
            weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ +
          ‖(∫ q in a..t,
              weightedMovingHeatL2Semigroup eta c (t - q) (F q)) -
            ∫ q in a..s,
              weightedMovingHeatL2Semigroup eta c (s - q) (F q)‖ := by
      have hrewrite :
          (weightedMovingHeatL2Semigroup eta c (t - a) Z₀ +
              ∫ q in a..t,
                weightedMovingHeatL2Semigroup eta c (t - q) (F q)) -
            (weightedMovingHeatL2Semigroup eta c (s - a) Z₀ +
              ∫ q in a..s,
                weightedMovingHeatL2Semigroup eta c (s - q) (F q)) =
          (weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
              weightedMovingHeatL2Semigroup eta c (s - a) Z₀) +
            ((∫ q in a..t,
                weightedMovingHeatL2Semigroup eta c (t - q) (F q)) -
              ∫ q in a..s,
                weightedMovingHeatL2Semigroup eta c (s - q) (F q)) := by
        abel
      rw [hrewrite]
      exact norm_add_le _ _
    _ ≤ (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
          delta⁻¹ * ‖Z₀‖) * Real.sqrt (t - s) +
        (3 * Real.exp (|eta ^ 2 - c * eta| * (R - a)) * K +
          2 * weightedMovingHeatGeneratorHorizonConst eta c (R - a) * K *
            Real.sqrt (R - a)) * Real.sqrt (t - s) :=
      add_le_add hhom_sqrt hduh
    _ = (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
            delta⁻¹ * ‖Z₀‖ +
          3 * Real.exp (|eta ^ 2 - c * eta| * (R - a)) * K +
          2 * weightedMovingHeatGeneratorHorizonConst eta c (R - a) * K *
            Real.sqrt (R - a)) * Real.sqrt (t - s) := by ring

section AxiomAudit

#print axioms
  weightedMovingHeatFullGeneratorCandidate_sub_norm_le_sqrt_of_history_measurable

end AxiomAudit

end ShenWork.Paper1
