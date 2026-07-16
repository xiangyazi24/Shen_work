import ShenWork.Paper1.WholeLineWeightedRegularityCompactHolderClosure
import ShenWork.Paper1.WholeLineWeightedRegularityDuhamelHolder
import ShenWork.Paper1.WholeLineWeightedRegularitySemigroupTimeModulus

open Filter MeasureTheory Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Uniform interior modulus for the full weighted mild candidate

The homogeneous heat orbit is Lipschitz after a positive lag and the
Duhamel history is square-root Hölder.  Compact-window boundedness closes
the estimate for time pairs outside the near-diagonal regime.
-/

/-- On a compact window strictly after its restart face, a uniformly forced
full-generator candidate admits one square-root Hölder constant for all
time pairs. -/
theorem
    exists_weightedMovingHeatFullGeneratorCandidate_uniform_sqrt_holder
    {eta c a L R K B : ℝ}
    (haL : a < L) (hLR : L ≤ R) (hK : 0 ≤ K) (hB : 0 ≤ B)
    {F : ℝ → WholeLineRealL2} (Z₀ : WholeLineRealL2)
    (hF : ∀ q ∈ Set.Icc a R, ‖F q‖ ≤ K)
    (hhist_meas : ∀ r : ℝ, AEStronglyMeasurable
      (fun q => weightedMovingHeatL2Semigroup eta c (r - q) (F q))
      (volume.restrict (Set.Icc a R)))
    (hcandidate_bound : ∀ q ∈ Set.Icc L R,
      ‖weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F q‖ ≤ B) :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc L R, ∀ t ∈ Set.Icc L R,
        ‖weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F s -
            weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t‖ ≤
          H * Real.sqrt |s - t| := by
  let delta : ℝ := L - a
  let rho : ℝ := min (delta / 2) 1
  let CH : ℝ := weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
    delta⁻¹ * ‖Z₀‖
  let CD : ℝ :=
    3 * Real.exp (|eta ^ 2 - c * eta| * (R - a)) * K +
      2 * weightedMovingHeatGeneratorHorizonConst eta c (R - a) * K *
        Real.sqrt (R - a)
  let C : ℝ := CH + CD
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min (by positivity) zero_lt_one
  have hRa : 0 ≤ R - a := by linarith
  have hGen : 0 ≤ weightedMovingHeatGeneratorHorizonConst eta c (R - a) :=
    weightedMovingHeatGeneratorHorizonConst_nonneg hRa
  have hCH : 0 ≤ CH := by
    dsimp only [CH]
    positivity
  have hCD : 0 ≤ CD := by
    dsimp only [CD]
    positivity
  have hC : 0 ≤ C := add_nonneg hCH hCD
  apply exists_uniform_sqrt_holder_of_local_and_bound hrho hC hB
    hcandidate_bound
  intro s hs t ht hst hstepSmall
  have has : a ≤ s := haL.le.trans hs.1
  have hat : a ≤ t := has.trans hst.le
  have htR : t ≤ R := ht.2
  have hstep : 0 < t - s := sub_pos.mpr hst
  have hsmall : t - s ≤ min (delta / 2) 1 := by
    simpa only [rho] using hstepSmall
  have hsInterior : a + delta ≤ s := by
    dsimp only [delta]
    linarith [hs.1]
  have hhomRaw := weightedMovingHeatL2Semigroup_sub_norm_le_of_positive_lag
    (eta := eta) (c := c) (H := R - a)
      (r := s - a) (h := t - s)
      (sub_pos.mpr (haL.trans_le hs.1)) hstep.le (by linarith [htR]) Z₀
  have hinv : (s - a)⁻¹ ≤ delta⁻¹ := by
    have hda : 0 < delta := hdelta
    have hds : delta ≤ s - a := by dsimp only [delta]; linarith [hs.1]
    simpa only [one_div] using one_div_le_one_div_of_le hda hds
  have hstep1 : t - s ≤ 1 :=
    hsmall.trans (min_le_right _ _)
  have hleSqrt : t - s ≤ Real.sqrt (t - s) := by
    rw [Real.le_sqrt' hstep]
    nlinarith
  have hhom :
      ‖weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
          weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ ≤
        CH * Real.sqrt (t - s) := by
    calc
      ‖weightedMovingHeatL2Semigroup eta c (t - a) Z₀ -
          weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ =
        ‖weightedMovingHeatL2Semigroup eta c ((s - a) + (t - s)) Z₀ -
          weightedMovingHeatL2Semigroup eta c (s - a) Z₀‖ := by
            congr 3
            ring
      _ ≤ (weightedMovingHeatGeneratorHorizonConst eta c (R - a) *
          (s - a)⁻¹ * ‖Z₀‖) * (t - s) := hhomRaw
      _ ≤ CH * (t - s) := by
        apply mul_le_mul_of_nonneg_right _ hstep.le
        dsimp only [CH]
        gcongr
      _ ≤ CH * Real.sqrt (t - s) :=
        mul_le_mul_of_nonneg_left hleSqrt hCH
  have hduh :=
    weightedMovingHeatL2Semigroup_duhamel_sub_norm_le_sqrt_of_history_measurable
      (eta := eta) (c := c) hdelta hK hsInterior hst.le htR hstep hsmall
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
        rw [show
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
                weightedMovingHeatL2Semigroup eta c (s - q) (F q)) by abel]
        exact norm_add_le _ _
    _ ≤ CH * Real.sqrt (t - s) + CD * Real.sqrt (t - s) := by
      exact add_le_add hhom (by simpa only [CD] using hduh)
    _ = C * Real.sqrt (t - s) := by
      dsimp only [C]
      ring

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.exists_weightedMovingHeatFullGeneratorCandidate_uniform_sqrt_holder
