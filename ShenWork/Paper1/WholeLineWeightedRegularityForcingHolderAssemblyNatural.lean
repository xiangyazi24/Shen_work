import ShenWork.Paper1.WholeLineWeightedRegularityGradientCandidateNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGradientTimeNatural
import ShenWork.Paper1.WholeLineWeightedRegularityForcingPowerHolderPhysicalWindow

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Natural assembly of the exact-weight forcing modulus

This file joins the exact-weight `H⁰/H¹` Hilbert trajectories to the
uniform forcing estimate.  In particular, the continuity and Hölder modulus
of the physical generator forcing are conclusions, not assumptions.
-/

/-- A nonnegative continuous scalar field has a measurable arbitrary real
power.  This auxiliary statement also covers the negative exponent occurring
in the secant derivative when `1 < m < 2`. -/
theorem measurable_rpow_const_of_continuous_nonneg
    {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ x, 0 ≤ f x)
    (q : ℝ) : Measurable (fun x => f x ^ q) := by
  by_cases hq : q = 0
  · subst q
    simpa only [Real.rpow_zero] using measurable_const
  · have hpoint : (fun x => f x ^ q) = fun x =>
        if f x = 0 then 0 else Real.exp (Real.log (f x) * q) := by
      funext x
      by_cases hx : f x = 0
      · rw [hx, Real.zero_rpow hq, if_pos rfl]
      · rw [if_neg hx, Real.rpow_def_of_pos (lt_of_le_of_ne
          (hfnn x) (Ne.symm hx))]
    rw [hpoint]
    exact Measurable.ite
      (measurableSet_eq_fun hf.measurable measurable_const)
      measurable_const
      (Real.measurable_exp.comp
        ((Real.measurable_log.comp hf.measurable).mul_const q))

/-- Spatial measurability of the paper's secant coefficient follows from
continuity and nonnegativity of its two profiles. -/
theorem paper5A_measurable_of_continuous_nonneg
    (beta : ℝ) {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {t : ℝ}
    (hu : Continuous (u t)) (hU : Continuous U)
    (hu0 : ∀ x, 0 ≤ u t x) (hU0 : ∀ x, 0 ≤ U x) :
    Measurable (paper5A beta u U t) := by
  unfold paper5A paper5MeanCoefficient
  exact Measurable.ite
    (measurableSet_eq_fun hu.measurable hU.measurable)
    (measurable_const.mul
      (measurable_rpow_const_of_continuous_nonneg hu hu0 (beta - 1)))
    (((measurable_rpow_const_of_continuous_nonneg hu hu0 beta).sub
      (measurable_rpow_const_of_continuous_nonneg hU hU0 beta)).div
        (hu.measurable.sub hU.measurable))

/-- Almost-everywhere strong form of
`paper5A_measurable_of_continuous_nonneg`. -/
theorem paper5A_aestronglyMeasurable_of_continuous_nonneg
    (beta : ℝ) {u : ℝ → ℝ → ℝ} {U : ℝ → ℝ} {t : ℝ}
    (hu : Continuous (u t)) (hU : Continuous U)
    (hu0 : ∀ x, 0 ≤ u t x) (hU0 : ∀ x, 0 ≤ U x) :
    AEStronglyMeasurable (paper5A beta u U t) volume :=
  (paper5A_measurable_of_continuous_nonneg beta hu hU hu0 hU0).aestronglyMeasurable

/-- The expanded forcing at one time depends only on the two spatial slices
at that time.  This is the bridge used after clamping a compact time window. -/
theorem paper5WeightedGeneratorForcingExpandedTrajectory_congr_slice
    (p : CMParams) (eta q : ℝ)
    {u₁ u₂ v₁ v₂ : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hu : u₁ q = u₂ q) (hv : v₁ q = v₂ q) :
    paper5WeightedGeneratorForcingExpandedTrajectory p eta u₁ v₁ U
        (paper5WeightedPopulation eta u₁ U)
        (paper5WeightedPopulationX eta u₁ U)
        (paper5WeightedSignal eta v₁ V)
        (paper5WeightedSignalX eta v₁ V) q =
      paper5WeightedGeneratorForcingExpandedTrajectory p eta u₂ v₂ U
        (paper5WeightedPopulation eta u₂ U)
        (paper5WeightedPopulationX eta u₂ U)
        (paper5WeightedSignal eta v₂ V)
        (paper5WeightedSignalX eta v₂ V) q := by
  funext x
  simp only [paper5WeightedGeneratorForcingExpandedTrajectory,
    paper5WeightedFluxDerivativeExpandedTrajectory,
    paper5WeightedFluxDerivativeExpanded,
    paper5WeightedReactionExpandedTrajectory,
    paper5B1, paper5B2, paper5CorrectedChemZeroCoefficient, paper5A,
    paper5WeightedPopulation, paper5WeightedPopulationX,
    paper5WeightedSignal, paper5WeightedSignalX, hu, hv]

set_option maxHeartbeats 6000000 in
/-- The two exact-weight population Hilbert trajectories, together with
the already established uniform coefficient bounds, produce the canonical
physical forcing trajectory with a uniform Hölder modulus.  The weighted
signal bounds are reconstructed here from the frozen elliptic resolver;
no continuity or Hölder hypothesis on the forcing itself is assumed. -/
theorem
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_data_of_population_H1_trajectories_and_coefficient_data
    (p : CMParams) {M T eta c a b Hu Blog : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    {K₁ K₂ K₃ K₄ KR EW EWx HW HWx : ℝ}
    {W X : ℝ → WholeLineRealL2}
    (hab : a ≤ b) (hdiam : b - a ≤ 1)
    (ha : 0 < a) (hbT : b < T)
    (hM : 1 ≤ M) (heta : 0 < eta) (heta1 : eta < 1)
    (hsol : IsClassicalSolution p T u v)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c u q))
    (hv2 : ∀ q ∈ Set.Icc a b, ContDiff ℝ 2 (coMovingPath c v q))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huC : ∀ q ∈ Set.Icc a b, IsCUnifBdd (coMovingPath c u q))
    (hUC : IsCUnifBdd U)
    (huM : ∀ q ∈ Set.Icc a b, ∀ x,
      coMovingPath c u q x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hUpos : ∀ x, 0 < U x)
    (hvEq : ∀ q ∈ Set.Icc a b,
      coMovingPath c v q = frozenElliptic p (coMovingPath c u q))
    (hVEq : V = frozenElliptic p U)
    (hHu : 0 ≤ Hu)
    (huHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |coMovingPath c u s x - coMovingPath c u t x| ≤
        Hu * |s - t| ^ (1 / 2 : ℝ))
    (hBlog : 0 ≤ Blog)
    (hlog : ∀ x, |deriv U x / U x| ≤ Blog)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hK₃ : 0 ≤ K₃) (hK₄ : 0 ≤ K₄) (hKR : 0 ≤ KR)
    (hB₁_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p (coMovingPath c u) (coMovingPath c v) q x| ≤ K₁)
    (hB₂_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta
        (coMovingPath c u) (coMovingPath c v) U q x| ≤ K₂)
    (hB₃_bound : ∀ x, |paper5B3 p U x| ≤ K₃)
    (hB₄_bound : ∀ x,
      |paper5WeightedFluxSignalCoefficient p eta U x| ≤ K₄)
    (hR_bound : ∀ q ∈ Set.Icc a b, ∀ x,
      |1 - paper5A (1 + p.α) (coMovingPath c u) U q x| ≤ KR)
    (hB₁_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5B1 p (coMovingPath c u) (coMovingPath c v) q) volume)
    (hB₂_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta
        (coMovingPath c u) (coMovingPath c v) U q) volume)
    (hB₃_meas : AEStronglyMeasurable (paper5B3 p U) volume)
    (hB₄_meas : AEStronglyMeasurable
      (paper5WeightedFluxSignalCoefficient p eta U) volume)
    (hR_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) (coMovingPath c u) U q x) volume)
    (hF_sq_phys : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V q x ^ 2) volume)
    (hEW : 0 ≤ EW) (hEWx : 0 ≤ EWx)
    (hHW : 0 ≤ HW) (hHWx : 0 ≤ HWx)
    (hWrep : ∀ q ∈ Set.Icc a b,
      (((W q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulation eta (coMovingPath c u) U q))
    (hXrep : ∀ q ∈ Set.Icc a b,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta (coMovingPath c u) U q))
    (hWnorm : ∀ q ∈ Set.Icc a b, ‖W q‖ ≤ EW)
    (hXnorm : ∀ q ∈ Set.Icc a b, ‖X q‖ ≤ EWx)
    (hWmod : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖W s - W t‖ ≤ HW * |s - t| ^ paper5ForcingTimeExponent p)
    (hXmod : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖X s - X t‖ ≤ HWx * |s - t| ^ paper5ForcingTimeExponent p) :
    ∃ H : ℝ, 0 ≤ H ∧
      (∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
        ‖paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab s -
            paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab t‖ ≤
          H * |s - t| ^ paper5ForcingTimeExponent p) ∧
      Continuous
        (paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
          p eta c u v U V hab) ∧
      ∀ q ∈ Set.Icc a b,
        (((paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
              p eta c u v U V hab q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedGeneratorForcing p eta
            (coMovingPath c u) (coMovingPath c v) U V q) := by
  let uc : ℝ → ℝ → ℝ :=
    paper5PositiveWindowClamp hab (coMovingPath c u)
  let vc : ℝ → ℝ → ℝ :=
    paper5PositiveWindowClamp hab (coMovingPath c v)
  have hproj : ∀ q : ℝ,
      (Set.projIcc a b hab q : ℝ) ∈ Set.Icc a b :=
    fun q => (Set.projIcc a b hab q).2
  have huc_eq : ∀ q ∈ Set.Icc a b, uc q = coMovingPath c u q := by
    intro q hq
    dsimp only [uc, paper5PositiveWindowClamp]
    simpa using congrArg (fun z : Set.Icc a b => coMovingPath c u z.1)
      (Set.projIcc_of_mem hab hq)
  have hvc_eq : ∀ q ∈ Set.Icc a b, vc q = coMovingPath c v q := by
    intro q hq
    dsimp only [vc, paper5PositiveWindowClamp]
    simpa using congrArg (fun z : Set.Icc a b => coMovingPath c v z.1)
      (Set.projIcc_of_mem hab hq)
  have hucC : ∀ q, IsCUnifBdd (uc q) :=
    fun q => huC _ (hproj q)
  have hucM : ∀ q x, uc q x ∈ Set.Icc (0 : ℝ) M :=
    fun q x => huM _ (hproj q) x
  have hvcEq : ∀ q, vc q = frozenElliptic p (uc q) :=
    fun q => hvEq _ (hproj q)
  have huc2 : ∀ q, ContDiff ℝ 2 (uc q) :=
    fun q => hu2 _ (hproj q)
  have hvc2 : ∀ q, ContDiff ℝ 2 (vc q) :=
    fun q => hv2 _ (hproj q)
  have hucHolder : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, ∀ x,
      |uc s x - uc t x| ≤ Hu * |s - t| ^ (1 / 2 : ℝ) := by
    intro s hs t ht x
    rw [huc_eq s hs, huc_eq t ht]
    exact huHolder s hs t ht x
  have hW_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulation eta uc U q) volume := by
    intro q
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((huc2 q).continuous.sub hU2.continuous)).aestronglyMeasurable
  have hWx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedPopulationX eta uc U q) volume := by
    intro q
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hux : Continuous (deriv (uc q)) :=
      (huc2 q).continuous_deriv (by norm_num)
    have hUx : Continuous (deriv U) := hU2.continuous_deriv (by norm_num)
    exact ((continuous_const.mul
        (hexp.mul ((huc2 q).continuous.sub hU2.continuous))).add
      (hexp.mul (hux.sub hUx))).aestronglyMeasurable
  have hZ_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignal eta vc V q) volume := by
    intro q
    exact ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        ((hvc2 q).continuous.sub hV2.continuous)).aestronglyMeasurable
  have hZx_meas : ∀ q, AEStronglyMeasurable
      (paper5WeightedSignalX eta vc V q) volume := by
    intro q
    have hexp : Continuous (fun x : ℝ => Real.exp (eta * x)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hvx : Continuous (deriv (vc q)) :=
      (hvc2 q).continuous_deriv (by norm_num)
    have hVx : Continuous (deriv V) := hV2.continuous_deriv (by norm_num)
    exact ((continuous_const.mul
        (hexp.mul ((hvc2 q).continuous.sub hV2.continuous))).add
      (hexp.mul (hvx.sub hVx))).aestronglyMeasurable
  have hW_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulation eta uc U q x ^ 2) volume := by
    intro q hq
    simpa only [paper5WeightedPopulation, huc_eq q hq] using
      integrable_sq_of_wholeLineRealL2_ae_eq (W q) (hWrep q hq)
  have hWx_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedPopulationX eta uc U q x ^ 2) volume := by
    intro q hq
    simpa only [paper5WeightedPopulationX, paper5WeightedPopulation,
      huc_eq q hq] using
      integrable_sq_of_wholeLineRealL2_ae_eq (X q) (hXrep q hq)
  have hWrep_c : ∀ q ∈ Set.Icc a b,
      (((W q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulation eta uc U q) := by
    intro q hq
    refine (hWrep q hq).trans (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulation
    rw [huc_eq q hq]
  have hXrep_c : ∀ q ∈ Set.Icc a b,
      (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
        paper5WeightedPopulationX eta uc U q) := by
    intro q hq
    refine (hXrep q hq).trans (Eventually.of_forall fun x => ?_)
    unfold paper5WeightedPopulationX paper5WeightedPopulation
    rw [huc_eq q hq]
  have hW_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      Integrable (fun x =>
        (paper5WeightedPopulation eta uc U s x -
          paper5WeightedPopulation eta uc U t x) ^ 2) volume := by
    intro s hs t ht
    exact integrable_sq_sub_of_integrable_sq
      (hW_meas s) (hW_meas t) (hW_sq s hs) (hW_sq t ht)
  have hWx_diff : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      Integrable (fun x =>
        (paper5WeightedPopulationX eta uc U s x -
          paper5WeightedPopulationX eta uc U t x) ^ 2) volume := by
    intro s hs t ht
    exact integrable_sq_sub_of_integrable_sq
      (hWx_meas s) (hWx_meas t) (hWx_sq s hs) (hWx_sq t ht)
  have hW_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedPopulation eta uc U q x ^ 2) ≤ EW ^ 2 := by
    intro q hq
    rw [← wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq (W q) (hWrep_c q hq)]
    nlinarith [hWnorm q hq, norm_nonneg (W q)]
  have hWx_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedPopulationX eta uc U q x ^ 2) ≤ EWx ^ 2 := by
    intro q hq
    rw [← wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq (X q) (hXrep_c q hq)]
    nlinarith [hXnorm q hq, norm_nonneg (X q)]
  have hW_diff_bound : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ, (paper5WeightedPopulation eta uc U s x -
        paper5WeightedPopulation eta uc U t x) ^ 2) ≤
        HW ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2 := by
    intro s hs t ht
    have hraw := wholeLineIntegral_sub_sq_le_of_norm_sub_le
      (W s) (W t)
      (hWrep_c s hs) (hWrep_c t ht)
      (mul_nonneg hHW (Real.rpow_nonneg (abs_nonneg _) _)) (hWmod s hs t ht)
    simpa only [mul_pow] using hraw
  have hWx_diff_bound : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      (∫ x : ℝ, (paper5WeightedPopulationX eta uc U s x -
        paper5WeightedPopulationX eta uc U t x) ^ 2) ≤
        HWx ^ 2 * (|s - t| ^ paper5ForcingTimeExponent p) ^ 2 := by
    intro s hs t ht
    have hraw := wholeLineIntegral_sub_sq_le_of_norm_sub_le
      (X s) (X t)
      (hXrep_c s hs) (hXrep_c t ht)
      (mul_nonneg hHWx (Real.rpow_nonneg (abs_nonneg _) _))
      (hXmod s hs t ht)
    simpa only [mul_pow] using hraw
  let RV := paper5WeightedResolverVFactor p M eta
  let RVx := paper5WeightedResolverVxFactor p M eta
  let EZ := Real.sqrt RV * EW
  let EZx := Real.sqrt RVx * EW
  have hRV : 0 ≤ RV := by
    unfold RV paper5WeightedResolverVFactor
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ)
        (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sq_nonneg (1 - eta))
  have hetaSq : eta ^ 2 < 1 := by
    have hp : 0 < (1 - eta) * (1 + eta) :=
      mul_pos (sub_pos.mpr heta1) (by linarith)
    nlinarith
  have hRVx : 0 ≤ RVx := by
    unfold RVx paper5WeightedResolverVxFactor
    exact div_nonneg
      (mul_nonneg (sq_nonneg p.γ)
        (Real.rpow_nonneg (zero_le_one.trans hM) _))
      (sub_nonneg.mpr hetaSq.le)
  have hEZ : 0 ≤ EZ := mul_nonneg (Real.sqrt_nonneg _) hEW
  have hEZx : 0 ≤ EZx := mul_nonneg (Real.sqrt_nonneg _) hEW
  have hsignal : ∀ q ∈ Set.Icc a b,
      Integrable (fun x => paper5WeightedSignal eta vc V q x ^ 2) volume ∧
      Integrable (fun x => paper5WeightedSignalX eta vc V q x ^ 2) volume ∧
      (∫ x : ℝ, paper5WeightedSignal eta vc V q x ^ 2) ≤
        RV * (∫ x : ℝ, paper5WeightedPopulation eta uc U q x ^ 2) ∧
      (∫ x : ℝ, paper5WeightedSignalX eta vc V q x ^ 2) ≤
        RVx * (∫ x : ℝ, paper5WeightedPopulation eta uc U q x ^ 2) := by
    intro q hq
    have hcoU : coMovingPath 0 uc q = uc q := by
      funext x
      simp [coMovingPath]
    have hcoV : coMovingPath 0 vc q = vc q := by
      funext x
      simp [coMovingPath]
    have hclose : Integrable (fun x =>
        Real.exp (2 * eta * x) * |uc q x - U x| ^ 2) volume := by
      refine (hW_sq q hq).congr (Eventually.of_forall fun x => ?_)
      change (Real.exp (eta * x) * (uc q x - U x)) ^ 2 =
        Real.exp (2 * eta * x) * |uc q x - U x| ^ 2
      rw [mul_pow, sq_abs]
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hclose_co : Integrable (fun x =>
        Real.exp (2 * eta * x) *
          |coMovingPath 0 uc q x - U x| ^ 2) volume := by
      simpa only [hcoU] using hclose
    simpa only [paper5WeightedSignal, paper5WeightedSignalX,
      paper5WeightedPopulation, hcoU, hcoV, RV, RVx] using
      paper5WeightedSignal_resolver_data p (c := 0) (t := q)
        (u := uc) (v := vc) (U := U) (V := V)
        hM heta heta1 (by simpa only [hcoU] using hucC q) hUC
        (by simpa only [hcoU] using hucM q) hUM
        (by simpa only [hcoU, hcoV] using hvcEq q)
        hVEq
        (by simpa only [hcoV] using
          (hvc2 q).differentiable (by norm_num))
        (hV2.differentiable (by norm_num)) hclose_co
  have hZ_sq := fun q hq => (hsignal q hq).1
  have hZx_sq := fun q hq => (hsignal q hq).2.1
  have hZ_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedSignal eta vc V q x ^ 2) ≤ EZ ^ 2 := by
    intro q hq
    calc
      (∫ x : ℝ, paper5WeightedSignal eta vc V q x ^ 2) ≤
          RV * (∫ x : ℝ,
            paper5WeightedPopulation eta uc U q x ^ 2) :=
        (hsignal q hq).2.2.1
      _ ≤ RV * EW ^ 2 := mul_le_mul_of_nonneg_left (hW_bound q hq) hRV
      _ = EZ ^ 2 := by
        dsimp only [EZ]
        rw [mul_pow, Real.sq_sqrt hRV]
  have hZx_bound : ∀ q ∈ Set.Icc a b,
      (∫ x : ℝ, paper5WeightedSignalX eta vc V q x ^ 2) ≤ EZx ^ 2 := by
    intro q hq
    calc
      (∫ x : ℝ, paper5WeightedSignalX eta vc V q x ^ 2) ≤
          RVx * (∫ x : ℝ,
            paper5WeightedPopulation eta uc U q x ^ 2) :=
        (hsignal q hq).2.2.2
      _ ≤ RVx * EW ^ 2 := mul_le_mul_of_nonneg_left (hW_bound q hq) hRVx
      _ = EZx ^ 2 := by
        dsimp only [EZx]
        rw [mul_pow, Real.sq_sqrt hRVx]
  have hB₁_meas_c : ∀ q, AEStronglyMeasurable (paper5B1 p uc vc q) volume := by
    intro q
    have hq := hproj q
    simpa only [uc, vc, paper5PositiveWindowClamp, paper5B1] using
      hB₁_meas (Set.projIcc a b hab q).1 hq
  have hB₂_meas_c : ∀ q, AEStronglyMeasurable
      (paper5WeightedFluxPopulationCoefficient p eta uc vc U q) volume := by
    intro q
    have hq := hproj q
    simpa only [uc, vc, paper5PositiveWindowClamp,
      paper5WeightedFluxPopulationCoefficient, paper5B1, paper5B2,
      paper5CorrectedChemZeroCoefficient, paper5A] using
      hB₂_meas (Set.projIcc a b hab q).1 hq
  have hR_meas_c : ∀ q, AEStronglyMeasurable
      (fun x => 1 - paper5A (1 + p.α) uc U q x) volume := by
    intro q
    have hq := hproj q
    simpa only [uc, paper5PositiveWindowClamp, paper5A] using
      hR_meas (Set.projIcc a b hab q).1 hq
  have hF_meas_phys : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedGeneratorForcing p eta
        (coMovingPath c u) (coMovingPath c v) U V q) volume := by
    intro q hq
    exact paper5WeightedGeneratorForcing_aestronglyMeasurable_of_classical_slices
      p (eta := eta) hsol (ha.trans_le hq.1) (hq.2.trans_lt hbT) hTW
        (hu2 q hq) (hv2 q hq) hU2 hV2
  have hExpandedEq : ∀ q ∈ Set.Icc a b,
      paper5WeightedGeneratorForcingExpandedTrajectory p eta uc vc U
          (paper5WeightedPopulation eta uc U)
          (paper5WeightedPopulationX eta uc U)
          (paper5WeightedSignal eta vc V)
          (paper5WeightedSignalX eta vc V) q =
        paper5WeightedGeneratorForcing p eta
          (coMovingPath c u) (coMovingPath c v) U V q := by
    intro q hq
    exact (paper5WeightedGeneratorForcingExpandedTrajectory_congr_slice
      p eta q (huc_eq q hq) (hvc_eq q hq)).trans
        (paper5WeightedGeneratorForcingExpandedTrajectory_fun_eq_generatorForcing
          p hsol (ha.trans_le hq.1) (hq.2.trans_lt hbT) hTW
            (fun x => (huM q hq x).1) ((hu2 q hq).of_le (by norm_num))
            (hv2 q hq) (hU2.of_le (by norm_num)) hV2)
  have hF_meas : ∀ q ∈ Set.Icc a b, AEStronglyMeasurable
      (paper5WeightedGeneratorForcingExpandedTrajectory p eta uc vc U
        (paper5WeightedPopulation eta uc U)
        (paper5WeightedPopulationX eta uc U)
        (paper5WeightedSignal eta vc V)
        (paper5WeightedSignalX eta vc V) q) volume := by
    intro q hq
    exact (hF_meas_phys q hq).congr
      (Eventually.of_forall fun x => congrFun (hExpandedEq q hq).symm x)
  have hF_sq : ∀ q ∈ Set.Icc a b, Integrable (fun x =>
      paper5WeightedGeneratorForcingExpandedTrajectory p eta uc vc U
        (paper5WeightedPopulation eta uc U)
        (paper5WeightedPopulationX eta uc U)
        (paper5WeightedSignal eta vc V)
        (paper5WeightedSignalX eta vc V) q x ^ 2) volume := by
    intro q hq
    exact (hF_sq_phys q hq).congr
      (Eventually.of_forall fun x =>
        (congrArg (fun z : ℝ => z ^ 2) (congrFun (hExpandedEq q hq) x)).symm)
  have hB₁_bound_c : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5B1 p uc vc q x| ≤ K₁ := by
    intro q hq x
    have huq := huc_eq q hq
    have hvq := hvc_eq q hq
    simpa only [paper5B1, huq, hvq] using hB₁_bound q hq x
  have hB₂_bound_c : ∀ q ∈ Set.Icc a b, ∀ x,
      |paper5WeightedFluxPopulationCoefficient p eta uc vc U q x| ≤ K₂ := by
    intro q hq x
    have huq := huc_eq q hq
    have hvq := hvc_eq q hq
    simpa only [paper5WeightedFluxPopulationCoefficient, paper5B1, paper5B2,
      paper5CorrectedChemZeroCoefficient, paper5A, huq, hvq] using
      hB₂_bound q hq x
  have hR_bound_c : ∀ q ∈ Set.Icc a b, ∀ x,
      |1 - paper5A (1 + p.α) uc U q x| ≤ KR := by
    intro q hq x
    have huq := huc_eq q hq
    simpa only [paper5A, huq] using hR_bound q hq x
  have hExpandedHolder :=
    exists_paper5WeightedGeneratorForcingExpandedPositiveWindowL2Trajectory_natural_uniform_holder
      p hab hdiam hM heta heta1 hucC hucM hUM hUpos
        hBlog hlog hvcEq
        (fun q => (hvc2 q).differentiable (by norm_num))
        hHu hucHolder hK₁ hK₂ hK₃ hK₄ hKR hEW hEWx hEZ hEZx
        hHW hHWx hB₁_bound_c hB₂_bound_c hB₃_bound hB₄_bound hR_bound_c
        hB₁_meas_c hB₂_meas_c hB₃_meas hB₄_meas hR_meas_c
        hW_meas hWx_meas hZ_meas hZx_meas hF_meas hF_sq
        hW_diff hWx_diff hW_sq hWx_sq hZ_sq hZx_sq
        hW_diff_bound hWx_diff_bound hW_bound hWx_bound hZ_bound hZx_bound
  have hClampTrajectoryEq :
      wholeLineRealL2PositiveWindowTrajectory hab
          (paper5WeightedGeneratorForcingExpandedTrajectory p eta uc vc U
            (paper5WeightedPopulation eta uc U)
            (paper5WeightedPopulationX eta uc U)
            (paper5WeightedSignal eta vc V)
            (paper5WeightedSignalX eta vc V)) =
        wholeLineRealL2PositiveWindowTrajectory hab
          (paper5WeightedGeneratorForcingExpandedTrajectory p eta
            (coMovingPath c u) (coMovingPath c v) U
            (paper5WeightedPopulation eta (coMovingPath c u) U)
            (paper5WeightedPopulationX eta (coMovingPath c u) U)
            (paper5WeightedSignal eta (coMovingPath c v) V)
            (paper5WeightedSignalX eta (coMovingPath c v) V)) := by
    apply wholeLineRealL2PositiveWindowTrajectory_congr
    intro q hq
    exact paper5WeightedGeneratorForcingExpandedTrajectory_congr_slice
      p eta q (huc_eq q hq) (hvc_eq q hq)
  have hExpandedHolderPhysical : ∃ H : ℝ, 0 ≤ H ∧
      ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖wholeLineRealL2PositiveWindowTrajectory hab
            (paper5WeightedGeneratorForcingExpandedTrajectory p eta
              (coMovingPath c u) (coMovingPath c v) U
              (paper5WeightedPopulation eta (coMovingPath c u) U)
              (paper5WeightedPopulationX eta (coMovingPath c u) U)
              (paper5WeightedSignal eta (coMovingPath c v) V)
              (paper5WeightedSignalX eta (coMovingPath c v) V)) s -
          wholeLineRealL2PositiveWindowTrajectory hab
            (paper5WeightedGeneratorForcingExpandedTrajectory p eta
              (coMovingPath c u) (coMovingPath c v) U
              (paper5WeightedPopulation eta (coMovingPath c u) U)
              (paper5WeightedPopulationX eta (coMovingPath c u) U)
              (paper5WeightedSignal eta (coMovingPath c v) V)
              (paper5WeightedSignalX eta (coMovingPath c v) V)) t‖ ≤
        H * |s - t| ^ paper5ForcingTimeExponent p := by
    rw [← hClampTrajectoryEq]
    exact hExpandedHolder
  obtain ⟨H, hH, hholder⟩ :=
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_of_expanded
      p hab ha hbT hsol hTW (fun q hq x => (huM q hq x).1)
        hu2 hv2 hU2 hV2 hExpandedHolderPhysical
  refine ⟨H, hH, hholder,
    wholeLineRealL2PositiveWindowTrajectory_continuous_of_holder
      hab (paper5ForcingTimeExponent_pos p) hH hholder, ?_⟩
  intro q hq
  exact paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_coe_ae
    p eta c u v U V hab hF_meas_phys hF_sq_phys hq

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.measurable_rpow_const_of_continuous_nonneg
#print axioms
  ShenWork.Paper1.paper5A_aestronglyMeasurable_of_continuous_nonneg
#print axioms
  ShenWork.Paper1.paper5WeightedGeneratorForcingExpandedTrajectory_congr_slice
#print axioms
  ShenWork.Paper1.exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_holder_data_of_population_H1_trajectories_and_coefficient_data
