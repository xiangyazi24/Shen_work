import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroForcingNatural
import ShenWork.Paper1.WholeLineWeightedRegularityNaturalCoreProducer
import ShenWork.Paper1.WholeLineWeightedRegularityRemainderNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Exact weighted energy at zero sensitivity

For `chi = 0` the signal terms disappear from the perturbation energy.
The lower-order source is the weighted logistic reaction difference plus the
scalar conjugation term.  This gives a direct energy estimate without the
resolver factors used in the nonzero-sensitivity proof.
-/

/-- At zero sensitivity, the corrected lower-order remainder is controlled
only by the weighted population.  This is the reaction-only replacement for
the resolver estimate in the nonzero-sensitivity energy producer. -/
theorem paper5CorrectedRemainderIntegral_le_chi_zero
    (p : CMParams) (hchi : p.χ = 0) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2)) :
    let W := paper5WeightedPopulation eta (coMovingPath c u) U t
    let R := paper5CorrectedRemainderDensity p eta c
      (coMovingPath c u) (coMovingPath c v) U W
      (paper5WeightedPopulationX eta (coMovingPath c u) U t)
      (paper5WeightedSignal eta (coMovingPath c v) V t)
      (paper5WeightedSignalX eta (coMovingPath c v) V t) t
    Integrable R ∧
      (∫ x : ℝ, R x) ≤
        (eta ^ 2 - c * eta + reactionLip p.α M) *
          ∫ x : ℝ, W x ^ 2 := by
  dsimp only
  let W : ℝ → ℝ :=
    paper5WeightedPopulation eta (coMovingPath c u) U t
  let F : ℝ → ℝ := paper5WeightedGeneratorForcing p eta
    (coMovingPath c u) (coMovingPath c v) U V t
  let R : ℝ → ℝ := paper5CorrectedRemainderDensity p eta c
    (coMovingPath c u) (coMovingPath c v) U W
    (paper5WeightedPopulationX eta (coMovingPath c u) U t)
    (paper5WeightedSignal eta (coMovingPath c v) V t)
    (paper5WeightedSignalX eta (coMovingPath c v) V t) t
  have huC : IsCUnifBdd (coMovingPath c u t) := by
    refine ⟨hu2.continuous, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (huM x).1]
    exact (huM x).2
  have hUC : IsCUnifBdd U := by
    refine ⟨hU2.continuous, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (hUM x).1]
    exact (hUM x).2
  have hW2 : Integrable (fun x => W x ^ 2) := by
    dsimp only [W]
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  have hF2 : Integrable (fun x => F x ^ 2) := by
    dsimp only [F]
    exact (paper5WeightedGeneratorForcing_chi_zero_l2_data
      p hchi hM huC hUC huM hUM hclose).1
  have hWcont : Continuous W := by
    dsimp only [W]
    unfold paper5WeightedPopulation
    exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul
        (hu2.continuous.sub hU2.continuous)
  have hFcont : Continuous F := by
    dsimp only [F]
    exact paper5WeightedGeneratorForcing_continuous_of_classical_slices
      p hsol ht0 htT hTW hu2 hv2 hU2 hV2
  have hWF : Integrable (fun x => W x * F x) :=
    integrable_mul_of_sq_integrable_of_continuous
      hWcont hFcont hW2 hF2
  have hgrowth : Integrable (fun x =>
      (eta ^ 2 - c * eta) * W x ^ 2) :=
    hW2.const_mul (eta ^ 2 - c * eta)
  have hR : Integrable R := by
    refine (hWF.add hgrowth).congr (Eventually.of_forall fun x => ?_)
    have hsource :=
      paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
        p (eta := eta) (c := c) hsol ht0 htT hTW
          (huM x).1 (hTW.U_pos x).le
          (hu2.of_le (by norm_num)) hv2
          (hU2.of_le (by norm_num)) hV2
    change W x * F x + (eta ^ 2 - c * eta) * W x ^ 2 = R x
    rw [show F x =
        paper5WeightedLowerOrderSource p eta c
            (coMovingPath c u) (coMovingPath c v) U W
            (paper5WeightedPopulationX eta (coMovingPath c u) U t)
            (paper5WeightedSignal eta (coMovingPath c v) V t)
            (paper5WeightedSignalX eta (coMovingPath c v) V t) t x -
          (eta ^ 2 - c * eta) * W x by
        simpa only [F, W] using hsource.symm]
    rw [show R x = W x * paper5WeightedLowerOrderSource p eta c
          (coMovingPath c u) (coMovingPath c v) U W
          (paper5WeightedPopulationX eta (coMovingPath c u) U t)
          (paper5WeightedSignal eta (coMovingPath c v) V t)
          (paper5WeightedSignalX eta (coMovingPath c v) V t) t x by
      simpa only [R] using
        paper5CorrectedRemainderDensity_eq_population_mul_lowerOrderSource
          p eta c (coMovingPath c u) (coMovingPath c v) U W
            (paper5WeightedPopulationX eta (coMovingPath c u) U t)
            (paper5WeightedSignal eta (coMovingPath c v) V t)
            (paper5WeightedSignalX eta (coMovingPath c v) V t) t x]
    ring
  have hLip : 0 ≤ reactionLip p.α M := reactionLip_nonneg p.hα hM
  have hFpoint : ∀ x, |F x| ≤ reactionLip p.α M * |W x| := by
    intro x
    have hr := reaction_increment_abs_le p.hα hM (hUM x) (huM x)
    rw [show F x = weightedReactionDifference p eta
        (coMovingPath c u t) U x by
      exact paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
        p hchi eta (coMovingPath c u) (coMovingPath c v) U V t x]
    unfold weightedReactionDifference W paper5WeightedPopulation
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
      abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (eta * x) *
          |reactionFun p.α (coMovingPath c u t x) - reactionFun p.α (U x)| ≤
        Real.exp (eta * x) *
          (reactionLip p.α M * |coMovingPath c u t x - U x|) :=
        mul_le_mul_of_nonneg_left hr (Real.exp_nonneg _)
      _ = reactionLip p.α M *
          (Real.exp (eta * x) * |coMovingPath c u t x - U x|) := by ring
  have hWFpoint : ∀ x, W x * F x ≤ reactionLip p.α M * W x ^ 2 := by
    intro x
    calc
      W x * F x ≤ |W x * F x| := le_abs_self _
      _ = |W x| * |F x| := abs_mul _ _
      _ ≤ |W x| * (reactionLip p.α M * |W x|) :=
        mul_le_mul_of_nonneg_left (hFpoint x) (abs_nonneg _)
      _ = reactionLip p.α M * W x ^ 2 := by
        rw [← sq_abs]
        ring
  have hpoint : ∀ x, R x ≤
      (eta ^ 2 - c * eta + reactionLip p.α M) * W x ^ 2 := by
    intro x
    have hsource :=
      paper5WeightedLowerOrderSource_sub_growth_eq_generatorForcing
        p (eta := eta) (c := c) hsol ht0 htT hTW
          (huM x).1 (hTW.U_pos x).le
          (hu2.of_le (by norm_num)) hv2
          (hU2.of_le (by norm_num)) hV2
    have hReq : R x = W x * F x +
        (eta ^ 2 - c * eta) * W x ^ 2 := by
      rw [show R x = W x * paper5WeightedLowerOrderSource p eta c
            (coMovingPath c u) (coMovingPath c v) U W
            (paper5WeightedPopulationX eta (coMovingPath c u) U t)
            (paper5WeightedSignal eta (coMovingPath c v) V t)
            (paper5WeightedSignalX eta (coMovingPath c v) V t) t x by
        simpa only [R] using
          paper5CorrectedRemainderDensity_eq_population_mul_lowerOrderSource
            p eta c (coMovingPath c u) (coMovingPath c v) U W
              (paper5WeightedPopulationX eta (coMovingPath c u) U t)
              (paper5WeightedSignal eta (coMovingPath c v) V t)
              (paper5WeightedSignalX eta (coMovingPath c v) V t) t x]
      rw [show paper5WeightedLowerOrderSource p eta c
            (coMovingPath c u) (coMovingPath c v) U W
            (paper5WeightedPopulationX eta (coMovingPath c u) U t)
            (paper5WeightedSignal eta (coMovingPath c v) V t)
            (paper5WeightedSignalX eta (coMovingPath c v) V t) t x =
          F x + (eta ^ 2 - c * eta) * W x by
        dsimp only [F, W]
        linarith [hsource]]
      ring
    rw [hReq]
    nlinarith [hWFpoint x]
  refine ⟨hR, ?_⟩
  calc
    (∫ x : ℝ, R x) ≤ ∫ x : ℝ,
        (eta ^ 2 - c * eta + reactionLip p.α M) * W x ^ 2 :=
      integral_mono_ae hR
        (hW2.const_mul (eta ^ 2 - c * eta + reactionLip p.α M))
        (Eventually.of_forall hpoint)
    _ = (eta ^ 2 - c * eta + reactionLip p.α M) *
        ∫ x : ℝ, W x ^ 2 := by rw [integral_const_mul]

/-- Direct zero-sensitivity full-energy inequality from the three exact
generator core inputs.  No signal resolver estimate and no nonzero-`chi`
coefficient package occurs in the proof. -/
theorem paper5WeightedEnergy_deriv_le_chi_zero_of_coreIntegrability
    (p : CMParams) (hchi : p.χ = 0) {M T eta c t : ℝ}
    {u v : ℝ → ℝ → ℝ} {U V : ℝ → ℝ}
    (hM : 0 ≤ M)
    (hsol : IsClassicalSolution p T u v) (ht0 : 0 < t) (htT : t < T)
    (hTW : IsTravelingWave p c U V)
    (hu2 : ContDiff ℝ 2 (coMovingPath c u t))
    (hv2 : ContDiff ℝ 2 (coMovingPath c v t))
    (hU2 : ContDiff ℝ 2 U) (hV2 : ContDiff ℝ 2 V)
    (huM : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    (hclose : Integrable (fun x =>
      Real.exp (2 * eta * x) * |coMovingPath c u t x - U x| ^ 2))
    (hhalf : HasDerivAt (paper5WeightedHalfEnergy eta c u U)
      (∫ x, paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationT eta
          (paper5CoMovingMaterialTime c u) t x) t)
    (hdiff_int : Integrable (fun x =>
      paper5WeightedPopulation eta (coMovingPath c u) U t x *
        paper5WeightedPopulationXX eta (coMovingPath c u) U t x))
    (hWx2 : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2)) :
    deriv (paper5WeightedEnergy eta c u U) t ≤
      2 * (eta ^ 2 - c * eta + reactionLip p.α M) *
        paper5WeightedEnergy eta c u U t := by
  let W : ℝ → ℝ :=
    paper5WeightedPopulation eta (coMovingPath c u) U t
  have hW2 : Integrable (fun x => W x ^ 2) := by
    dsimp only [W]
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  obtain ⟨hdrift_int, hdiff_decay_bot, hdiff_decay_top,
      hdrift_decay_bot, hdrift_decay_top⟩ :=
    paper5WeightedPopulation_spatial_product_data hu2 hU2
      hW2 hWx2 hdiff_int
  obtain ⟨hrem_int, hrem_le⟩ :=
    paper5CorrectedRemainderIntegral_le_chi_zero
      p hchi hM hsol ht0 htT hTW hu2 hv2 hU2 hV2 huM hUM hclose
  have hpoint := paper5CorrectedWeightedDensity_identity_of_classical p
    (η := eta) hsol ht0 htT hTW (fun x => (huM x).1)
      (hu2.of_le (by norm_num)) hv2
      (hU2.of_le (by norm_num)) hV2
  have hpde := paper5CorrectedWeightedTimeIntegral_eq p hpoint
    hdiff_int hdrift_int hrem_int
  have hgrad_int : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) U t x *
        paper5WeightedPopulationX eta (coMovingPath c u) U t x) := by
    simpa only [pow_two] using hWx2
  have hdiff := paper5WeightedPopulation_diffusion_ibp hu2 hU2
    hdiff_int hgrad_int hdiff_decay_bot hdiff_decay_top
  have hdrift := paper5WeightedPopulation_driftIntegral_eq_zero
    (hu2.of_le (by norm_num)) (hU2.of_le (by norm_num)) hdrift_int
    hdrift_decay_bot hdrift_decay_top
  have hgrad_nonneg : 0 ≤ ∫ x,
      paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hrem_le' :
      (∫ x, paper5CorrectedRemainderDensity p eta c
        (coMovingPath c u) (coMovingPath c v) U
        (paper5WeightedPopulation eta (coMovingPath c u) U t)
        (paper5WeightedPopulationX eta (coMovingPath c u) U t)
        (paper5WeightedSignal eta (coMovingPath c v) V t)
        (paper5WeightedSignalX eta (coMovingPath c v) V t) t x) ≤
      (1 / 2 : ℝ) * (∫ x,
        paper5WeightedPopulationX eta (coMovingPath c u) U t x ^ 2) +
      (eta ^ 2 - c * eta + reactionLip p.α M) *
        (∫ x, W x ^ 2) := by
    linarith
  have hhalf_le := paper5CorrectedHalfEnergy_deriv_le_of_remainder
    hhalf.deriv hpde hdiff hdrift hrem_le' hgrad_nonneg
  rw [hhalf.deriv] at hhalf_le
  apply paper5WeightedEnergy_deriv_le_of_half hhalf
  simpa only [W] using hhalf_le

/-- Canonical positive-window zero-sensitivity energy producer.

The realized state restart and spatial-gradient trajectory are the two
semigroup-side window objects.  The physical forcing trajectory, its norm
bound, its Holder modulus, and its representative are all constructed here
from the population value modulus by the reaction-only producer.  The three
energy-core integrability conclusions and the final differential inequality
are then obtained without any nonzero-sensitivity input. -/
theorem
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_chi_zero_of_realized_window
    (p : CMParams) (hchi : p.χ = 0)
    {M T eta c a r t theta EW HW : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ha : 0 < a) (hat : a < t) (htr : t < r) (hrT : r < T)
    (htheta : 0 < theta)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M)
    {U V : ℝ → ℝ}
    (hTW : IsTravelingWave p c U V)
    (hreg : TravelingWaveRegularity p c U V)
    (hUM : ∀ x, U x ∈ Set.Icc (0 : ℝ) M)
    {X : ℝ → WholeLineRealL2}
    (hXcont : ContinuousOn X (Set.Icc a r))
    (hclose :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Icc a r, Integrable (fun x =>
        Real.exp (2 * eta * x) * |coMovingPath c u q x - U x| ^ 2))
    (hclose_le :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Icc a r,
        (∫ x, Real.exp (2 * eta * x) *
          |coMovingPath c u q x - U x| ^ 2) ≤ EW ^ 2)
    (hWdiff :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
        Integrable (fun x =>
          (paper5WeightedPopulation eta (coMovingPath c u) U s x -
            paper5WeightedPopulation eta (coMovingPath c u) U q x) ^ 2))
    (hWdiff_le :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ s ∈ Set.Icc a r, ∀ q ∈ Set.Icc a r,
        (∫ x,
          (paper5WeightedPopulation eta (coMovingPath c u) U s x -
            paper5WeightedPopulation eta (coMovingPath c u) U q x) ^ 2) ≤
          HW ^ 2 * (|s - q| ^ theta) ^ 2)
    (hactual :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
      let F := paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
        p eta c u v U V (hat.le.trans htr.le)
      ∀ q ∈ Set.Icc a r,
        wholeLineRealL2Total
            (paper5WeightedPopulation eta (coMovingPath c u) U q) =
          weightedMovingHeatFullGeneratorCandidate eta c a
            (wholeLineRealL2Total
              (paper5WeightedPopulation eta (coMovingPath c u) U a)) F q)
    (hWx2 :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Ioo a r, Integrable (fun x =>
        paper5WeightedPopulationX eta (coMovingPath c u) U q x ^ 2))
    (hXrep :
      let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
      let u : ℝ → ℝ → ℝ := fun s x =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 x
      ∀ q ∈ Set.Ioo a r,
        (((X q : WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
          paper5WeightedPopulationX eta (coMovingPath c u) U q)) :
    let Traj := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun s x =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 x
    deriv (paper5WeightedEnergy eta c u U) t ≤
      2 * (eta ^ 2 - c * eta + reactionLip p.α M) *
        paper5WeightedEnergy eta c u U t := by
  dsimp only at hclose hclose_le hWdiff hWdiff_le hactual hWx2 hXrep ⊢
  let Traj : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend hT Traj s).1 x
  let v : ℝ → ℝ → ℝ := fun s => frozenElliptic p (u s)
  have har : a ≤ r := (hat.trans htr).le
  have huC : ∀ q ∈ Set.Icc a r, IsCUnifBdd (coMovingPath c u q) := by
    intro q hq
    have hq0 : 0 ≤ q := ha.le.trans hq.1
    let zq : Set.Icc (0 : ℝ) T :=
      ⟨q, hq0, hq.2.trans hrT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj q = Traj zq :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zq.2
    have huq : IsCUnifBdd (u q) := by
      simpa only [u, hext] using WholeLineBUC.isCUnifBdd (Traj zq)
    simpa only [coMovingPath] using
      isCUnifBdd_comp_add_const huq (c * q)
  have hUC : IsCUnifBdd U := by
    refine ⟨hreg.U_cont, ⟨M, fun x => ?_⟩⟩
    rw [abs_of_nonneg (hUM x).1]
    exact (hUM x).2
  have huM : ∀ q ∈ Set.Icc a r, ∀ x,
      coMovingPath c u q x ∈ Set.Icc (0 : ℝ) M := by
    intro q hq x
    have hq0 : 0 ≤ q := ha.le.trans hq.1
    let zq : Set.Icc (0 : ℝ) T :=
      ⟨q, hq0, hq.2.trans hrT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT Traj q = Traj zq :=
      wholeLineBUCTrajectoryExtend_eq hT Traj zq.2
    simpa only [coMovingPath, u, hext, Traj, zq] using
      hstrip zq (x + c * q)
  let F : ℝ → WholeLineRealL2 :=
    paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory
      p eta c u v U V har
  obtain ⟨H, hH, hFdata, hFholder, hFcont, hFrep⟩ :=
    exists_paper5WeightedGeneratorForcingNaturalPositiveWindowL2Trajectory_chi_zero_data
      p hchi har hM htheta huC hUC huM hUM hclose hclose_le
        hWdiff hWdiff_le
  let C : ℝ := reactionLip p.α M ^ 2 * EW ^ 2
  let K : ℝ := Real.sqrt C
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hFbound : ∀ q ∈ Set.Icc a r, ‖F q‖ ≤ K := by
    intro q hq
    have hnormsq := wholeLineRealL2_norm_sq_eq_integral_sq_of_aeEq
      (F q) (hFrep q hq)
    have hsquare : ‖F q‖ ^ 2 ≤ K ^ 2 := by
      rw [hnormsq, show K ^ 2 = C by exact Real.sq_sqrt hC]
      exact hFdata q hq |>.2
    exact (sq_le_sq₀ (norm_nonneg _) hK).mp hsquare
  obtain ⟨hu2, hhalf, hdiff, hgrad⟩ :=
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_regularInputs_of_realized_window
      p hM hT ha hat htr hrT htheta hH hK u₀ hsmall hstrip hTW hreg
        hXcont hFcont hFbound hFholder hactual
        (fun q hq => hclose q ⟨hq.1.le, hq.2.le⟩) hWx2 hXrep
        (fun q hq => hFrep q ⟨hq.1.le, hq.2.le⟩)
  obtain ⟨hsol, huMwin, _hu2win, hv2win⟩ :=
    wholeLineCauchyBUCMildFixedPoint_positive_window_slice_data
      (c := c) p hM hT (ha.trans hat) (le_refl t) (htr.trans hrT)
        u₀ hsmall hstrip
  dsimp only at hsol huMwin hv2win
  have huMt : ∀ x, coMovingPath c u t x ∈ Set.Icc (0 : ℝ) M :=
    fun x => huMwin t ⟨le_rfl, le_rfl⟩ x
  have hv2 : ContDiff ℝ 2 (coMovingPath c v t) :=
    hv2win t ⟨le_rfl, le_rfl⟩
  exact paper5WeightedEnergy_deriv_le_chi_zero_of_coreIntegrability
    p hchi hM hsol (ha.trans hat) (htr.trans hrT) hTW hu2 hv2
      (hreg.U_contDiff_two hTW) (hreg.V_contDiff_two hTW) huMt hUM
      (hclose t ⟨hat.le, htr.le⟩) hhalf hdiff hgrad

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.paper5CorrectedRemainderIntegral_le_chi_zero
#print axioms
  ShenWork.Paper1.paper5WeightedEnergy_deriv_le_chi_zero_of_coreIntegrability
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_chi_zero_of_realized_window
