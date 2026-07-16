import ShenWork.Paper1.WholeLineWeightedRegularityChiZeroEnergyNatural

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

/-!
# Sharp zero-sensitivity logistic energy

The logistic map `s ↦ s(1-s^α)` is one-sided Lipschitz with sharp
constant one on the nonnegative half-line.  At zero sensitivity this replaces
the bounded-box absolute Lipschitz constant in the weighted energy estimate.
-/

/-- Sharp one-sided logistic pairing on the nonnegative half-line. -/
theorem reactionFun_sub_mul_sub_le_sq_of_nonneg
    {α a b : ℝ} (hα : 1 ≤ α) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) * (reactionFun α a - reactionFun α b) ≤ (a - b) ^ 2 := by
  have hα0 : 0 ≤ α := zero_le_one.trans hα
  have hmonotoneProduct :
      0 ≤ (a - b) * (a * a ^ α - b * b ^ α) := by
    by_cases hab : a ≤ b
    · have hpow : a ^ α ≤ b ^ α :=
        Real.rpow_le_rpow ha hab hα0
      have hprod : a * a ^ α ≤ b * b ^ α :=
        mul_le_mul hab hpow (Real.rpow_nonneg ha _) hb
      exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr hab) (sub_nonpos.mpr hprod)
    · have hba : b ≤ a := le_of_not_ge hab
      have hpow : b ^ α ≤ a ^ α :=
        Real.rpow_le_rpow hb hba hα0
      have hprod : b * b ^ α ≤ a * a ^ α :=
        mul_le_mul hba hpow (Real.rpow_nonneg hb _) ha
      exact mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hprod)
  have hid :
      (a - b) * (reactionFun α a - reactionFun α b) =
        (a - b) ^ 2 - (a - b) * (a * a ^ α - b * b ^ α) := by
    unfold reactionFun
    ring
  rw [hid]
  linarith

/-- Sharp zero-sensitivity remainder estimate.  The old bounded-box estimate
is used only for integrability; its `reactionLip` coefficient is discarded.
-/
theorem paper5CorrectedRemainderIntegral_le_chi_zero_sharp
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
        (eta ^ 2 - c * eta + 1) * ∫ x : ℝ, W x ^ 2 := by
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
  obtain ⟨hR, _hcoarse⟩ :=
    paper5CorrectedRemainderIntegral_le_chi_zero
      p hchi hM hsol ht0 htT hTW hu2 hv2 hU2 hV2 huM hUM hclose
  have hW2 : Integrable (fun x => W x ^ 2) := by
    dsimp only [W]
    exact paper5WeightedPopulation_sq_integrable_of_weighted_difference hclose
  have hWFpoint : ∀ x, W x * F x ≤ W x ^ 2 := by
    intro x
    have hpair := reactionFun_sub_mul_sub_le_sq_of_nonneg
      p.hα (huM x).1 (hUM x).1
    rw [show F x = weightedReactionDifference p eta
        (coMovingPath c u t) U x by
      exact
        paper5WeightedGeneratorForcing_eq_weightedReactionDifference_of_chi_zero
          p hchi eta (coMovingPath c u) (coMovingPath c v) U V t x]
    dsimp only [W]
    unfold paper5WeightedPopulation weightedReactionDifference
    calc
      (Real.exp (eta * x) * (coMovingPath c u t x - U x)) *
          (Real.exp (eta * x) *
            (reactionFun p.α (coMovingPath c u t x) -
              reactionFun p.α (U x))) =
        Real.exp (eta * x) ^ 2 *
          ((coMovingPath c u t x - U x) *
            (reactionFun p.α (coMovingPath c u t x) -
              reactionFun p.α (U x))) := by ring
      _ ≤ Real.exp (eta * x) ^ 2 *
          (coMovingPath c u t x - U x) ^ 2 :=
        mul_le_mul_of_nonneg_left hpair (sq_nonneg _)
      _ = (Real.exp (eta * x) *
          (coMovingPath c u t x - U x)) ^ 2 := by ring
  have hpoint : ∀ x, R x ≤
      (eta ^ 2 - c * eta + 1) * W x ^ 2 := by
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
        (eta ^ 2 - c * eta + 1) * W x ^ 2 :=
      integral_mono_ae hR
        (hW2.const_mul (eta ^ 2 - c * eta + 1))
        (Eventually.of_forall hpoint)
    _ = (eta ^ 2 - c * eta + 1) * ∫ x : ℝ, W x ^ 2 := by
      rw [integral_const_mul]

/-- Sharp zero-sensitivity core energy inequality. -/
theorem paper5WeightedEnergy_deriv_le_chi_zero_sharp_of_coreIntegrability
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
      2 * (eta ^ 2 - c * eta + 1) *
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
    paper5CorrectedRemainderIntegral_le_chi_zero_sharp
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
      (eta ^ 2 - c * eta + 1) * (∫ x, W x ^ 2) := by
    linarith
  have hhalf_le := paper5CorrectedHalfEnergy_deriv_le_of_remainder
    hhalf.deriv hpde hdiff hdrift hrem_le' hgrad_nonneg
  rw [hhalf.deriv] at hhalf_le
  apply paper5WeightedEnergy_deriv_le_of_half hhalf
  simpa only [W] using hhalf_le

/-- Sharp canonical positive-window producer from a realized Hilbert restart.
The window construction is unchanged; only the final logistic pairing is
strengthened from the bounded-box Lipschitz constant to one. -/
theorem
    wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_chi_zero_sharp_of_realized_window
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
      2 * (eta ^ 2 - c * eta + 1) *
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
  exact paper5WeightedEnergy_deriv_le_chi_zero_sharp_of_coreIntegrability
    p hchi hM hsol (ha.trans hat) (htr.trans hrT) hTW hu2 hv2
      (hreg.U_contDiff_two hTW) (hreg.V_contDiff_two hTW) huMt hUM
      (hclose t ⟨hat.le, htr.le⟩) hhalf hdiff hgrad

section AxiomAudit

#print axioms reactionFun_sub_mul_sub_le_sq_of_nonneg
#print axioms paper5CorrectedRemainderIntegral_le_chi_zero_sharp
#print axioms paper5WeightedEnergy_deriv_le_chi_zero_sharp_of_coreIntegrability
#print axioms
  wholeLineCauchyBUCMildFixedPoint_weightedEnergy_deriv_le_chi_zero_sharp_of_realized_window

end AxiomAudit

end ShenWork.Paper1
