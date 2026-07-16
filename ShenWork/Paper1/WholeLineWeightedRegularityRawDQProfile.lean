import ShenWork.Paper1.WholeLineWeightedRegularityRawDQHistory

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical `L²` profile for the co-moving raw spatial quotient

The Volterra closure for the positive-time spatial difference quotient needs
one canonical `L²` representative at every intermediate time.  The scalar
representative below is defined directly from the canonical BUC trajectory;
in particular, it does not use a spatial derivative of the solution.
-/

/-- The cap-weighted conjugated raw quotient of the co-moving perturbation. -/
def capWeightedCoMovingRawDQScalar
    {T : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (s x : ℝ) : ℝ :=
  capWeightSqrt eta R x *
    rawSpatialDifferenceQuotient eta h (fun y =>
      (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W.1 y) x

theorem capWeightedCoMovingRawDQScalar_joint_continuous
    {T : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    Continuous (fun q : ℝ × ℝ =>
      capWeightedCoMovingRawDQScalar hT eta R c h Traj W q.1 q.2) := by
  have heval : Continuous (fun q : WholeLineBUC × ℝ => q.1.1 q.2) := by
    fun_prop
  have hu0 : Continuous (fun q : ℝ × ℝ =>
      (wholeLineBUCTrajectoryExtend hT Traj q.1).1 (q.2 + c * q.1)) := by
    exact heval.comp
      (Continuous.prodMk
        ((wholeLineBUCTrajectoryExtend_continuous hT Traj).comp continuous_fst)
        (continuous_snd.add (continuous_const.mul continuous_fst)))
  have huh : Continuous (fun q : ℝ × ℝ =>
      (wholeLineBUCTrajectoryExtend hT Traj q.1).1
        (q.2 + h + c * q.1)) := by
    exact heval.comp
      (Continuous.prodMk
        ((wholeLineBUCTrajectoryExtend_continuous hT Traj).comp continuous_fst)
        ((continuous_snd.add continuous_const).add
          (continuous_const.mul continuous_fst)))
  have hW0 : Continuous (fun q : ℝ × ℝ => W.1 q.2) :=
    W.1.continuous.comp continuous_snd
  have hWh : Continuous (fun q : ℝ × ℝ => W.1 (q.2 + h)) :=
    W.1.continuous.comp (continuous_snd.add continuous_const)
  have hraw : Continuous (fun q : ℝ × ℝ =>
      rawSpatialDifferenceQuotient eta h (fun y =>
        (wholeLineBUCTrajectoryExtend hT Traj q.1).1
            (y + c * q.1) - W.1 y) q.2) := by
    simp only [rawSpatialDifferenceQuotient, spatialDifferenceQuotient]
    fun_prop
  exact ((capWeightSqrt_continuous eta R).comp continuous_snd).mul hraw

theorem capWeightedCoMovingRawDQScalar_continuous
    {T s : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    Continuous (capWeightedCoMovingRawDQScalar hT eta R c h Traj W s) := by
  exact (capWeightedCoMovingRawDQScalar_joint_continuous
    hT eta R c h Traj W).comp
      (Continuous.prodMk continuous_const continuous_id)

/-- Translation is jointly continuous in the shift and the BUC profile. -/
theorem wholeLineBUCTranslate_joint_continuous :
    Continuous (fun q : ℝ × WholeLineBUC =>
      wholeLineBUCTranslate q.1 q.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, u⟩
  rw [Metric.continuousAt_iff]
  intro eps heps
  obtain ⟨da, hda, hshift⟩ :=
    (Metric.continuousAt_iff.mp
      (wholeLineBUCTranslate_continuous u).continuousAt)
      (eps / 2) (by linarith)
  refine ⟨min da (eps / 2), lt_min hda (by linarith), ?_⟩
  rintro ⟨b, v⟩ hbv
  have hbv' : max (dist b a) (dist v u) < min da (eps / 2) := by
    simpa only [Prod.dist_eq] using hbv
  have hb : dist b a < da :=
    lt_of_le_of_lt (le_max_left _ _) (hbv'.trans_le (min_le_left _ _))
  have hv : dist v u < eps / 2 :=
    lt_of_le_of_lt (le_max_right _ _) (hbv'.trans_le (min_le_right _ _))
  calc
    dist (wholeLineBUCTranslate b v) (wholeLineBUCTranslate a u) ≤
        dist (wholeLineBUCTranslate b v) (wholeLineBUCTranslate b u) +
          dist (wholeLineBUCTranslate b u) (wholeLineBUCTranslate a u) :=
      dist_triangle _ _ _
    _ < eps / 2 + eps / 2 :=
      add_lt_add
        ((wholeLineBUCTranslate_dist_le' b v u).trans_lt hv)
        (hshift hb)
    _ = eps := by ring

/-- BUC-valued realization of the canonical cap-weighted raw quotient. -/
def capWeightedCoMovingRawDQBUCHistory
    {T : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (s : ℝ) : WholeLineBUC :=
  capWeightSqrtMulBUC eta R heta
    (wholeLineBUCRawSpatialDifferenceQuotientCLM eta h
      (wholeLineBUCPointwiseSub
        (wholeLineBUCTranslate (c * s)
          (wholeLineBUCTrajectoryExtend hT Traj s)) W))

@[simp] theorem capWeightedCoMovingRawDQBUCHistory_apply
    {T s x : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    (capWeightedCoMovingRawDQBUCHistory
      hT eta R c h heta Traj W s).1 x =
      capWeightedCoMovingRawDQScalar hT eta R c h Traj W s x := by
  simp only [capWeightedCoMovingRawDQBUCHistory,
    capWeightSqrtMulBUC_apply,
    wholeLineBUCRawSpatialDifferenceQuotientCLM_coe,
    capWeightedCoMovingRawDQScalar]
  congr 1

theorem capWeightedCoMovingRawDQBUCHistory_continuous
    {T : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    Continuous
      (capWeightedCoMovingRawDQBUCHistory hT eta R c h heta Traj W) := by
  have hpair : Continuous (fun s : ℝ =>
      (c * s, wholeLineBUCTrajectoryExtend hT Traj s)) :=
    Continuous.prodMk (continuous_const.mul continuous_id)
      (wholeLineBUCTrajectoryExtend_continuous hT Traj)
  have htrans : Continuous (fun s : ℝ =>
      wholeLineBUCTranslate (c * s)
        (wholeLineBUCTrajectoryExtend hT Traj s)) :=
    wholeLineBUCTranslate_joint_continuous.comp hpair
  have hsub : Continuous (fun s : ℝ => wholeLineBUCPointwiseSub
      (wholeLineBUCTranslate (c * s)
        (wholeLineBUCTrajectoryExtend hT Traj s)) W) := by
    rw [← continuousOn_univ]
    exact wholeLineBUCPointwiseSub_continuousOn
      htrans.continuousOn continuous_const.continuousOn
  exact (capWeightSqrtMulBUC_lipschitz eta R heta).continuous.comp
    ((wholeLineBUCRawSpatialDifferenceQuotientCLM eta h).continuous.comp hsub)

/-- Canonical `L²` realization of the cap-weighted raw quotient profile. -/
def capWeightedCoMovingRawDQL2Profile
    {T : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ s, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W s).1 x ^ 2)
      volume) :
    ℝ → WholeLineRealL2 :=
  wholeLineRealL2Section
    (fun s x => (capWeightedCoMovingRawDQBUCHistory
      hT eta R c h heta Traj W s).1 x)
    (fun s => (capWeightedCoMovingRawDQBUCHistory
      hT eta R c h heta Traj W s).1.continuous.aestronglyMeasurable)
    hraw2

theorem capWeightedCoMovingRawDQL2Profile_coe_ae
    {T s : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q).1 x ^ 2)
      volume) :
    (((capWeightedCoMovingRawDQL2Profile hT eta R c h heta Traj W hraw2 s :
          WholeLineRealL2) : ℝ → ℝ) =ᵐ[volume]
      fun x => (capWeightedCoMovingRawDQBUCHistory
        hT eta R c h heta Traj W s).1 x) := by
  exact wholeLineRealL2Section_coe_ae _ _ _ s

theorem capWeightedCoMovingRawDQL2Profile_norm_sq
    {T s : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q).1 x ^ 2)
      volume) :
    ‖capWeightedCoMovingRawDQL2Profile hT eta R c h heta Traj W hraw2 s‖ ^ 2 =
      ∫ x : ℝ,
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W s).1 x ^ 2 := by
  exact wholeLineRealL2Section_norm_sq _ _ _ s

theorem capWeightedCoMovingRawDQL2Profile_norm_eq_sqrt
    {T s : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q).1 x ^ 2)
      volume) :
    ‖capWeightedCoMovingRawDQL2Profile hT eta R c h heta Traj W hraw2 s‖ =
      Real.sqrt (∫ x : ℝ,
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W s).1 x ^ 2) := by
  rw [← capWeightedCoMovingRawDQL2Profile_norm_sq
    hT eta R c h heta Traj W hraw2]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem capWeightedCoMovingRawDQL2Profile_aestronglyMeasurable
    {T : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ)
    (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q).1 x ^ 2)
      volume) :
    AEStronglyMeasurable
      (capWeightedCoMovingRawDQL2Profile hT eta R c h heta Traj W hraw2)
      volume := by
  let F : ℝ → WholeLineBUC :=
    capWeightedCoMovingRawDQBUCHistory hT eta R c h heta Traj W
  have hF : Continuous F :=
    capWeightedCoMovingRawDQBUCHistory_continuous
      hT eta R c h heta Traj W
  simpa only [capWeightedCoMovingRawDQL2Profile, F] using
    (wholeLineRealL2Section_aestronglyMeasurable_of_continuous_buc hF hraw2)

theorem capWeightedCoMovingRawDQL2Profile_intervalIntegrable_of_uniform_bound
    {T r B : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ)
    (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q).1 x ^ 2)
      volume)
    (hr : 0 ≤ r)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) r,
      ‖capWeightedCoMovingRawDQL2Profile
        hT eta R c h heta Traj W hraw2 s‖ ≤ B) :
    IntervalIntegrable
      (capWeightedCoMovingRawDQL2Profile hT eta R c h heta Traj W hraw2)
      volume 0 r := by
  have hconst : IntervalIntegrable (fun _ : ℝ => B) volume 0 r :=
    intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hr] at hconst ⊢
  apply Integrable.mono' hconst
  · exact (capWeightedCoMovingRawDQL2Profile_aestronglyMeasurable
      hT eta R c h heta Traj W hraw2).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound s hs

/-- The canonical norm is exactly the cap energy of the unweighted raw
quotient. -/
theorem capWeightedCoMovingRawDQL2Profile_energy_eq_norm_sq
    {T s : ℝ} (hT : 0 ≤ T) (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable
      (fun x : ℝ =>
        (capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q).1 x ^ 2)
      volume) :
    (∫ x : ℝ, capWeight eta R x *
      |rawSpatialDifferenceQuotient eta h (fun y =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W.1 y) x| ^ 2) =
      ‖capWeightedCoMovingRawDQL2Profile
        hT eta R c h heta Traj W hraw2 s‖ ^ 2 := by
  rw [capWeightedCoMovingRawDQL2Profile_norm_sq
    hT eta R c h heta Traj W hraw2]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W.1 y) x| ^ 2 =
      (capWeightedCoMovingRawDQBUCHistory
        hT eta R c h heta Traj W s).1 x ^ 2
    rw [capWeightedCoMovingRawDQBUCHistory_apply]
    exact (capWeightSqrt_mul_sq_eq eta R x _).symm

end ShenWork.Paper1

#print axioms ShenWork.Paper1.capWeightedCoMovingRawDQScalar_joint_continuous
#print axioms ShenWork.Paper1.capWeightedCoMovingRawDQL2Profile_aestronglyMeasurable
#print axioms ShenWork.Paper1.capWeightedCoMovingRawDQL2Profile_intervalIntegrable_of_uniform_bound
#print axioms ShenWork.Paper1.capWeightedCoMovingRawDQL2Profile_energy_eq_norm_sq
