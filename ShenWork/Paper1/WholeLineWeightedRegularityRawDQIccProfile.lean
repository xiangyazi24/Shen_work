import ShenWork.Paper1.WholeLineWeightedRegularityRawDQProfile

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical raw-DQ profile totalized from a finite restart window

The classical solution is controlled only on its actual time horizon.  This
file therefore clamps the canonical raw-quotient profile to `[0,r]`, instead
of imposing square-integrability at arbitrary real times.
-/

def capWeightedCoMovingRawDQBUCHistoryIcc
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (s : ℝ) : WholeLineBUC :=
  capWeightedCoMovingRawDQBUCHistory hT eta R c h heta Traj W
    (Set.projIcc 0 r hr s)

theorem capWeightedCoMovingRawDQBUCHistoryIcc_continuous
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC) :
    Continuous (capWeightedCoMovingRawDQBUCHistoryIcc
      hT hr eta R c h heta Traj W) :=
  (capWeightedCoMovingRawDQBUCHistory_continuous
    hT eta R c h heta Traj W).comp
      (continuous_subtype_val.comp continuous_projIcc)

@[simp] theorem capWeightedCoMovingRawDQBUCHistoryIcc_of_mem
    {T r s : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hs : s ∈ Set.Icc (0 : ℝ) r) :
    capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W s =
      capWeightedCoMovingRawDQBUCHistory
        hT eta R c h heta Traj W s := by
  simp only [capWeightedCoMovingRawDQBUCHistoryIcc]
  rw [Set.projIcc_of_mem hr hs]

theorem capWeightedCoMovingRawDQBUCHistoryIcc_sq_integrable
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw : ∀ s ∈ Set.Icc (0 : ℝ) r, Integrable (fun x : ℝ =>
      capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W.1 y) x| ^ 2)
      volume) :
    ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W s).1 x ^ 2) volume := by
  intro s
  let q : ℝ := Set.projIcc 0 r hr s
  have hq : q ∈ Set.Icc (0 : ℝ) r := by
    simpa only [q] using (Set.projIcc 0 r hr s).property
  refine (hraw q hq).congr (ae_of_all _ fun x => ?_)
  rw [show capWeightedCoMovingRawDQBUCHistoryIcc
      hT hr eta R c h heta Traj W s =
        capWeightedCoMovingRawDQBUCHistory
          hT eta R c h heta Traj W q by rfl]
  change capWeight eta R x *
      |rawSpatialDifferenceQuotient eta h (fun y =>
        (wholeLineBUCTrajectoryExtend hT Traj q).1 (y + c * q) - W.1 y) x| ^ 2 =
    (capWeightedCoMovingRawDQBUCHistory
      hT eta R c h heta Traj W q).1 x ^ 2
  rw [capWeightedCoMovingRawDQBUCHistory_apply]
  unfold capWeightedCoMovingRawDQScalar
  exact (capWeightSqrt_mul_sq_eq eta R x _).symm

/-- Canonical `L²` history obtained from the finite-window raw cap data. -/
def capWeightedCoMovingRawDQL2ProfileIcc
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ s, Integrable (fun x : ℝ =>
      (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W s).1 x ^ 2) volume) :
    ℝ → WholeLineRealL2 :=
  wholeLineRealL2Section
    (fun s x => (capWeightedCoMovingRawDQBUCHistoryIcc
      hT hr eta R c h heta Traj W s).1 x)
    (fun s => (capWeightedCoMovingRawDQBUCHistoryIcc
      hT hr eta R c h heta Traj W s).1.continuous.aestronglyMeasurable)
    hraw2

theorem capWeightedCoMovingRawDQL2ProfileIcc_coe_ae
    {T r s : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W q).1 x ^ 2) volume) :
    (((capWeightedCoMovingRawDQL2ProfileIcc
      hT hr eta R c h heta Traj W hraw2 s : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W s).1 x) :=
  wholeLineRealL2Section_coe_ae _ _ _ s

theorem capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
    {T r s : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W q).1 x ^ 2) volume)
    (hs : s ∈ Set.Icc (0 : ℝ) r) :
    (∫ x : ℝ, capWeight eta R x *
      |rawSpatialDifferenceQuotient eta h (fun y =>
        (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W.1 y) x| ^ 2) =
      ‖capWeightedCoMovingRawDQL2ProfileIcc
        hT hr eta R c h heta Traj W hraw2 s‖ ^ 2 := by
  unfold capWeightedCoMovingRawDQL2ProfileIcc
  rw [wholeLineRealL2Section_norm_sq]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    rw [capWeightedCoMovingRawDQBUCHistoryIcc_of_mem
      hT hr eta R c h heta Traj W hs]
    change capWeight eta R x *
        |rawSpatialDifferenceQuotient eta h (fun y =>
          (wholeLineBUCTrajectoryExtend hT Traj s).1 (y + c * s) - W.1 y) x| ^ 2 =
      (capWeightedCoMovingRawDQBUCHistory
        hT eta R c h heta Traj W s).1 x ^ 2
    rw [capWeightedCoMovingRawDQBUCHistory_apply]
    unfold capWeightedCoMovingRawDQScalar
    exact (capWeightSqrt_mul_sq_eq eta R x _).symm

theorem capWeightedCoMovingRawDQL2ProfileIcc_aestronglyMeasurable
    {T r : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W q).1 x ^ 2) volume) :
    AEStronglyMeasurable (capWeightedCoMovingRawDQL2ProfileIcc
      hT hr eta R c h heta Traj W hraw2) volume := by
  exact wholeLineRealL2Section_aestronglyMeasurable_of_continuous_buc
    (capWeightedCoMovingRawDQBUCHistoryIcc_continuous
      hT hr eta R c h heta Traj W) hraw2

theorem capWeightedCoMovingRawDQL2ProfileIcc_intervalIntegrable_of_bound
    {T r B : ℝ} (hT : 0 ≤ T) (hr : 0 ≤ r)
    (eta R c h : ℝ) (heta : 0 ≤ eta)
    (Traj : WholeLineBUCTrajectory T) (W : WholeLineBUC)
    (hraw2 : ∀ q, Integrable (fun x : ℝ =>
      (capWeightedCoMovingRawDQBUCHistoryIcc
        hT hr eta R c h heta Traj W q).1 x ^ 2) volume)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) r,
      ‖capWeightedCoMovingRawDQL2ProfileIcc
        hT hr eta R c h heta Traj W hraw2 s‖ ≤ B) :
    IntervalIntegrable (capWeightedCoMovingRawDQL2ProfileIcc
      hT hr eta R c h heta Traj W hraw2) volume 0 r := by
  have hconst : IntervalIntegrable (fun _ : ℝ => B) volume 0 r :=
    intervalIntegrable_const
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hr] at hconst ⊢
  apply Integrable.mono' hconst
  · exact (capWeightedCoMovingRawDQL2ProfileIcc_aestronglyMeasurable
      hT hr eta R c h heta Traj W hraw2).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound s hs

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.capWeightedCoMovingRawDQBUCHistoryIcc_sq_integrable
#print axioms
  ShenWork.Paper1.capWeightedCoMovingRawDQL2ProfileIcc_energy_eq_norm_sq
#print axioms
  ShenWork.Paper1.capWeightedCoMovingRawDQL2ProfileIcc_intervalIntegrable_of_bound
