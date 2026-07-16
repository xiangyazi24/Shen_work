import ShenWork.Paper1.WholeLineWeightedRegularityGlobalRestart
import ShenWork.Paper1.WholeLineWeightedRegularityGradientNatural
import ShenWork.Paper1.WholeLineWeightedRegularityDQCommutation

open Filter Function MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Global weighted spatial-gradient regularity

The local weighted-gradient producer is phase-normalized at the initial
face of a canonical fixed-point segment.  At a positive global time, the
preferred segment begins at a positive laboratory time.  We remove that
phase by translating the entire canonical segment in space.  Translation
covariance of the truncated mild map then identifies this translated
segment with the canonical fixed point issued from the translated restart
datum.
-/

/-- Apply one fixed spatial translation to every slice of a compact BUC
trajectory. -/
def wholeLineBUCTrajectorySpatialTranslate
    {T : ℝ} (_hT : 0 ≤ T) (d : ℝ) (U : WholeLineBUCTrajectory T) :
    WholeLineBUCTrajectory T :=
  ⟨fun z => wholeLineBUCTranslate d (U z),
    wholeLineBUCTranslate_joint_continuous.comp
      ((continuous_const.prodMk U.continuous))⟩

@[simp] theorem wholeLineBUCTrajectorySpatialTranslate_apply
    {T : ℝ} (hT : 0 ≤ T) (d : ℝ) (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) :
    (wholeLineBUCTrajectorySpatialTranslate hT d U z).1 x =
      (U z).1 (x + d) := by
  rfl

/-- Constant time extension commutes with a fixed spatial translation. -/
theorem wholeLineBUCTrajectoryExtend_spatialTranslate
    {T s d : ℝ} (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T) :
    wholeLineBUCTrajectoryExtend hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) s =
      wholeLineBUCTranslate d (wholeLineBUCTrajectoryExtend hT U s) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  rfl

/-- The totalized modified heat flow commutes with spatial translation. -/
theorem wholeLineCauchyHeatBUCTotal_spatialTranslate
    (t d : ℝ) (u : WholeLineBUC) :
    wholeLineCauchyHeatBUCTotal t (wholeLineBUCTranslate d u) =
      wholeLineBUCTranslate d (wholeLineCauchyHeatBUCTotal t u) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  by_cases ht : 0 < t
  · simp only [wholeLineCauchyHeatBUCTotal, dif_pos ht,
      wholeLineCauchyHeatBUC_apply, wholeLineBUCTranslate_apply]
    simpa only [wholeLineBUCTranslate_apply] using
      (wholeLineCauchyHeatOp_eval_shift_eq_input_shift t d u.1 x).symm
  · simp [wholeLineCauchyHeatBUCTotal, ht]

/-- The totalized modified heat-gradient flow commutes with spatial
translation. -/
theorem wholeLineCauchyHeatGradientBUCTotal_spatialTranslate
    (t d : ℝ) (u : WholeLineBUC) :
    wholeLineCauchyHeatGradientBUCTotal t (wholeLineBUCTranslate d u) =
      wholeLineBUCTranslate d (wholeLineCauchyHeatGradientBUCTotal t u) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  by_cases ht : 0 < t
  · simp only [wholeLineCauchyHeatGradientBUCTotal, dif_pos ht,
      wholeLineCauchyHeatGradientBUC_apply, wholeLineBUCTranslate_apply]
    simpa only [wholeLineBUCTranslate_apply] using
      (wholeLineCauchyHeatGradOp_eval_shift_eq_input_shift t d u.1 x).symm
  · simp [wholeLineCauchyHeatGradientBUCTotal, ht,
      wholeLineBUCTranslate_apply]

/-- The truncated chemotactic flux commutes with spatial translation. -/
theorem wholeLineCauchyTruncatedFluxBUC_spatialTranslate
    (p : CMParams) {M d : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) :
    wholeLineCauchyTruncatedFluxBUC p M hM
        (wholeLineBUCTranslate d u) =
      wholeLineBUCTranslate d
        (wholeLineCauchyTruncatedFluxBUC p M hM u) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [wholeLineCauchyTruncatedFluxBUC_apply,
    wholeLineBUCTranslate_apply]
  simpa only [wholeLineCauchyTruncatedFlux] using
    (wholeLineCauchyTruncatedFlux_comp_add_const p hM
      (WholeLineBUC.isCUnifBdd u) d x).symm

/-- The truncated shifted reaction commutes with spatial translation. -/
theorem wholeLineCauchyTruncatedReactionBUC_spatialTranslate
    (p : CMParams) {M d : ℝ} (hM : 0 ≤ M) (u : WholeLineBUC) :
    wholeLineCauchyTruncatedReactionBUC p M hM
        (wholeLineBUCTranslate d u) =
      wholeLineBUCTranslate d
        (wholeLineCauchyTruncatedReactionBUC p M hM u) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  simp only [wholeLineCauchyTruncatedReactionBUC_apply,
    wholeLineBUCTranslate_apply]
  rfl

/-- The compact-trajectory flux source commutes with a fixed spatial
translation. -/
theorem wholeLineCauchyFluxSourceTrajectory_spatialTranslate
    (p : CMParams) {M T d s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyFluxSourceTrajectory p hM hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) s =
      wholeLineBUCTranslate d
        (wholeLineCauchyFluxSourceTrajectory p hM hT U s) := by
  unfold wholeLineCauchyFluxSourceTrajectory
  rw [wholeLineBUCTrajectoryExtend_spatialTranslate]
  exact wholeLineCauchyTruncatedFluxBUC_spatialTranslate p hM _

/-- The compact-trajectory reaction source commutes with a fixed spatial
translation. -/
theorem wholeLineCauchyReactionSourceTrajectory_spatialTranslate
    (p : CMParams) {M T d s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyReactionSourceTrajectory p hM hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) s =
      wholeLineBUCTranslate d
        (wholeLineCauchyReactionSourceTrajectory p hM hT U s) := by
  unfold wholeLineCauchyReactionSourceTrajectory
  rw [wholeLineBUCTrajectoryExtend_spatialTranslate]
  exact wholeLineCauchyTruncatedReactionBUC_spatialTranslate p hM _

/-- The gradient Duhamel integrand is spatially translation covariant. -/
theorem wholeLineCauchyGradientBUCIntegrand_spatialTranslate
    (p : CMParams) {M T d t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyGradientBUCIntegrand p hM hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) t s =
      wholeLineBUCTranslate d
        (wholeLineCauchyGradientBUCIntegrand p hM hT U t s) := by
  unfold wholeLineCauchyGradientBUCIntegrand
  rw [wholeLineCauchyFluxSourceTrajectory_spatialTranslate]
  exact wholeLineCauchyHeatGradientBUCTotal_spatialTranslate _ _ _

/-- The value Duhamel integrand is spatially translation covariant. -/
theorem wholeLineCauchyValueBUCIntegrand_spatialTranslate
    (p : CMParams) {M T d t s : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyValueBUCIntegrand p hM hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) t s =
      wholeLineBUCTranslate d
        (wholeLineCauchyValueBUCIntegrand p hM hT U t s) := by
  unfold wholeLineCauchyValueBUCIntegrand
  rw [wholeLineCauchyReactionSourceTrajectory_spatialTranslate]
  exact wholeLineCauchyHeatBUCTotal_spatialTranslate _ _ _

/-- A fixed BUC translation commutes with Bochner interval integration. -/
theorem wholeLineBUCTranslate_intervalIntegral
    {a b d : ℝ} {F : ℝ → WholeLineBUC}
    (hF : IntervalIntegrable F volume a b) :
    wholeLineBUCTranslate d (∫ s in a..b, F s) =
      ∫ s in a..b, wholeLineBUCTranslate d (F s) := by
  have hcomm :
      (∫ s in a..b, wholeLineBUCTranslateCLM d (F s)) =
        wholeLineBUCTranslateCLM d (∫ s in a..b, F s) :=
    @ContinuousLinearMap.intervalIntegral_comp_comm
      ℝ WholeLineBUC WholeLineBUC
      WholeLineBUC.normedAddCommGroup inferInstance
      a b volume F
      inferInstance inferInstance WholeLineBUC.normedAddCommGroup
      inferInstance inferInstance
      wholeLineBUCMetricCompleteSpace wholeLineBUCMetricCompleteSpace
      (wholeLineBUCTranslateCLM d) hF
  simpa only [wholeLineBUCTranslateCLM_apply] using hcomm.symm

/-- The gradient Duhamel leg commutes with a fixed spatial translation. -/
theorem wholeLineCauchyGradientDuhamelBUC_spatialTranslate
    (p : CMParams) {M T d t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    wholeLineCauchyGradientDuhamelBUC p hM hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) t =
      wholeLineBUCTranslate d
        (wholeLineCauchyGradientDuhamelBUC p hM hT U t) := by
  unfold wholeLineCauchyGradientDuhamelBUC
  rw [wholeLineBUCTranslate_intervalIntegral
    (wholeLineCauchyGradientBUCIntegrand_intervalIntegrable
      p hM hT U ht)]
  apply intervalIntegral.integral_congr
  intro s _
  exact wholeLineCauchyGradientBUCIntegrand_spatialTranslate
    p hM hT U

/-- The value Duhamel leg commutes with a fixed spatial translation. -/
theorem wholeLineCauchyValueDuhamelBUC_spatialTranslate
    (p : CMParams) {M T d t : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T) (ht : 0 ≤ t) :
    wholeLineCauchyValueDuhamelBUC p hM hT
        (wholeLineBUCTrajectorySpatialTranslate hT d U) t =
      wholeLineBUCTranslate d
        (wholeLineCauchyValueDuhamelBUC p hM hT U t) := by
  unfold wholeLineCauchyValueDuhamelBUC
  rw [wholeLineBUCTranslate_intervalIntegral
    (wholeLineCauchyValueBUCIntegrand_intervalIntegrable
      p hM hT U ht)]
  apply intervalIntegral.integral_congr
  intro s _
  exact wholeLineCauchyValueBUCIntegrand_spatialTranslate
    p hM hT U

/-- The full truncated BUC mild map is covariant under a fixed spatial
translation of both datum and trajectory. -/
theorem wholeLineCauchyBUCMildMap_spatialTranslate
    (p : CMParams) {M T d : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyBUCMildMap p hM hT (wholeLineBUCTranslate d u₀)
        (wholeLineBUCTrajectorySpatialTranslate hT d U) =
      wholeLineBUCTrajectorySpatialTranslate hT d
        (wholeLineCauchyBUCMildMap p hM hT u₀ U) := by
  apply ContinuousMap.ext
  intro z
  simp only [wholeLineCauchyBUCMildMap_apply]
  rw [wholeLineCauchyHeatBUCTotal_spatialTranslate]
  rw [wholeLineCauchyGradientDuhamelBUC_spatialTranslate
    p hM hT U z.2.1]
  rw [wholeLineCauchyValueDuhamelBUC_spatialTranslate
    p hM hT U z.2.1]
  change
    wholeLineBUCTranslate d (wholeLineCauchyHeatBUCTotal z.1 u₀) +
          (-p.χ) • wholeLineBUCTranslate d
            (wholeLineCauchyGradientDuhamelBUC p hM hT U z.1) +
        wholeLineBUCTranslate d
          (wholeLineCauchyValueDuhamelBUC p hM hT U z.1) =
      wholeLineBUCTranslate d
        (wholeLineCauchyHeatBUCTotal z.1 u₀ +
            (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U z.1 +
          wholeLineCauchyValueDuhamelBUC p hM hT U z.1)
  rw [wholeLineBUCTranslate_add, wholeLineBUCTranslate_add,
    wholeLineBUCTranslate_smul]

/-- Spatial covariance of the canonical Banach fixed point. -/
theorem wholeLineCauchyBUCMildFixedPoint_spatialTranslate
    (p : CMParams) {M T d : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    wholeLineCauchyBUCMildFixedPoint p hM hT
        (wholeLineBUCTranslate d u₀) hsmall =
      wholeLineBUCTrajectorySpatialTranslate hT d
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) := by
  let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall
  let V := wholeLineBUCTrajectorySpatialTranslate hT d U
  have hVfix : IsFixedPt
      (wholeLineCauchyBUCMildMap p hM hT (wholeLineBUCTranslate d u₀)) V := by
    change wholeLineCauchyBUCMildMap p hM hT
        (wholeLineBUCTranslate d u₀) V = V
    rw [show wholeLineCauchyBUCMildMap p hM hT
        (wholeLineBUCTranslate d u₀) V =
          wholeLineBUCTrajectorySpatialTranslate hT d
            (wholeLineCauchyBUCMildMap p hM hT u₀ U) by
      simpa only [U, V] using
        wholeLineCauchyBUCMildMap_spatialTranslate p hM hT u₀ U]
    rw [show wholeLineCauchyBUCMildMap p hM hT u₀ U = U by
      exact wholeLineCauchyBUCMildFixedPoint_isFixedPt
        p hM hT u₀ hsmall]
  have hcanon := wholeLineCauchyBUCMildFixedPoint_isFixedPt
    p hM hT (wholeLineBUCTranslate d u₀) hsmall
  exact (wholeLineCauchyBUCMildMap_contracting p hM hT
    (wholeLineBUCTranslate d u₀) hsmall).fixedPoint_unique'
      hcanon hVfix

/-! ## Preferred translated global segment -/

/-- Spatial phase accumulated before the preferred global segment. -/
def wholeLineCauchyGlobalPreferredSpatialShift
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : ℝ :=
  c * ((wholeLineCauchyGlobalIndex p u₀ t : ℝ) *
    wholeLineCauchyGlobalStep p u₀)

/-- The preferred restart datum translated so that the global traveling-wave
phase is again normalized at zero. -/
def wholeLineCauchyGlobalPreferredTranslatedDatum
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) : WholeLineBUC :=
  wholeLineBUCTranslate
    (wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t)
    (wholeLineCauchyGlobalDatum p u₀
      (wholeLineCauchyGlobalIndex p u₀ t))

/-- Canonical fixed point issued from the phase-normalized preferred restart
datum. -/
def wholeLineCauchyGlobalPreferredTranslatedSegment
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) :
    WholeLineBUCTrajectory (wholeLineCauchyGlobalSegmentTime p u₀) :=
  wholeLineCauchyBUCMildFixedPoint p
    (wholeLineCauchyGlobalClamp_pos p u₀).le
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t)
    (wholeLineCauchyGlobalSegmentTime_rate p u₀)

/-- The preferred translated segment is exactly the spatial translate of the
untranslated preferred segment. -/
theorem wholeLineCauchyGlobalPreferredTranslatedSegment_eq
    (p : CMParams) (u₀ : WholeLineBUC) (c t : ℝ) :
    wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t =
      wholeLineBUCTrajectorySpatialTranslate
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t)
        (wholeLineCauchyGlobalSegment p u₀
          (wholeLineCauchyGlobalIndex p u₀ t)) := by
  simpa only [wholeLineCauchyGlobalPreferredTranslatedSegment,
    wholeLineCauchyGlobalPreferredTranslatedDatum,
    wholeLineCauchyGlobalSegment] using
    wholeLineCauchyBUCMildFixedPoint_spatialTranslate p
      (wholeLineCauchyGlobalClamp_pos p u₀).le
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalDatum p u₀
        (wholeLineCauchyGlobalIndex p u₀ t))
      (wholeLineCauchyGlobalSegmentTime_rate p u₀)

/-- At a positive global time, the global moving-frame slice equals the
moving-frame slice of the phase-normalized preferred translated segment at
its local time. -/
theorem wholeLineCauchyGlobal_coMoving_eq_preferredTranslatedSegment
    (p : CMParams) (u₀ : WholeLineBUC) {c t : ℝ} (ht : 0 < t) :
    coMovingPath c (wholeLineCauchyGlobalU p u₀) t =
      coMovingPath c
        (fun s x =>
          (wholeLineBUCTrajectoryExtend
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
            (wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t) s).1 x)
        (wholeLineCauchyGlobalLocalTime p u₀ t) := by
  funext x
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let d := wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t
  have hq : q ∈ Set.Icc (0 : ℝ)
      (wholeLineCauchyGlobalSegmentTime p u₀) :=
    ⟨(wholeLineCauchyGlobalLocalTime_pos p u₀ ht).le,
      (wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le).le⟩
  have hext := wholeLineBUCTrajectoryExtend_eq
    (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
    (wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t) hq
  have hglobal := congrFun
    (wholeLineCauchyGlobal_coMoving_eq_fixedPointCoMoving_localTime
      p u₀ (c := c) ht) x
  have hglobal' : wholeLineCauchyGlobalU p u₀ t (x + c * t) =
      (wholeLineCauchyGlobalSegment p u₀
        (wholeLineCauchyGlobalIndex p u₀ t) ⟨q, hq⟩).1
        (x + d + c * q) := by
    calc
      wholeLineCauchyGlobalU p u₀ t (x + c * t) =
          wholeLineCauchyBUCMildFixedPointCoMovingPath p
            (wholeLineCauchyGlobalClamp_pos p u₀).le
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
            (wholeLineCauchyGlobalDatum p u₀
              (wholeLineCauchyGlobalIndex p u₀ t))
            (wholeLineCauchyGlobalSegmentTime_rate p u₀) c q (x + d) := by
        simpa only [q, d, wholeLineCauchyGlobalPreferredSpatialShift,
          mul_assoc] using hglobal
      _ = (wholeLineCauchyGlobalSegment p u₀
            (wholeLineCauchyGlobalIndex p u₀ t) ⟨q, hq⟩).1
            (x + d + c * q) := by
        rw [wholeLineCauchyBUCMildFixedPointCoMovingPath_of_mem
          p (wholeLineCauchyGlobalClamp_pos p u₀).le
            (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
            (wholeLineCauchyGlobalDatum p u₀
              (wholeLineCauchyGlobalIndex p u₀ t))
            (wholeLineCauchyGlobalSegmentTime_rate p u₀) c q (x + d) hq]
        rfl
  unfold coMovingPath at hglobal ⊢
  change wholeLineCauchyGlobalU p u₀ t (x + c * t) =
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
      (wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t) q).1
        (x + c * q)
  rw [hext]
  rw [wholeLineCauchyGlobalPreferredTranslatedSegment_eq]
  simp only [wholeLineBUCTrajectorySpatialTranslate_apply]
  rw [hglobal']
  congr 1
  dsimp only [d]
  ring

/-! ## Global weighted-gradient producer -/

/-- At an arbitrary positive global time, the local raw-DQ/Henry producer
applies to the phase-normalized preferred segment.  The sole global weighted
input is exact-weight `H0` integrability of that segment's translated restart
datum. -/
theorem paper5WeightedPopulationX_sq_integrable_global_positive
    (p : CMParams) (hregime : WholeLineCauchyCeilingRegime p)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t) (hBlog : 0 ≤ Blog)
    (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |(wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t).1 y -
        Uw y| ^ 2)) :
    Integrable (fun x =>
      paper5WeightedPopulationX eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) Uw t x ^ 2)
      volume := by
  let H := wholeLineCauchyGlobalSegmentTime p u₀
  let q := wholeLineCauchyGlobalLocalTime p u₀ t
  let n := wholeLineCauchyGlobalIndex p u₀ t
  let d := wholeLineCauchyGlobalPreferredSpatialShift p u₀ c t
  let Traj := wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t
  let u : ℝ → ℝ → ℝ := fun s x =>
    (wholeLineBUCTrajectoryExtend
      (wholeLineCauchyGlobalSegmentTime_pos p u₀).le Traj s).1 x
  have hq : 0 < q := by
    simpa only [q] using wholeLineCauchyGlobalLocalTime_pos p u₀ ht
  have hqH : q ≤ H := by
    exact (show q < H from by
      simpa only [q, H] using
        wholeLineCauchyGlobalLocalTime_lt_segmentTime p u₀ ht.le).le
  have hstrip : ∀ z : Set.Icc (0 : ℝ) H, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        (wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀) z).1 x ∈
          Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀) := by
    intro z x
    have hbase :=
      (wholeLineCauchyGlobalDatum_segment_bounds
        p hregime u₀ hu₀ n).2.1 z (x + d)
    change
      (wholeLineCauchyGlobalPreferredTranslatedSegment p u₀ c t z).1 x ∈
        Set.Icc (0 : ℝ) (wholeLineCauchyGlobalClamp p u₀)
    rw [wholeLineCauchyGlobalPreferredTranslatedSegment_eq]
    simpa only [wholeLineBUCTrajectorySpatialTranslate_apply, n, d, H]
      using hbase
  have hlocal : Integrable (fun x =>
      paper5WeightedPopulationX eta (coMovingPath c u) Uw q x ^ 2)
      volume := by
    simpa only [u, Traj, H, q] using
      (paper5WeightedPopulationX_sq_integrable_mildFixedPoint_wave_positive
        p
        (M := wholeLineCauchyGlobalClamp p u₀)
        (T := wholeLineCauchyGlobalSegmentTime p u₀)
        (Blog := Blog) (eta := eta) (c := c)
        (t := wholeLineCauchyGlobalLocalTime p u₀ t)
        (D := D) (E := E) (Kflux := Kflux) (FD := FD) (B := B)
        (wholeLineCauchyGlobalClamp_pos p u₀).le
        (wholeLineCauchyGlobalSegmentTime_pos p u₀).le
        hq hqH hBlog heta heta_one
        (wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t)
        (wholeLineCauchyGlobalSegmentTime_rate p u₀)
        hstrip hTW hbound hreg hMChi hlog hD hFD hB hUd hUdd hUddcont
        hflux hfluxd hflux_has hfluxd_cont hreact hreact_cont hgrad_int
        hdata_full)
  have hco : coMovingPath c (wholeLineCauchyGlobalU p u₀) t =
      coMovingPath c u q := by
    simpa only [u, Traj, q] using
      wholeLineCauchyGlobal_coMoving_eq_preferredTranslatedSegment
        p u₀ (c := c) ht
  have hfield : (fun x =>
      paper5WeightedPopulationX eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) Uw t x ^ 2) =
      fun x => paper5WeightedPopulationX eta (coMovingPath c u) Uw q x ^ 2 := by
    funext x
    unfold paper5WeightedPopulationX paper5WeightedPopulation
    rw [hco]
  rw [hfield]
  exact hlocal

/-- Nonpositive sensitivity supplies both the canonical ceiling regime and
the `MChi`-inside-clamp condition automatically.  Thus, in the Paper 1
stability branch, the only global weighted premise left by the preferred
restart construction is the exact-weight `H0` datum at that restart. -/
theorem paper5WeightedPopulationX_sq_integrable_global_chi_nonpos
    (p : CMParams) (hchi : p.χ ≤ 0)
    (u₀ : WholeLineBUC) (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    {Blog eta c t D E Kflux FD B : ℝ}
    (ht : 0 < t) (hBlog : 0 ≤ Blog)
    (heta : 0 < eta) (heta_one : eta < 1)
    {Uw Vw : ℝ → ℝ}
    (hTW : IsTravelingWave p c Uw Vw)
    (hbound : HasWaveUpperTailBound p c Uw)
    (hreg : TravelingWaveRegularity p c Uw Vw)
    (hlog : ∀ y, |deriv Uw y / Uw y| ≤ Blog)
    (hD : 0 ≤ D) (hFD : 0 ≤ FD) (hB : 0 ≤ B)
    (hUd : ∀ y, |deriv Uw y| ≤ D)
    (hUdd : ∀ y, |deriv (deriv Uw) y| ≤ E)
    (hUddcont : Continuous (deriv (deriv Uw)))
    (hflux : ∀ y, |wholeLineTravelingWaveFlux p Uw Vw y| ≤ Kflux)
    (hfluxd : ∀ y,
      |deriv (wholeLineTravelingWaveFlux p Uw Vw) y| ≤ FD)
    (hflux_has : ∀ y, HasDerivAt
      (wholeLineTravelingWaveFlux p Uw Vw)
      (deriv (wholeLineTravelingWaveFlux p Uw Vw) y) y)
    (hfluxd_cont : Continuous
      (deriv (wholeLineTravelingWaveFlux p Uw Vw)))
    (hreact : ∀ y, |wholeLineCauchyShiftedReaction p Uw y| ≤ B)
    (hreact_cont : Continuous (wholeLineCauchyShiftedReaction p Uw))
    (hgrad_int : ∀ q, 0 < q → ∀ x, IntervalIntegrable
      (fun r : ℝ => paper5MovingFrameHeatGradOp c r
        (wholeLineTravelingWaveFlux p Uw Vw) x) volume 0 q)
    (hdata_full : Integrable (fun y : ℝ => Real.exp (2 * eta * y) *
      |(wholeLineCauchyGlobalPreferredTranslatedDatum p u₀ c t).1 y -
        Uw y| ^ 2)) :
    Integrable (fun x =>
      paper5WeightedPopulationX eta
        (coMovingPath c (wholeLineCauchyGlobalU p u₀)) Uw t x ^ 2)
      volume := by
  have hregime : WholeLineCauchyCeilingRegime p :=
    WholeLineCauchyCeilingRegime.of_nonpositive hchi
  have hMChi : MChi p ≤ wholeLineCauchyGlobalClamp p u₀ := by
    rw [MChi_eq_one_of_chi_nonpos p hchi]
    have hstable : 1 ≤ wholeLineCauchyStableCeiling p u₀ :=
      wholeLineCauchyStableCeiling_one_le hregime u₀
    unfold wholeLineCauchyGlobalClamp
    linarith
  exact paper5WeightedPopulationX_sq_integrable_global_positive
    p hregime u₀ hu₀ ht hBlog heta heta_one hTW hbound hreg hMChi hlog
      hD hFD hB hUd hUdd hUddcont hflux hfluxd hflux_has hfluxd_cont
      hreact hreact_cont hgrad_int hdata_full

end ShenWork.Paper1

#print axioms
  ShenWork.Paper1.wholeLineBUCTrajectoryExtend_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyHeatBUCTotal_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyHeatGradientBUCTotal_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyGradientBUCIntegrand_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyValueBUCIntegrand_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyGradientDuhamelBUC_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyValueDuhamelBUC_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildMap_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyBUCMildFixedPoint_spatialTranslate
#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobalPreferredTranslatedSegment_eq
#print axioms
  ShenWork.Paper1.wholeLineCauchyGlobal_coMoving_eq_preferredTranslatedSegment
#print axioms
  ShenWork.Paper1.paper5WeightedPopulationX_sq_integrable_global_positive
#print axioms
  ShenWork.Paper1.paper5WeightedPopulationX_sq_integrable_global_chi_nonpos
