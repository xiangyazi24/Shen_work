import ShenWork.Paper1.WholeLineWeightedRegularityActualHistory
import ShenWork.Paper1.WholeLineWeightedRegularityCanonicalSlice
import ShenWork.Paper1.WholeLineWeightedRegularityBUCHistory
import ShenWork.Paper1.WholeLineWeightedRegularityBUCTranslate
import ShenWork.Paper1.WholeLineWeightedRegularityPicard

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section
namespace ShenWork.Paper1

theorem capWeightSqrt_le_plateau
    (eta R x : ℝ) :
    capWeightSqrt eta R x ≤ Real.exp (eta * R) := by
  unfold capWeightSqrt
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · calc
      capWeight eta R x ≤ Real.exp (2 * eta * R) :=
        capWeight_le_plateau eta R x
      _ = Real.exp (eta * R) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring

theorem capWeightSqrt_hasDerivAt
    (eta R x : ℝ) :
    HasDerivAt (capWeightSqrt eta R)
      (eta * capWeightSqrt eta R x /
        (1 + Real.exp (2 * eta * (x - R)))) x := by
  have h := (capWeight_hasDerivAt eta R x).sqrt
    (ne_of_gt (capWeight_pos eta R x))
  unfold capWeightSqrt
  convert h using 1
  have hs : Real.sqrt (capWeight eta R x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (capWeight_pos eta R x))
  field_simp [hs]
  rw [Real.sq_sqrt (capWeight_pos eta R x).le]

theorem capWeightSqrt_abs_deriv_le
    {eta : ℝ} (heta : 0 ≤ eta) (R x : ℝ) :
    |deriv (capWeightSqrt eta R) x| ≤
      eta * Real.exp (eta * R) := by
  rw [(capWeightSqrt_hasDerivAt eta R x).deriv,
    abs_of_nonneg (div_nonneg
      (mul_nonneg heta (capWeightSqrt_pos eta R x).le) (by positivity))]
  have hden : 1 ≤ 1 + Real.exp (2 * eta * (x - R)) := by
    linarith [Real.exp_pos (2 * eta * (x - R))]
  calc
    eta * capWeightSqrt eta R x /
          (1 + Real.exp (2 * eta * (x - R))) ≤
        eta * capWeightSqrt eta R x :=
      div_le_self (mul_nonneg heta (capWeightSqrt_pos eta R x).le) hden
    _ ≤ eta * Real.exp (eta * R) :=
      mul_le_mul_of_nonneg_left (capWeightSqrt_le_plateau eta R x) heta

theorem capWeightSqrt_lipschitz
    {eta : ℝ} (heta : 0 ≤ eta) (R : ℝ) :
    LipschitzWith (Real.toNNReal (eta * Real.exp (eta * R)))
      (capWeightSqrt eta R) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (capWeightSqrt_hasDerivAt eta R x).differentiableAt
  · intro x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
      Real.coe_toNNReal _ (mul_nonneg heta (Real.exp_pos _).le)]
    exact capWeightSqrt_abs_deriv_le heta R x

def capWeightSqrtBUC
    (eta R : ℝ) (heta : 0 ≤ eta) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (capWeightSqrt eta R)
    (capWeightSqrt_lipschitz heta R).uniformContinuous
    (Real.exp (eta * R))
    (fun x => by
      rw [abs_of_pos (capWeightSqrt_pos eta R x)]
      exact capWeightSqrt_le_plateau eta R x)

@[simp] theorem capWeightSqrtBUC_apply
    (eta R : ℝ) (heta : 0 ≤ eta) (x : ℝ) :
    (capWeightSqrtBUC eta R heta).1 x = capWeightSqrt eta R x := rfl

/-- Pointwise multiplication by the fixed cap square root as a BUC map. -/
def capWeightSqrtMulBUC
    (eta R : ℝ) (heta : 0 ≤ eta) (u : WholeLineBUC) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (fun x => capWeightSqrt eta R x * u.1 x)
    (uniformContinuous_mul_of_bounded
      (capWeightSqrt_lipschitz heta R).uniformContinuous u.2
      (fun x => by
        rw [abs_of_pos (capWeightSqrt_pos eta R x)]
        exact capWeightSqrt_le_plateau eta R x)
      (fun x => WholeLineBUC.abs_apply_le_norm u x))
    (Real.exp (eta * R) * ‖u‖)
    (fun x => by
      rw [abs_mul]
      exact mul_le_mul
        (by
          rw [abs_of_pos (capWeightSqrt_pos eta R x)]
          exact capWeightSqrt_le_plateau eta R x)
        (WholeLineBUC.abs_apply_le_norm u x)
        (abs_nonneg _) (Real.exp_pos _).le)

@[simp] theorem capWeightSqrtMulBUC_apply
    (eta R : ℝ) (heta : 0 ≤ eta) (u : WholeLineBUC) (x : ℝ) :
    (capWeightSqrtMulBUC eta R heta u).1 x =
      capWeightSqrt eta R x * u.1 x := rfl

theorem capWeightSqrtMulBUC_dist_le
    (eta R : ℝ) (heta : 0 ≤ eta) (u v : WholeLineBUC) :
    dist (capWeightSqrtMulBUC eta R heta u)
        (capWeightSqrtMulBUC eta R heta v) ≤
      Real.exp (eta * R) * dist u v := by
  change dist
      (capWeightSqrtMulBUC eta R heta u).1
      (capWeightSqrtMulBUC eta R heta v).1 ≤ _
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  rw [Real.dist_eq]
  change |capWeightSqrt eta R x * u.1 x -
      capWeightSqrt eta R x * v.1 x| ≤ _
  rw [← mul_sub, abs_mul]
  have hpoint : |u.1 x - v.1 x| ≤ dist u v := by
    change dist (u.1 x) (v.1 x) ≤ dist u.1 v.1
    exact BoundedContinuousFunction.dist_coe_le_dist x
  exact mul_le_mul
    (by
      rw [abs_of_pos (capWeightSqrt_pos eta R x)]
      exact capWeightSqrt_le_plateau eta R x)
    hpoint (abs_nonneg _) (Real.exp_pos _).le

theorem capWeightSqrtMulBUC_lipschitz
    (eta R : ℝ) (heta : 0 ≤ eta) :
    LipschitzWith (Real.toNNReal (Real.exp (eta * R)))
      (capWeightSqrtMulBUC eta R heta) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro u v
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  exact capWeightSqrtMulBUC_dist_le eta R heta u v

theorem wholeLineBUCTranslate_dist_le'
    (a : ℝ) (u v : WholeLineBUC) :
    dist (wholeLineBUCTranslate a u) (wholeLineBUCTranslate a v) ≤
      dist u v := by
  change dist (wholeLineBUCTranslate a u).1
      (wholeLineBUCTranslate a v).1 ≤ dist u.1 v.1
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  change dist (u.1 (x + a)) (v.1 (x + a)) ≤ dist u.1 v.1
  exact BoundedContinuousFunction.dist_coe_le_dist (x + a)

theorem wholeLineBUCTranslate_lipschitz'
    (a : ℝ) :
    LipschitzWith 1 (wholeLineBUCTranslate a) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro u v
  simpa only [NNReal.coe_one, one_mul] using
    wholeLineBUCTranslate_dist_le' a u v

/-- Pointwise difference with an explicit BUC construction.  Keeping this
away from the reducible submodule's inherited `Sub` instance also makes the
topological continuity proof instance-stable. -/
def wholeLineBUCPointwiseSub (u v : WholeLineBUC) : WholeLineBUC :=
  wholeLineBUCOfUniformBound
    (fun x => u.1 x - v.1 x)
    (u.2.sub v.2)
    (‖u‖ + ‖v‖)
    (fun x => by
      exact (abs_sub (u.1 x) (v.1 x)).trans
        (add_le_add (WholeLineBUC.abs_apply_le_norm u x)
          (WholeLineBUC.abs_apply_le_norm v x)))

@[simp] theorem wholeLineBUCPointwiseSub_apply
    (u v : WholeLineBUC) (x : ℝ) :
    (wholeLineBUCPointwiseSub u v).1 x = u.1 x - v.1 x := rfl

theorem wholeLineBUCPointwiseSub_dist_le
    (u₂ u₁ v₂ v₁ : WholeLineBUC) :
    dist (wholeLineBUCPointwiseSub u₂ u₁)
        (wholeLineBUCPointwiseSub v₂ v₁) ≤
      dist u₂ v₂ + dist u₁ v₁ := by
  change dist (wholeLineBUCPointwiseSub u₂ u₁).1
      (wholeLineBUCPointwiseSub v₂ v₁).1 ≤ _
  rw [BoundedContinuousFunction.dist_le_iff_of_nonempty]
  intro x
  rw [Real.dist_eq]
  change |(u₂.1 x - u₁.1 x) - (v₂.1 x - v₁.1 x)| ≤ _
  calc
    |(u₂.1 x - u₁.1 x) - (v₂.1 x - v₁.1 x)| ≤
        |u₂.1 x - v₂.1 x| + |u₁.1 x - v₁.1 x| := by
      rw [show (u₂.1 x - u₁.1 x) - (v₂.1 x - v₁.1 x) =
        (u₂.1 x - v₂.1 x) - (u₁.1 x - v₁.1 x) by ring]
      exact abs_sub _ _
    _ ≤ dist u₂ v₂ + dist u₁ v₁ := by
      apply add_le_add
      · change dist (u₂.1 x) (v₂.1 x) ≤ dist u₂.1 v₂.1
        exact BoundedContinuousFunction.dist_coe_le_dist x
      · change dist (u₁.1 x) (v₁.1 x) ≤ dist u₁.1 v₁.1
        exact BoundedContinuousFunction.dist_coe_le_dist x

theorem wholeLineBUCPointwiseSub_continuousOn
    {f g : ℝ → WholeLineBUC} {S : Set ℝ}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
    ContinuousOn (fun s => wholeLineBUCPointwiseSub (f s) (g s)) S := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨δf, hδf, hfmod⟩ := (Metric.continuousWithinAt_iff.mp (hf s hs))
    (eps / 2) (by linarith)
  obtain ⟨δg, hδg, hgmod⟩ := (Metric.continuousWithinAt_iff.mp (hg s hs))
    (eps / 2) (by linarith)
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro y hyS hys
  have hfy := hfmod hyS (lt_of_lt_of_le hys (min_le_left _ _))
  have hgy := hgmod hyS (lt_of_lt_of_le hys (min_le_right _ _))
  exact lt_of_le_of_lt
    (wholeLineBUCPointwiseSub_dist_le (f y) (g y) (f s) (g s))
    (by linarith)

/-- The cap-conjugated chemotaxis slice in a moving-frame Picard comparison. -/

def capWeightedPicardChemotaxisBUCHistory
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c : ℝ) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (t s : ℝ) : WholeLineBUC :=
  capWeightSqrtMulBUC eta R heta
    ((-p.χ) • wholeLineBUCTranslate (c * t)
      (wholeLineBUCPointwiseSub
        (wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s)
        (wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s)))

/-- BUC-valued cap-conjugated reaction history. -/
def capWeightedPicardReactionBUCHistory
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c : ℝ) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (t s : ℝ) : WholeLineBUC :=
  capWeightSqrtMulBUC eta R heta
    (wholeLineBUCTranslate (c * t)
      (wholeLineBUCPointwiseSub
        (wholeLineCauchyValueBUCIntegrand p hM hT U₂ t s)
        (wholeLineCauchyValueBUCIntegrand p hM hT U₁ t s)))

/-- Scalar heat convolution preserves pointwise differences of BUC inputs.
This is stated at the scalar operator level to avoid the duplicate additive
instances carried by the reducible BUC submodule abbreviation. -/

theorem capWeightedPicardChemotaxisBUCHistory_apply_of_lt
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (hst : s < t) (x : ℝ) :
    (capWeightedPicardChemotaxisBUCHistory
        p hM hT eta R c heta U₂ U₁ t s).1 x =
      capWeightedPicardChemotaxisHistoryRaw
        p hM hT eta R c U₂ U₁ t s x := by
  rw [capWeightedPicardChemotaxisHistoryRaw_eq_gradientBUCIntegrand
    p hM hT U₂ U₁ hst x]
  simp only [capWeightedPicardChemotaxisBUCHistory,
    capWeightSqrtMulBUC_apply, wholeLineBUCTranslate_apply,
    Submodule.coe_smul_of_tower, BoundedContinuousFunction.coe_smul,
    wholeLineBUCPointwiseSub_apply, smul_eq_mul]
  ring

theorem capWeightedPicardReactionBUCHistory_apply_of_lt
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (hst : s < t) (x : ℝ) :
    (capWeightedPicardReactionBUCHistory
        p hM hT eta R c heta U₂ U₁ t s).1 x =
      capWeightedPicardReactionHistoryRaw
        p hM hT eta R c U₂ U₁ t s x := by
  rw [capWeightedPicardReactionHistoryRaw_eq_valueBUCIntegrand
    p hM hT U₂ U₁ hst x]
  simp only [capWeightedPicardReactionBUCHistory,
    capWeightSqrtMulBUC_apply, wholeLineBUCTranslate_apply,
    wholeLineBUCPointwiseSub_apply]

theorem capWeightedPicardChemotaxisBUCHistory_continuousOn_Iio
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    ContinuousOn
      (capWeightedPicardChemotaxisBUCHistory
        p hM hT eta R c heta U₂ U₁ t) (Set.Iio t) := by
  have hsub : ContinuousOn
      (fun s => wholeLineBUCPointwiseSub
        (wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s)
        (wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s))
      (Set.Iio t) :=
    wholeLineBUCPointwiseSub_continuousOn
      (wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
        p hM hT U₂)
      (wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
        p hM hT U₁)
  have htrans : ContinuousOn
      (fun s => wholeLineBUCTranslate (c * t)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s)
          (wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s)))
      (Set.Iio t) :=
    by
      simpa only [Function.comp_def] using
        (wholeLineBUCTranslate_lipschitz' (c * t)).continuous.comp_continuousOn hsub
  have hsmul : ContinuousOn
      (fun s => (-p.χ) • wholeLineBUCTranslate (c * t)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s)
          (wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s)))
      (Set.Iio t) := continuousOn_const.smul htrans
  simpa only [capWeightedPicardChemotaxisBUCHistory, Function.comp_def] using
    (capWeightSqrtMulBUC_lipschitz eta R heta).continuous.comp_continuousOn hsmul

theorem capWeightedPicardReactionBUCHistory_continuousOn_Iio
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    ContinuousOn
      (capWeightedPicardReactionBUCHistory
        p hM hT eta R c heta U₂ U₁ t) (Set.Iio t) := by
  have hsub : ContinuousOn
      (fun s => wholeLineBUCPointwiseSub
        (wholeLineCauchyValueBUCIntegrand p hM hT U₂ t s)
        (wholeLineCauchyValueBUCIntegrand p hM hT U₁ t s))
      (Set.Iio t) :=
    wholeLineBUCPointwiseSub_continuousOn
      (wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
        p hM hT U₂)
      (wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
        p hM hT U₁)
  have htrans : ContinuousOn
      (fun s => wholeLineBUCTranslate (c * t)
        (wholeLineBUCPointwiseSub
          (wholeLineCauchyValueBUCIntegrand p hM hT U₂ t s)
          (wholeLineCauchyValueBUCIntegrand p hM hT U₁ t s)))
      (Set.Iio t) :=
    by
      simpa only [Function.comp_def] using
        (wholeLineBUCTranslate_lipschitz' (c * t)).continuous.comp_continuousOn hsub
  simpa only [capWeightedPicardReactionBUCHistory, Function.comp_def] using
    (capWeightSqrtMulBUC_lipschitz eta R heta).continuous.comp_continuousOn htrans

/-- Terminal-zero totalization of the BUC chemotaxis history. -/
def capWeightedPicardChemotaxisBUCHistoryIio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c : ℝ) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (t s : ℝ) : WholeLineBUC :=
  if s < t then
    capWeightedPicardChemotaxisBUCHistory
      p hM hT eta R c heta U₂ U₁ t s
  else 0

/-- Terminal-zero totalization of the BUC reaction history. -/
def capWeightedPicardReactionBUCHistoryIio
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (eta R c : ℝ) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (t s : ℝ) : WholeLineBUC :=
  if s < t then
    capWeightedPicardReactionBUCHistory
      p hM hT eta R c heta U₂ U₁ t s
  else 0

theorem capWeightedPicardChemotaxisBUCHistoryIio_continuousOn_Iio
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    ContinuousOn
      (capWeightedPicardChemotaxisBUCHistoryIio
        p hM hT eta R c heta U₂ U₁ t) (Set.Iio t) := by
  refine (capWeightedPicardChemotaxisBUCHistory_continuousOn_Iio
    p hM hT (R := R) (c := c) heta U₂ U₁).congr ?_
  intro s hs
  have hst : s < t := hs
  simp only [capWeightedPicardChemotaxisBUCHistoryIio, if_pos hst]

theorem capWeightedPicardReactionBUCHistoryIio_continuousOn_Iio
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    ContinuousOn
      (capWeightedPicardReactionBUCHistoryIio
        p hM hT eta R c heta U₂ U₁ t) (Set.Iio t) := by
  refine (capWeightedPicardReactionBUCHistory_continuousOn_Iio
    p hM hT (R := R) (c := c) heta U₂ U₁).congr ?_
  intro s hs
  have hst : s < t := hs
  simp only [capWeightedPicardReactionBUCHistoryIio, if_pos hst]

theorem capWeightedPicardChemotaxisBUCHistoryIio_aestronglyMeasurable
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    AEStronglyMeasurable
      (capWeightedPicardChemotaxisBUCHistoryIio
        p hM hT eta R c heta U₂ U₁ t) volume := by
  let F := capWeightedPicardChemotaxisBUCHistory
    p hM hT eta R c heta U₂ U₁ t
  have hFIio : AEStronglyMeasurable F (volume.restrict (Set.Iio t)) :=
    (capWeightedPicardChemotaxisBUCHistory_continuousOn_Iio
      p hM hT heta U₂ U₁).aestronglyMeasurable measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio t).indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hFIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    by_cases hst : s < t
    · simp [capWeightedPicardChemotaxisBUCHistoryIio, F, hst]
    · simp [capWeightedPicardChemotaxisBUCHistoryIio, F, hst])

theorem capWeightedPicardReactionBUCHistoryIio_aestronglyMeasurable
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    AEStronglyMeasurable
      (capWeightedPicardReactionBUCHistoryIio
        p hM hT eta R c heta U₂ U₁ t) volume := by
  let F := capWeightedPicardReactionBUCHistory
    p hM hT eta R c heta U₂ U₁ t
  have hFIio : AEStronglyMeasurable F (volume.restrict (Set.Iio t)) :=
    (capWeightedPicardReactionBUCHistory_continuousOn_Iio
      p hM hT heta U₂ U₁).aestronglyMeasurable measurableSet_Iio
  have hind : AEStronglyMeasurable ((Set.Iio t).indicator F) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Iio).2 hFIio
  exact hind.congr (Eventually.of_forall fun s => by
    simp only [Set.indicator_apply, Set.mem_Iio]
    by_cases hst : s < t
    · simp [capWeightedPicardReactionBUCHistoryIio, F, hst]
    · simp [capWeightedPicardReactionBUCHistoryIio, F, hst])

theorem capWeightSqrtMulBUC_norm_le
    (eta R : ℝ) (heta : 0 ≤ eta) (u : WholeLineBUC) :
    ‖capWeightSqrtMulBUC eta R heta u‖ ≤
      Real.exp (eta * R) * ‖u‖ := by
  change ‖(capWeightSqrtMulBUC eta R heta u).1‖ ≤ _
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg u))).2
  intro x
  change |capWeightSqrt eta R x * u.1 x| ≤ Real.exp (eta * R) * ‖u‖
  rw [abs_mul]
  exact mul_le_mul
    (by
      rw [abs_of_pos (capWeightSqrt_pos eta R x)]
      exact capWeightSqrt_le_plateau eta R x)
    (WholeLineBUC.abs_apply_le_norm u x)
    (abs_nonneg _) (Real.exp_pos _).le

theorem wholeLineBUCTranslate_norm_le'
    (a : ℝ) (u : WholeLineBUC) :
    ‖wholeLineBUCTranslate a u‖ ≤ ‖u‖ := by
  change ‖(wholeLineBUCTranslate a u).1‖ ≤ ‖u.1‖
  apply (BoundedContinuousFunction.norm_le (norm_nonneg u.1)).2
  intro x
  exact WholeLineBUC.abs_apply_le_norm u (x + a)

theorem wholeLineBUCPointwiseSub_norm_le_dist
    (u v : WholeLineBUC) :
    ‖wholeLineBUCPointwiseSub u v‖ ≤ dist u v := by
  change ‖(wholeLineBUCPointwiseSub u v).1‖ ≤ dist u.1 v.1
  apply (BoundedContinuousFunction.norm_le dist_nonneg).2
  intro x
  change |u.1 x - v.1 x| ≤ dist u.1 v.1
  exact BoundedContinuousFunction.dist_coe_le_dist
    (f := u.1) (g := v.1) (x : ℝ)

theorem capWeightedPicardChemotaxisBUCHistoryIio_norm_le
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (hst : s < t) :
    ‖capWeightedPicardChemotaxisBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t s‖ ≤
      Real.exp (eta * R) * |p.χ| *
        ((2 / Real.sqrt (4 * Real.pi)) *
          (wholeLineCauchyFluxLip p M * dist U₂ U₁)) *
            (t - s) ^ (-(1 / 2 : ℝ)) := by
  let I₂ := wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t s
  let I₁ := wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t s
  have hdist : dist I₂ I₁ ≤
      ((2 / Real.sqrt (4 * Real.pi)) *
        (wholeLineCauchyFluxLip p M * dist U₂ U₁)) *
          (t - s) ^ (-(1 / 2 : ℝ)) := by
    rw [WholeLineBUC.dist_eq_norm_sub]
    exact wholeLineCauchyGradientBUCIntegrand_sub_norm_le
      p hM hT U₂ U₁ hst
  rw [capWeightedPicardChemotaxisBUCHistoryIio, if_pos hst]
  calc
    ‖capWeightedPicardChemotaxisBUCHistory
        p hM hT eta R c heta U₂ U₁ t s‖ ≤
        Real.exp (eta * R) *
          ‖(-p.χ) • wholeLineBUCTranslate (c * t)
            (wholeLineBUCPointwiseSub I₂ I₁)‖ :=
      capWeightSqrtMulBUC_norm_le eta R heta _
    _ = Real.exp (eta * R) * |p.χ| *
          ‖wholeLineBUCTranslate (c * t)
            (wholeLineBUCPointwiseSub I₂ I₁)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg]
      ring
    _ ≤ Real.exp (eta * R) * |p.χ| *
          ‖wholeLineBUCPointwiseSub I₂ I₁‖ := by
      gcongr
      exact wholeLineBUCTranslate_norm_le' _ _
    _ ≤ Real.exp (eta * R) * |p.χ| * dist I₂ I₁ := by
      gcongr
      exact wholeLineBUCPointwiseSub_norm_le_dist I₂ I₁
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hdist
        (mul_nonneg (Real.exp_pos (eta * R)).le (abs_nonneg p.χ))
      convert h using 1 <;> ring

theorem capWeightedPicardReactionBUCHistoryIio_norm_le
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) (hst : s < t) :
    ‖capWeightedPicardReactionBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t s‖ ≤
      Real.exp (eta * R) *
        ((1 + reactionLip p.α M) * dist U₂ U₁) := by
  let I₂ := wholeLineCauchyValueBUCIntegrand p hM hT U₂ t s
  let I₁ := wholeLineCauchyValueBUCIntegrand p hM hT U₁ t s
  have hdist : dist I₂ I₁ ≤
      (1 + reactionLip p.α M) * dist U₂ U₁ := by
    rw [WholeLineBUC.dist_eq_norm_sub]
    exact wholeLineCauchyValueBUCIntegrand_sub_norm_le
      p hM hT U₂ U₁ hst.le
  rw [capWeightedPicardReactionBUCHistoryIio, if_pos hst]
  calc
    ‖capWeightedPicardReactionBUCHistory
        p hM hT eta R c heta U₂ U₁ t s‖ ≤
        Real.exp (eta * R) *
          ‖wholeLineBUCTranslate (c * t)
            (wholeLineBUCPointwiseSub I₂ I₁)‖ :=
      capWeightSqrtMulBUC_norm_le eta R heta _
    _ ≤ Real.exp (eta * R) *
          ‖wholeLineBUCPointwiseSub I₂ I₁‖ := by
      gcongr
      exact wholeLineBUCTranslate_norm_le' _ _
    _ ≤ Real.exp (eta * R) * dist I₂ I₁ := by
      gcongr
      exact wholeLineBUCPointwiseSub_norm_le_dist I₂ I₁
    _ ≤ _ := by
      gcongr

theorem capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (heta : 0 ≤ eta) (heta_one : eta < 1)
    (U₂ U₁ : WholeLineBUCTrajectory T) {r : ℝ → ℝ}
    (hr : ∀ s, s < t → 0 ≤ r s)
    (hclose : ∀ s, s < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2) :
    ∀ s, Integrable (fun x : ℝ =>
      (capWeightedPicardChemotaxisBUCHistoryIio
        p hM hT eta R c heta U₂ U₁ t s).1 x ^ 2) volume := by
  intro s
  by_cases hst : s < t
  · rcases exists_canonical_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
      p hM heta heta_one (sub_pos.mpr hst) le_rfl (hr s hst)
      (wholeLineBUCTrajectoryExtend hT U₂ s)
      (wholeLineBUCTrajectoryExtend hT U₁ s)
      (hclose s hst) (henergy s hst) with ⟨hgmeas, hg2, _hbound⟩
    refine hg2.congr (Eventually.of_forall fun x => ?_)
    change (capWeightedPicardChemotaxisHistoryRaw
      p hM hT eta R c U₂ U₁ t s x) ^ 2 =
        (capWeightedPicardChemotaxisBUCHistoryIio
          p hM hT eta R c heta U₂ U₁ t s).1 x ^ 2
    rw [capWeightedPicardChemotaxisBUCHistoryIio, if_pos hst,
      capWeightedPicardChemotaxisBUCHistory_apply_of_lt
        p hM hT heta U₂ U₁ hst x]
  · simp [capWeightedPicardChemotaxisBUCHistoryIio, hst]

theorem capWeightedPicardReactionBUCHistoryIio_sq_integrable
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) {r : ℝ → ℝ}
    (hr : ∀ s, s < t → 0 ≤ r s)
    (hclose : ∀ s, s < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2) :
    ∀ s, Integrable (fun x : ℝ =>
      (capWeightedPicardReactionBUCHistoryIio
        p hM hT eta R c heta U₂ U₁ t s).1 x ^ 2) volume := by
  intro s
  by_cases hst : s < t
  · rcases exists_canonical_capWeightedMovingHeat_truncatedReactionL2_le_kernel
      p hM heta (sub_pos.mpr hst) le_rfl (hr s hst)
      (wholeLineBUCTrajectoryExtend hT U₂ s)
      (wholeLineBUCTrajectoryExtend hT U₁ s)
      (hclose s hst) (henergy s hst) with ⟨hgmeas, hg2, _hbound⟩
    refine hg2.congr (Eventually.of_forall fun x => ?_)
    change (capWeightedPicardReactionHistoryRaw
      p hM hT eta R c U₂ U₁ t s x) ^ 2 =
        (capWeightedPicardReactionBUCHistoryIio
          p hM hT eta R c heta U₂ U₁ t s).1 x ^ 2
    rw [capWeightedPicardReactionBUCHistoryIio, if_pos hst,
      capWeightedPicardReactionBUCHistory_apply_of_lt
        p hM hT heta U₂ U₁ hst x]
  · simp [capWeightedPicardReactionBUCHistoryIio, hst]

theorem capWeightedPicardChemotaxisL2History_norm_le
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (htT : t ≤ T)
    (heta : 0 ≤ eta) (heta_one : eta < 1)
    (U₂ U₁ : WholeLineBUCTrajectory T) {r : ℝ → ℝ}
    (hr : ∀ q, q < t → 0 ≤ r q)
    (hclose : ∀ q, q < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ q).1 (x + c * q) -
        (wholeLineBUCTrajectoryExtend hT U₁ q).1 (x + c * q)| ^ 2))
    (henergy : ∀ q, q < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ q).1 (x + c * q) -
        (wholeLineBUCTrajectoryExtend hT U₁ q).1 (x + c * q)| ^ 2) ≤
          (r q) ^ 2)
    (hs : s ∈ Set.Icc (0 : ℝ) t) (hst : s < t) :
    let F := capWeightedPicardChemotaxisBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t
    let hF2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
      p hM hT heta heta_one U₂ U₁ hr hclose henergy
    ‖wholeLineRealL2Section
      (fun q x => (F q).1 x)
      (fun q => (F q).1.continuous.aestronglyMeasurable)
      hF2 s‖ ≤
        ((2 * capMildGrowthBound eta c T * eta *
              Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)) +
          capMildKernelInvSqrtConstant p M eta c T *
            (t - s) ^ (-(1 / 2 : ℝ))) * r s := by
  dsimp only
  let F := capWeightedPicardChemotaxisBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ t
  let hF2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
    p hM hT heta heta_one U₂ U₁ hr hclose henergy
  let g : ℝ → ℝ := capWeightedPicardChemotaxisHistoryRaw
    p hM hT eta R c U₂ U₁ t s
  rcases exists_canonical_capWeightedMovingHeatGradient_truncatedChemotaxisL2_le_kernel
      (T := T) p hM heta heta_one (sub_pos.mpr hst)
      (by linarith [hs.1, htT]) (hr s hst)
      (wholeLineBUCTrajectoryExtend hT U₂ s)
      (wholeLineBUCTrajectoryExtend hT U₁ s)
      (hclose s hst) (henergy s hst) with ⟨hgmeas, hg2, hbound⟩
  let Z := wholeLineRealL2Section
    (fun q x => (F q).1 x)
    (fun q => (F q).1.continuous.aestronglyMeasurable)
    hF2
  have hfun : (fun x => (F s).1 x) = g := by
    funext x
    simp only [F, g, capWeightedPicardChemotaxisBUCHistoryIio,
      if_pos hst]
    exact capWeightedPicardChemotaxisBUCHistory_apply_of_lt
      p hM hT heta U₂ U₁ hst x
  have hZeq : Z s = wholeLineRealL2OfSqIntegrable g hgmeas hg2 := by
    apply Lp.ext
    filter_upwards [wholeLineRealL2Section_coe_ae
      (fun q x => (F q).1 x)
      (fun q => (F q).1.continuous.aestronglyMeasurable) hF2 s,
      wholeLineRealL2OfSqIntegrable_coe_ae g hgmeas hg2]
      with x hx hgx
    rw [hx, hgx]
    exact congrFun hfun x
  change ‖Z s‖ ≤ _
  rw [hZeq]
  exact hbound

theorem capWeightedPicardReactionL2History_norm_le
    (p : CMParams) {M T eta R c t s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (htT : t ≤ T)
    (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) {r : ℝ → ℝ}
    (hr : ∀ q, q < t → 0 ≤ r q)
    (hclose : ∀ q, q < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ q).1 (x + c * q) -
        (wholeLineBUCTrajectoryExtend hT U₁ q).1 (x + c * q)| ^ 2))
    (henergy : ∀ q, q < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ q).1 (x + c * q) -
        (wholeLineBUCTrajectoryExtend hT U₁ q).1 (x + c * q)| ^ 2) ≤
          (r q) ^ 2)
    (hs : s ∈ Set.Icc (0 : ℝ) t) (hst : s < t) :
    let F := capWeightedPicardReactionBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t
    let hF2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
      p hM hT heta U₂ U₁ hr hclose henergy
    ‖wholeLineRealL2Section
      (fun q x => (F q).1 x)
      (fun q => (F q).1.continuous.aestronglyMeasurable)
      hF2 s‖ ≤
        (2 * capMildGrowthBound eta c T *
          (1 + reactionLip p.α M)) * r s := by
  dsimp only
  let F := capWeightedPicardReactionBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ t
  let hF2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
    p hM hT heta U₂ U₁ hr hclose henergy
  let g : ℝ → ℝ := capWeightedPicardReactionHistoryRaw
    p hM hT eta R c U₂ U₁ t s
  rcases exists_canonical_capWeightedMovingHeat_truncatedReactionL2_le_kernel
      (T := T) p hM heta (sub_pos.mpr hst)
      (by linarith [hs.1, htT]) (hr s hst)
      (wholeLineBUCTrajectoryExtend hT U₂ s)
      (wholeLineBUCTrajectoryExtend hT U₁ s)
      (hclose s hst) (henergy s hst) with ⟨hgmeas, hg2, hbound⟩
  let Z := wholeLineRealL2Section
    (fun q x => (F q).1 x)
    (fun q => (F q).1.continuous.aestronglyMeasurable)
    hF2
  have hfun : (fun x => (F s).1 x) = g := by
    funext x
    simp only [F, g, capWeightedPicardReactionBUCHistoryIio,
      if_pos hst]
    exact capWeightedPicardReactionBUCHistory_apply_of_lt
      p hM hT heta U₂ U₁ hst x
  have hZeq : Z s = wholeLineRealL2OfSqIntegrable g hgmeas hg2 := by
    apply Lp.ext
    filter_upwards [wholeLineRealL2Section_coe_ae
      (fun q x => (F q).1 x)
      (fun q => (F q).1.continuous.aestronglyMeasurable) hF2 s,
      wholeLineRealL2OfSqIntegrable_coe_ae g hgmeas hg2]
      with x hx hgx
    rw [hx, hgx]
    exact congrFun hfun x
  change ‖Z s‖ ≤ _
  rw [hZeq]
  exact hbound

/-- The terminal-zero cap-weighted chemotaxis history is Bochner integrable
in `BUC(ℝ)` on every positive time window.  The only singularity is the
integrable heat-gradient factor `(t-s)⁻¹ᐟ²`. -/
theorem capWeightedPicardChemotaxisBUCHistoryIio_norm_integrable
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    Integrable (fun s => ‖capWeightedPicardChemotaxisBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t s‖)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
  let C : ℝ := Real.exp (eta * R) * |p.χ| *
    ((2 / Real.sqrt (4 * Real.pi)) *
      (wholeLineCauchyFluxLip p M * dist U₂ U₁))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      (mul_nonneg
        (div_nonneg (by norm_num)
          (Real.sqrt_pos.2 (by positivity)).le)
        (mul_nonneg (wholeLineCauchyFluxLip_nonneg p hM) dist_nonneg))
  have hdomII : IntervalIntegrable
      (fun s : ℝ => C * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul C
  have hdom : Integrable
      (fun s : ℝ => C * (t - s) ^ (-(1 / 2 : ℝ)))
      (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hdomII
  refine Integrable.mono' hdom
    ((capWeightedPicardChemotaxisBUCHistoryIio_aestronglyMeasurable
      p hM hT heta U₂ U₁).norm.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  by_cases hst : s < t
  · simpa only [C, mul_assoc] using
      capWeightedPicardChemotaxisBUCHistoryIio_norm_le
        p hM hT heta U₂ U₁ hst
  · have hse : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp [capWeightedPicardChemotaxisBUCHistoryIio]

/-- The terminal-zero cap-weighted reaction history is Bochner integrable
in `BUC(ℝ)` on every positive time window. -/
theorem capWeightedPicardReactionBUCHistoryIio_norm_integrable
    (p : CMParams) {M T eta R c t : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 ≤ t) (heta : 0 ≤ eta)
    (U₂ U₁ : WholeLineBUCTrajectory T) :
    Integrable (fun s => ‖capWeightedPicardReactionBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t s‖)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
  let C : ℝ := Real.exp (eta * R) *
    ((1 + reactionLip p.α M) * dist U₂ U₁)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg
        (add_nonneg zero_le_one (reactionLip_nonneg p.hα hM)) dist_nonneg)
  have hdomII : IntervalIntegrable (fun _s : ℝ => C) volume 0 t :=
    intervalIntegrable_const
  have hdom : Integrable (fun _s : ℝ => C)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp hdomII
  refine Integrable.mono' hdom
    ((capWeightedPicardReactionBUCHistoryIio_aestronglyMeasurable
      p hM hT heta U₂ U₁).norm.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  by_cases hst : s < t
  · simpa only [C] using
      capWeightedPicardReactionBUCHistoryIio_norm_le
        p hM hT heta U₂ U₁ hst
  · have hse : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp [capWeightedPicardReactionBUCHistoryIio, C, hC]

/-- A Banach-valued history which is strongly measurable strictly before its
terminal time and dominated by the heat-gradient singularity is Bochner
interval integrable.  The endpoint value is irrelevant. -/
theorem intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_sub_rpow_neg_half
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t A : ℝ} {Z : ℝ → E}
    (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hZmeas : AEStronglyMeasurable Z
      (volume.restrict (Set.Iio t)))
    (hZnorm : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖Z s‖ ≤ A * (t - s) ^ (-(1 / 2 : ℝ))) :
    IntervalIntegrable Z volume 0 t := by
  have hdomII : IntervalIntegrable
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half
      t).const_mul A
  have hdom : IntegrableOn
      (fun s : ℝ => A * (t - s) ^ (-(1 / 2 : ℝ)))
      (Set.Ico (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht).1 hdomII
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le ht]
  refine ⟨hZmeas.mono_set Set.Ico_subset_Iio_self, ?_⟩
  exact hdom.2.mono_enorm (by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    have hnorm := hZnorm s hs
    have hg : 0 ≤ A * (t - s) ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hA (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _)
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs, abs_of_nonneg hg] using hnorm)

/-- Constant-majorant companion to the preceding terminal-time lemma. -/
theorem intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t A : ℝ} {Z : ℝ → E}
    (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hZmeas : AEStronglyMeasurable Z
      (volume.restrict (Set.Iio t)))
    (hZnorm : ∀ s ∈ Set.Ico (0 : ℝ) t, ‖Z s‖ ≤ A) :
    IntervalIntegrable Z volume 0 t := by
  have hdomII : IntervalIntegrable (fun _s : ℝ => A) volume 0 t :=
    intervalIntegrable_const
  have hdom : IntegrableOn (fun _s : ℝ => A)
      (Set.Ico (0 : ℝ) t) volume :=
    (intervalIntegrable_iff_integrableOn_Ico_of_le ht).1 hdomII
  rw [intervalIntegrable_iff_integrableOn_Ico_of_le ht]
  refine ⟨hZmeas.mono_set Set.Ico_subset_Iio_self, ?_⟩
  exact hdom.2.mono_enorm (by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with s hs
    have hnorm := hZnorm s hs
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs, abs_of_nonneg hA] using hnorm)

/-- The canonical cap-weighted chemotaxis history is Bochner interval
integrable whenever the input trajectory difference stays in one fixed
cap-energy ball. -/
theorem capWeightedPicardChemotaxisL2History_intervalIntegrable_of_uniform_cap
    (p : CMParams) {M T eta R c t B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T)
    (heta : 0 ≤ eta) (heta_one : eta < 1) (hB : 0 ≤ B)
    (U₂ U₁ : WholeLineBUCTrajectory T)
    (hr : ∀ s, s < t → 0 ≤ r s)
    (hclose : ∀ s, s < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) t, s < t → r s ≤ B) :
    let F := capWeightedPicardChemotaxisBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t
    let hF2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
      p hM hT heta heta_one U₂ U₁ hr hclose henergy
    IntervalIntegrable
      (wholeLineRealL2Section
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2) volume 0 t := by
  dsimp only
  let F := capWeightedPicardChemotaxisBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ t
  let hF2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
    p hM hT heta heta_one U₂ U₁ hr hclose henergy
  let Z := wholeLineRealL2Section
    (fun s x => (F s).1 x)
    (fun s => (F s).1.continuous.aestronglyMeasurable)
    hF2
  let C0 : ℝ := 2 * capMildGrowthBound eta c T * eta *
    Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)
  let C1 : ℝ := capMildKernelInvSqrtConstant p M eta c T
  let q : ℝ → ℝ := fun s =>
    (C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ))) * B
  have hC0 : 0 ≤ C0 := by
    dsimp [C0, capMildGrowthBound]
    unfold capWeightedChemotaxisOperatorSquareConstant
      capWeightedFluxSquareConstant
    positivity
  have hC1 : 0 ≤ C1 :=
    capMildKernelInvSqrtConstant_nonneg p hM heta hT c
  have hq_int : IntervalIntegrable q volume 0 t := by
    dsimp only [q]
    exact (intervalIntegrable_const_add_mul_invSqrt_sub
      (t := t) (C0 := C0) (C1 := C1)).mul_const B
  have hq_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ q s := by
    intro s hs
    exact mul_nonneg
      (add_nonneg hC0
        (mul_nonneg hC1 (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))) hB
  have htot : IntervalIntegrable
      (fun s => if s < t then Z s else 0) volume 0 t := by
    apply wholeLineRealL2Section_Iio_totalized_intervalIntegrable_of_majorant
      ht
      (capWeightedPicardChemotaxisBUCHistoryIio_continuousOn_Iio
        p hM hT heta U₂ U₁)
      hF2 hq_int hq_nonneg
    intro s hs hst
    have hnorm := capWeightedPicardChemotaxisL2History_norm_le
      p hM hT htT heta heta_one U₂ U₁ hr hclose henergy hs hst
    have hcoef : 0 ≤ C0 + C1 * (t - s) ^ (-(1 / 2 : ℝ)) :=
      add_nonneg hC0
        (mul_nonneg hC1 (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
    simpa only [Z, F, hF2, q, C0, C1] using
      hnorm.trans (mul_le_mul_of_nonneg_left (hrB s hs hst) hcoef)
  change IntervalIntegrable Z volume 0 t
  refine IntervalIntegrable.congr ?_ htot
  intro s hs
  rw [Set.uIoc_of_le ht] at hs
  by_cases hst : s < t
  · simp [hst]
  · have hFs : F s = 0 := by
      simp [F, capWeightedPicardChemotaxisBUCHistoryIio, hst]
    have hZs : Z s = 0 := by
      apply Lp.ext
      filter_upwards [wholeLineRealL2Section_coe_ae
        (fun q x => (F q).1 x)
        (fun q => (F q).1.continuous.aestronglyMeasurable) hF2 s]
        with x hx
      rw [hx]
      simp [hFs]
    simp [hst, hZs]

/-- The canonical cap-weighted reaction history is Bochner interval
integrable under the same fixed cap-energy bound. -/
theorem capWeightedPicardReactionL2History_intervalIntegrable_of_uniform_cap
    (p : CMParams) {M T eta R c t B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T)
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (U₂ U₁ : WholeLineBUCTrajectory T)
    (hr : ∀ s, s < t → 0 ≤ r s)
    (hclose : ∀ s, s < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) t, s < t → r s ≤ B) :
    let F := capWeightedPicardReactionBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t
    let hF2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
      p hM hT heta U₂ U₁ hr hclose henergy
    IntervalIntegrable
      (wholeLineRealL2Section
        (fun s x => (F s).1 x)
        (fun s => (F s).1.continuous.aestronglyMeasurable)
        hF2) volume 0 t := by
  dsimp only
  let F := capWeightedPicardReactionBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ t
  let hF2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
    p hM hT heta U₂ U₁ hr hclose henergy
  let Z := wholeLineRealL2Section
    (fun s x => (F s).1 x)
    (fun s => (F s).1.continuous.aestronglyMeasurable)
    hF2
  let C : ℝ := 2 * capMildGrowthBound eta c T *
    (1 + reactionLip p.α M)
  let q : ℝ → ℝ := fun _s => C * B
  have hC : 0 ≤ C := by
    dsimp [C, capMildGrowthBound]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (add_nonneg zero_le_one (reactionLip_nonneg p.hα hM))
  have hq_int : IntervalIntegrable q volume 0 t :=
    intervalIntegrable_const
  have hq_nonneg : ∀ s ∈ Set.Icc (0 : ℝ) t, 0 ≤ q s := by
    intro _s _hs
    exact mul_nonneg hC hB
  have htot : IntervalIntegrable
      (fun s => if s < t then Z s else 0) volume 0 t := by
    apply wholeLineRealL2Section_Iio_totalized_intervalIntegrable_of_majorant
      ht
      (capWeightedPicardReactionBUCHistoryIio_continuousOn_Iio
        p hM hT heta U₂ U₁)
      hF2 hq_int hq_nonneg
    intro s hs hst
    have hnorm := capWeightedPicardReactionL2History_norm_le
      p hM hT htT heta U₂ U₁ hr hclose henergy hs hst
    simpa only [Z, F, hF2, q, C] using
      hnorm.trans (mul_le_mul_of_nonneg_left (hrB s hs hst) hC)
  change IntervalIntegrable Z volume 0 t
  refine IntervalIntegrable.congr ?_ htot
  intro s hs
  rw [Set.uIoc_of_le ht] at hs
  by_cases hst : s < t
  · simp [hst]
  · have hFs : F s = 0 := by
      simp [F, capWeightedPicardReactionBUCHistoryIio, hst]
    have hZs : Z s = 0 := by
      apply Lp.ext
      filter_upwards [wholeLineRealL2Section_coe_ae
        (fun q x => (F q).1 x)
        (fun q => (F q).1.continuous.aestronglyMeasurable) hF2 s]
        with x hx
      rw [hx]
      simp [hFs]
    simp [hst, hZs]

/-- The Bochner integral of the canonical chemotaxis history realizes the
actual cap-weighted moving-frame difference of the two BUC Duhamel legs. -/
theorem capWeightedPicardChemotaxisL2History_integral_rep_of_uniform_cap
    (p : CMParams) {M T eta R c t B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T)
    (heta : 0 ≤ eta) (heta_one : eta < 1) (hB : 0 ≤ B)
    (U₂ U₁ : WholeLineBUCTrajectory T)
    (hr : ∀ s, s < t → 0 ≤ r s)
    (hclose : ∀ s, s < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) t, s < t → r s ≤ B) :
    let F := capWeightedPicardChemotaxisBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t
    let hF2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
      p hM hT heta heta_one U₂ U₁ hr hclose henergy
    let Z := wholeLineRealL2Section
      (fun s x => (F s).1 x)
      (fun s => (F s).1.continuous.aestronglyMeasurable)
      hF2
    ((((∫ s in (0 : ℝ)..t, Z s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x =>
        capWeightSqrt eta R x * (-p.χ) *
          ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ t).1
              (x + c * t) -
            (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ t).1
              (x + c * t))) := by
  dsimp only
  let F := capWeightedPicardChemotaxisBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ t
  let hF2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
    p hM hT heta heta_one U₂ U₁ hr hclose henergy
  let Z := wholeLineRealL2Section
    (fun s x => (F s).1 x)
    (fun s => (F s).1.continuous.aestronglyMeasurable)
    hF2
  have hZint : IntervalIntegrable Z volume 0 t := by
    simpa only [Z, F, hF2] using
      capWeightedPicardChemotaxisL2History_intervalIntegrable_of_uniform_cap
        p hM hT ht htT heta heta_one hB U₂ U₁
          hr hclose henergy hrB
  have hFub : ((((∫ s in (0 : ℝ)..t, Z s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ s in (0 : ℝ)..t, (F s).1 x) := by
    apply wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history ht
    · exact (capWeightedPicardChemotaxisBUCHistoryIio_aestronglyMeasurable
        p hM hT heta U₂ U₁).restrict
    · exact capWeightedPicardChemotaxisBUCHistoryIio_norm_integrable
        p hM hT ht heta U₂ U₁
    · exact hZint
  refine hFub.trans (Eventually.of_forall fun x => ?_)
  let I₂ := wholeLineCauchyGradientBUCIntegrand p hM hT U₂ t
  let I₁ := wholeLineCauchyGradientBUCIntegrand p hM hT U₁ t
  let A : ℝ := (2 / Real.sqrt (4 * Real.pi)) *
    (M ^ p.m * M ^ p.γ)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hI₂ : IntervalIntegrable
      (fun s => (I₂ s).1 (x + c * t)) volume 0 t := by
    apply intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_sub_rpow_neg_half
      ht hA
    · exact ((wholeLineBUCEvalCLM (x + c * t)).continuous.comp_continuousOn
        (wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
          p hM hT U₂)).aestronglyMeasurable measurableSet_Iio
    · intro s hs
      calc
        ‖(I₂ s).1 (x + c * t)‖ ≤ ‖I₂ s‖ := by
          simpa only [Real.norm_eq_abs] using
            WholeLineBUC.abs_apply_le_norm (I₂ s) (x + c * t)
        _ ≤ A * (t - s) ^ (-(1 / 2 : ℝ)) := by
          simpa only [I₂, A] using
            wholeLineCauchyGradientBUCIntegrand_norm_le
              p hM hT U₂ hs.2
  have hI₁ : IntervalIntegrable
      (fun s => (I₁ s).1 (x + c * t)) volume 0 t := by
    apply intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_sub_rpow_neg_half
      ht hA
    · exact ((wholeLineBUCEvalCLM (x + c * t)).continuous.comp_continuousOn
        (wholeLineCauchyGradientBUCIntegrand_continuousOn_Iio
          p hM hT U₁)).aestronglyMeasurable measurableSet_Iio
    · intro s hs
      calc
        ‖(I₁ s).1 (x + c * t)‖ ≤ ‖I₁ s‖ := by
          simpa only [Real.norm_eq_abs] using
            WholeLineBUC.abs_apply_le_norm (I₁ s) (x + c * t)
        _ ≤ A * (t - s) ^ (-(1 / 2 : ℝ)) := by
          simpa only [I₁, A] using
            wholeLineCauchyGradientBUCIntegrand_norm_le
              p hM hT U₁ hs.2
  calc
    (∫ s in (0 : ℝ)..t, (F s).1 x) =
        ∫ s in (0 : ℝ)..t,
          (capWeightSqrt eta R x * (-p.χ)) *
            ((I₂ s).1 (x + c * t) - (I₁ s).1 (x + c * t)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume t] with s hne hs
      rw [Set.uIoc_of_le ht] at hs
      have hst : s < t := lt_of_le_of_ne hs.2 hne
      simp only [F, capWeightedPicardChemotaxisBUCHistoryIio, if_pos hst]
      rw [capWeightedPicardChemotaxisBUCHistory_apply_of_lt
          p hM hT heta U₂ U₁ hst x,
        capWeightedPicardChemotaxisHistoryRaw_eq_gradientBUCIntegrand
          p hM hT U₂ U₁ hst x]
    _ = (capWeightSqrt eta R x * (-p.χ)) *
        (∫ s in (0 : ℝ)..t,
          ((I₂ s).1 (x + c * t) - (I₁ s).1 (x + c * t))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = capWeightSqrt eta R x * (-p.χ) *
        ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ t).1
            (x + c * t) -
          (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ t).1
            (x + c * t)) := by
      rw [intervalIntegral.integral_sub hI₂ hI₁,
        wholeLineCauchyGradientDuhamelBUC_apply p hM hT U₂ ht,
        wholeLineCauchyGradientDuhamelBUC_apply p hM hT U₁ ht]

/-- The canonical reaction history has the parallel exact Duhamel
representative. -/
theorem capWeightedPicardReactionL2History_integral_rep_of_uniform_cap
    (p : CMParams) {M T eta R c t B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (ht : 0 ≤ t) (htT : t ≤ T)
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (U₂ U₁ : WholeLineBUCTrajectory T)
    (hr : ∀ s, s < t → 0 ≤ r s)
    (hclose : ∀ s, s < t → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < t → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) t, s < t → r s ≤ B) :
    let F := capWeightedPicardReactionBUCHistoryIio
      p hM hT eta R c heta U₂ U₁ t
    let hF2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
      p hM hT heta U₂ U₁ hr hclose henergy
    let Z := wholeLineRealL2Section
      (fun s x => (F s).1 x)
      (fun s => (F s).1.continuous.aestronglyMeasurable)
      hF2
    ((((∫ s in (0 : ℝ)..t, Z s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ t).1
              (x + c * t) -
            (wholeLineCauchyValueDuhamelBUC p hM hT U₁ t).1
              (x + c * t))) := by
  dsimp only
  let F := capWeightedPicardReactionBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ t
  let hF2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
    p hM hT heta U₂ U₁ hr hclose henergy
  let Z := wholeLineRealL2Section
    (fun s x => (F s).1 x)
    (fun s => (F s).1.continuous.aestronglyMeasurable)
    hF2
  have hZint : IntervalIntegrable Z volume 0 t := by
    simpa only [Z, F, hF2] using
      capWeightedPicardReactionL2History_intervalIntegrable_of_uniform_cap
        p hM hT ht htT heta hB U₂ U₁ hr hclose henergy hrB
  have hFub : ((((∫ s in (0 : ℝ)..t, Z s) : WholeLineRealL2) : ℝ → ℝ)
      =ᵐ[volume] fun x => ∫ s in (0 : ℝ)..t, (F s).1 x) := by
    apply wholeLineRealL2_intervalIntegral_coe_ae_of_buc_history ht
    · exact (capWeightedPicardReactionBUCHistoryIio_aestronglyMeasurable
        p hM hT heta U₂ U₁).restrict
    · exact capWeightedPicardReactionBUCHistoryIio_norm_integrable
        p hM hT ht heta U₂ U₁
    · exact hZint
  refine hFub.trans (Eventually.of_forall fun x => ?_)
  let I₂ := wholeLineCauchyValueBUCIntegrand p hM hT U₂ t
  let I₁ := wholeLineCauchyValueBUCIntegrand p hM hT U₁ t
  let A : ℝ := M + M * (1 + M ^ p.α)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hI₂ : IntervalIntegrable
      (fun s => (I₂ s).1 (x + c * t)) volume 0 t := by
    apply intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_const
      ht hA
    · exact ((wholeLineBUCEvalCLM (x + c * t)).continuous.comp_continuousOn
        (wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
          p hM hT U₂)).aestronglyMeasurable measurableSet_Iio
    · intro s hs
      calc
        ‖(I₂ s).1 (x + c * t)‖ ≤ ‖I₂ s‖ := by
          simpa only [Real.norm_eq_abs] using
            WholeLineBUC.abs_apply_le_norm (I₂ s) (x + c * t)
        _ ≤ A := by
          simpa only [I₂, A] using
            wholeLineCauchyValueBUCIntegrand_norm_le
              p hM hT U₂ hs.2.le
  have hI₁ : IntervalIntegrable
      (fun s => (I₁ s).1 (x + c * t)) volume 0 t := by
    apply intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_const
      ht hA
    · exact ((wholeLineBUCEvalCLM (x + c * t)).continuous.comp_continuousOn
        (wholeLineCauchyValueBUCIntegrand_continuousOn_Iio
          p hM hT U₁)).aestronglyMeasurable measurableSet_Iio
    · intro s hs
      calc
        ‖(I₁ s).1 (x + c * t)‖ ≤ ‖I₁ s‖ := by
          simpa only [Real.norm_eq_abs] using
            WholeLineBUC.abs_apply_le_norm (I₁ s) (x + c * t)
        _ ≤ A := by
          simpa only [I₁, A] using
            wholeLineCauchyValueBUCIntegrand_norm_le
              p hM hT U₁ hs.2.le
  calc
    (∫ s in (0 : ℝ)..t, (F s).1 x) =
        ∫ s in (0 : ℝ)..t,
          capWeightSqrt eta R x *
            ((I₂ s).1 (x + c * t) - (I₁ s).1 (x + c * t)) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [Measure.ae_ne volume t] with s hne hs
      rw [Set.uIoc_of_le ht] at hs
      have hst : s < t := lt_of_le_of_ne hs.2 hne
      simp only [F, capWeightedPicardReactionBUCHistoryIio, if_pos hst]
      rw [capWeightedPicardReactionBUCHistory_apply_of_lt
          p hM hT heta U₂ U₁ hst x,
        capWeightedPicardReactionHistoryRaw_eq_valueBUCIntegrand
          p hM hT U₂ U₁ hst x]
    _ = capWeightSqrt eta R x *
        (∫ s in (0 : ℝ)..t,
          ((I₂ s).1 (x + c * t) - (I₁ s).1 (x + c * t))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = capWeightSqrt eta R x *
        ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ t).1
            (x + c * t) -
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ t).1
            (x + c * t)) := by
      rw [intervalIntegral.integral_sub hI₂ hI₁,
        wholeLineCauchyValueDuhamelBUC_apply p hM hT U₂ ht,
        wholeLineCauchyValueDuhamelBUC_apply p hM hT U₁ ht]

/-- Concrete H0 one-step producer.  A uniform cap-energy bound for the two
input trajectories supplies the canonical measurable histories internally,
so the conclusion has no history-selection premise. -/
theorem exists_capWeighted_coMoving_bucMildMap_differenceL2_of_cap_majorant_history
    (p : CMParams) {M T eta R c B₀ B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (U₂ U₁ : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (hr : ∀ s, s < z.1 → 0 ≤ r s)
    (hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) z.1, s < z.1 → r s ≤ B) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1
              (x + c * z.1) -
            (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1
              (x + c * z.1))) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c T * B₀ +
        ∫ s in (0 : ℝ)..z.1,
          (capMildKernelConstant p M eta c T +
            capMildKernelInvSqrtConstant p M eta c T *
              (z.1 - s) ^ (-(1 / 2 : ℝ))) * B := by
  let FG := capWeightedPicardChemotaxisBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ z.1
  let hFG2 := capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
    p hM hT heta heta_one U₂ U₁ hr hclose henergy
  let ZG := wholeLineRealL2Section
    (fun s x => (FG s).1 x)
    (fun s => (FG s).1.continuous.aestronglyMeasurable)
    hFG2
  let FR := capWeightedPicardReactionBUCHistoryIio
    p hM hT eta R c heta U₂ U₁ z.1
  let hFR2 := capWeightedPicardReactionBUCHistoryIio_sq_integrable
    p hM hT heta U₂ U₁ hr hclose henergy
  let ZR := wholeLineRealL2Section
    (fun s x => (FR s).1 x)
    (fun s => (FR s).1.continuous.aestronglyMeasurable)
    hFR2
  let CG0 : ℝ := 2 * capMildGrowthBound eta c T * eta *
    Real.sqrt (capWeightedChemotaxisOperatorSquareConstant p M eta)
  let CR0 : ℝ := 2 * capMildGrowthBound eta c T *
    (1 + reactionLip p.α M)
  let C1 : ℝ := capMildKernelInvSqrtConstant p M eta c T
  let gG : ℝ → ℝ := fun s =>
    (CG0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ))) * B
  let gR : ℝ → ℝ := fun _s => CR0 * B
  have hCG0 : 0 ≤ CG0 := by
    dsimp [CG0, capMildGrowthBound]
    unfold capWeightedChemotaxisOperatorSquareConstant
      capWeightedFluxSquareConstant
    positivity
  have hCR0 : 0 ≤ CR0 := by
    dsimp [CR0, capMildGrowthBound]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (add_nonneg zero_le_one (reactionLip_nonneg p.hα hM))
  have hC1 : 0 ≤ C1 :=
    capMildKernelInvSqrtConstant_nonneg p hM heta hT c
  have hZGint : IntervalIntegrable ZG volume 0 z.1 := by
    simpa only [ZG, FG, hFG2] using
      capWeightedPicardChemotaxisL2History_intervalIntegrable_of_uniform_cap
        p hM hT hz.le z.2.2 heta heta_one hB U₂ U₁
          hr hclose henergy hrB
  have hZRint : IntervalIntegrable ZR volume 0 z.1 := by
    simpa only [ZR, FR, hFR2] using
      capWeightedPicardReactionL2History_intervalIntegrable_of_uniform_cap
        p hM hT hz.le z.2.2 heta hB U₂ U₁
          hr hclose henergy hrB
  have hgGint : IntervalIntegrable gG volume 0 z.1 := by
    dsimp only [gG]
    exact (intervalIntegrable_const_add_mul_invSqrt_sub
      (t := z.1) (C0 := CG0) (C1 := C1)).mul_const B
  have hgRint : IntervalIntegrable gR volume 0 z.1 :=
    intervalIntegrable_const
  have hZG : ∀ s ∈ Set.Icc (0 : ℝ) z.1, ‖ZG s‖ ≤ gG s := by
    intro s hs
    by_cases hst : s < z.1
    · have hnorm := capWeightedPicardChemotaxisL2History_norm_le
        p hM hT z.2.2 heta heta_one U₂ U₁
          hr hclose henergy hs hst
      have hcoef : 0 ≤ CG0 + C1 * (z.1 - s) ^ (-(1 / 2 : ℝ)) :=
        add_nonneg hCG0
          (mul_nonneg hC1 (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
      simpa only [ZG, FG, hFG2, gG, CG0, C1] using
        hnorm.trans (mul_le_mul_of_nonneg_left (hrB s hs hst) hcoef)
    · have hFs : FG s = 0 := by
        simp [FG, capWeightedPicardChemotaxisBUCHistoryIio, hst]
      have hZs : ZG s = 0 := by
        apply Lp.ext
        filter_upwards [wholeLineRealL2Section_coe_ae
          (fun q x => (FG q).1 x)
          (fun q => (FG q).1.continuous.aestronglyMeasurable) hFG2 s]
          with x hx
        rw [hx]
        simp [hFs]
      rw [hZs, norm_zero]
      exact mul_nonneg
        (add_nonneg hCG0
          (mul_nonneg hC1 (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))) hB
  have hZR : ∀ s ∈ Set.Icc (0 : ℝ) z.1, ‖ZR s‖ ≤ gR s := by
    intro s hs
    by_cases hst : s < z.1
    · have hnorm := capWeightedPicardReactionL2History_norm_le
        p hM hT z.2.2 heta U₂ U₁ hr hclose henergy hs hst
      simpa only [ZR, FR, hFR2, gR, CR0] using
        hnorm.trans (mul_le_mul_of_nonneg_left (hrB s hs hst) hCR0)
    · have hFs : FR s = 0 := by
        simp [FR, capWeightedPicardReactionBUCHistoryIio, hst]
      have hZs : ZR s = 0 := by
        apply Lp.ext
        filter_upwards [wholeLineRealL2Section_coe_ae
          (fun q x => (FR q).1 x)
          (fun q => (FR q).1.continuous.aestronglyMeasurable) hFR2 s]
          with x hx
        rw [hx]
        simp [hFs]
      rw [hZs, norm_zero]
      exact mul_nonneg hCR0 hB
  have hZGrep : (((∫ s in (0 : ℝ)..z.1, ZG s) : WholeLineRealL2) :
      ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x * (-p.χ) *
        ((wholeLineCauchyGradientDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyGradientDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)) := by
    simpa only [ZG, FG, hFG2] using
      capWeightedPicardChemotaxisL2History_integral_rep_of_uniform_cap
        p hM hT hz.le z.2.2 heta heta_one hB U₂ U₁
          hr hclose henergy hrB
  have hZRrep : (((∫ s in (0 : ℝ)..z.1, ZR s) : WholeLineRealL2) :
      ℝ → ℝ) =ᵐ[volume] fun x =>
      capWeightSqrt eta R x *
        ((wholeLineCauchyValueDuhamelBUC p hM hT U₂ z.1).1
            (x + c * z.1) -
          (wholeLineCauchyValueDuhamelBUC p hM hT U₁ z.1).1
            (x + c * z.1)) := by
    simpa only [ZR, FR, hFR2] using
      capWeightedPicardReactionL2History_integral_rep_of_uniform_cap
        p hM hT hz.le z.2.2 heta hB U₂ U₁
          hr hclose henergy hrB
  rcases exists_capWeighted_coMoving_bucMildMap_differenceL2_of_history
      p hM heta hT hB₀ R u₀₂ u₀₁ U₂ U₁ z hz
      hdata_meas hdata_cap hdata_energy ZG ZR gG gR
      hZGint hZRint hgGint hgRint hZG hZR hZGrep hZRrep with
    ⟨Z, hZrep, hZbound⟩
  refine ⟨Z, hZrep, hZbound.trans_eq ?_⟩
  congr 1
  apply intervalIntegral.integral_congr
  intro s _hs
  dsimp only [gG, gR, CG0, CR0, C1, capMildKernelConstant]
  ring

/-- Constant-majorant specialization of the concrete H0 one-step producer. -/
theorem exists_capWeighted_coMoving_bucMildMap_differenceL2_of_uniform_cap_history
    (p : CMParams) {M T eta R c B₀ B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (U₂ U₁ : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1
              (x + c * z.1) -
            (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1
              (x + c * z.1))) ∧
      ‖Z‖ ≤ 2 * capMildGrowthBound eta c T * B₀ +
        ∫ s in (0 : ℝ)..z.1,
          (capMildKernelConstant p M eta c T +
            capMildKernelInvSqrtConstant p M eta c T *
              (z.1 - s) ^ (-(1 / 2 : ℝ))) * B := by
  exact exists_capWeighted_coMoving_bucMildMap_differenceL2_of_cap_majorant_history
    p hM hT heta heta_one hB₀ hB u₀₂ u₀₁ U₂ U₁ z hz
      hdata_meas hdata_cap hdata_energy (fun _ _ => hB)
      hclose henergy (fun _ _ _ => le_rfl)

/-- A closed scalar cap ball is preserved by one concrete BUC mild-map
step.  The only history input is the cap-energy bound itself; the actual
chemotaxis and reaction histories are constructed internally by
`exists_capWeighted_coMoving_bucMildMap_differenceL2_of_uniform_cap_history`.
-/
theorem exists_capWeighted_coMoving_bucMildMap_differenceL2_le_of_cap_majorant_history
    (p : CMParams) {M T eta R c B₀ B : ℝ} {r : ℝ → ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (hball : 2 * capMildGrowthBound eta c T * B₀ +
      (capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (U₂ U₁ : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (hr : ∀ s, s < z.1 → 0 ≤ r s)
    (hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤
          (r s) ^ 2)
    (hrB : ∀ s ∈ Set.Icc (0 : ℝ) z.1, s < z.1 → r s ≤ B) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1
              (x + c * z.1) -
            (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1
              (x + c * z.1))) ∧
      ‖Z‖ ≤ B := by
  rcases
      exists_capWeighted_coMoving_bucMildMap_differenceL2_of_cap_majorant_history
        p hM hT heta heta_one hB₀ hB u₀₂ u₀₁ U₂ U₁ z hz
        hdata_meas hdata_cap hdata_energy hr hclose henergy hrB with
    ⟨Z, hZrep, hZbound⟩
  refine ⟨Z, hZrep, hZbound.trans ?_⟩
  let C₀ : ℝ := capMildKernelConstant p M eta c T
  let C₁ : ℝ := capMildKernelInvSqrtConstant p M eta c T
  have hC₀ : 0 ≤ C₀ := capMildKernelConstant_nonneg p hM heta hT c
  have hC₁ : 0 ≤ C₁ :=
    capMildKernelInvSqrtConstant_nonneg p hM heta hT c
  have hmass :
      (∫ s in (0 : ℝ)..z.1,
          (C₀ + C₁ * (z.1 - s) ^ (-(1 / 2 : ℝ)))) ≤
        C₀ * T + 2 * C₁ * Real.sqrt T :=
    intervalIntegral_const_add_mul_invSqrt_sub_le hz z.2.2 hC₀ hC₁
  have hint :
      (∫ s in (0 : ℝ)..z.1,
          (C₀ + C₁ * (z.1 - s) ^ (-(1 / 2 : ℝ))) * B) ≤
        (C₀ * T + 2 * C₁ * Real.sqrt T) * B := by
    rw [intervalIntegral.integral_mul_const]
    exact mul_le_mul_of_nonneg_right hmass hB
  calc
    2 * capMildGrowthBound eta c T * B₀ +
          (∫ s in (0 : ℝ)..z.1,
            (C₀ + C₁ * (z.1 - s) ^ (-(1 / 2 : ℝ))) * B) ≤
        2 * capMildGrowthBound eta c T * B₀ +
          (C₀ * T + 2 * C₁ * Real.sqrt T) * B :=
      by
        simpa only [add_comm] using
          (add_le_add_left hint (2 * capMildGrowthBound eta c T * B₀))
    _ ≤ B := by
      simpa only [C₀, C₁] using hball

/-- Constant-majorant closed-ball specialization. -/
theorem exists_capWeighted_coMoving_bucMildMap_differenceL2_le_of_uniform_cap_history
    (p : CMParams) {M T eta R c B₀ B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (hball : 2 * capMildGrowthBound eta c T * B₀ +
      (capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (U₂ U₁ : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (hz : 0 < z.1)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2)
    (hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2))
    (henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
      |(wholeLineBUCTrajectoryExtend hT U₂ s).1 (x + c * s) -
        (wholeLineBUCTrajectoryExtend hT U₁ s).1 (x + c * s)| ^ 2) ≤ B ^ 2) :
    ∃ Z : WholeLineRealL2,
      ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
        capWeightSqrt eta R x *
          ((wholeLineCauchyBUCMildMap p hM hT u₀₂ U₂ z).1
              (x + c * z.1) -
            (wholeLineCauchyBUCMildMap p hM hT u₀₁ U₁ z).1
              (x + c * z.1))) ∧
      ‖Z‖ ≤ B := by
  exact exists_capWeighted_coMoving_bucMildMap_differenceL2_le_of_cap_majorant_history
    p hM hT heta heta_one hB₀ hB hball u₀₂ u₀₁ U₂ U₁ z hz
      hdata_meas hdata_cap hdata_energy (fun _ _ => hB)
      hclose henergy (fun _ _ _ => le_rfl)

/-- An `L²` representative of a cap-weighted difference recovers both
the raw weighted-square integrability and its scalar energy bound. -/
theorem capEnergy_of_wholeLineRealL2_rep
    {eta R B : ℝ} {d : ℝ → ℝ} (hB : 0 ≤ B)
    (Z : WholeLineRealL2)
    (hrep : ((Z : ℝ → ℝ) =ᵐ[volume]
      fun x => capWeightSqrt eta R x * d x))
    (hZnorm : ‖Z‖ ≤ B) :
    Integrable (fun x : ℝ => capWeight eta R x * |d x| ^ 2) ∧
      (∫ x : ℝ, capWeight eta R x * |d x| ^ 2) ≤ B ^ 2 := by
  have hZsq : Integrable (fun x : ℝ => Z x ^ 2) volume :=
    (memLp_two_iff_integrable_sq (Lp.memLp Z).1).1 (Lp.memLp Z)
  have hcap : Integrable (fun x : ℝ =>
      (capWeightSqrt eta R x * d x) ^ 2) volume := by
    refine hZsq.congr ?_
    filter_upwards [hrep] with x hx
    rw [hx]
  have hweighted : Integrable (fun x : ℝ =>
      capWeight eta R x * |d x| ^ 2) volume := by
    refine hcap.congr (ae_of_all _ ?_)
    intro x
    exact capWeightSqrt_mul_sq_eq eta R x (d x)
  refine ⟨hweighted, ?_⟩
  have hinner := wholeLineIntegral_mul_eq_inner_of_aeEq Z Z hrep hrep
  rw [real_inner_self_eq_norm_sq] at hinner
  have heq : (∫ x : ℝ, capWeight eta R x * |d x| ^ 2) = ‖Z‖ ^ 2 := by
    rw [← hinner]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      simpa only [pow_two] using
        (capWeightSqrt_mul_sq_eq eta R x (d x)).symm)
  rw [heq]
  exact (sq_le_sq₀ (norm_nonneg Z) hB).2 hZnorm


theorem wholeLineCauchyBUCMildMap_zero_eq_data (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T) :
    wholeLineCauchyBUCMildMap p hM hT u₀ U ⟨0, le_rfl, hT⟩ = u₀ := by
  ext x
  simp [wholeLineCauchyBUCMildMap,
    wholeLineCauchyGradientDuhamelBUC,
    wholeLineCauchyValueDuhamelBUC,
    wholeLineCauchyHeatBUCTotal]

theorem wholeLineCauchyBUCMildPicardFrom_zero_eq_data_of_ne_zero (p : CMParams) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (W : WholeLineBUCTrajectory T) :
    ∀ n : ℕ, n ≠ 0 →
      wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n
          ⟨0, le_rfl, hT⟩ = u₀ := by
  intro n hn
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Nat.succ_eq_add_one,
    wholeLineCauchyBUCMildPicardFrom_succ]
  exact wholeLineCauchyBUCMildMap_zero_eq_data p hM hT u₀ _

theorem wholeLineCauchyBUCMildFixedReference_zero_eq_data (p : CMParams) {M T : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀) W) :
    W ⟨0, le_rfl, hT⟩ = u₀ := by
  have h := congrArg
    (fun V : WholeLineBUCTrajectory T => V ⟨0, le_rfl, hT⟩) hfixed
  simpa only [wholeLineCauchyBUCMildMap_zero_eq_data p hM hT u₀ W] using h.symm

theorem exists_capWeighted_coMoving_bucMildPicardFrom_differenceL2_le
    (p : CMParams) {M T eta R c B₀ B : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (heta_one : eta < 1) (hB₀ : 0 ≤ B₀) (hB : 0 ≤ B)
    (hB₀B : B₀ ≤ B)
    (hball : 2 * capMildGrowthBound eta c T * B₀ +
      (capMildKernelConstant p M eta c T * T +
        2 * capMildKernelInvSqrtConstant p M eta c T * Real.sqrt T) * B ≤ B)
    (u₀₂ u₀₁ : WholeLineBUC) (W : WholeLineBUCTrajectory T)
    (hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀₁) W)
    (hdata_meas : Measurable (fun y : ℝ => u₀₂.1 y - u₀₁.1 y))
    (hdata_cap : Integrable (fun y : ℝ => capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2))
    (hdata_energy : (∫ y : ℝ, capWeight eta R y *
      |u₀₂.1 y - u₀₁.1 y| ^ 2) ≤ B₀ ^ 2) :
    ∀ n : ℕ, ∀ z : Set.Icc (0 : ℝ) T,
      ∃ Z : WholeLineRealL2,
        ((Z : ℝ → ℝ) =ᵐ[volume] fun x =>
          capWeightSqrt eta R x *
            ((wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n z).1
                (x + c * z.1) -
              (W z).1 (x + c * z.1))) ∧
        ‖Z‖ ≤ B := by
  intro n
  induction n with
  | zero =>
      intro z
      refine ⟨0, ?_, by simpa using hB⟩
      filter_upwards [] with x
      simp [wholeLineCauchyBUCMildPicardFrom]
  | succ n ih =>
      intro z
      by_cases hz0 : z.1 = 0
      · have hz : z = ⟨0, le_rfl, hT⟩ := Subtype.ext hz0
        subst z
        let Zd := wholeLineRealL2OfSqIntegrable
          (fun x : ℝ => capWeightSqrt eta R x *
            (u₀₂.1 x - u₀₁.1 x))
          ((capWeightSqrt_continuous eta R).mul
            (u₀₂.1.continuous.sub u₀₁.1.continuous)).aestronglyMeasurable
          (by
            refine hdata_cap.congr (ae_of_all _ ?_)
            intro x
            exact (capWeightSqrt_mul_sq_eq eta R x
              (u₀₂.1 x - u₀₁.1 x)).symm)
        have hZdrep : ((Zd : ℝ → ℝ) =ᵐ[volume] fun x : ℝ =>
            capWeightSqrt eta R x * (u₀₂.1 x - u₀₁.1 x)) :=
          wholeLineRealL2OfSqIntegrable_coe_ae _ _ _
        have hZdnorm : ‖Zd‖ ≤ B := by
          apply (sq_le_sq₀ (norm_nonneg Zd) hB).mp
          rw [wholeLineRealL2OfSqIntegrable_norm_sq]
          calc
            (∫ x : ℝ,
                (capWeightSqrt eta R x *
                  (u₀₂.1 x - u₀₁.1 x)) ^ 2) =
                ∫ x : ℝ, capWeight eta R x *
                  |u₀₂.1 x - u₀₁.1 x| ^ 2 := by
              apply integral_congr_ae
              exact ae_of_all _ (fun x =>
                capWeightSqrt_mul_sq_eq eta R x
                  (u₀₂.1 x - u₀₁.1 x))
            _ ≤ B₀ ^ 2 := hdata_energy
            _ ≤ B ^ 2 := (sq_le_sq₀ hB₀ hB).2 hB₀B
        refine ⟨Zd, ?_, hZdnorm⟩
        filter_upwards [hZdrep] with x hx
        simpa only [Nat.succ_eq_add_one,
          wholeLineCauchyBUCMildPicardFrom_succ,
          wholeLineCauchyBUCMildMap_zero_eq_data p hM hT u₀₂,
          wholeLineCauchyBUCMildFixedReference_zero_eq_data p hM hT u₀₁ W hfixed,
          mul_zero, add_zero] using hx
      · have hz : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz0)
        let r : ℝ → ℝ := fun s =>
          if s < 0 then Real.exp (eta * |c * s|) * B₀ else B
        have hr : ∀ s, s < z.1 → 0 ≤ r s := by
          intro s _hs
          dsimp only [r]
          split_ifs
          · exact mul_nonneg (Real.exp_pos _).le hB₀
          · exact hB
        have hrB : ∀ s ∈ Set.Icc (0 : ℝ) z.1, s < z.1 → r s ≤ B := by
          intro s hs _hst
          simp [r, not_lt.mpr hs.1]
        have hclose : ∀ s, s < z.1 → Integrable (fun x => capWeight eta R x *
            |(wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s).1
                  (x + c * s) -
              (wholeLineBUCTrajectoryExtend hT W s).1 (x + c * s)| ^ 2) := by
          intro s hs
          by_cases hs0 : s ≤ 0
          · have hextP : wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s =
                wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n
                  ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            have hextW : wholeLineBUCTrajectoryExtend hT W s =
                W ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            by_cases hn0 : n = 0
            · subst n
              simp [hextP, hextW, wholeLineCauchyBUCMildPicardFrom]
            · rw [hextP, hextW,
                wholeLineCauchyBUCMildPicardFrom_zero_eq_data_of_ne_zero p hM hT u₀₂ W n hn0,
                wholeLineCauchyBUCMildFixedReference_zero_eq_data p hM hT u₀₁ W hfixed]
              by_cases hsneg : s < 0
              · exact (capWeight_shift_sq_integrable_and_integral_le
                    (d := c * s) heta
                    (u₀₂.1.continuous.sub u₀₁.1.continuous)
                    hdata_cap).1
              · have hs_eq : s = 0 := le_antisymm hs0 (not_lt.mp hsneg)
                subst s
                simpa using hdata_cap
          · have hspos : 0 < s := lt_of_not_ge hs0
            have hsT : s ≤ T := (le_of_lt hs).trans z.2.2
            let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT⟩
            obtain ⟨Zs, hZsrep, hZsnorm⟩ := ih zs
            have hsenergy := capEnergy_of_wholeLineRealL2_rep hB Zs hZsrep hZsnorm
            rw [wholeLineBUCTrajectoryExtend_eq hT _ zs.2,
              wholeLineBUCTrajectoryExtend_eq hT W zs.2]
            simpa only [zs] using hsenergy.1
        have henergy : ∀ s, s < z.1 → (∫ x : ℝ, capWeight eta R x *
            |(wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s).1
                  (x + c * s) -
              (wholeLineBUCTrajectoryExtend hT W s).1 (x + c * s)| ^ 2) ≤
                (r s) ^ 2 := by
          intro s hs
          by_cases hs0 : s ≤ 0
          · have hextP : wholeLineBUCTrajectoryExtend hT
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) s =
                wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n
                  ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            have hextW : wholeLineBUCTrajectoryExtend hT W s =
                W ⟨0, le_rfl, hT⟩ := by
              unfold wholeLineBUCTrajectoryExtend
              rw [Set.projIcc_of_le_left hT hs0]
            by_cases hn0 : n = 0
            · subst n
              simp [hextP, hextW, wholeLineCauchyBUCMildPicardFrom,
                sq_nonneg (r s)]
            · rw [hextP, hextW,
                wholeLineCauchyBUCMildPicardFrom_zero_eq_data_of_ne_zero p hM hT u₀₂ W n hn0,
                wholeLineCauchyBUCMildFixedReference_zero_eq_data p hM hT u₀₁ W hfixed]
              by_cases hsneg : s < 0
              · have hshift := capWeight_shift_sq_integrable_and_integral_le
                    (d := c * s) heta
                    (u₀₂.1.continuous.sub u₀₁.1.continuous)
                    hdata_cap
                calc
                  (∫ x : ℝ, capWeight eta R x *
                      |u₀₂.1 (x + c * s) - u₀₁.1 (x + c * s)| ^ 2) ≤
                      Real.exp (2 * eta * |c * s|) *
                        ∫ x : ℝ, capWeight eta R x *
                          |u₀₂.1 x - u₀₁.1 x| ^ 2 := hshift.2
                  _ ≤ Real.exp (2 * eta * |c * s|) * B₀ ^ 2 :=
                    mul_le_mul_of_nonneg_left hdata_energy (Real.exp_pos _).le
                  _ = (r s) ^ 2 := by
                    simp only [r, if_pos hsneg]
                    rw [mul_pow, ← Real.exp_nat_mul]
                    congr 2
                    ring
              · have hs_eq : s = 0 := le_antisymm hs0 (not_lt.mp hsneg)
                subst s
                simp only [mul_zero, add_zero, r, lt_self_iff_false, ↓reduceIte]
                exact hdata_energy.trans ((sq_le_sq₀ hB₀ hB).2 hB₀B)
          · have hspos : 0 < s := lt_of_not_ge hs0
            have hsT : s ≤ T := (le_of_lt hs).trans z.2.2
            let zs : Set.Icc (0 : ℝ) T := ⟨s, hspos.le, hsT⟩
            obtain ⟨Zs, hZsrep, hZsnorm⟩ := ih zs
            have hsenergy := capEnergy_of_wholeLineRealL2_rep hB Zs hZsrep hZsnorm
            rw [wholeLineBUCTrajectoryExtend_eq hT _ zs.2,
              wholeLineBUCTrajectoryExtend_eq hT W zs.2]
            simpa only [zs, r, if_neg (not_lt.mpr hspos.le)] using hsenergy.2
        rcases
            exists_capWeighted_coMoving_bucMildMap_differenceL2_le_of_cap_majorant_history
              p hM hT heta heta_one hB₀ hB hball u₀₂ u₀₁
                (wholeLineCauchyBUCMildPicardFrom p hM hT u₀₂ W n) W z hz
                hdata_meas hdata_cap hdata_energy hr hclose henergy hrB with
          ⟨Z, hZrep, hZnorm⟩
        refine ⟨Z, ?_, hZnorm⟩
        rw [hfixed] at hZrep
        simpa only [Nat.succ_eq_add_one,
          wholeLineCauchyBUCMildPicardFrom_succ] using hZrep



end ShenWork.Paper1

#print axioms ShenWork.Paper1.capWeightedPicardChemotaxisBUCHistoryIio_sq_integrable
#print axioms ShenWork.Paper1.capWeightedPicardReactionBUCHistoryIio_sq_integrable
#print axioms ShenWork.Paper1.capWeightedPicardChemotaxisL2History_norm_le
#print axioms ShenWork.Paper1.capWeightedPicardReactionL2History_norm_le
#print axioms
  ShenWork.Paper1.capWeightedPicardChemotaxisBUCHistoryIio_norm_integrable
#print axioms
  ShenWork.Paper1.capWeightedPicardReactionBUCHistoryIio_norm_integrable
#print axioms
  ShenWork.Paper1.intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_sub_rpow_neg_half
#print axioms
  ShenWork.Paper1.intervalIntegrable_of_aestronglyMeasurableOn_Iio_of_norm_le_const
#print axioms
  ShenWork.Paper1.capWeightedPicardChemotaxisL2History_intervalIntegrable_of_uniform_cap
#print axioms
  ShenWork.Paper1.capWeightedPicardReactionL2History_intervalIntegrable_of_uniform_cap
#print axioms
  ShenWork.Paper1.capWeightedPicardChemotaxisL2History_integral_rep_of_uniform_cap
#print axioms
  ShenWork.Paper1.capWeightedPicardReactionL2History_integral_rep_of_uniform_cap
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_bucMildMap_differenceL2_of_uniform_cap_history
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_bucMildMap_differenceL2_le_of_uniform_cap_history
#print axioms ShenWork.Paper1.capEnergy_of_wholeLineRealL2_rep
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_bucMildMap_differenceL2_of_cap_majorant_history
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_bucMildMap_differenceL2_le_of_cap_majorant_history
#print axioms
  ShenWork.Paper1.exists_capWeighted_coMoving_bucMildPicardFrom_differenceL2_le
