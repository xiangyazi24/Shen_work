import ShenWork.Paper1.WholeLineWeightedRegularityMild

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- Picard iterates of the canonical globally truncated BUC mild map,
started from an arbitrary reference trajectory (in the application, the
translated traveling-wave trajectory). -/
def wholeLineCauchyBUCMildPicardFrom
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (W : WholeLineBUCTrajectory T) (n : ℕ) :
    WholeLineBUCTrajectory T :=
  (wholeLineCauchyBUCMildMap p hM hT u₀)^[n] W

@[simp] theorem wholeLineCauchyBUCMildPicardFrom_zero
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (W : WholeLineBUCTrajectory T) :
    wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W 0 = W := by
  simp [wholeLineCauchyBUCMildPicardFrom]

theorem wholeLineCauchyBUCMildPicardFrom_succ
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (W : WholeLineBUCTrajectory T) (n : ℕ) :
    wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W (n + 1) =
      wholeLineCauchyBUCMildMap p hM hT u₀
        (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n) := by
  simp [wholeLineCauchyBUCMildPicardFrom, Function.iterate_succ_apply']

/-- The trajectory Picard sequence converges in the compact-time sup metric
to the canonical Banach fixed point. -/
theorem wholeLineCauchyBUCMildPicardFrom_tendsto_fixedPoint
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (W : WholeLineBUCTrajectory T) :
    Tendsto
      (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W)
      atTop
      (𝓝 (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall)) := by
  simpa [wholeLineCauchyBUCMildPicardFrom,
    wholeLineCauchyBUCMildFixedPoint] using
    (wholeLineCauchyBUCMildMap_contracting p hM hT u₀ hsmall).tendsto_iterate_fixedPoint W

/-- Quantitative geometric version of the same Picard convergence. -/
theorem wholeLineCauchyBUCMildPicardFrom_dist_fixedPoint_le
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (W : WholeLineBUCTrajectory T) (n : ℕ) :
    dist (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n)
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) ≤
      dist W (wholeLineCauchyBUCMildMap p hM hT u₀ W) *
        (wholeLineCauchyBUCMildRate p M T) ^ n /
          (1 - wholeLineCauchyBUCMildRate p M T) := by
  simpa [wholeLineCauchyBUCMildPicardFrom,
    wholeLineCauchyBUCMildFixedPoint] using
    (wholeLineCauchyBUCMildMap_contracting p hM hT u₀ hsmall).apriori_dist_iterate_fixedPoint_le W n

/-- Explicit uniform form: eventually every time slice and every spatial
point are within `eps` of the canonical fixed point.  The first sup metric is
over the compact time interval and the second is the BUC spatial sup norm. -/
theorem wholeLineCauchyBUCMildPicardFrom_eventually_uniform
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (W : WholeLineBUCTrajectory T) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in atTop, ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      |(wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n z).1 x -
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x| < eps := by
  have hconv := wholeLineCauchyBUCMildPicardFrom_tendsto_fixedPoint
    p hM hT u₀ hsmall W
  have hball : ∀ᶠ n in atTop,
      wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n ∈
        Metric.ball
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) eps :=
    hconv.eventually (Metric.ball_mem_nhds _ heps)
  have hevent : ∀ᶠ n in atTop,
      dist (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n)
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) < eps := by
    filter_upwards [hball] with n hn
    simpa [Metric.mem_ball] using hn
  filter_upwards [hevent] with n hn
  intro z x
  have htime :
      dist (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n z)
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z) ≤
        dist (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n)
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) :=
    ContinuousMap.dist_apply_le_dist z
  have hspace :
      |(wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n z).1 x -
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z).1 x| ≤
        dist (wholeLineCauchyBUCMildPicardFrom p hM hT u₀ W n z)
          (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall z) :=
    WholeLineBUC.pointwise_abs_sub_le_dist _ _ x
  exact hspace.trans_lt (htime.trans_lt hn)

#print axioms wholeLineCauchyBUCMildPicardFrom_tendsto_fixedPoint
#print axioms wholeLineCauchyBUCMildPicardFrom_dist_fixedPoint_le
#print axioms wholeLineCauchyBUCMildPicardFrom_eventually_uniform

end ShenWork.Paper1
