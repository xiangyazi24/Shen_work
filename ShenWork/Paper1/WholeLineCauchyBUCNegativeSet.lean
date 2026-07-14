import ShenWork.Paper1.WholeLineCauchyBUCFixedPoint

open Filter Topology MeasureTheory Real Set

noncomputable section

namespace ShenWork.Paper1

/-!
# Vanishing of the clamped sources on the negative set

The globally clamped fixed point need not yet be known nonnegative.  At every
strictly negative point, however, joint continuity gives a space-time
neighborhood on which the clamp is identically zero.  Both nonlinear sources
therefore vanish on that neighborhood.  This is the local input for the
off-support Gaussian differentiation argument.
-/

theorem clampIcc_eq_zero_of_nonpos
    {M s : ℝ} (hM : 0 ≤ M) (hs : s ≤ 0) :
    clampIcc M s = 0 := by
  unfold clampIcc
  rw [min_eq_right (hs.trans hM), max_eq_left hs]

theorem wholeLineCauchyTruncatedFlux_eq_zero_of_nonpos
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ} {x : ℝ}
    (hx : u x ≤ 0) :
    wholeLineCauchyTruncatedFlux p M u x = 0 := by
  unfold wholeLineCauchyTruncatedFlux wholeLineChemotaxisFlux
    wholeLineCauchyClampProfile
  rw [clampIcc_eq_zero_of_nonpos hM hx]
  simp [Real.zero_rpow (ne_of_gt (zero_lt_one.trans_le p.hm))]

theorem wholeLineCauchyTruncatedReaction_eq_zero_of_nonpos
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) {u : ℝ → ℝ} {x : ℝ}
    (hx : u x ≤ 0) :
    wholeLineCauchyTruncatedReaction p M u x = 0 := by
  unfold wholeLineCauchyTruncatedReaction
  rw [wholeLineCauchyShiftedReaction_eq]
  have hclamp : wholeLineCauchyClampProfile M u x = 0 :=
    clampIcc_eq_zero_of_nonpos hM hx
  rw [hclamp]
  simp

/-- A strict negative value of a continuous BUC trajectory persists on a
product metric neighborhood inside the compact time cylinder. -/
theorem wholeLineBUCTrajectory_negative_product_ball
    {T : ℝ} (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) (hneg : (U z).1 x < 0) :
    ∃ ε > 0, ∀ w : Set.Icc (0 : ℝ) T, ∀ y : ℝ,
      dist w z < ε → dist y x < ε → (U w).1 y < 0 := by
  let F : Set.Icc (0 : ℝ) T × ℝ → ℝ := fun q => (U q.1).1 q.2
  have hpre : F ⁻¹' Set.Iio 0 ∈ 𝓝 (z, x) :=
    (wholeLineBUCTrajectory_jointContinuous U).continuousAt
      (Iio_mem_nhds hneg)
  rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro w y hw hy
  have hmem : (w, y) ∈ Metric.ball (z, x) ε := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hw, hy⟩
  simpa [F] using hball hmem

/-- Both clamped source trajectories vanish on the product neighborhood of a
strictly negative trajectory point. -/
theorem wholeLineCauchy_sourceTrajectories_zero_near_negative
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) (x : ℝ) (hneg : (U z).1 x < 0) :
    ∃ ε > 0, ∀ w : Set.Icc (0 : ℝ) T, ∀ y : ℝ,
      dist w z < ε → dist y x < ε →
        (wholeLineCauchyFluxSourceTrajectory p hM hT U w.1).1 y = 0 ∧
        (wholeLineCauchyReactionSourceTrajectory p hM hT U w.1).1 y = 0 := by
  rcases wholeLineBUCTrajectory_negative_product_ball U z x hneg with
    ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro w y hw hy
  have hwy : (U w).1 y ≤ 0 := (hball w y hw hy).le
  have hext : wholeLineBUCTrajectoryExtend hT U w.1 = U w := by
    exact wholeLineBUCTrajectoryExtend_eq hT U w.2
  constructor
  · simp only [wholeLineCauchyFluxSourceTrajectory,
      wholeLineCauchyTruncatedFluxBUC_apply, hext]
    exact wholeLineCauchyTruncatedFlux_eq_zero_of_nonpos p hM hwy
  · simp only [wholeLineCauchyReactionSourceTrajectory,
      wholeLineCauchyTruncatedReactionBUC_apply, hext]
    exact wholeLineCauchyTruncatedReaction_eq_zero_of_nonpos p hM hwy

section WholeLineCauchyBUCNegativeSetAxiomAudit

#print axioms wholeLineCauchyTruncatedFlux_eq_zero_of_nonpos
#print axioms wholeLineCauchyTruncatedReaction_eq_zero_of_nonpos
#print axioms wholeLineCauchy_sourceTrajectories_zero_near_negative

end WholeLineCauchyBUCNegativeSetAxiomAudit

end ShenWork.Paper1
