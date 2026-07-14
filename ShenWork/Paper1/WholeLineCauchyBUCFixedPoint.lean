import ShenWork.Paper1.WholeLineCauchyBUCDuhamelContinuity
import Mathlib.Topology.MetricSpace.Contracting

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

set_option maxSynthPendingDepth 10

/-!
# The whole-line BUC contraction map

This file assembles the homogeneous modified heat flow and the two genuine
BUC-valued Bochner Duhamel legs into a self-map of the complete trajectory
space.  The global clamp makes this self-map globally Lipschitz; small time
then gives a Banach contraction without assuming a ball is invariant.
-/

theorem wholeLineCauchyHomogeneousBUC_continuous
    {T : ℝ} (hT : 0 ≤ T) (u₀ : WholeLineBUC) :
    Continuous
      (fun z : Set.Icc (0 : ℝ) T =>
        wholeLineCauchyHeatBUCTotal z.1 u₀) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.1 = 0
  · exact (wholeLineCauchyHeatBUCTotal_continuousAt_zero u₀).comp_of_eq
      continuousAt_subtype_val hz
  · have hzpos : 0 < z.1 := lt_of_le_of_ne z.2.1 (Ne.symm hz)
    exact (wholeLineCauchyHeatBUCTotal_continuousAt_of_pos hzpos u₀).comp'
      continuousAt_subtype_val

/-- Homogeneous modified heat trajectory issued from `u₀`. -/
def wholeLineCauchyHomogeneousTrajectory
    {T : ℝ} (hT : 0 ≤ T) (u₀ : WholeLineBUC) :
    WholeLineBUCTrajectory T :=
  ⟨fun z => wholeLineCauchyHeatBUCTotal z.1 u₀,
    wholeLineCauchyHomogeneousBUC_continuous hT u₀⟩

@[simp] theorem wholeLineCauchyHomogeneousTrajectory_apply
    {T : ℝ} (hT : 0 ≤ T) (u₀ : WholeLineBUC)
    (z : Set.Icc (0 : ℝ) T) :
    wholeLineCauchyHomogeneousTrajectory hT u₀ z =
      wholeLineCauchyHeatBUCTotal z.1 u₀ :=
  rfl

/-- The globally truncated mild map on continuous BUC trajectories. -/
def wholeLineCauchyBUCMildMap
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T) :
    WholeLineBUCTrajectory T :=
  ⟨fun z =>
      wholeLineCauchyHeatBUCTotal z.1 u₀ +
        (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U z.1 +
        wholeLineCauchyValueDuhamelBUC p hM hT U z.1,
    (wholeLineCauchyHomogeneousBUC_continuous hT u₀).add
      (continuous_const.smul
        (wholeLineCauchyGradientDuhamelBUC_continuous p hM hT U)) |>.add
      (wholeLineCauchyValueDuhamelBUC_continuous p hM hT U)⟩

@[simp] theorem wholeLineCauchyBUCMildMap_apply
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) :
    wholeLineCauchyBUCMildMap p hM hT u₀ U z =
      wholeLineCauchyHeatBUCTotal z.1 u₀ +
        (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U z.1 +
        wholeLineCauchyValueDuhamelBUC p hM hT U z.1 :=
  rfl

/-- Sup-distance contraction coefficient of the truncated mild map. -/
def wholeLineCauchyBUCMildRate
    (p : CMParams) (M T : ℝ) : ℝ :=
  |p.χ| *
      (((2 / Real.sqrt (4 * Real.pi)) * wholeLineCauchyFluxLip p M) *
        (2 * Real.sqrt T)) +
    (1 + reactionLip p.α M) * T

theorem wholeLineCauchyBUCMildRate_nonneg
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 ≤ wholeLineCauchyBUCMildRate p M T := by
  unfold wholeLineCauchyBUCMildRate
  have hflux := wholeLineCauchyFluxLip_nonneg p hM
  have hreact := reactionLip_nonneg p.hα hM
  positivity

theorem wholeLineCauchyBUCMildMap_apply_dist_le
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U W : WholeLineBUCTrajectory T)
    (z : Set.Icc (0 : ℝ) T) :
    dist (wholeLineCauchyBUCMildMap p hM hT u₀ U z)
        (wholeLineCauchyBUCMildMap p hM hT u₀ W z) ≤
      wholeLineCauchyBUCMildRate p M T * dist U W := by
  let H := wholeLineCauchyHeatBUCTotal z.1 u₀
  let GU := wholeLineCauchyGradientDuhamelBUC p hM hT U z.1
  let GW := wholeLineCauchyGradientDuhamelBUC p hM hT W z.1
  let VU := wholeLineCauchyValueDuhamelBUC p hM hT U z.1
  let VW := wholeLineCauchyValueDuhamelBUC p hM hT W z.1
  have hbase : 0 ≤
      (2 / Real.sqrt (4 * Real.pi)) * wholeLineCauchyFluxLip p M := by
    have := wholeLineCauchyFluxLip_nonneg p hM
    positivity
  have hgradT :
      dist GU GW ≤
        (((2 / Real.sqrt (4 * Real.pi)) * wholeLineCauchyFluxLip p M) *
          (2 * Real.sqrt T)) * dist U W := by
    have hsqrt : Real.sqrt z.1 ≤ Real.sqrt T :=
      Real.sqrt_le_sqrt z.2.2
    calc
      dist GU GW ≤
          ((2 / Real.sqrt (4 * Real.pi)) *
              (wholeLineCauchyFluxLip p M * dist U W)) *
            (2 * Real.sqrt z.1) :=
        wholeLineCauchyGradientDuhamelBUC_dist_le
          p hM hT U W z.2.1
      _ = (((2 / Real.sqrt (4 * Real.pi)) *
              wholeLineCauchyFluxLip p M) *
            (2 * Real.sqrt z.1)) * dist U W := by ring
      _ ≤ (((2 / Real.sqrt (4 * Real.pi)) *
              wholeLineCauchyFluxLip p M) *
            (2 * Real.sqrt T)) * dist U W := by
        apply mul_le_mul_of_nonneg_right _ dist_nonneg
        apply mul_le_mul_of_nonneg_left _ hbase
        exact mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  have hvalueT :
      dist VU VW ≤ ((1 + reactionLip p.α M) * T) * dist U W := by
    have hreact : 0 ≤ 1 + reactionLip p.α M := by
      linarith [reactionLip_nonneg p.hα hM]
    calc
      dist VU VW ≤
          ((1 + reactionLip p.α M) * dist U W) * z.1 :=
        wholeLineCauchyValueDuhamelBUC_dist_le
          p hM hT U W z.2.1
      _ = ((1 + reactionLip p.α M) * z.1) * dist U W := by ring
      _ ≤ ((1 + reactionLip p.α M) * T) * dist U W := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left z.2.2 hreact) dist_nonneg
  have hchem : dist ((-p.χ) • GU) ((-p.χ) • GW) ≤
      |p.χ| * ((((2 / Real.sqrt (4 * Real.pi)) *
        wholeLineCauchyFluxLip p M) * (2 * Real.sqrt T)) * dist U W) := by
    calc
      dist ((-p.χ) • GU) ((-p.χ) • GW) ≤
          ‖-p.χ‖ * dist GU GW := dist_smul_le _ _ _
      _ ≤ |p.χ| * ((((2 / Real.sqrt (4 * Real.pi)) *
          wholeLineCauchyFluxLip p M) * (2 * Real.sqrt T)) * dist U W) := by
        rw [Real.norm_eq_abs, abs_neg]
        exact mul_le_mul_of_nonneg_left hgradT (abs_nonneg _)
  change dist (H + (-p.χ) • GU + VU) (H + (-p.χ) • GW + VW) ≤ _
  calc
    dist (H + (-p.χ) • GU + VU) (H + (-p.χ) • GW + VW) ≤
        dist (H + (-p.χ) • GU) (H + (-p.χ) • GW) + dist VU VW :=
      dist_add_add_le _ _ _ _
    _ ≤ (dist H H + dist ((-p.χ) • GU) ((-p.χ) • GW)) + dist VU VW := by
      gcongr
      exact dist_add_add_le _ _ _ _
    _ ≤ |p.χ| * ((((2 / Real.sqrt (4 * Real.pi)) *
          wholeLineCauchyFluxLip p M) * (2 * Real.sqrt T)) * dist U W) +
        ((1 + reactionLip p.α M) * T) * dist U W := by
      rw [dist_self, zero_add]
      exact add_le_add hchem hvalueT
    _ = wholeLineCauchyBUCMildRate p M T * dist U W := by
      unfold wholeLineCauchyBUCMildRate
      ring

theorem wholeLineCauchyBUCMildMap_dist_le
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (U W : WholeLineBUCTrajectory T) :
    dist (wholeLineCauchyBUCMildMap p hM hT u₀ U)
        (wholeLineCauchyBUCMildMap p hM hT u₀ W) ≤
      wholeLineCauchyBUCMildRate p M T * dist U W := by
  refine (ContinuousMap.dist_le
    (mul_nonneg (wholeLineCauchyBUCMildRate_nonneg p hM hT) dist_nonneg)).2 ?_
  intro z
  exact wholeLineCauchyBUCMildMap_apply_dist_le p hM hT u₀ U W z

theorem wholeLineCauchyBUCMildMap_lipschitz
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) :
    LipschitzWith
      ⟨wholeLineCauchyBUCMildRate p M T,
        wholeLineCauchyBUCMildRate_nonneg p hM hT⟩
      (wholeLineCauchyBUCMildMap p hM hT u₀) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro U W
  exact wholeLineCauchyBUCMildMap_dist_le p hM hT u₀ U W

theorem wholeLineCauchyBUCMildMap_contracting
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    ContractingWith
      ⟨wholeLineCauchyBUCMildRate p M T,
        wholeLineCauchyBUCMildRate_nonneg p hM hT⟩
      (wholeLineCauchyBUCMildMap p hM hT u₀) :=
  ⟨by simpa using hsmall,
    wholeLineCauchyBUCMildMap_lipschitz p hM hT u₀⟩

theorem exists_pos_time_wholeLineCauchyBUCMildRate_lt_one
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    ∃ T : ℝ, 0 < T ∧ wholeLineCauchyBUCMildRate p M T < 1 := by
  have hcont : ContinuousAt
      (fun T : ℝ => wholeLineCauchyBUCMildRate p M T) 0 := by
    unfold wholeLineCauchyBUCMildRate
    fun_prop
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hclose⟩ := hcont 1 (by norm_num)
  let T : ℝ := δ / 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hdist : dist T 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hT]
    dsimp [T]
    linarith
  have hnear := hclose hdist
  have hzero : wholeLineCauchyBUCMildRate p M 0 = 0 := by
    simp [wholeLineCauchyBUCMildRate]
  rw [hzero, Real.dist_eq, sub_zero,
    abs_of_nonneg (wholeLineCauchyBUCMildRate_nonneg p hM hT.le)] at hnear
  exact ⟨T, hT, hnear⟩

/-- The Banach fixed point of the globally truncated mild map. -/
def wholeLineCauchyBUCMildFixedPoint
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    WholeLineBUCTrajectory T :=
  ContractingWith.fixedPoint
    (wholeLineCauchyBUCMildMap p hM hT u₀)
    (wholeLineCauchyBUCMildMap_contracting p hM hT u₀ hsmall)

theorem wholeLineCauchyBUCMildFixedPoint_isFixedPt
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    IsFixedPt (wholeLineCauchyBUCMildMap p hM hT u₀)
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) :=
  (wholeLineCauchyBUCMildMap_contracting
    p hM hT u₀ hsmall).fixedPoint_isFixedPt

theorem wholeLineCauchyBUCMildFixedPoint_eq_mildMap
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1) :
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall =
      wholeLineCauchyBUCMildMap p hM hT u₀
        (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall) :=
  (wholeLineCauchyBUCMildFixedPoint_isFixedPt
    p hM hT u₀ hsmall).symm

theorem wholeLineCauchyBUCMildFixedPoint_initial
    (p : CMParams) {M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC) (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩) :
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmall ⟨0, hzero⟩ = u₀ := by
  have hfix := congrArg
    (fun U : WholeLineBUCTrajectory T => U ⟨0, hzero⟩)
    (wholeLineCauchyBUCMildFixedPoint_eq_mildMap
      p hM hT u₀ hsmall)
  simpa [wholeLineCauchyBUCMildMap,
    wholeLineCauchyHeatBUCTotal,
    wholeLineCauchyGradientDuhamelBUC,
    wholeLineCauchyValueDuhamelBUC] using hfix

theorem exists_wholeLineCauchyBUCMildFixedPoint
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) (u₀ : WholeLineBUC) :
    ∃ (T : ℝ) (hT : 0 < T) (U : WholeLineBUCTrajectory T),
      IsFixedPt (wholeLineCauchyBUCMildMap p hM hT.le u₀) U := by
  obtain ⟨T, hT, hsmall⟩ :=
    exists_pos_time_wholeLineCauchyBUCMildRate_lt_one p hM
  refine ⟨T, hT, wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall, ?_⟩
  exact wholeLineCauchyBUCMildFixedPoint_isFixedPt p hM hT.le u₀ hsmall

section WholeLineCauchyBUCFixedPointAxiomAudit

#print axioms wholeLineCauchyBUCMildMap_contracting
#print axioms exists_pos_time_wholeLineCauchyBUCMildRate_lt_one
#print axioms wholeLineCauchyBUCMildFixedPoint_isFixedPt
#print axioms wholeLineCauchyBUCMildFixedPoint_initial
#print axioms exists_wholeLineCauchyBUCMildFixedPoint

end WholeLineCauchyBUCFixedPointAxiomAudit

end ShenWork.Paper1
