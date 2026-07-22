import ShenWork.Paper1.WholeLinePhysicalMildUniqueness

/-!
# Finite physical mild segments on the whole line

This file packages the finite objects used in the maximal-continuation
construction.  The package deliberately remembers the `BUC` trajectory and
the original (unclamped) mild equation.  Compactness of the time interval
then supplies a common physical clamp whenever the truncated fixed-point
interface is needed.
-/

open Filter MeasureTheory Real Set Topology Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-- The original mild map at time `t` only uses trajectory values in
`[0,t]`. -/
theorem wholeLineCauchyMildMap_congr_on_Icc_segments
    (p : CMParams) (u₀ : ℝ → ℝ) {U W : ℝ → ℝ → ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hUW : ∀ s ∈ Set.Icc (0 : ℝ) t, U s = W s) (x : ℝ) :
    wholeLineCauchyMildMap p u₀ U t x =
      wholeLineCauchyMildMap p u₀ W t x := by
  by_cases ht0 : t = 0
  · subst t
    simp [wholeLineCauchyMildMap]
  · have hchem : wholeLineCauchyChemDuhamel p U t x =
        wholeLineCauchyChemDuhamel p W t x := by
      unfold wholeLineCauchyChemDuhamel wholeLineCauchyGradientDuhamel
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      change wholeLineCauchyHeatGradOp (t - s)
          (wholeLineChemotaxisFlux p (U s)) x =
        wholeLineCauchyHeatGradOp (t - s)
          (wholeLineChemotaxisFlux p (W s)) x
      rw [hUW s hs]
    have hreaction : wholeLineCauchyReactionDuhamel p U t x =
        wholeLineCauchyReactionDuhamel p W t x := by
      unfold wholeLineCauchyReactionDuhamel wholeLineCauchyValueDuhamel
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [hUW s hs]
    simp only [wholeLineCauchyMildMap, if_neg ht0, hchem, hreaction]

/-- A positive finite `BUC` trajectory which is nonnegative and solves the
original whole-line mild equation. -/
structure WholeLinePhysicalMildSegment
    (p : CMParams) (u₀ : WholeLineBUC) (T : ℝ) where
  T_pos : 0 < T
  traj : WholeLineBUCTrajectory T
  nonnegative : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ, 0 ≤ (traj z).1 x
  mild : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
    (traj z).1 x = wholeLineCauchyMildMap p u₀.1
      (fun t y => (wholeLineBUCTrajectoryExtend T_pos.le traj t).1 y)
      z.1 x

namespace WholeLinePhysicalMildSegment

/-- Ambient constant-endpoint extension of a finite segment. -/
def extend {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) : ℝ → WholeLineBUC :=
  wholeLineBUCTrajectoryExtend d.T_pos.le d.traj

/-- The scalar population carried by a finite segment. -/
def population {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) : ℝ → ℝ → ℝ :=
  fun t x => (d.extend t).1 x

theorem initial
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) :
    d.traj ⟨0, le_rfl, d.T_pos.le⟩ = u₀ := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  have h := d.mild ⟨0, le_rfl, d.T_pos.le⟩ x
  simpa [wholeLineCauchyMildMap] using h

theorem extend_zero
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) : d.extend 0 = u₀ := by
  rw [extend, wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj
    ⟨le_rfl, d.T_pos.le⟩]
  exact d.initial

theorem hasInitialDatum
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) :
    HasInitialDatum d.population u₀.1 := by
  intro x
  exact congrArg (fun w : WholeLineBUC => w.1 x) d.extend_zero

theorem hasUniformInitialTrace
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) :
    HasUniformInitialTrace d.population u₀.1 := by
  simpa [population, extend] using
    wholeLineBUCTrajectoryExtend_hasUniformInitialTrace
      d.T_pos.le d.traj u₀ d.initial

/-- Every finite segment is contained in one nonnegative physical strip. -/
theorem exists_physical_clamp
    {p : CMParams} {u₀ : WholeLineBUC} {T : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      (d.traj z).1 x ∈ Set.Icc (0 : ℝ) M := by
  have hnormCont : Continuous (fun z : Set.Icc (0 : ℝ) T => ‖d.traj z‖) :=
    d.traj.continuous.norm
  obtain ⟨B, hB⟩ :=
    isCompact_univ.bddAbove_image hnormCont.continuousOn
  let M : ℝ := max B 0
  refine ⟨M, le_max_right _ _, ?_⟩
  intro z x
  have hzB : ‖d.traj z‖ ≤ B :=
    hB (Set.mem_image_of_mem (fun q => ‖d.traj q‖) (Set.mem_univ z))
  exact ⟨d.nonnegative z x,
    (WholeLineBUC.apply_le_norm (d.traj z) x).trans
      (hzB.trans (le_max_left _ _))⟩

/-- With any physical clamp containing it, a segment is a fixed point of the
corresponding truncated BUC map. -/
theorem isFixedPt
    {p : CMParams} {u₀ : WholeLineBUC} {T M : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T) (hM : 0 ≤ M)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      (d.traj z).1 x ∈ Set.Icc (0 : ℝ) M) :
    IsFixedPt (wholeLineCauchyBUCMildMap p hM d.T_pos.le u₀) d.traj :=
  wholeLinePhysicalOriginalMild_isFixedPt
    p hM d.T_pos.le u₀ d.traj hstrip d.mild

/-- Restriction to a shorter positive initial interval. -/
def restrict
    {p : CMParams} {u₀ : WholeLineBUC} {T h : ℝ}
    (d : WholeLinePhysicalMildSegment p u₀ T)
    (hh : 0 < h) (hhT : h ≤ T) :
    WholeLinePhysicalMildSegment p u₀ h where
  T_pos := hh
  traj := wholeLineBUCTrajectoryShift le_rfl hh.le (by simpa using hhT) d.traj
  nonnegative := by
    intro z x
    simpa [wholeLineBUCTrajectoryShift] using
      d.nonnegative ⟨z.1, z.2.1, z.2.2.trans hhT⟩ x
  mild := by
    intro z x
    let zT : Set.Icc (0 : ℝ) T := ⟨z.1, z.2.1, z.2.2.trans hhT⟩
    have hraw := d.mild zT x
    have hagree : ∀ s ∈ Set.Icc (0 : ℝ) z.1,
        (fun q y => (wholeLineBUCTrajectoryExtend d.T_pos.le d.traj q).1 y) s =
          (fun q y =>
            (wholeLineBUCTrajectoryExtend hh.le
              (wholeLineBUCTrajectoryShift le_rfl hh.le
                (by simpa using hhT) d.traj) q).1 y) s := by
      intro s hs
      funext y
      have hsT : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨hs.1, (hs.2.trans z.2.2).trans hhT⟩
      have hsh : s ∈ Set.Icc (0 : ℝ) h :=
        ⟨hs.1, hs.2.trans z.2.2⟩
      change
        (wholeLineBUCTrajectoryExtend d.T_pos.le d.traj s).1 y =
          (wholeLineBUCTrajectoryExtend hh.le
            (wholeLineBUCTrajectoryShift le_rfl hh.le
              (by simpa using hhT) d.traj) s).1 y
      rw [wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj hsT,
        wholeLineBUCTrajectoryExtend_eq hh.le _ hsh]
      simp [wholeLineBUCTrajectoryShift]
    have hcongr := wholeLineCauchyMildMap_congr_on_Icc_segments
      p u₀.1 z.2.1 hagree x
    simpa [wholeLineBUCTrajectoryShift, zT] using hraw.trans hcongr

/-- Two finite physical mild segments with the same datum agree on every
positive common initial horizon. -/
theorem restrict_eq
    {p : CMParams} {u₀ : WholeLineBUC} {T₁ T₂ h : ℝ}
    (d₁ : WholeLinePhysicalMildSegment p u₀ T₁)
    (d₂ : WholeLinePhysicalMildSegment p u₀ T₂)
    (hh : 0 < h) (hhT₁ : h ≤ T₁) (hhT₂ : h ≤ T₂) :
    (d₁.restrict hh hhT₁).traj = (d₂.restrict hh hhT₂).traj := by
  obtain ⟨M₁, hM₁, hstrip₁⟩ := d₁.exists_physical_clamp
  obtain ⟨M₂, hM₂, hstrip₂⟩ := d₂.exists_physical_clamp
  let M : ℝ := max M₁ M₂
  have hM : 0 ≤ M := hM₁.trans (le_max_left _ _)
  apply wholeLinePhysicalOriginalMild_unique
    p hM hh.le u₀ (d₁.restrict hh hhT₁).traj
      (d₂.restrict hh hhT₂).traj
  · intro z x
    constructor
    · exact (d₁.restrict hh hhT₁).nonnegative z x
    · have hslice : (d₁.restrict hh hhT₁).traj z =
          d₁.traj ⟨z.1, z.2.1, z.2.2.trans hhT₁⟩ := by
        simp [restrict, wholeLineBUCTrajectoryShift]
      rw [hslice]
      exact (hstrip₁ ⟨z.1, z.2.1, z.2.2.trans hhT₁⟩ x).2.trans
        (by dsimp [M]; exact le_max_left _ _)
  · intro z x
    constructor
    · exact (d₂.restrict hh hhT₂).nonnegative z x
    · have hslice : (d₂.restrict hh hhT₂).traj z =
          d₂.traj ⟨z.1, z.2.1, z.2.2.trans hhT₂⟩ := by
        simp [restrict, wholeLineBUCTrajectoryShift]
      rw [hslice]
      exact (hstrip₂ ⟨z.1, z.2.1, z.2.2.trans hhT₂⟩ x).2.trans
        (by dsimp [M]; exact le_max_right _ _)
  · exact (d₁.restrict hh hhT₁).mild
  · exact (d₂.restrict hh hhT₂).mild

theorem eq_on_common_Icc
    {p : CMParams} {u₀ : WholeLineBUC} {T₁ T₂ h : ℝ}
    (d₁ : WholeLinePhysicalMildSegment p u₀ T₁)
    (d₂ : WholeLinePhysicalMildSegment p u₀ T₂)
    (hh : 0 < h) (hhT₁ : h ≤ T₁) (hhT₂ : h ≤ T₂)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) h) :
    d₁.traj ⟨t, ht.1, ht.2.trans hhT₁⟩ =
      d₂.traj ⟨t, ht.1, ht.2.trans hhT₂⟩ := by
  have happ := congrArg
    (fun Q : WholeLineBUCTrajectory h => Q ⟨t, ht⟩)
    (d₁.restrict_eq d₂ hh hhT₁ hhT₂)
  simpa [restrict, wholeLineBUCTrajectoryShift] using happ

end WholeLinePhysicalMildSegment

/-- The canonical short-time solution gives a finite physical mild segment. -/
theorem exists_wholeLinePhysicalMildSegment
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    ∃ T : ℝ, Nonempty (WholeLinePhysicalMildSegment p u₀ T) := by
  obtain ⟨T, hT, hsmall, hstrip, hmild⟩ :=
    exists_wholeLineCauchy_original_BUC_mildSolution p u₀ hu₀
  let M : ℝ := ‖u₀‖ + 1
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p (by positivity) hT.le u₀ hsmall
  refine ⟨T, ⟨?_⟩⟩
  refine { T_pos := hT, traj := U, nonnegative := ?_, mild := ?_ }
  · intro z x
    exact (hstrip z x).1
  · simpa [U] using hmild

section AxiomAudit

#print axioms WholeLinePhysicalMildSegment.exists_physical_clamp
#print axioms WholeLinePhysicalMildSegment.restrict_eq
#print axioms exists_wholeLinePhysicalMildSegment

end AxiomAudit

end ShenWork.Paper1
