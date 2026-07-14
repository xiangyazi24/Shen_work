import ShenWork.Paper1.WholeLineCauchyClassicalSolution

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Uniform whole-line Cauchy restart window

The contraction time and displacement estimate depend on a fixed clamp
ceiling, not on the individual datum.  Consequently every nonnegative datum
whose BUC norm stays a fixed positive distance below that ceiling has a
classical solution on one common positive time interval.  This is the local
lifespan atom needed by a non-vacuous continuation construction.
-/

/-- A fixed ceiling `M` and norm margin `eta` give one classical lifespan for
all nonnegative BUC data satisfying `‖u₀‖ + eta ≤ M`. -/
theorem exists_uniform_wholeLineCauchy_classicalRestart
    (p : CMParams) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 < eta) :
    ∃ T > 0, ∀ u₀ : WholeLineBUC,
      (∀ x : ℝ, 0 ≤ u₀.1 x) → ‖u₀‖ + eta ≤ M →
        ∃ u v : ℝ → ℝ → ℝ,
          IsClassicalSolution p T u v ∧
            HasInitialDatum u u₀.1 ∧ HasUniformInitialTrace u u₀.1 ∧
            ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
              u t x ∈ Set.Icc (0 : ℝ) M := by
  obtain ⟨T, hT, hsmall, hdisp⟩ :=
    exists_pos_time_wholeLineCauchyBUCRate_and_displacement p hM heta
  refine ⟨T, hT, ?_⟩
  intro u₀ hu₀ hmargin
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun t x =>
    (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
  have hupper : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ, (U z).1 x ≤ M := by
    intro z x
    let H : WholeLineBUC := wholeLineCauchyHeatBUCTotal z.1 u₀
    have hUH : dist (U z) H ≤ wholeLineCauchyBUCMildDisplacement p M T :=
      wholeLineCauchyBUCMildFixedPoint_dist_homogeneous_le
        p hM hT.le u₀ hsmall z
    have hpoint : |(U z).1 x - H.1 x| ≤
        wholeLineCauchyBUCMildDisplacement p M T :=
      (WholeLineBUC.pointwise_abs_sub_le_dist (U z) H x).trans hUH
    have hHnorm : ‖H‖ ≤ ‖u₀‖ :=
      wholeLineCauchyHeatBUCTotal_norm_le_of_nonneg z.2.1 u₀
    exact (show (U z).1 x < M from by
      calc
        (U z).1 x ≤ H.1 x + |(U z).1 x - H.1 x| := by
          linarith [le_abs_self ((U z).1 x - H.1 x)]
        _ ≤ ‖H‖ + wholeLineCauchyBUCMildDisplacement p M T :=
          add_le_add (WholeLineBUC.apply_le_norm H x) hpoint
        _ ≤ ‖u₀‖ + wholeLineCauchyBUCMildDisplacement p M T :=
          add_le_add hHnorm le_rfl
        _ < ‖u₀‖ + eta := by linarith
        _ ≤ M := hmargin).le
  have hnonneg : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ, 0 ≤ (U z).1 x := by
    intro z x
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_nonnegative
      p hM hT u₀ hu₀ hsmall z x
  have hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 x ∈
        Set.Icc (0 : ℝ) M := by
    intro z x
    exact ⟨by simpa [U] using hnonneg z x, by simpa [U] using hupper z x⟩
  have hclass : IsClassicalSolution p T u v := by
    simpa [U, u, v] using
      (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
        p (M := M) (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        hM hT u₀ hsmall
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip)
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hinitU : U ⟨0, hzero⟩ = u₀ := by
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
      p hM hT.le u₀ hsmall hzero
  have hdatum : HasInitialDatum u u₀.1 := by
    intro x
    have hext0 : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hzero
    simp [u, hext0, hinitU]
  have htrace : HasUniformInitialTrace u u₀.1 := by
    simpa [u] using wholeLineBUCTrajectoryExtend_hasUniformInitialTrace
      hT.le U u₀ hinitU
  have hclosedStrip : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
      u t x ∈ Set.Icc (0 : ℝ) M := by
    intro t ht x
    let z : Set.Icc (0 : ℝ) T := ⟨t, ht⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U z :=
      wholeLineBUCTrajectoryExtend_eq hT.le U ht
    exact ⟨by simpa [u, hext] using hnonneg z x,
      by simpa [u, hext] using hupper z x⟩
  exact ⟨u, v, hclass, hdatum, htrace, hclosedStrip⟩

section WholeLineCauchyUniformRestartAxiomAudit

#print axioms exists_uniform_wholeLineCauchy_classicalRestart

end WholeLineCauchyUniformRestartAxiomAudit

end ShenWork.Paper1
