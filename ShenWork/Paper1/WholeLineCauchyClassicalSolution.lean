import ShenWork.Paper1.WholeLineCauchyTimeRegularity

open Filter Topology MeasureTheory Real Set
open scoped BoundedContinuousFunction Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# The canonical whole-line Cauchy fixed point is classical

This file packages the positive-time space and time regularity of the
canonical BUC mild fixed point together with the frozen elliptic resolver.
The result is the semantic `IsClassicalSolution` interface used by the
continuation and traveling-wave arguments.
-/

/-- Norm continuity of a BUC trajectory gives the uniform initial trace
required by the Paper 1 Cauchy-solution interface. -/
theorem wholeLineBUCTrajectoryExtend_hasUniformInitialTrace
    {T : ℝ} (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (u₀ : WholeLineBUC)
    (hinit : U ⟨0, le_rfl, hT⟩ = u₀) :
    HasUniformInitialTrace
      (fun t x => (wholeLineBUCTrajectoryExtend hT U t).1 x) u₀.1 := by
  intro ε hε
  have hcont : ContinuousAt (wholeLineBUCTrajectoryExtend hT U) 0 :=
    (wholeLineBUCTrajectoryExtend_continuous hT U).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  rcases hcont ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro t x ht htδ
  have hdist : dist t 0 < δ := by
    simpa [Real.dist_eq, abs_of_nonneg ht] using htδ
  have hclose' := hclose hdist
  have hext0 : wholeLineBUCTrajectoryExtend hT U 0 = U ⟨0, le_rfl, hT⟩ :=
    wholeLineBUCTrajectoryExtend_eq hT U ⟨le_rfl, hT⟩
  rw [hext0, hinit] at hclose'
  exact (WholeLineBUC.pointwise_abs_sub_le_dist
    (wholeLineBUCTrajectoryExtend hT U t) u₀ x).trans_lt hclose'

/-- On every physical construction strip, the canonical population and its
frozen elliptic resolver form a classical solution of the original system. -/
theorem wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
    (p : CMParams) {M T theta eta : ℝ}
    (hM : 0 ≤ M) (hT : 0 < T)
    (u₀ : WholeLineBUC)
    (hsmall : wholeLineCauchyBUCMildRate p M T < 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hrel : eta * (1 + theta) < theta)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall z).1 y ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
    let u : ℝ → ℝ → ℝ := fun t x =>
      (wholeLineBUCTrajectoryExtend hT.le U t).1 x
    let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
    IsClassicalSolution p T u v := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT.le u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun t x =>
    (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
  refine
    { hT := hT
      u_smooth := ?_
      v_smooth := ?_
      pde_u := ?_
      pde_v := ?_ }
  · intro t x ht htT
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U zt :=
      wholeLineBUCTrajectoryExtend_eq hT.le U zt.2
    constructor
    · simpa [u, U] using
        (wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
          p hM hT.le u₀ hsmall ht htT htheta0 htheta1
            heta0 heta1 hrel hstrip x).differentiableAt
    · have hspace :=
        (wholeLineCauchyBUCMildFixedPoint_spatial_hasDerivAt_positive
          p hM hT.le u₀ hsmall zt ht x).differentiableAt
      change DifferentiableAt ℝ
        (fun y : ℝ => (wholeLineBUCTrajectoryExtend hT.le U t).1 y) x
      rw [hext]
      exact hspace
  · intro t x ht htT
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U zt :=
      wholeLineBUCTrajectoryExtend_eq hT.le U zt.2
    have huC : IsCUnifBdd (u t) := by
      simpa [u, hext] using WholeLineBUC.isCUnifBdd (U zt)
    have hu0 : ∀ y, 0 ≤ u t y := by
      intro y
      simpa [u, hext] using (hstrip zt y).1
    exact frozenElliptic_differentiable p huC hu0 x
  · intro t x ht htT
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U zt :=
      wholeLineBUCTrajectoryExtend_eq hT.le U zt.2
    have hpde :=
      (wholeLineCauchyBUCMildFixedPoint_physical_pde_hasDerivAt
        p hM hT.le u₀ hsmall ht htT htheta0 htheta1
          heta0 heta1 hrel hstrip x).deriv
    simpa [u, v, U, hext, wholeLineChemotaxisFlux,
      wholeLineLogisticSource, reactionFun, iteratedDeriv_succ,
      iteratedDeriv_zero] using hpde
  · intro t x ht htT
    let zt : Set.Icc (0 : ℝ) T := ⟨t, ht.le, htT.le⟩
    have hext : wholeLineBUCTrajectoryExtend hT.le U t = U zt :=
      wholeLineBUCTrajectoryExtend_eq hT.le U zt.2
    have huC : IsCUnifBdd (u t) := by
      simpa [u, hext] using WholeLineBUC.isCUnifBdd (U zt)
    have hu0 : ∀ y, 0 ≤ u t y := by
      intro y
      simpa [u, hext] using (hstrip zt y).1
    exact frozenElliptic_ode p huC hu0 x

/-- Every nonnegative whole-line BUC datum generates a genuine classical
solution on a positive time interval, with the prescribed uniform trace. -/
theorem exists_wholeLineCauchy_classicalSolution
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x : ℝ, 0 ≤ u₀.1 x) :
    ∃ (T : ℝ) (u v : ℝ → ℝ → ℝ),
      0 < T ∧ IsClassicalSolution p T u v ∧
        HasInitialDatum u u₀.1 ∧ HasUniformInitialTrace u u₀.1 := by
  let M : ℝ := ‖u₀‖ + 1
  rcases exists_wholeLineCauchyBUCMildFixedPoint_in_physical_strip p u₀ hu₀ with
    ⟨T, hT, hsmall, hstripIco⟩
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p (by dsimp [M]; positivity) hT.le
      u₀ hsmall
  let u : ℝ → ℝ → ℝ := fun t x =>
    (wholeLineBUCTrajectoryExtend hT.le U t).1 x
  let v : ℝ → ℝ → ℝ := fun t => frozenElliptic p (u t)
  have hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ y,
      (wholeLineCauchyBUCMildFixedPoint p (by dsimp [M]; positivity) hT.le
        u₀ hsmall z).1 y ∈ Set.Icc (0 : ℝ) M := by
    intro z y
    exact ⟨(hstripIco z y).1, (hstripIco z y).2.le⟩
  have hclass : IsClassicalSolution p T u v := by
    simpa [U, u, v] using
      (wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
        p (M := M) (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
        (by dsimp [M]; positivity) hT u₀ hsmall
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hstrip)
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hinitU : U ⟨0, hzero⟩ = u₀ := by
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
      p (M := M) (T := T) (by dsimp [M]; positivity) hT.le u₀ hsmall hzero
  have hdatum : HasInitialDatum u u₀.1 := by
    intro x
    have hext0 : wholeLineBUCTrajectoryExtend hT.le U 0 = U ⟨0, hzero⟩ :=
      wholeLineBUCTrajectoryExtend_eq hT.le U hzero
    simp [u, hext0, hinitU]
  have htrace : HasUniformInitialTrace u u₀.1 := by
    simpa [u] using wholeLineBUCTrajectoryExtend_hasUniformInitialTrace
      hT.le U u₀ hinitU
  exact ⟨T, u, v, hT, hclass, hdatum, htrace⟩

section WholeLineCauchyClassicalSolutionAxiomAudit

#print axioms wholeLineCauchyBUCMildFixedPoint_isClassicalSolution
#print axioms wholeLineBUCTrajectoryExtend_hasUniformInitialTrace
#print axioms exists_wholeLineCauchy_classicalSolution

end WholeLineCauchyClassicalSolutionAxiomAudit

end ShenWork.Paper1
