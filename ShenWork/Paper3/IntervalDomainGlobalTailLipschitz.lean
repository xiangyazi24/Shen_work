import ShenWork.Paper3.IntervalDomainExplicitPositiveTimeC1
import ShenWork.Paper3.IntervalDomainClassicalRestartPointwise

/-!
# Uniform tail Lipschitz regularity of bounded interval orbits

This file extracts the concrete compactness input needed by the negative-
sensitivity global-attractor argument.  A bounded global classical orbit is
restarted on a fixed unit window.  The physical restart identity turns that
window into the existing conjugate mild-solution package, and the explicit
positive-time smoothing estimate then gives a spatial derivative bound whose
constant is independent of the absolute restart time.

No `CompactnessData` field is used.
-/

namespace ShenWork.Paper3

open Filter Set Topology MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalConjugatePicard

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

private theorem abs_le_supNorm_of_bddAbove
    {f : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (Set.range (fun x : intervalDomainPoint ↦ |f x|)))
    (x : intervalDomainPoint) :
    |f x| ≤ intervalDomain.supNorm f := by
  change |f x| ≤ intervalDomainSupNorm f
  unfold intervalDomainSupNorm
  exact le_csSup hbdd ⟨x, rfl⟩

/-- A fixed physical restart window of a tail-bounded global orbit is a
conjugate mild solution with the same uniform ceiling. -/
def intervalDomain_tailRestartMildData
    (p : CM2Params) (hm : p.m = 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain p u v)
    {a h M : ℝ} (ha : 0 < a) (hh : 0 < h) (hM : 0 < M)
    (hub : ∀ t, a ≤ t → intervalDomain.supNorm (u t) ≤ M) :
    ConjugateMildSolutionData p (u a) := by
  let H : ℝ := a + h + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hahH : a + h < H := by dsimp [H]; linarith
  have hsol := hglobal H hH
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  let w := intervalDomainRestartTrajectory a h u
  refine
    { T := h
      hT := hh
      M := M
      hM := hM
      u := w
      hmild := ?_
      hbound := ?_
      hnonneg := ?_
      hpos := ?_
      hcont := ?_
      hmeas := ?_ }
  · intro r hr0 hrh x
    have hpoint := intervalDomain_classical_bform_restart_pointwise
      hsol hm ha hh.le hahH hr0 hrh x
    have hrmem : r ∈ Set.Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun
        (intervalDomainRestartTrajectory_eq
          (a := a) (h := h) (u := u) hrmem) x
    rw [hw]
    exact hpoint
  · intro r hr0 hrh x
    have hrmem : r ∈ Set.Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have ht : a + r ∈ Set.Ioo (0 : ℝ) H := by
      constructor
      · linarith
      · exact lt_of_le_of_lt (by linarith) hahH
    have hbdd : BddAbove
        (Set.range (fun y : intervalDomainPoint ↦ |u (a + r) y|)) :=
      ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove hsolM ht
    have hpoint := abs_le_supNorm_of_bddAbove hbdd x
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun
        (intervalDomainRestartTrajectory_eq
          (a := a) (h := h) (u := u) hrmem) x
    rw [hw]
    exact hpoint.trans (hub (a + r) (by linarith))
  · intro r hr0 hrh x
    have hrmem : r ∈ Set.Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun
        (intervalDomainRestartTrajectory_eq
          (a := a) (h := h) (u := u) hrmem) x
    rw [hw]
    exact (hsol.u_pos' (by linarith) (lt_of_le_of_lt (by linarith) hahH)).le
  · intro r hr0 hrh x
    have hrmem : r ∈ Set.Icc (0 : ℝ) h := ⟨hr0.le, hrh⟩
    have hw : w r x = u (a + r) x := by
      simpa [w] using congrFun
        (intervalDomainRestartTrajectory_eq
          (a := a) (h := h) (u := u) hrmem) x
    rw [hw]
    exact hsol.u_pos' (by linarith) (lt_of_le_of_lt (by linarith) hahH)
  · simpa [w] using
      intervalDomainRestartTrajectory_hasContinuousSlices
        hsolM ha hh.le hahH
  · simpa [w] using
      intervalDomainRestartTrajectory_hasJointMeasurability
        hsolM ha hh.le hahH

/-- A bounded global orbit has a uniform spatial derivative bound after a
positive delay.  The bound is the explicit unit-window smoothing constant. -/
theorem intervalDomain_globalBounded_eventual_deriv_bound
    (p : CM2Params) (hm : p.m = 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ T M G : ℝ, 0 < T ∧ 0 < M ∧ 0 ≤ G ∧
      ∀ t, T ≤ t → ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        |deriv (intervalDomainLift (u t)) x| ≤ G := by
  rcases huv.bounded with ⟨M₀, hM₀⟩
  rcases eventually_atTop.1 hM₀ with ⟨T₀, hT₀⟩
  let M : ℝ := max M₀ 1
  let G : ℝ := paper3MildDerivPositiveTimeConstant p M 1 1
  let T : ℝ := max (T₀ + 1) 2
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hG : 0 ≤ G := by
    dsimp [G]
    exact paper3MildDerivPositiveTimeConstant_nonneg
      p hM.le (by norm_num) (by norm_num)
  have hT : 0 < T := by
    dsimp [T]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨T, M, G, hT, hM, hG, ?_⟩
  intro t ht x hx
  let a : ℝ := t - 1
  have ha : 0 < a := by
    dsimp [a, T] at *
    linarith [le_max_right (T₀ + 1) (2 : ℝ)]
  have hT₀a : T₀ ≤ a := by
    dsimp [a, T] at *
    linarith [le_max_left (T₀ + 1) (2 : ℝ)]
  have hub : ∀ s, a ≤ s → intervalDomain.supNorm (u s) ≤ M := by
    intro s has
    exact (hT₀ s (le_trans hT₀a has)).trans (le_max_left _ _)
  let D := intervalDomain_tailRestartMildData
    p hm huv.classical ha (show (0 : ℝ) < 1 by norm_num) hM hub
  have huaBound : ∀ y, |intervalDomainLift (u a) y| ≤ D.M := by
    intro y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · have Hpos : 0 < a + 2 := by linarith
      have hsol := huv.classical (a + 2) Hpos
      have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
        p hm hsol
      have hbdd : BddAbove
          (Set.range (fun z : intervalDomainPoint ↦ |u a z|)) :=
        ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove
          hsolM ⟨ha, by linarith⟩
      have hpoint := abs_le_supNorm_of_bddAbove
        hbdd ⟨y, hy⟩
      simpa [D, intervalDomain_tailRestartMildData, intervalDomainLift, hy]
        using hpoint.trans (hub a le_rfl)
    · simp [intervalDomainLift, hy, D, intervalDomain_tailRestartMildData,
        hM.le]
  have huaMeas : AEStronglyMeasurable
      (intervalDomainLift (u a)) (intervalMeasure 1) := by
    have Hpos : 0 < a + 2 := by linarith
    have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
      p hm (huv.classical (a + 2) Hpos)
    exact
      (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
        (ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous
          hsolM ⟨ha, by linarith⟩)).aestronglyMeasurable
  have hder := conjugateMild_intervalDomainLift_deriv_positiveTime_explicit
    D huaBound huaMeas (tau := (1 : ℝ)) (by norm_num)
      1 le_rfl le_rfl x hx
  have hslice : D.u 1 = u t := by
    have hr : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    rw [show D.u = intervalDomainRestartTrajectory a 1 u by rfl,
      intervalDomainRestartTrajectory_eq hr]
    dsimp [a]
    congr 1
    ring
  simpa [G, hslice] using hder

/-- Tail slices of a bounded global orbit share one spatial Lipschitz
constant on the closed unit interval. -/
theorem intervalDomain_globalBounded_eventual_lipschitz
    (p : CM2Params) (hm : p.m = 1)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (huv : PositiveGlobalBoundedSolution intervalDomain p u v) :
    ∃ T G : ℝ, 0 ≤ G ∧ ∀ t, T ≤ t →
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |intervalDomainLift (u t) x - intervalDomainLift (u t) y| ≤
          G * |x - y| := by
  rcases intervalDomain_globalBounded_eventual_deriv_bound p hm huv with
    ⟨T, _M, G, hT, _hM, hG, hder⟩
  refine ⟨T, G, hG, ?_⟩
  intro t ht x hx y hy
  let f : ℝ → ℝ := intervalDomainLift (u t)
  have htpos : 0 < t := lt_of_lt_of_le hT ht
  have Hpos : 0 < t + 1 := by linarith
  have hsol := huv.classical (t + 1) Hpos
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    dsimp [f]
    exact ((hsol.regularity.2.2.2.2.1 t ⟨htpos, by linarith⟩).1.1).continuousOn
  have hdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ f z := by
    intro z hz
    exact ((hsol.regularity.2.2.2.2.1 t ⟨htpos, by linarith⟩).1.1
      |>.differentiableOn (by norm_num)
      |>.mono Set.Ioo_subset_Icc_self)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hlipOpen : LipschitzOnWith ⟨G, hG⟩ f (Set.Ioo (0 : ℝ) 1) :=
    Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Ioo (0 : ℝ) 1)
      (fun z hz ↦ (hdiff z hz).hasDerivAt.hasDerivWithinAt)
      (fun z hz ↦ by
        simpa [NNReal.coe_mk, Real.nnnorm_of_nonneg]
          using hder t ht z hz)
  have hlipClosed : LipschitzOnWith ⟨G, hG⟩ f (Set.Icc (0 : ℝ) 1) := by
    rw [← closure_Ioo (zero_ne_one' ℝ)]
    exact hlipOpen.closure (by rwa [closure_Ioo (zero_ne_one' ℝ)])
  have hdist := hlipClosed.dist_le_mul x hx y hy
  simpa [f, Real.dist_eq, NNReal.coe_mk] using hdist

#print axioms intervalDomain_tailRestartMildData
#print axioms intervalDomain_globalBounded_eventual_deriv_bound
#print axioms intervalDomain_globalBounded_eventual_lipschitz

end

end ShenWork.Paper3
