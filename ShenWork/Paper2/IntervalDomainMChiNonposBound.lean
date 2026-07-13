import ShenWork.Paper2.IntervalDomainGlobalWellposed
import ShenWork.Paper2.IntervalDomainMCriticalLpSeed

/-!
# Nonpositive-sensitivity bounds for the faithful critical interval equation

This file extends the interval maximum-principle exit to the missing amended
parameter slice `a = 0`, `b ≥ 0`.  At a spatial maximum the reaction is then
nonpositive, so the same Dini argument as the zero-reaction branch applies.
Together with the existing `a,b > 0` branch this gives one horizon-independent
supremum bound under the corrected guard `a = 0 ∨ 0 < b`.
-/

open Filter Set
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMChiNonposBound

open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainGlobalWellposed
open ShenWork.Paper2.Lemma31Closure

/-- The maximum-principle branch with zero linear growth and arbitrary
nonnegative damping.  This is the missing `a = 0`, `b > 0` companion to
`lemma31_zero`. -/
theorem lemma31_zero_growth_intervalDomainM
    {p : CM2Params} (hchi : p.χ₀ ≤ 0) (ha : p.a = 0) (hm : p.m = 1)
    {T : ℝ} (_hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsolM : IsPaper2ClassicalSolution intervalDomainM p T u v) :
    SupNormNonincreasingOn intervalDomainM u (Ioo (0 : ℝ) T) := by
  have hsol : IsPaper2ClassicalSolution intervalDomain p T u v :=
    classicalSolution_intervalDomain_of_m_eq_one hm hsolM
  have hlegacy : SupNormNonincreasingOn intervalDomain u (Ioo (0 : ℝ) T) := by
    refine supNorm_nonincr_core hsol ?_
    intro s hs xs hxs hargmax
    have hmax : ∀ y, u s y ≤ u s ⟨xs, hxs⟩ := by
      intro y
      have hcontU : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1) := by
        obtain ⟨_, _, _, _, hClosed, _, _⟩ := hsol.regularity
        exact (hClosed s hs).1.1.continuousOn
      have hbdd : BddAbove (intervalDomainLift (u s) '' Icc (0 : ℝ) 1) :=
        (isCompact_Icc.image_of_continuousOn hcontU).bddAbove
      have huy : u s y = intervalDomainLift (u s) y.1 := by
        rw [intervalDomainLift,
          dif_pos (show (y.1 : ℝ) ∈ Icc (0 : ℝ) 1 from y.2), Subtype.coe_eta]
      have huq : u s ⟨xs, hxs⟩ = intervalDomainLift (u s) xs := by
        rw [intervalDomainLift, dif_pos hxs]
      rw [huy, huq, hargmax]
      exact le_csSup hbdd (Set.mem_image_of_mem _ y.2)
    have hsl := max_point_slope_bound hchi hsol hs.1 hs.2 hmax
    have htd : intervalDomain.timeDeriv u s ⟨xs, hxs⟩ =
        deriv (fun r => intervalDomainLift (u r) xs) s := by
      show deriv (fun r => u r ⟨xs, hxs⟩) s =
        deriv (fun r => intervalDomainLift (u r) xs) s
      congr 1
      funext r
      rw [intervalDomainLift, dif_pos hxs]
    rw [htd, ha] at hsl
    have hu : 0 ≤ intervalDomainLift (u s) xs := by
      rw [intervalDomainLift, dif_pos hxs]
      exact (hsol.u_pos' hs.1 hs.2).le
    have hdamp : 0 ≤ p.b * intervalDomainLift (u s) xs ^ p.α :=
      mul_nonneg p.hb (Real.rpow_nonneg hu _)
    nlinarith
  simpa [intervalDomainM, intervalDomain] using hlegacy

/-- Monotonicity on `(0,T)` plus the initial trace gives the initial supremum
as a pointwise-in-time upper bound. -/
theorem zero_growth_supNorm_le_initial
    {p : CM2Params} (hchi : p.χ₀ ≤ 0) (ha : p.a = 0) (hm : p.m = 1)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ t, 0 < t → t < T → intervalDomainM.supNorm (u t) ≤ intervalDomainM.supNorm u₀ := by
  have hmono := lemma31_zero_growth_intervalDomainM hchi ha hm hT hsol
  have hu₀legacy : PositiveInitialDatum intervalDomain u₀ := by
    simpa [intervalDomainM, intervalDomain] using hu₀
  have htraceLegacy : InitialTrace intervalDomain u₀ u := by
    simpa [intervalDomainM, intervalDomain] using htrace
  have hsolLegacy : IsPaper2ClassicalSolution intervalDomain p T u v :=
    classicalSolution_intervalDomain_of_m_eq_one hm hsol
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
      intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε := by
    intro ε hε
    exact ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
      p u₀ hu₀legacy hu₀legacy.admissible.1 hT hsolLegacy htraceLegacy hε
  intro t ht0 htT
  by_contra hnot
  push Not at hnot
  let gap : ℝ := intervalDomainM.supNorm (u t) - intervalDomainM.supNorm u₀
  have hgap : 0 < gap := by linarith
  obtain ⟨δ, hδ, _hδT, hδbound⟩ := happroach (gap / 2) (half_pos hgap)
  let s : ℝ := min (δ / 2) (t / 2)
  have hs0 : 0 < s := lt_min (half_pos hδ) (half_pos ht0)
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hst : s < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsT : s < T := hst.trans htT
  have hstmono := hmono s ⟨hs0, hsT⟩ t ⟨ht0, htT⟩ hst.le
  have hsbound := hδbound s hs0 hsδ
  have hsboundM : intervalDomainM.supNorm (u s) ≤
      intervalDomainM.supNorm u₀ + gap / 2 := by
    simpa [intervalDomainM, intervalDomain] using hsbound
  dsimp [gap] at hgap
  linarith

/-- Under the corrected parameter guard, every nonpositive-sensitivity
critical solution obeys one explicit horizon-independent supremum bound. -/
theorem nonpos_guard_supNorm_bound
    {p : CM2Params} (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : p.m = 1)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ t, 0 < t → t < T →
      intervalDomainM.supNorm (u t) ≤
        max (intervalDomainM.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)) := by
  rcases hguard with ha | hb
  · intro t ht0 htT
    exact (zero_growth_supNorm_le_initial hchi ha hm hu₀ hT hsol htrace
      t ht0 htT).trans (le_max_left _ _)
  · rcases eq_or_lt_of_le p.ha with ha | ha
    · intro t ht0 htT
      exact (zero_growth_supNorm_le_initial hchi ha.symm hm hu₀ hT hsol htrace
        t ht0 htT).trans (le_max_left _ _)
    · have hu₀legacy : PositiveInitialDatum intervalDomain u₀ := by
        simpa [intervalDomainM, intervalDomain] using hu₀
      have htraceLegacy : InitialTrace intervalDomain u₀ u := by
        simpa [intervalDomainM, intervalDomain] using htrace
      have hsolLegacy : IsPaper2ClassicalSolution intervalDomain p T u v :=
        classicalSolution_intervalDomain_of_m_eq_one hm hsol
      have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧ ∀ s, 0 < s → s < δ →
          intervalDomain.supNorm (u s) ≤ intervalDomain.supNorm u₀ + ε := by
        intro ε hε
        exact ShenWork.IntervalDomainExistence.initialSupNormApproach_intervalDomain
          p u₀ hu₀legacy hu₀legacy.admissible.1 hT hsolLegacy htraceLegacy hε
      simpa [intervalDomainM, intervalDomain] using
        (nonminimal_supNorm_bound_of_corrected_initial_approach
          p hchi ha hb hT hsolLegacy happroach)

theorem critical_bounded_before_nonpos
    {p : CM2Params} (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : p.m = 1)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  refine ⟨max (intervalDomainM.supNorm u₀) ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  exact nonpos_guard_supNorm_bound hguard hchi hm hu₀ hsol.1 hsol htrace

theorem critical_bounded_global_nonpos
    {p : CM2Params} (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : p.m = 1)
    {u₀ : intervalDomainPoint → ℝ} (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    IsPaper2Bounded intervalDomainM u := by
  apply IsPaper2Bounded.of_forall_ge_supNorm_le (T := 1)
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  exact nonpos_guard_supNorm_bound hguard hchi hm hu₀ hT
    (hglobal.classical hT) htrace t ht0 htT

#print axioms lemma31_zero_growth_intervalDomainM
#print axioms critical_bounded_before_nonpos
#print axioms critical_bounded_global_nonpos

end ShenWork.Paper2.IntervalDomainMChiNonposBound

end
