/-
  The faithful finite-horizon continuation alternative on `intervalDomainM`.
-/
import ShenWork.Paper2.IntervalDomainMContinuationExtension

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMContinuation

open ShenWork.Paper2.IntervalDomainM

/-! ## Closed-interval consequences of interior bounds -/

/-- A continuous upper bound on the open unit interval extends to the closed
unit interval.  This is stated for the physical lift, avoiding any dependence
on reducibility of the `BoundedDomainData.Point` projection. -/
theorem continuousOn_le_Icc_of_le_Ioo
    {f : ℝ → ℝ} {M : ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hM : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ≤ M) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≤ M := by
  intro x hx
  have hx' : x ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  apply le_on_closure hM
  · rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  · exact continuousOn_const
  · exact hx'

/-- A continuous lower bound on the open unit interval extends to the closed
unit interval. -/
theorem continuousOn_ge_Icc_of_ge_Ioo
    {f : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hc : ∀ x ∈ Set.Ioo (0 : ℝ) 1, c ≤ f x) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, c ≤ f x := by
  intro x hx
  have hx' : x ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  apply le_on_closure hc continuousOn_const
  · rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  · exact hx'

private theorem solution_slice_le_closed_of_inside_M
    {p : CM2Params} {T t B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hinside : ∀ x : intervalDomainPoint,
      x ∈ intervalDomainM.inside → u t x ≤ B) :
    ∀ x : intervalDomainPoint, u t x ≤ B := by
  have hcont :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
      hsol ⟨ht0, htT⟩
  have hIoo : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (u t) y ≤ B := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hyinside :
        (⟨y, hyIcc⟩ : intervalDomainPoint) ∈ intervalDomainM.inside := by
      simpa [intervalDomainM] using hy
    simpa [intervalDomainLift, hyIcc] using
      hinside ⟨y, hyIcc⟩ hyinside
  have hclosed := continuousOn_le_Icc_of_le_Ioo hcont hIoo
  intro x
  simpa [intervalDomainLift, x.2] using hclosed x.1 x.2

private theorem solution_slice_ge_closed_of_inside_M
    {p : CM2Params} {T t c : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hinside : ∀ x : intervalDomainPoint,
      x ∈ intervalDomainM.inside → c ≤ u t x) :
    ∀ x : intervalDomainPoint, c ≤ u t x := by
  have hcont :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
      hsol ⟨ht0, htT⟩
  have hIoo : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      c ≤ intervalDomainLift (u t) y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
    have hyinside :
        (⟨y, hyIcc⟩ : intervalDomainPoint) ∈ intervalDomainM.inside := by
      simpa [intervalDomainM] using hy
    simpa [intervalDomainLift, hyIcc] using
      hinside ⟨y, hyIcc⟩ hyinside
  have hclosed := continuousOn_ge_Icc_of_ge_Ioo hcont hIoo
  intro x
  simpa [intervalDomainLift, x.2] using hclosed x.1 x.2

/-- Failure of finite-time upper blow-up supplies the uniform sup-norm bound
needed by the continuation theorem. -/
theorem boundedBeforeM_of_not_mgeOneFiniteHorizonAlternative
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hnot :
      ¬ MGeOneFiniteHorizonAlternative intervalDomainM T u) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  unfold MGeOneFiniteHorizonAlternative at hnot
  push Not at hnot
  obtain ⟨M, hM⟩ := hnot
  refine ⟨M, ?_⟩
  intro t ht0 htT
  change intervalDomainSupNorm (u t) ≤ M
  unfold intervalDomainSupNorm
  apply csSup_le
  · exact ⟨|u t ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩|,
      ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩, rfl⟩⟩
  · rintro _ ⟨x, rfl⟩
    change |u t x| ≤ M
    rw [abs_of_pos
      (ShenWork.Paper2.IntervalDomainM.u_pos hsol ht0 htT x)]
    exact solution_slice_le_closed_of_inside_M hsol ht0 htT
      (fun y hy => hM t y ht0 htT hy) x

/-- Failure of the floor-collapse branch supplies one positive floor on every
closed spatial slice before the horizon. -/
theorem uniformFloorM_of_not_floorCollapseAlternative
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hnot :
      ¬ (∀ δ > 0, ∃ t x,
        0 < t ∧ t < T ∧
        x ∈ intervalDomainM.inside ∧ u t x < δ)) :
    ∃ c > 0,
      ∀ t, 0 < t → t < T →
        ∀ x : intervalDomainPoint, c ≤ u t x := by
  push Not at hnot
  obtain ⟨c, hc, hfloorInside⟩ := hnot
  refine ⟨c, hc, ?_⟩
  intro t ht0 htT x
  exact solution_slice_ge_closed_of_inside_M hsol ht0 htT
    (fun y hy => hfloorInside t y ht0 htT hy) x

/-! ## Continuation from explicit upper and lower controls -/

/-- A bounded faithful branch with a uniform positive floor can be continued
past its current horizon for every positive exponent `m`. -/
theorem reachablePastM_of_bounded_and_uniform_floor
    (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbdd : IsPaper2BoundedBefore intervalDomainM T u)
    (hfloor : ∃ c : ℝ, 0 < c ∧
      ∀ t, 0 < t → t < T → ∀ x, c ≤ u t x) :
    ReachablePastM p u₀ T := by
  obtain ⟨c, hc, hpersist⟩ := hfloor
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨B₀, hB₀⟩ := hu₀.admissible.1
  obtain ⟨eta, heta, hetau₀⟩ := hu₀.floor
  let c' : ℝ := min c eta
  have hc' : 0 < c' := lt_min hc heta
  let M : ℝ := max (max B B₀) 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hu₀_bound : ∀ x, |u₀ x| ≤ M := by
    intro x
    exact (hB₀ (Set.mem_range_self x)).trans
      ((le_max_right B B₀).trans (le_max_left _ _))
  have hu₀_floor : ∀ x, c' ≤ u₀ x := fun x =>
    (min_le_right c eta).trans (hetau₀ x)
  have hslice_bound : ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M := by
    intro t ht0 htT x
    have habs : |u t x| ≤ intervalDomainSupNorm (u t) :=
      le_csSup
        (ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove
          hsol ⟨ht0, htT⟩)
        ⟨x, rfl⟩
    exact (habs.trans (hB t ht0 htT)).trans
      ((le_max_left B B₀).trans (le_max_left _ _))
  obtain ⟨delta, hdelta, hfactory⟩ :=
    intervalDomainM_thresholdLocalExistence_positiveStrip_allExponents
      p M c' hM hc'
  by_cases hsmall : T ≤ delta / 2
  · obtain ⟨uw, vw, hsolw, htracew⟩ :=
      hfactory u₀ hu₀.admissible.2 hu₀_bound hu₀_floor
    exact ⟨delta, by linarith, hdelta, uw, vw, hsolw, htracew⟩
  · push Not at hsmall
    let tau : ℝ := T - delta / 4
    have htau0 : 0 < tau := by dsimp [tau]; linarith
    have htauT : tau < T := by dsimp [tau]; linarith
    have htaumem : tau ∈ Set.Ioo (0 : ℝ) T := ⟨htau0, htauT⟩
    have htaupaper : PaperPositiveInitialDatum intervalDomainM (u tau) :=
      classicalSolution_slice_paperPositiveInitialDatumM hsol htaumem
    have htaufloor : ∀ x, c' ≤ u tau x := fun x =>
      (min_le_left c eta).trans (hpersist tau htau0 htauT x)
    obtain ⟨w, z, hsolw, htracew⟩ :=
      hfactory (u tau) htaupaper.admissible.2
        (hslice_bound tau htau0 htauT) htaufloor
    have hshift := classicalSolution_timeShiftM hsol htau0 htauT
    have hshiftTrace := timeShiftInitialTraceM hsol htau0 htauT
    have huniq : IntervalMClassicalSolutionOverlapUniqueAt p (u tau) :=
      intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive htaupaper
    have hmin : min (T - tau) delta = T - tau := by
      rw [min_eq_left]
      dsimp [tau]
      linarith
    have hoverU : ∀ s, tau < s → s < T → ∀ x,
        u s x = w (s - tau) x := by
      intro s hstau hsT x
      have hs := huniq
        { T_pos := by dsimp [tau]; linarith
          u := fun t x => u (t + tau) x
          v := fun t x => v (t + tau) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hdelta, u := w, v := z, sol := hsolw, trace := htracew }
        (s - tau) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.1
    have hoverV : ∀ s, tau < s → s < T → ∀ x,
        v s x = z (s - tau) x := by
      intro s hstau hsT x
      have hs := huniq
        { T_pos := by dsimp [tau]; linarith
          u := fun t x => u (t + tau) x
          v := fun t x => v (t + tau) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hdelta, u := w, v := z, sol := hsolw, trace := htracew }
        (s - tau) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.2
    let T' : ℝ := T + delta / 2
    have hT' : 0 < T' := by dsimp [T']; linarith
    have hT'le : T' ≤ tau + delta := by dsimp [T', tau]; linarith
    have hsol' :=
      ShenWork.Paper2.IntervalDomainMPiecewiseClassical.piecewiseClassicalWorksM
        p hT hdelta htau0 htauT hsol hsolw hoverU hoverV hT' hT'le
    have htrace' : InitialTrace intervalDomainM u₀
        (fun t x => if t < T then u t x else w (t - tau) x) := by
      intro eps heps
      obtain ⟨d, hd, htr⟩ := htrace eps heps
      refine ⟨min d T, lt_min hd hT, ?_⟩
      intro t ht0 htd
      have htT' : t < T := lt_of_lt_of_le htd (min_le_right _ _)
      have htd' : t < d := lt_of_lt_of_le htd (min_le_left _ _)
      have heq :
          (fun x => (if t < T then u t x else w (t - tau) x) - u₀ x) =
          (fun x => u t x - u₀ x) := by
        funext x
        rw [if_pos htT']
      simpa [intervalDomainM, heq] using htr t ht0 htd'
    exact ⟨T', by dsimp [T']; linarith, hT', _, _, hsol', htrace'⟩

/-! ## The alternatives at the canonical finite maximal horizon -/

/-- At the supremum of the faithful reachable horizons, either the population
becomes arbitrarily large or its positive floor collapses. -/
theorem finiteHorizonAlternative_at_finiteMaximalReachableHorizonM
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p
      (finiteMaximalReachableHorizonM p u₀) u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    FiniteHorizonAlternative intervalDomainM
      (finiteMaximalReachableHorizonM p u₀) u := by
  by_contra halt
  have hnotUpper :
      ¬ MGeOneFiniteHorizonAlternative intervalDomainM
        (finiteMaximalReachableHorizonM p u₀) u :=
    fun h => halt (Or.inl h)
  have hnotFloor :
      ¬ (∀ δ > 0, ∃ t x,
        0 < t ∧ t < finiteMaximalReachableHorizonM p u₀ ∧
        x ∈ intervalDomainM.inside ∧ u t x < δ) :=
    fun h => halt (Or.inr h)
  have hbounded :=
    boundedBeforeM_of_not_mgeOneFiniteHorizonAlternative hsol hnotUpper
  obtain ⟨c, hc, hfloor⟩ :=
    uniformFloorM_of_not_floorCollapseAlternative hsol hnotFloor
  have hpast :=
    reachablePastM_of_bounded_and_uniform_floor
      p hu₀ hsol.1 hsol htrace hbounded ⟨c, hc, hfloor⟩
  exact not_reachablePast_finiteMaximalReachableHorizonM hbdd hpast

/-- When `m ≥ 1`, the committed minimum-persistence theorem rules out floor
collapse, so a finite maximal horizon forces upper blow-up. -/
theorem mgeOneFiniteHorizonAlternative_at_finiteMaximalReachableHorizonM
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hm : 1 ≤ p.m)
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p
      (finiteMaximalReachableHorizonM p u₀) u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    MGeOneFiniteHorizonAlternative intervalDomainM
      (finiteMaximalReachableHorizonM p u₀) u := by
  by_contra hnot
  have hbounded :=
    boundedBeforeM_of_not_mgeOneFiniteHorizonAlternative hsol hnot
  have hpast :=
    reachablePastM_of_bounded p hm hu₀ hsol.1 hsol htrace hbounded
  exact not_reachablePast_finiteMaximalReachableHorizonM hbdd hpast

section AxiomAudit

#print axioms continuousOn_le_Icc_of_le_Ioo
#print axioms continuousOn_ge_Icc_of_ge_Ioo
#print axioms boundedBeforeM_of_not_mgeOneFiniteHorizonAlternative
#print axioms uniformFloorM_of_not_floorCollapseAlternative
#print axioms reachablePastM_of_bounded_and_uniform_floor
#print axioms finiteHorizonAlternative_at_finiteMaximalReachableHorizonM
#print axioms mgeOneFiniteHorizonAlternative_at_finiteMaximalReachableHorizonM

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMContinuation
