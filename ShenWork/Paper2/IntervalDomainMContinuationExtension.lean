/-
  Constructive continuation past a bounded faithful general-m branch.
-/
import ShenWork.Paper2.IntervalDomainMMinimumPersistence
import ShenWork.Paper2.IntervalDomainMPiecewiseClassical
import ShenWork.Paper2.IntervalDomainMLocalExistenceAllExponents
import ShenWork.Paper2.IntervalDomainMBoundedReachability
import ShenWork.Paper2.IntervalDomainTimeShift

open Filter Set Topology
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMContinuation

open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMMinPersistence

/-- Autonomy of the faithful general-`m` equation under a positive time
shift. -/
theorem classicalSolution_timeShiftM
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hτ0 : 0 < τ) (hτT : τ < T) :
    IsPaper2ClassicalSolution intervalDomainM p (T - τ)
      (fun t x => u (t + τ) x) (fun t x => v (t + τ) x) := by
  obtain ⟨_, hreg, hposu, hposv, hpdeu, hpdev, hneu⟩ := hsol
  refine IsPaper2ClassicalSolution.of_components (by linarith)
    (ShenWork.Paper2.TimeShift.regularityTimeShiftWorks hreg hτ0 hτT)
    ?_ ?_ ?_ ?_ ?_
  · intro t x ht0 htT
    exact hposu (t + τ) x (by linarith) (by linarith)
  · intro t x ht0 htT
    exact hposv (t + τ) x (by linarith) (by linarith)
  · intro t x ht0 htT hx
    have hpde := hpdeu (t + τ) x (by linarith) (by linarith) hx
    simp only [intervalDomainM] at hpde ⊢
    show deriv (fun s => u (s + τ) x) t = _
    rw [deriv_comp_add_const (f := fun s => u s x) (a := τ) t]
    exact hpde
  · intro t x ht0 htT hx
    exact hpdev (t + τ) x (by linarith) (by linarith) hx
  · intro t x ht0 htT hx
    exact hneu (t + τ) x (by linarith) (by linarith) hx

/-- Joint closed-slab continuity gives the initial trace of a shifted faithful
solution. -/
theorem timeShiftInitialTraceM
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hτ0 : 0 < τ) (hτT : τ < T) :
    InitialTrace intervalDomainM (u τ) (fun t x => u (t + τ) x) := by
  intro ε hε
  have hcont : ContinuousOn
      (Function.uncurry (fun (t : ℝ) (x : ℝ) => intervalDomainLift (u t) x))
      (Set.Ioo 0 T ×ˢ Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.2.2).1
  have hτmem : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
  obtain ⟨nbhd, hnbhd_mem, hnbhd⟩ :=
    IsCompact.mem_uniformity_of_prod (k := Set.Icc (0 : ℝ) 1) isCompact_Icc
      hcont hτmem (Metric.dist_mem_uniformity hε)
  rw [Metric.mem_nhdsWithin_iff] at hnbhd_mem
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := hnbhd_mem
  have hTτ : 0 < T - τ := by linarith
  refine ⟨min (δ₀ / 2) ((T - τ) / 2), by positivity, ?_⟩
  intro t ht0 htδ
  have htδ₀ : t < δ₀ := by
    have := lt_of_lt_of_le htδ (min_le_left _ _)
    linarith
  have htTτ : t < T - τ := by
    have := lt_of_lt_of_le htδ (min_le_right _ _)
    linarith
  have htτmem : t + τ ∈ Set.Ioo (0 : ℝ) T := ⟨by linarith, by linarith⟩
  have hdist : dist (t + τ) τ < δ₀ := by
    rw [Real.dist_eq]
    ring_nf
    rw [abs_of_pos ht0]
    exact htδ₀
  have htτnbhd : t + τ ∈ nbhd :=
    hδ₀sub ⟨Metric.mem_ball.mpr hdist, htτmem⟩
  have hpt : ∀ x : intervalDomainPoint,
      |u (t + τ) x - u τ x| < ε := by
    intro x
    have hmem := hnbhd (t + τ) htτnbhd x.1 x.2
    have h1 : intervalDomainLift (u (t + τ)) x.1 = u (t + τ) x := by
      simp [intervalDomainLift, x.2]
    have h2 : intervalDomainLift (u τ) x.1 = u τ x := by
      simp [intervalDomainLift, x.2]
    simp only [Set.mem_setOf_eq] at hmem
    rw [h1, h2, Real.dist_eq] at hmem
    exact hmem
  change intervalDomainSupNorm (fun x => u (t + τ) x - u τ x) < ε
  unfold intervalDomainSupNorm
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hcont_t : Continuous (u (t + τ)) := by
    have hc := ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
      hsol htτmem
    have hcomp := hc.comp_continuous continuous_subtype_val
      (fun x : intervalDomainPoint => x.2)
    exact hcomp.congr (fun x => by simp [Function.comp, intervalDomainLift, x.2])
  have hcont_τ : Continuous (u τ) := by
    have hc := ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc
      hsol hτmem
    have hcomp := hc.comp_continuous continuous_subtype_val
      (fun x : intervalDomainPoint => x.2)
    exact hcomp.congr (fun x => by simp [Function.comp, intervalDomainLift, x.2])
  have hfcont : Continuous
      (fun x : intervalDomainPoint => |u (t + τ) x - u τ x|) :=
    (hcont_t.sub hcont_τ).abs
  have hrange_ne :
      (Set.range (fun x : intervalDomainPoint =>
        |u (t + τ) x - u τ x|)).Nonempty := Set.range_nonempty _
  have hrange_bdd : BddAbove
      (Set.range (fun x : intervalDomainPoint =>
        |u (t + τ) x - u τ x|)) :=
    ⟨ε, fun _ ⟨x, hx⟩ => hx ▸ (hpt x).le⟩
  have hrange_closed : IsClosed
      (Set.range (fun x : intervalDomainPoint =>
        |u (t + τ) x - u τ x|)) :=
    (isCompact_range hfcont).isClosed
  obtain ⟨xmax, hxmax⟩ :=
    Set.mem_range.mp (hrange_closed.csSup_mem hrange_ne hrange_bdd)
  rw [← hxmax]
  exact hpt xmax

/-- Every positive-time slice of a faithful solution is a paper-positive
datum. -/
theorem classicalSolution_slice_paperPositiveInitialDatumM
    {p : CM2Params} {T τ : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hτ : τ ∈ Set.Ioo (0 : ℝ) T) :
    PaperPositiveInitialDatum intervalDomainM (u τ) := by
  have hcontOn :=
    ShenWork.Paper2.IntervalDomainM.solution_lift_continuousOn_Icc hsol hτ
  have hcont : Continuous (u τ) := by
    have hcomp := hcontOn.comp_continuous continuous_subtype_val
      (fun x : intervalDomainPoint => x.2)
    exact hcomp.congr (fun x => by simp [Function.comp, intervalDomainLift, x.2])
  have hbdd :=
    ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove hsol hτ
  refine ⟨⟨by simpa [intervalDomainM] using hbdd, hcont⟩, ?_⟩
  haveI : CompactSpace intervalDomainPoint :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hne : (Set.univ : Set intervalDomainPoint).Nonempty :=
    ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩, Set.mem_univ _⟩
  obtain ⟨x₀, _, hx₀⟩ :=
    isCompact_univ.exists_isMinOn hne hcont.continuousOn
  exact ⟨u τ x₀, hsol.u_pos' hτ.1 hτ.2,
    fun x => hx₀ (Set.mem_univ x)⟩

/-- A bounded faithful branch with `m ≥ 1` can be extended to a strictly
larger reachable horizon. -/
theorem reachablePastM_of_bounded
    (p : CM2Params) (hm : 1 ≤ p.m)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hbdd : IsPaper2BoundedBefore intervalDomainM T u) :
    ReachablePastM p u₀ T := by
  obtain ⟨c, hc, hpersist⟩ := minimumPersistenceM_of_bounded hm hsol hbdd
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨B₀, hB₀⟩ := hu₀.admissible.1
  obtain ⟨η, hη, hηu₀⟩ := hu₀.floor
  let c' : ℝ := min c η
  have hc' : 0 < c' := lt_min hc hη
  let M : ℝ := max (max B B₀) 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hu₀_bound : ∀ x, |u₀ x| ≤ M := by
    intro x
    exact (hB₀ (Set.mem_range_self x)).trans
      ((le_max_right B B₀).trans (le_max_left _ _))
  have hu₀_floor : ∀ x, c' ≤ u₀ x := fun x =>
    (min_le_right c η).trans (hηu₀ x)
  have hslice_bound : ∀ t, 0 < t → t < T → ∀ x, |u t x| ≤ M := by
    intro t ht0 htT x
    have habs : |u t x| ≤ intervalDomainSupNorm (u t) :=
      le_csSup
        (ShenWork.Paper2.IntervalDomainM.solution_slice_abs_bddAbove
          hsol ⟨ht0, htT⟩)
        ⟨x, rfl⟩
    exact (habs.trans (hB t ht0 htT)).trans
      ((le_max_left B B₀).trans (le_max_left _ _))
  obtain ⟨δ, hδ, hfactory⟩ :=
    intervalDomainM_thresholdLocalExistence_positiveStrip_allExponents
      p M c' hM hc'
  by_cases hsmall : T ≤ δ / 2
  · obtain ⟨uw, vw, hsolw, htracew⟩ :=
      hfactory u₀ hu₀.admissible.2 hu₀_bound hu₀_floor
    exact ⟨δ, by linarith, hδ, uw, vw, hsolw, htracew⟩
  · push Not at hsmall
    let τ : ℝ := T - δ / 4
    have hτ0 : 0 < τ := by dsimp [τ]; linarith
    have hτT : τ < T := by dsimp [τ]; linarith
    have hτmem : τ ∈ Set.Ioo (0 : ℝ) T := ⟨hτ0, hτT⟩
    have hτpaper : PaperPositiveInitialDatum intervalDomainM (u τ) :=
      classicalSolution_slice_paperPositiveInitialDatumM hsol hτmem
    have hτfloor : ∀ x, c' ≤ u τ x := fun x =>
      (min_le_left c η).trans
        (hpersist τ (by dsimp [τ]; linarith) hτT x)
    obtain ⟨w, z, hsolw, htracew⟩ :=
      hfactory (u τ) hτpaper.admissible.2
        (hslice_bound τ hτ0 hτT) hτfloor
    have hshift := classicalSolution_timeShiftM hsol hτ0 hτT
    have hshiftTrace := timeShiftInitialTraceM hsol hτ0 hτT
    have huniq : IntervalMClassicalSolutionOverlapUniqueAt p (u τ) :=
      intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hτpaper
    have hmin : min (T - τ) δ = T - τ := by
      rw [min_eq_left]
      dsimp [τ]
      linarith
    have hoverU : ∀ s, τ < s → s < T → ∀ x,
        u s x = w (s - τ) x := by
      intro s hsτ hsT x
      have hs := huniq
        { T_pos := by dsimp [τ]; linarith
          u := fun t x => u (t + τ) x
          v := fun t x => v (t + τ) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hδ, u := w, v := z, sol := hsolw, trace := htracew }
        (s - τ) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.1
    have hoverV : ∀ s, τ < s → s < T → ∀ x,
        v s x = z (s - τ) x := by
      intro s hsτ hsT x
      have hs := huniq
        { T_pos := by dsimp [τ]; linarith
          u := fun t x => u (t + τ) x
          v := fun t x => v (t + τ) x
          sol := hshift, trace := hshiftTrace }
        { T_pos := hδ, u := w, v := z, sol := hsolw, trace := htracew }
        (s - τ) (by linarith) (by rw [hmin]; linarith) x
      simpa using hs.2
    let T' : ℝ := T + δ / 2
    have hT' : 0 < T' := by dsimp [T']; linarith
    have hT'le : T' ≤ τ + δ := by dsimp [T', τ]; linarith
    have hsol' :=
      ShenWork.Paper2.IntervalDomainMPiecewiseClassical.piecewiseClassicalWorksM
        p hT hδ hτ0 hτT hsol hsolw hoverU hoverV hT' hT'le
    have htrace' : InitialTrace intervalDomainM u₀
        (fun t x => if t < T then u t x else w (t - τ) x) := by
      intro ε hε
      obtain ⟨d, hd, htr⟩ := htrace ε hε
      refine ⟨min d T, lt_min hd hT, ?_⟩
      intro t ht0 htd
      have htT' : t < T := lt_of_lt_of_le htd (min_le_right _ _)
      have htd' : t < d := lt_of_lt_of_le htd (min_le_left _ _)
      have heq :
          (fun x => (if t < T then u t x else w (t - τ) x) - u₀ x) =
          (fun x => u t x - u₀ x) := by
        funext x
        rw [if_pos htT']
      simpa [intervalDomainM, heq] using htr t ht0 htd'
    exact ⟨T', by dsimp [T']; linarith, hT', _, _, hsol', htrace'⟩

section AxiomAudit

#print axioms classicalSolution_timeShiftM
#print axioms timeShiftInitialTraceM
#print axioms reachablePastM_of_bounded

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMContinuation
