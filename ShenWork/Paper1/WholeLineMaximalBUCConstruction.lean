import ShenWork.Paper1.WholeLinePhysicalMildReachability
import ShenWork.Paper1.WholeLineMaximalBUCImport

/-!
# Construction of maximal whole-line BUC orbits

Finite physical mild segments are unique on overlaps and append under a
bounded endpoint norm.  Taking the supremum of their reachable horizons
therefore gives the standard maximal orbit and its BUC blow-up alternative.
-/

open Filter MeasureTheory Real Set Topology Function
open scoped BoundedContinuousFunction Interval NNReal ENNReal

noncomputable section

namespace ShenWork.Paper1

/-- Restriction of the classical horizon. -/
theorem isClassicalSolution_mono
    {p : CMParams} {S T : ℝ} {u v : ℝ → ℝ → ℝ}
    (hT : 0 < T) (hTS : T ≤ S) (hsol : IsClassicalSolution p S u v) :
    IsClassicalSolution p T u v :=
  { hT := hT
    u_smooth := fun t x ht htT =>
      hsol.u_smooth t x ht (htT.trans_le hTS)
    v_smooth := fun t x ht htT =>
      hsol.v_smooth t x ht (htT.trans_le hTS)
    pde_u := fun t x ht htT =>
      hsol.pde_u t x ht (htT.trans_le hTS)
    pde_v := fun t x ht htT =>
      hsol.pde_v t x ht (htT.trans_le hTS) }

/-- The classical solution predicate is local on the open time slab. -/
theorem isClassicalSolution_congr_on_Ioo
    {p : CMParams} {T : ℝ}
    {u v U V : ℝ → ℝ → ℝ}
    (hsol : IsClassicalSolution p T u v)
    (hu : ∀ t ∈ Set.Ioo (0 : ℝ) T, U t = u t)
    (hv : ∀ t ∈ Set.Ioo (0 : ℝ) T, V t = v t) :
    IsClassicalSolution p T U V := by
  refine
    { hT := hsol.hT
      u_smooth := ?_
      v_smooth := ?_
      pde_u := ?_
      pde_v := ?_ }
  · intro t x ht0 htT
    have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    have hev : (fun s => U s x) =ᶠ[nhds t] (fun s => u s x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [hu s hs]
    constructor
    · exact (hev.differentiableAt_iff).2 (hsol.u_smooth t x ht0 htT).1
    · rw [hu t ht]
      exact (hsol.u_smooth t x ht0 htT).2
  · intro t x ht0 htT
    rw [hv t ⟨ht0, htT⟩]
    exact hsol.v_smooth t x ht0 htT
  · intro t x ht0 htT
    have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    have hev : (fun s => U s x) =ᶠ[nhds t] (fun s => u s x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [hu s hs]
    rw [hev.deriv_eq, hu t ht, hv t ht]
    exact hsol.pde_u t x ht0 htT
  · intro t x ht0 htT
    have ht : t ∈ Set.Ioo (0 : ℝ) T := ⟨ht0, htT⟩
    rw [hu t ht, hv t ht]
    exact hsol.pde_v t x ht0 htT

private theorem boundedWholeLinePhysicalMildGlued_hasUniformInitialTrace
    {p : CMParams} {u₀ : WholeLineBUC}
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀))
    (hne : (wholeLinePhysicalMildReachableSet p u₀).Nonempty) :
    HasUniformInitialTrace
      (fun t x => (boundedWholeLinePhysicalMildGluedBUC hbdd hne t).1 x)
      u₀.1 := by
  obtain ⟨S, hS⟩ := hne
  have hne' : (wholeLinePhysicalMildReachableSet p u₀).Nonempty := ⟨S, hS⟩
  let d := wholeLinePhysicalMildSegmentOfReach hS
  have htrace := d.hasUniformInitialTrace
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := htrace ε hε
  refine ⟨min δ S, lt_min hδ d.T_pos, ?_⟩
  intro t x ht0 htmin
  have htδ : t < δ := htmin.trans_le (min_le_left _ _)
  have htS : t < S := htmin.trans_le (min_le_right _ _)
  have heq := boundedWholeLinePhysicalMildGluedBUC_eq_segment
    hbdd hne' d ht0 htS
  change |(boundedWholeLinePhysicalMildGluedBUC hbdd hne' t).1 x - u₀.1 x| < ε
  rw [heq]
  exact hclose t x ht0 htδ

private theorem unboundedWholeLinePhysicalMildGlued_hasUniformInitialTrace
    {p : CMParams} {u₀ : WholeLineBUC}
    (hnbdd : ¬ BddAbove (wholeLinePhysicalMildReachableSet p u₀)) :
    HasUniformInitialTrace
      (fun t x => (unboundedWholeLinePhysicalMildGluedBUC hnbdd t).1 x)
      u₀.1 := by
  let pick := wholeLinePickUnboundedReachableAbove hnbdd 0
  let d := wholeLinePickUnboundedReachableAboveData hnbdd 0
  have htrace := d.hasUniformInitialTrace
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := htrace ε hε
  refine ⟨min δ pick.1, lt_min hδ d.T_pos, ?_⟩
  intro t x ht0 htmin
  have htδ : t < δ := htmin.trans_le (min_le_left _ _)
  have htS : t < pick.1 := htmin.trans_le (min_le_right _ _)
  have heq := unboundedWholeLinePhysicalMildGluedBUC_eq_segment
    hnbdd d ht0 htS
  change |(unboundedWholeLinePhysicalMildGluedBUC hnbdd t).1 x - u₀.1 x| < ε
  rw [heq]
  exact hclose t x ht0 htδ

/-- The bounded reachable-horizon branch is a maximal orbit with the BUC
blow-up alternative. -/
theorem boundedWholeLinePhysicalMildGlued_isMaximalBUCOrbit
    (p : CMParams) (u₀ : WholeLineBUC)
    (hu₀ : ∀ x, 0 ≤ u₀.1 x)
    (hbdd : BddAbove (wholeLinePhysicalMildReachableSet p u₀)) :
    let hne := wholeLinePhysicalMildReachableSet_nonempty p u₀ hu₀
    let τ := finiteMaximalWholeLinePhysicalMildHorizon p u₀
    let U := boundedWholeLinePhysicalMildGluedBUC hbdd hne
    IsWholeLineMaximalBUCOrbit p u₀.1 (τ : WithTop ℝ) U := by
  dsimp only
  let hne := wholeLinePhysicalMildReachableSet_nonempty p u₀ hu₀
  let τ := finiteMaximalWholeLinePhysicalMildHorizon p u₀
  let U : ℝ → WholeLineBUC := boundedWholeLinePhysicalMildGluedBUC hbdd hne
  have hτ : 0 < τ :=
    finiteMaximalWholeLinePhysicalMildHorizon_pos hbdd hne
  change
    0 < (τ : WithTop ℝ) ∧
      HasInitialDatum (fun t x => (U t).1 x) u₀.1 ∧
      HasUniformInitialTrace (fun t x => (U t).1 x) u₀.1 ∧
      (∀ T : ℝ, 0 ≤ T → (T : WithTop ℝ) < (τ : WithTop ℝ) →
        ContinuousOn U (Set.Icc (0 : ℝ) T)) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < (τ : WithTop ℝ) →
        IsClassicalSolution p T (fun t x => (U t).1 x)
          (fun t => frozenElliptic p (fun x => (U t).1 x))) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < (τ : WithTop ℝ) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
          (U t).1 x = wholeLineCauchyMildMap p u₀.1
            (fun q y => (U q).1 y) t x) ∧
      (∀ t x : ℝ, 0 ≤ t → (t : WithTop ℝ) < (τ : WithTop ℝ) →
        0 ≤ (U t).1 x) ∧
      ((∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
          (t : WithTop ℝ) < (τ : WithTop ℝ) → ‖U t‖ ≤ C) →
        (τ : WithTop ℝ) = ⊤)
  refine ⟨by exact_mod_cast hτ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [U, boundedWholeLinePhysicalMildGluedBUC]
  · simpa [U, hne] using
      boundedWholeLinePhysicalMildGlued_hasUniformInitialTrace hbdd hne
  · intro R hR hRτ
    have hRτ' : R < τ := WithTop.coe_lt_coe.mp hRτ
    let pick := wholeLinePickReachableAbove hbdd hne hRτ'
    let d := wholeLinePickReachableAboveData hbdd hne hRτ'
    have hcont : ContinuousOn d.extend (Set.Icc (0 : ℝ) R) :=
      (wholeLineBUCTrajectoryExtend_continuous
        d.T_pos.le d.traj).continuousOn
    apply hcont.congr
    intro s hs
    simpa [U] using boundedWholeLinePhysicalMildGluedBUC_eq_segment
      hbdd hne d hs.1 (hs.2.trans_lt pick.2.2)
  · intro R hR hRτ
    have hRτ' : R < τ := WithTop.coe_lt_coe.mp hRτ
    let pick := wholeLinePickReachableAbove hbdd hne hRτ'
    let d := wholeLinePickReachableAboveData hbdd hne hRτ'
    have hclassR := isClassicalSolution_mono hR pick.2.2.le
      d.isClassicalSolution
    apply isClassicalSolution_congr_on_Ioo hclassR
    · intro t ht
      funext x
      exact congrArg (fun w : WholeLineBUC => w.1 x)
        (boundedWholeLinePhysicalMildGluedBUC_eq_segment
          hbdd hne d ht.1.le (ht.2.trans pick.2.2))
    · intro t ht
      congr 1
      funext x
      exact congrArg (fun w : WholeLineBUC => w.1 x)
        (boundedWholeLinePhysicalMildGluedBUC_eq_segment
          hbdd hne d ht.1.le (ht.2.trans pick.2.2))
  · intro R hR hRτ t ht x
    have hRτ' : R < τ := WithTop.coe_lt_coe.mp hRτ
    let pick := wholeLinePickReachableAbove hbdd hne hRτ'
    let d := wholeLinePickReachableAboveData hbdd hne hRτ'
    have htS : t < pick.1 := ht.2.trans_lt pick.2.2
    have heqT := boundedWholeLinePhysicalMildGluedBUC_eq_segment
      hbdd hne d ht.1 htS
    have htmem : t ∈ Set.Icc (0 : ℝ) pick.1 := ⟨ht.1, htS.le⟩
    have hextT := wholeLineBUCTrajectoryExtend_eq
      d.T_pos.le d.traj htmem
    have hagree : ∀ s ∈ Set.Icc (0 : ℝ) t,
        (fun q y => (d.extend q).1 y) s = (fun q y => (U q).1 y) s := by
      intro s hs
      funext y
      exact congrArg (fun w : WholeLineBUC => w.1 y)
        (boundedWholeLinePhysicalMildGluedBUC_eq_segment
          hbdd hne d hs.1 (hs.2.trans_lt htS)).symm
    have hcongr := wholeLineCauchyMildMap_congr_on_Icc_segments
      p u₀.1 ht.1 hagree x
    have hraw := d.mild ⟨t, htmem⟩ x
    change (boundedWholeLinePhysicalMildGluedBUC hbdd hne t).1 x =
      wholeLineCauchyMildMap p u₀.1
        (fun q y => (boundedWholeLinePhysicalMildGluedBUC hbdd hne q).1 y)
        t x
    rw [heqT, WholeLinePhysicalMildSegment.extend, hextT]
    exact hraw.trans hcongr
  · intro t x ht0 htτ
    have htτ' : t < τ := WithTop.coe_lt_coe.mp htτ
    by_cases htzero : t = 0
    · subst t
      simpa [U, boundedWholeLinePhysicalMildGluedBUC] using hu₀ x
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
      let pick := wholeLinePickReachableAbove hbdd hne htτ'
      let d := wholeLinePickReachableAboveData hbdd hne htτ'
      have heq := boundedWholeLinePhysicalMildGluedBUC_eq_segment
        hbdd hne d ht0 pick.2.2
      have htmem : t ∈ Set.Icc (0 : ℝ) pick.1 :=
        ⟨ht0, pick.2.2.le⟩
      change 0 ≤ (boundedWholeLinePhysicalMildGluedBUC hbdd hne t).1 x
      rw [heq, WholeLinePhysicalMildSegment.extend,
        wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj htmem]
      exact d.nonnegative ⟨t, htmem⟩ x
  · rintro ⟨C, hbound⟩
    obtain ⟨H, hH, huniform⟩ :=
      exists_uniform_wholeLinePhysicalMildSegment p C
    let a : ℝ := max (τ - H / 2) (τ / 2)
    have ha0 : 0 < a := by
      have : τ / 2 ≤ a := le_max_right _ _
      linarith
    have haτ : a < τ := by
      apply max_lt
      · linarith
      · linarith
    have haH : τ < a + H := by
      have : τ - H / 2 ≤ a := le_max_left _ _
      linarith
    let pick := wholeLinePickReachableAbove hbdd hne haτ
    let d := wholeLinePickReachableAboveData hbdd hne haτ
    have hSτ : pick.1 ≤ τ :=
      wholeLinePhysicalMildReachable_le_finiteMaximal hbdd pick.2.1
    let b : ℝ := (a + pick.1) / 2
    have hab : a < b := by dsimp [b]; linarith [pick.2.2]
    have hbS : b < pick.1 := by dsimp [b]; linarith [pick.2.2]
    have hb0 : 0 < b := ha0.trans hab
    have hbτ : b < τ := by dsimp [b]; linarith [haτ, hSτ]
    have hbH : τ < b + H := by linarith [hab, haH]
    let db := d.restrict hb0 hbS.le
    let zb : Set.Icc (0 : ℝ) b := ⟨b, hb0.le, le_rfl⟩
    let wb : WholeLineBUC := db.traj zb
    have hUeq : U b = d.extend b :=
      boundedWholeLinePhysicalMildGluedBUC_eq_segment
        hbdd hne d hb0.le hbS
    have hdb : wb = d.extend b := by
      dsimp [wb, zb, db, WholeLinePhysicalMildSegment.restrict,
        WholeLinePhysicalMildSegment.extend]
      rw [wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj
        ⟨hb0.le, hbS.le⟩]
      simp
    have hwbC : ‖wb‖ ≤ C := by
      rw [hdb, ← hUeq]
      exact hbound b hb0.le (WithTop.coe_lt_coe.mpr hbτ)
    have hwb0 : ∀ x, 0 ≤ wb.1 x := by
      intro x
      exact db.nonnegative zb x
    obtain ⟨e⟩ := huniform wb hwb0 hwbC
    have hpast : WholeLinePhysicalMildReachable p u₀ (b + H) := by
      exact db.append e
    have hle : b + H ≤ τ :=
      wholeLinePhysicalMildReachable_le_finiteMaximal hbdd hpast
    exact False.elim ((not_lt_of_ge hle) hbH)

/-- The unbounded reachable-horizon branch gives a global maximal orbit. -/
theorem unboundedWholeLinePhysicalMildGlued_isMaximalBUCOrbit
    (p : CMParams) (u₀ : WholeLineBUC)
    (hnbdd : ¬ BddAbove (wholeLinePhysicalMildReachableSet p u₀)) :
    let U := unboundedWholeLinePhysicalMildGluedBUC hnbdd
    IsWholeLineMaximalBUCOrbit p u₀.1 (⊤ : WithTop ℝ) U := by
  dsimp only
  let U : ℝ → WholeLineBUC := unboundedWholeLinePhysicalMildGluedBUC hnbdd
  change
    0 < (⊤ : WithTop ℝ) ∧
      HasInitialDatum (fun t x => (U t).1 x) u₀.1 ∧
      HasUniformInitialTrace (fun t x => (U t).1 x) u₀.1 ∧
      (∀ T : ℝ, 0 ≤ T → (T : WithTop ℝ) < ⊤ →
        ContinuousOn U (Set.Icc (0 : ℝ) T)) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < ⊤ →
        IsClassicalSolution p T (fun t x => (U t).1 x)
          (fun t => frozenElliptic p (fun x => (U t).1 x))) ∧
      (∀ T : ℝ, 0 < T → (T : WithTop ℝ) < ⊤ →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ,
          (U t).1 x = wholeLineCauchyMildMap p u₀.1
            (fun q y => (U q).1 y) t x) ∧
      (∀ t x : ℝ, 0 ≤ t → (t : WithTop ℝ) < ⊤ → 0 ≤ (U t).1 x) ∧
      ((∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
          (t : WithTop ℝ) < ⊤ → ‖U t‖ ≤ C) →
        (⊤ : WithTop ℝ) = ⊤)
  refine ⟨WithTop.coe_lt_top 0, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
  · intro x
    simp [U, unboundedWholeLinePhysicalMildGluedBUC]
  · simpa [U] using
      unboundedWholeLinePhysicalMildGlued_hasUniformInitialTrace hnbdd
  · intro R hR _
    let pick := wholeLinePickUnboundedReachableAbove hnbdd R
    let d := wholeLinePickUnboundedReachableAboveData hnbdd R
    have hcont : ContinuousOn d.extend (Set.Icc (0 : ℝ) R) :=
      (wholeLineBUCTrajectoryExtend_continuous
        d.T_pos.le d.traj).continuousOn
    apply hcont.congr
    intro s hs
    simpa [U] using unboundedWholeLinePhysicalMildGluedBUC_eq_segment
      hnbdd d hs.1 (hs.2.trans_lt pick.2.2)
  · intro R hR _
    let pick := wholeLinePickUnboundedReachableAbove hnbdd R
    let d := wholeLinePickUnboundedReachableAboveData hnbdd R
    have hclassR := isClassicalSolution_mono hR pick.2.2.le
      d.isClassicalSolution
    apply isClassicalSolution_congr_on_Ioo hclassR
    · intro t ht
      funext x
      exact congrArg (fun w : WholeLineBUC => w.1 x)
        (unboundedWholeLinePhysicalMildGluedBUC_eq_segment
          hnbdd d ht.1.le (ht.2.trans pick.2.2))
    · intro t ht
      congr 1
      funext x
      exact congrArg (fun w : WholeLineBUC => w.1 x)
        (unboundedWholeLinePhysicalMildGluedBUC_eq_segment
          hnbdd d ht.1.le (ht.2.trans pick.2.2))
  · intro R hR _ t ht x
    let pick := wholeLinePickUnboundedReachableAbove hnbdd R
    let d := wholeLinePickUnboundedReachableAboveData hnbdd R
    have htS : t < pick.1 := ht.2.trans_lt pick.2.2
    have heqT := unboundedWholeLinePhysicalMildGluedBUC_eq_segment
      hnbdd d ht.1 htS
    have htmem : t ∈ Set.Icc (0 : ℝ) pick.1 := ⟨ht.1, htS.le⟩
    have hextT := wholeLineBUCTrajectoryExtend_eq
      d.T_pos.le d.traj htmem
    have hagree : ∀ s ∈ Set.Icc (0 : ℝ) t,
        (fun q y => (d.extend q).1 y) s = (fun q y => (U q).1 y) s := by
      intro s hs
      funext y
      exact congrArg (fun w : WholeLineBUC => w.1 y)
        (unboundedWholeLinePhysicalMildGluedBUC_eq_segment
          hnbdd d hs.1 (hs.2.trans_lt htS)).symm
    have hcongr := wholeLineCauchyMildMap_congr_on_Icc_segments
      p u₀.1 ht.1 hagree x
    have hraw := d.mild ⟨t, htmem⟩ x
    change (unboundedWholeLinePhysicalMildGluedBUC hnbdd t).1 x =
      wholeLineCauchyMildMap p u₀.1
        (fun q y => (unboundedWholeLinePhysicalMildGluedBUC hnbdd q).1 y)
        t x
    rw [heqT, WholeLinePhysicalMildSegment.extend, hextT]
    exact hraw.trans hcongr
  · intro t x ht0 _
    by_cases htzero : t = 0
    · subst t
      let pick := wholeLinePickUnboundedReachableAbove hnbdd 0
      let d := wholeLinePickUnboundedReachableAboveData hnbdd 0
      have hinit := d.initial
      have hd0 : 0 ≤ u₀.1 x := by
        have := d.nonnegative ⟨0, le_rfl, d.T_pos.le⟩ x
        simpa [hinit] using this
      simpa [U, unboundedWholeLinePhysicalMildGluedBUC] using hd0
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
      let pick := wholeLinePickUnboundedReachableAbove hnbdd t
      let d := wholeLinePickUnboundedReachableAboveData hnbdd t
      have heq := unboundedWholeLinePhysicalMildGluedBUC_eq_segment
        hnbdd d ht0 pick.2.2
      have htmem : t ∈ Set.Icc (0 : ℝ) pick.1 :=
        ⟨ht0, pick.2.2.le⟩
      change 0 ≤ (unboundedWholeLinePhysicalMildGluedBUC hnbdd t).1 x
      rw [heq, WholeLinePhysicalMildSegment.extend,
        wholeLineBUCTrajectoryExtend_eq d.T_pos.le d.traj htmem]
      exact d.nonnegative ⟨t, htmem⟩ x

/-- The short-time fixed point and continuation construction discharge the
whole-line maximal BUC import for every parameter tuple. -/
theorem wholeLineMaximalBUCImport_constructed (p : CMParams) :
    WholeLineMaximalBUCImport p := by
  intro u₀ hu₀
  let w : WholeLineBUC := wholeLineBUCOfPaperCUnifBdd u₀ hu₀.1
  have hw0 : ∀ x, 0 ≤ w.1 x := by
    intro x
    simpa [w] using hu₀.2 x
  by_cases hbdd : BddAbove (wholeLinePhysicalMildReachableSet p w)
  · let hne := wholeLinePhysicalMildReachableSet_nonempty p w hw0
    let τ := finiteMaximalWholeLinePhysicalMildHorizon p w
    let U := boundedWholeLinePhysicalMildGluedBUC hbdd hne
    refine ⟨(τ : WithTop ℝ), U, ?_⟩
    simpa [w, hne, τ, U] using
      boundedWholeLinePhysicalMildGlued_isMaximalBUCOrbit p w hw0 hbdd
  · let U := unboundedWholeLinePhysicalMildGluedBUC hbdd
    refine ⟨(⊤ : WithTop ℝ), U, ?_⟩
    simpa [w, U] using
      unboundedWholeLinePhysicalMildGlued_isMaximalBUCOrbit p w hbdd

section AxiomAudit

#print axioms boundedWholeLinePhysicalMildGlued_isMaximalBUCOrbit
#print axioms unboundedWholeLinePhysicalMildGlued_isMaximalBUCOrbit
#print axioms wholeLineMaximalBUCImport_constructed

end AxiomAudit

end ShenWork.Paper1
