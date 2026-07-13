/-
  Realization of a bounded supremum of reachable horizons for the faithful
  general-m interval problem.

  The key structural observation is that the classical predicate is open at
  its terminal time.  It is therefore enough to prove that one fixed glued
  pair is classical on every strict subhorizon of the supremum; no endpoint
  compactness argument is needed.
-/
import ShenWork.Paper2.IntervalDomainMReachability

open Filter Topology Set

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMContinuation

open ShenWork.Paper2
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift intervalDomainM
    intervalDomainClassicalRegularity)
open ShenWork.IntervalDomainExistence

/-! ## Strict-subhorizon closure -/

/-- Raw interval classical regularity is determined by all strict positive
subhorizons.  This packages the locality needed at a finite reachable
supremum. -/
theorem intervalDomainClassicalRegularity_of_strict_subhorizons
    {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (_hT : 0 < T)
    (hsub : ∀ S, 0 < S → S < T →
      intervalDomainClassicalRegularity S u v) :
    intervalDomainClassicalRegularity T u v := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht0' : 0 < t := ht.1
    have htT' : t < T := ht.2
    let S : ℝ := (t + T) / 2
    have hS0 : 0 < S := by dsimp [S]; linarith
    have htS : t < S := by dsimp [S]; linarith
    have hST : S < T := by dsimp [S]; linarith
    exact (hsub S hS0 hST).1 t ⟨ht.1, htS⟩
  · intro x t ht
    have ht0' : 0 < t := ht.1
    have htT' : t < T := ht.2
    let S : ℝ := (t + T) / 2
    have hS0 : 0 < S := by dsimp [S]; linarith
    have htS : t < S := by dsimp [S]; linarith
    have hST : S < T := by dsimp [S]; linarith
    have hregS := hsub S hS0 hST
    refine ⟨(hregS.2.1 x t ⟨ht.1, htS⟩).1, ?_, ?_⟩
    · apply continuousOn_of_locally_continuousOn
      intro s hs
      have hs0' : 0 < s := hs.1
      have hsT' : s < T := hs.2
      let R : ℝ := (s + T) / 2
      have hR0 : 0 < R := by dsimp [R]; linarith
      have hsR : s < R := by dsimp [R]; linarith
      have hRT : R < T := by dsimp [R]; linarith
      refine ⟨Set.Ioo (0 : ℝ) R, isOpen_Ioo, ⟨hs.1, hsR⟩, ?_⟩
      exact (((hsub R hR0 hRT).2.1 x s ⟨hs.1, hsR⟩).2.1).mono
        Set.inter_subset_right
    · apply continuousOn_of_locally_continuousOn
      intro s hs
      have hs0' : 0 < s := hs.1
      have hsT' : s < T := hs.2
      let R : ℝ := (s + T) / 2
      have hR0 : 0 < R := by dsimp [R]; linarith
      have hsR : s < R := by dsimp [R]; linarith
      have hRT : R < T := by dsimp [R]; linarith
      refine ⟨Set.Ioo (0 : ℝ) R, isOpen_Ioo, ⟨hs.1, hsR⟩, ?_⟩
      exact (((hsub R hR0 hRT).2.1 x s ⟨hs.1, hsR⟩).2.2).mono
        Set.inter_subset_right
  · constructor
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht0' : 0 < t := ht.1
      have htT' : t < T := ht.2
      let S : ℝ := (t + T) / 2
      have hS0 : 0 < S := by dsimp [S]; linarith
      have htS : t < S := by dsimp [S]; linarith
      have hST : S < T := by dsimp [S]; linarith
      refine ⟨Set.Ioo (0 : ℝ) S ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ, ⟨⟨ht.1, htS⟩, Set.mem_univ _⟩, ?_⟩
      apply ((hsub S hS0 hST).2.2.1.1).mono
      rintro ⟨s, y⟩ ⟨⟨_hsT, hy⟩, hsS, _⟩
      exact ⟨hsS, hy⟩
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht0' : 0 < t := ht.1
      have htT' : t < T := ht.2
      let S : ℝ := (t + T) / 2
      have hS0 : 0 < S := by dsimp [S]; linarith
      have htS : t < S := by dsimp [S]; linarith
      have hST : S < T := by dsimp [S]; linarith
      refine ⟨Set.Ioo (0 : ℝ) S ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ, ⟨⟨ht.1, htS⟩, Set.mem_univ _⟩, ?_⟩
      apply ((hsub S hS0 hST).2.2.1.2).mono
      rintro ⟨s, y⟩ ⟨⟨_hsT, hy⟩, hsS, _⟩
      exact ⟨hsS, hy⟩
  · intro t ht
    have ht0' : 0 < t := ht.1
    have htT' : t < T := ht.2
    let S : ℝ := (t + T) / 2
    have hS0 : 0 < S := by dsimp [S]; linarith
    have htS : t < S := by dsimp [S]; linarith
    have hST : S < T := by dsimp [S]; linarith
    exact (hsub S hS0 hST).2.2.2.1 t ⟨ht.1, htS⟩
  · intro t ht
    have ht0' : 0 < t := ht.1
    have htT' : t < T := ht.2
    let S : ℝ := (t + T) / 2
    have hS0 : 0 < S := by dsimp [S]; linarith
    have htS : t < S := by dsimp [S]; linarith
    have hST : S < T := by dsimp [S]; linarith
    exact (hsub S hS0 hST).2.2.2.2.1 t ⟨ht.1, htS⟩
  · constructor
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht0' : 0 < t := ht.1
      have htT' : t < T := ht.2
      let S : ℝ := (t + T) / 2
      have hS0 : 0 < S := by dsimp [S]; linarith
      have htS : t < S := by dsimp [S]; linarith
      have hST : S < T := by dsimp [S]; linarith
      refine ⟨Set.Ioo (0 : ℝ) S ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ, ⟨⟨ht.1, htS⟩, Set.mem_univ _⟩, ?_⟩
      apply ((hsub S hS0 hST).2.2.2.2.2.1.1).mono
      rintro ⟨s, y⟩ ⟨⟨_hsT, hy⟩, hsS, _⟩
      exact ⟨hsS, hy⟩
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht0' : 0 < t := ht.1
      have htT' : t < T := ht.2
      let S : ℝ := (t + T) / 2
      have hS0 : 0 < S := by dsimp [S]; linarith
      have htS : t < S := by dsimp [S]; linarith
      have hST : S < T := by dsimp [S]; linarith
      refine ⟨Set.Ioo (0 : ℝ) S ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ, ⟨⟨ht.1, htS⟩, Set.mem_univ _⟩, ?_⟩
      apply ((hsub S hS0 hST).2.2.2.2.2.1.2).mono
      rintro ⟨s, y⟩ ⟨⟨_hsT, hy⟩, hsS, _⟩
      exact ⟨hsS, hy⟩
  · constructor
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht0' : 0 < t := ht.1
      have htT' : t < T := ht.2
      let S : ℝ := (t + T) / 2
      have hS0 : 0 < S := by dsimp [S]; linarith
      have htS : t < S := by dsimp [S]; linarith
      have hST : S < T := by dsimp [S]; linarith
      refine ⟨Set.Ioo (0 : ℝ) S ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ, ⟨⟨ht.1, htS⟩, Set.mem_univ _⟩, ?_⟩
      apply ((hsub S hS0 hST).2.2.2.2.2.2.1).mono
      rintro ⟨s, y⟩ ⟨⟨_hsT, hy⟩, hsS, _⟩
      exact ⟨hsS, hy⟩
    · apply continuousOn_of_locally_continuousOn
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht0' : 0 < t := ht.1
      have htT' : t < T := ht.2
      let S : ℝ := (t + T) / 2
      have hS0 : 0 < S := by dsimp [S]; linarith
      have htS : t < S := by dsimp [S]; linarith
      have hST : S < T := by dsimp [S]; linarith
      refine ⟨Set.Ioo (0 : ℝ) S ×ˢ Set.univ,
        isOpen_Ioo.prod isOpen_univ, ⟨⟨ht.1, htS⟩, Set.mem_univ _⟩, ?_⟩
      apply ((hsub S hS0 hST).2.2.2.2.2.2.2).mono
      rintro ⟨s, y⟩ ⟨⟨_hsT, hy⟩, hsS, _⟩
      exact ⟨hsS, hy⟩

/-- The faithful general-`m` classical predicate is likewise determined by
its strict positive subhorizons. -/
theorem isPaper2ClassicalSolution_intervalDomainM_of_strict_subhorizons
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hT : 0 < T)
    (hsub : ∀ S, 0 < S → S < T →
      IsPaper2ClassicalSolution intervalDomainM p S u v) :
    IsPaper2ClassicalSolution intervalDomainM p T u v := by
  refine IsPaper2ClassicalSolution.of_components hT
    (intervalDomainClassicalRegularity_of_strict_subhorizons hT
      (fun S hS0 hST => (hsub S hS0 hST).regularity)) ?_ ?_ ?_ ?_ ?_
  · intro t x ht0 htT
    let S : ℝ := (t + T) / 2
    exact (hsub S (by dsimp [S]; linarith) (by dsimp [S]; linarith)).u_pos'
      ht0 (by dsimp [S]; linarith)
  · intro t x ht0 htT
    let S : ℝ := (t + T) / 2
    exact (hsub S (by dsimp [S]; linarith) (by dsimp [S]; linarith)).v_nonneg
      ht0 (by dsimp [S]; linarith)
  · intro t x ht0 htT hx
    let S : ℝ := (t + T) / 2
    exact (hsub S (by dsimp [S]; linarith) (by dsimp [S]; linarith)).pde_u
      ht0 (by dsimp [S]; linarith) hx
  · intro t x ht0 htT hx
    let S : ℝ := (t + T) / 2
    exact (hsub S (by dsimp [S]; linarith) (by dsimp [S]; linarith)).pde_v
      ht0 (by dsimp [S]; linarith) hx
  · intro t x ht0 htT hx
    let S : ℝ := (t + T) / 2
    exact (hsub S (by dsimp [S]; linarith) (by dsimp [S]; linarith)).neumann
      ht0 (by dsimp [S]; linarith) hx

/-! ## Bounded reachable supremum -/

/-- Supremum of the faithful reachable-horizon set. -/
noncomputable def finiteMaximalReachableHorizonM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) : ℝ :=
  sSup (reachableClassicalHorizonSetM p u₀)

theorem reachable_le_finiteMaximalReachableHorizonM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    {T : ℝ} (hreach : ReachableClassicalHorizonM p u₀ T) :
    T ≤ finiteMaximalReachableHorizonM p u₀ := by
  exact le_csSup hbdd hreach

theorem finiteMaximalReachableHorizonM_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty) :
    0 < finiteMaximalReachableHorizonM p u₀ := by
  obtain ⟨T, hT⟩ := hne
  exact lt_of_lt_of_le hT.1
    (reachable_le_finiteMaximalReachableHorizonM hbdd hT)

/-- A faithful branch exists strictly past `T`. -/
def ReachablePastM
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ) : Prop :=
  ∃ T', T < T' ∧ ReachableClassicalHorizonM p u₀ T'

theorem not_reachablePast_finiteMaximalReachableHorizonM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀)) :
    ¬ ReachablePastM p u₀ (finiteMaximalReachableHorizonM p u₀) := by
  rintro ⟨T', hlt, hreach⟩
  exact (not_lt_of_ge
    (reachable_le_finiteMaximalReachableHorizonM hbdd hreach)) hlt

private noncomputable def pickReachableAboveM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalReachableHorizonM p u₀) :
    {T : ℝ // ReachableClassicalHorizonM p u₀ T ∧ t < T} :=
  let h : ∃ T ∈ reachableClassicalHorizonSetM p u₀, t < T :=
    (lt_csSup_iff hbdd hne).mp ht
  ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2⟩

private noncomputable def pickReachableAboveDataM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty)
    {t : ℝ} (ht : t < finiteMaximalReachableHorizonM p u₀) :
    ReachableClassicalSolutionDataM p u₀
      (pickReachableAboveM hbdd hne ht).1 :=
  reachableClassicalSolutionDataMOfReach
    (pickReachableAboveM hbdd hne ht).2.1

noncomputable def boundedReachableGluedUM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : 0 < t ∧ t < finiteMaximalReachableHorizonM p u₀ then
      (pickReachableAboveDataM hbdd hne h.2).u t x
    else 0

noncomputable def boundedReachableGluedVM
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty) :
    ℝ → intervalDomainPoint → ℝ :=
  fun t x =>
    if h : 0 < t ∧ t < finiteMaximalReachableHorizonM p u₀ then
      (pickReachableAboveDataM hbdd hne h.2).v t x
    else 0

theorem boundedReachableGluedM_eq_reachableData_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty)
    {T : ℝ} (d : ReachableClassicalSolutionDataM p u₀ T) :
    ∀ t, 0 < t → t < T → ∀ x : intervalDomainPoint,
      boundedReachableGluedUM hbdd hne t x = d.u t x ∧
      boundedReachableGluedVM hbdd hne t x = d.v t x := by
  intro t ht0 htT x
  have hTle : T ≤ finiteMaximalReachableHorizonM p u₀ :=
    reachable_le_finiteMaximalReachableHorizonM hbdd
      ⟨d.T_pos, d.u, d.v, d.sol, d.trace⟩
  have htmax : t < finiteMaximalReachableHorizonM p u₀ :=
    lt_of_lt_of_le htT hTle
  let dpick := pickReachableAboveDataM hbdd hne htmax
  have htpick : t < (pickReachableAboveM hbdd hne htmax).1 :=
    (pickReachableAboveM hbdd hne htmax).2.2
  have hsame := huniq dpick d t ht0 (lt_min htpick htT) x
  constructor
  · have hglue : boundedReachableGluedUM hbdd hne t x = dpick.u t x := by
      unfold boundedReachableGluedUM
      simp only [ht0, htmax, and_self, dite_true, dpick,
        pickReachableAboveDataM]
    rw [hglue]
    exact hsame.1
  · have hglue : boundedReachableGluedVM hbdd hne t x = dpick.v t x := by
      unfold boundedReachableGluedVM
      simp only [ht0, htmax, and_self, dite_true, dpick,
        pickReachableAboveDataM]
    rw [hglue]
    exact hsame.2

theorem boundedReachableGluedM_isClassical_on_strict_subhorizon
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty)
    {S : ℝ} (hS0 : 0 < S)
    (hSmax : S < finiteMaximalReachableHorizonM p u₀) :
    IsPaper2ClassicalSolution intervalDomainM p S
      (boundedReachableGluedUM hbdd hne)
      (boundedReachableGluedVM hbdd hne) := by
  let Tpick : ℝ := (pickReachableAboveM hbdd hne hSmax).1
  let d : ReachableClassicalSolutionDataM p u₀ Tpick :=
    pickReachableAboveDataM hbdd hne hSmax
  have hST : S < Tpick := (pickReachableAboveM hbdd hne hSmax).2.2
  refine classicalSolutionLocalityUnderIooAgreement_intervalDomainM p hS0
    (isPaper2ClassicalSolution_intervalDomainM_mono hS0 (le_of_lt hST) d.sol) ?_
  intro t ht0 htS x
  exact boundedReachableGluedM_eq_reachableData_of_overlapUnique
    huniq hbdd hne d t ht0 (lt_trans htS hST) x

theorem boundedReachableGluedM_initialTrace_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty) :
    InitialTrace intervalDomainM u₀ (boundedReachableGluedUM hbdd hne) := by
  obtain ⟨T, hreach⟩ := hne
  have hne_again : (reachableClassicalHorizonSetM p u₀).Nonempty :=
    ⟨T, hreach⟩
  let d : ReachableClassicalSolutionDataM p u₀ T :=
    reachableClassicalSolutionDataMOfReach hreach
  intro ε hε
  obtain ⟨δ, hδ, htr⟩ := d.trace ε hε
  refine ⟨min δ T, lt_min hδ d.T_pos, ?_⟩
  intro t ht0 htmin
  have htδ : t < δ := lt_of_lt_of_le htmin (min_le_left _ _)
  have htT : t < T := lt_of_lt_of_le htmin (min_le_right _ _)
  have hsame := boundedReachableGluedM_eq_reachableData_of_overlapUnique
    huniq hbdd hne_again d t ht0 htT
  have hfun :
      (fun x : intervalDomainPoint =>
        boundedReachableGluedUM hbdd hne_again t x - u₀ x) =
      (fun x : intervalDomainPoint => d.u t x - u₀ x) := by
    funext x
    rw [(hsame x).1]
  change ShenWork.IntervalDomain.intervalDomainSupNorm
    (fun x : intervalDomainPoint =>
      boundedReachableGluedUM hbdd hne_again t x - u₀ x) < ε
  rw [hfun]
  simpa [intervalDomainM] using htr t ht0 htδ

/-- The bounded reachable supremum itself is realized by a faithful classical
solution and the original trace. -/
theorem realize_at_finiteMaximalReachableHorizonM_of_overlapUnique
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀)
    (hbdd : BddAbove (reachableClassicalHorizonSetM p u₀))
    (hne : (reachableClassicalHorizonSetM p u₀).Nonempty) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomainM p
        (finiteMaximalReachableHorizonM p u₀) u v ∧
      InitialTrace intervalDomainM u₀ u := by
  let u := boundedReachableGluedUM hbdd hne
  let v := boundedReachableGluedVM hbdd hne
  have hT := finiteMaximalReachableHorizonM_pos hbdd hne
  refine ⟨u, v, ?_, ?_⟩
  · exact isPaper2ClassicalSolution_intervalDomainM_of_strict_subhorizons hT
      (fun S hS0 hSmax =>
        boundedReachableGluedM_isClassical_on_strict_subhorizon
          huniq hbdd hne hS0 hSmax)
  · exact boundedReachableGluedM_initialTrace_of_overlapUnique
      huniq hbdd hne

section AxiomAudit

#print axioms intervalDomainClassicalRegularity_of_strict_subhorizons
#print axioms isPaper2ClassicalSolution_intervalDomainM_of_strict_subhorizons
#print axioms boundedReachableGluedM_isClassical_on_strict_subhorizon
#print axioms realize_at_finiteMaximalReachableHorizonM_of_overlapUnique

end AxiomAudit

end ShenWork.Paper2.IntervalDomainMContinuation
