/-
  Boundedness and global continuation for nonpositive sensitivity and m >= 1.
-/
import ShenWork.Paper2.IntervalDomainMChiNonposLemma31
import ShenWork.Paper2.IntervalDomainMContinuationExtension

open Set
open ShenWork.IntervalDomain ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMChiNonpos

open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.IntervalDomainMContinuation

private theorem classicalSolutionM_u_range_bddAbove
    {p : CM2Params} {T : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    BddAbove (Set.range (fun x : intervalDomainPoint => |u t x|)) := by
  have hcont : ContinuousOn (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1.continuousOn
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc.image_of_continuousOn hcont.abs).bddAbove
  refine ⟨B, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hBx : |intervalDomainLift (u t) x.1| ≤ B :=
    hB ⟨x.1, x.2, rfl⟩
  have hlift : intervalDomainLift (u t) x.1 = u t x := by
    simp [intervalDomainLift]
  simpa only [hlift] using hBx

private theorem initialSupNormApproach_M
    {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ}
    (hbdd_u0 : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    {T : ℝ} (hT : 0 < T)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ T ∧ ∀ t, 0 < t → t < δ →
      intervalDomainM.supNorm (u t) ≤ intervalDomainM.supNorm u₀ + ε := by
  obtain ⟨δ₁, hδ₁_pos, hδ₁_bound⟩ := htrace ε hε
  refine ⟨min δ₁ T, lt_min hδ₁_pos hT, min_le_right _ _,
    fun t ht0 htδ => ?_⟩
  have ht_lt_δ₁ : t < δ₁ := lt_of_lt_of_le htδ (min_le_left _ _)
  have hsup_diff : intervalDomainSupNorm (fun x => u t x - u₀ x) < ε :=
    hδ₁_bound t ht0 ht_lt_δ₁
  change intervalDomainSupNorm (u t) ≤ intervalDomainSupNorm u₀ + ε
  have htT : t < T := lt_of_lt_of_le htδ (min_le_right _ _)
  have hbdd_ut := classicalSolutionM_u_range_bddAbove hsol ⟨ht0, htT⟩
  have hbdd_diff : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u t x - u₀ x|)) := by
    obtain ⟨M₁, hM₁⟩ := hbdd_ut
    obtain ⟨M₂, hM₂⟩ := hbdd_u0
    exact ⟨M₁ + M₂, fun _ ⟨x, hx⟩ => hx ▸
      (abs_sub (u t x) (u₀ x)).trans
        (add_le_add (hM₁ ⟨x, rfl⟩) (hM₂ ⟨x, rfl⟩))⟩
  unfold intervalDomainSupNorm
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, le_rfl, zero_le_one⟩⟩
  have hne : (Set.range (fun x : intervalDomainPoint => |u t x|)).Nonempty :=
    Set.range_nonempty _
  apply csSup_le hne
  rintro _ ⟨x, rfl⟩
  have hxdiff : |u t x - u₀ x| < ε :=
    lt_of_le_of_lt (le_csSup hbdd_diff ⟨x, rfl⟩) hsup_diff
  calc
    |u t x| = |u₀ x + (u t x - u₀ x)| := by ring_nf
    _ ≤ |u₀ x| + |u t x - u₀ x| := abs_add_le _ _
    _ ≤ sSup (Set.range (fun x => |u₀ x|)) + |u t x - u₀ x| :=
      add_le_add (le_csSup hbdd_u0 ⟨x, rfl⟩) le_rfl
    _ ≤ sSup (Set.range (fun x => |u₀ x|)) + ε := by linarith

private theorem supNorm_le_initial_of_Ioo_M
    {u : ℝ → intervalDomainPoint → ℝ}
    {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hmono : SupNormNonincreasingOn intervalDomainM u
      (Set.Ioo (0 : ℝ) T))
    (happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧
      ∀ s, 0 < s → s < δ →
        intervalDomainM.supNorm (u s) ≤
          intervalDomainM.supNorm u₀ + ε)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    intervalDomainM.supNorm (u t) ≤ intervalDomainM.supNorm u₀ := by
  by_contra hgt
  push Not at hgt
  set gap := intervalDomainM.supNorm (u t) -
    intervalDomainM.supNorm u₀ with hgap_def
  have hgap : 0 < gap := by linarith
  obtain ⟨δ, hδ, _hδT, hδbound⟩ :=
    happroach (gap / 2) (by linarith)
  set s := min (δ / 2) (t / 2) with hs_def
  have hs0 : 0 < s := lt_min (by linarith) (by linarith)
  have hsδ : s < δ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hst : s < t :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmono_st := hmono s ⟨hs0, hst.trans htT⟩
    t ⟨ht0, htT⟩ hst.le
  have hsbound := hδbound s hs0 hsδ
  linarith

/-- For zero linear growth, the initial sup norm bounds every positive time. -/
theorem zero_growth_supNorm_le_initial_M
    {p : CM2Params} (hchi : p.χ₀ ≤ 0) (ha : p.a = 0)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ t, 0 < t → t < T →
      intervalDomainM.supNorm (u t) ≤ intervalDomainM.supNorm u₀ := by
  have hmono := lemma31_zero_M p hchi ha hT hsol
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧
      ∀ s, 0 < s → s < δ →
        intervalDomainM.supNorm (u s) ≤
          intervalDomainM.supNorm u₀ + ε := by
    intro ε hε
    exact initialSupNormApproach_M hu₀.admissible.1 hT hsol htrace hε
  intro t ht0 htT
  exact supNorm_le_initial_of_Ioo_M hmono happroach ht0 htT

/-- Positive logistic damping gives the carrying-capacity maximum bound. -/
theorem positive_growth_supNorm_bound_M
    {p : CM2Params} (hchi : p.χ₀ ≤ 0)
    (ha : 0 < p.a) (hb : 0 < p.b)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ t, 0 < t → t < T →
      intervalDomainM.supNorm (u t) ≤
        max (intervalDomainM.supNorm u₀)
          ((p.a / p.b) ^ (1 / p.α)) := by
  have happroach : ∀ ε > 0, ∃ δ > 0, δ ≤ T ∧
      ∀ s, 0 < s → s < δ →
        intervalDomainM.supNorm (u s) ≤
          intervalDomainM.supNorm u₀ + ε := by
    intro ε hε
    exact initialSupNormApproach_M hu₀.admissible.1 hT hsol htrace hε
  intro t ht0 htT
  by_cases hbelow : intervalDomainM.supNorm (u t) ≤
      (p.a / p.b) ^ (1 / p.α)
  · exact hbelow.trans (le_max_right _ _)
  · push Not at hbelow
    have hmono := lemma31_above_capacity_M p hchi ha hb hT hsol
      ht0 htT hbelow
    have hinit : intervalDomainM.supNorm (u t) ≤
        intervalDomainM.supNorm u₀ := by
      by_contra hgt
      push Not at hgt
      set gap := intervalDomainM.supNorm (u t) -
        intervalDomainM.supNorm u₀ with hgap_def
      have hgap : 0 < gap := by linarith
      obtain ⟨δ, hδ, _hδT, hδbound⟩ :=
        happroach (gap / 2) (by linarith)
      set s := min (δ / 2) (t / 2) with hs_def
      have hs0 : 0 < s := lt_min (by linarith) (by linarith)
      have hsδ : s < δ :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hst : s < t :=
        lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hmono_st := hmono s ⟨hs0, hst.le⟩ t ⟨ht0, le_rfl⟩ hst.le
      have hsbound := hδbound s hs0 hsδ
      linarith
    exact hinit.trans (le_max_left _ _)

/-- Horizon-independent bound under the corrected reaction guard. -/
theorem nonpos_guard_supNorm_bound_M
    {p : CM2Params} (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} (hT : 0 < T) {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    ∀ t, 0 < t → t < T →
      intervalDomainM.supNorm (u t) ≤
        max (intervalDomainM.supNorm u₀)
          ((p.a / p.b) ^ (1 / p.α)) := by
  rcases hguard with ha | hb
  · intro t ht0 htT
    exact (zero_growth_supNorm_le_initial_M hchi ha hu₀ hT hsol htrace
      t ht0 htT).trans (le_max_left _ _)
  · rcases eq_or_lt_of_le p.ha with ha | ha
    · intro t ht0 htT
      exact (zero_growth_supNorm_le_initial_M hchi ha.symm hu₀ hT
        hsol htrace t ht0 htT).trans (le_max_left _ _)
    · exact positive_growth_supNorm_bound_M hchi ha hb hu₀ hT
        hsol htrace

/-- Boundedness before a finite horizon; `hm` records the continuation
hypothesis, while the maximum-principle estimate itself holds for every `m`. -/
theorem critical_bounded_before_nonpos_m_ge_one
    {p : CM2Params} (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (_hm : 1 ≤ p.m)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {T : ℝ} {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    IsPaper2BoundedBefore intervalDomainM T u := by
  refine ⟨max (intervalDomainM.supNorm u₀)
    ((p.a / p.b) ^ (1 / p.α)), ?_⟩
  exact nonpos_guard_supNorm_bound_M hguard hchi hu₀ hsol.1 hsol htrace

/-- The same explicit bound for a global general-`m` solution. -/
theorem critical_bounded_global_nonpos_m_ge_one
    {p : CM2Params} (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (_hm : 1 ≤ p.m)
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomainM p u v)
    (htrace : InitialTrace intervalDomainM u₀ u) :
    IsPaper2Bounded intervalDomainM u := by
  apply IsPaper2Bounded.of_forall_ge_supNorm_le (T := 1)
    (M := max (intervalDomainM.supNorm u₀)
      ((p.a / p.b) ^ (1 / p.α)))
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let T : ℝ := t + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have htT : t < T := by dsimp [T]; linarith
  exact nonpos_guard_supNorm_bound_M hguard hchi hu₀ hT
    (hglobal.classical hT) htrace t ht0 htT

/-- Every positive finite horizon is reachable when `m >= 1`. -/
theorem reachableArbitrarilyLongM_chiNonpos_m_ge_one
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    ReachableArbitrarilyLongM p u₀ := by
  obtain ⟨T, hT, u, v, hsol, htrace⟩ :=
    intervalDomainM_localExistence_paperPositive_allExponents p u₀ hu₀
  have hne : (reachableClassicalHorizonSetM p u₀).Nonempty :=
    ⟨T, hT, u, v, hsol, htrace⟩
  have huniq : IntervalMClassicalSolutionOverlapUniqueAt p u₀ :=
    intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hu₀
  by_cases hbdd : BddAbove (reachableClassicalHorizonSetM p u₀)
  · let Tmax := finiteMaximalReachableHorizonM p u₀
    have hTmax : 0 < Tmax := finiteMaximalReachableHorizonM_pos hbdd hne
    obtain ⟨U, V, hsolMax, htraceMax⟩ :=
      realize_at_finiteMaximalReachableHorizonM_of_overlapUnique
        huniq hbdd hne
    have hbounded : IsPaper2BoundedBefore intervalDomainM Tmax U :=
      critical_bounded_before_nonpos_m_ge_one hguard hchi hm
        hu₀.toPositive hsolMax htraceMax
    have hpast : ReachablePastM p u₀ Tmax :=
      reachablePastM_of_bounded p hm hu₀ hTmax hsolMax htraceMax
        hbounded
    exact False.elim
      ((not_reachablePast_finiteMaximalReachableHorizonM hbdd) hpast)
  · exact reachableArbitrarilyLongM_of_not_bddAbove hbdd

/-- Global classical solution and uniform bound for `chi0 <= 0`, `m >= 1`. -/
theorem globalSolution_chiNonpos_m_ge_one
    (p : CM2Params) (hguard : p.a = 0 ∨ 0 < p.b)
    (hchi : p.χ₀ ≤ 0) (hm : 1 ≤ p.m)
    (u₀ : intervalDomainPoint → ℝ)
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀) :
    ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomainM p u v ∧
      InitialTrace intervalDomainM u₀ u ∧
      IsPaper2Bounded intervalDomainM u := by
  have hreach := reachableArbitrarilyLongM_chiNonpos_m_ge_one
    p hguard hchi hm u₀ hu₀
  obtain ⟨u, v, hglobal, htrace⟩ :=
    globalSolutionM_of_reachableArbitrarilyLong_of_overlapUniqueAt
      (intervalMClassicalSolutionOverlapUniqueAt_of_paperPositive hu₀)
      hreach
  exact ⟨u, v, hglobal, htrace,
    critical_bounded_global_nonpos_m_ge_one hguard hchi hm
      hu₀.toPositive hglobal htrace⟩

end ShenWork.Paper2.IntervalDomainMChiNonpos
