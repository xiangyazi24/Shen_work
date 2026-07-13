/- Closed bootstrap for an already constructed weighted Duhamel trajectory. -/
import ShenWork.Paper3.WeightedTailDuhamelContraction

namespace ShenWork.Paper3

open Set

noncomputable section

/-- If a continuous weighted size starts strictly below `R`, and whenever its
entire past is bounded by `R` the Duhamel estimate improves its current value
to a strict `B<R`, then it never reaches `R`.  This is the identification tool
for an already constructed classical solution; no fixed-point uniqueness
assumption is needed. -/
theorem weightedTail_strict_bound_of_bootstrap
    {z : ℝ → ℝ} {R B : ℝ}
    (_hR : 0 < R) (hB : B < R)
    (hcont : ContinuousOn z (Set.Ici (0 : ℝ)))
    (hz0 : z 0 < R)
    (hstep : ∀ t, 0 ≤ t →
      (∀ s ∈ Set.Icc (0 : ℝ) t, z s ≤ R) → z t ≤ B) :
    ∀ t, 0 ≤ t → z t < R := by
  intro t ht
  by_contra hnot
  have hzt : R ≤ z t := le_of_not_gt hnot
  have h0t : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have htt : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hcont0t : ContinuousOn z (Set.Icc (0 : ℝ) t) :=
    hcont.mono (fun _x hx => hx.1)
  let Z : Set ℝ := {s | s ∈ Set.Icc (0 : ℝ) t ∧ z s = R}
  have hZ_nonempty : Z.Nonempty := by
    have hRmem : R ∈ Set.Icc (z 0) (z t) :=
      ⟨le_of_lt hz0, hzt⟩
    rcases isPreconnected_Icc.intermediate_value h0t htt hcont0t hRmem with
      ⟨s, hsI, hsR⟩
    exact ⟨s, hsI, hsR⟩
  have hZ_compact : IsCompact Z := by
    have hclosed : IsClosed
        (Set.Icc (0 : ℝ) t ∩ z ⁻¹' ({R} : Set ℝ)) :=
      hcont0t.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hc : IsCompact
        (Set.Icc (0 : ℝ) t ∩ z ⁻¹' ({R} : Set ℝ)) :=
      IsCompact.of_isClosed_subset isCompact_Icc hclosed (fun _x hx => hx.1)
    simpa [Z, Set.setOf_and] using hc
  obtain ⟨tau, htauZ, htaumin⟩ :=
    hZ_compact.exists_isMinOn hZ_nonempty continuousOn_id
  have htauI : tau ∈ Set.Icc (0 : ℝ) t := htauZ.1
  have hztau : z tau = R := htauZ.2
  have htau0 : 0 < tau := by
    rcases eq_or_lt_of_le htauI.1 with heq | hlt
    · subst tau
      linarith
    · exact hlt
  have hpast : ∀ s ∈ Set.Icc (0 : ℝ) tau, z s ≤ R := by
    intro s hs
    by_contra hsnot
    have hRlt : R < z s := lt_of_not_ge hsnot
    have hspos : 0 < s := by
      rcases eq_or_lt_of_le hs.1 with heq | hlt
      · subst s
        linarith
      · exact hlt
    have hcont0s : ContinuousOn z (Set.Icc (0 : ℝ) s) :=
      hcont.mono (fun _x hx => hx.1)
    have h0s : (0 : ℝ) ∈ Set.Icc (0 : ℝ) s :=
      ⟨le_rfl, hspos.le⟩
    have hss : s ∈ Set.Icc (0 : ℝ) s := ⟨hspos.le, le_rfl⟩
    have hRmem : R ∈ Set.Icc (z 0) (z s) :=
      ⟨le_of_lt hz0, le_of_lt hRlt⟩
    rcases isPreconnected_Icc.intermediate_value h0s hss hcont0s hRmem with
      ⟨q, hqI, hzq⟩
    have hqZ : q ∈ Z := by
      refine ⟨⟨hqI.1, le_trans hqI.2 (le_trans hs.2 htauI.2)⟩, hzq⟩
    have htauleq : tau ≤ q := htaumin hqZ
    have htaus : tau ≤ s := le_trans htauleq hqI.2
    have hseq : s = tau := le_antisymm hs.2 htaus
    subst s
    linarith
  have himprove := hstep tau htauI.1 hpast
  linarith

/-- Non-strict version convenient for norm estimates. -/
theorem weightedTail_bound_of_bootstrap
    {z : ℝ → ℝ} {R B : ℝ}
    (hR : 0 < R) (hB : B < R)
    (hcont : ContinuousOn z (Set.Ici (0 : ℝ)))
    (hz0 : z 0 < R)
    (hstep : ∀ t, 0 ≤ t →
      (∀ s ∈ Set.Icc (0 : ℝ) t, z s ≤ R) → z t ≤ B) :
    ∀ t, 0 ≤ t → z t ≤ R := by
  intro t ht
  exact (weightedTail_strict_bound_of_bootstrap
    hR hB hcont hz0 hstep t ht).le

#print axioms weightedTail_strict_bound_of_bootstrap
#print axioms weightedTail_bound_of_bootstrap

end

end ShenWork.Paper3
