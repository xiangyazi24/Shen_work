import Mathlib

open Filter Topology

namespace ShenWork.Paper3

noncomputable section

theorem compact_near_argmin_lower_of_exact
    {K : Set ℝ} {F dF : ℝ → ℝ} {z G : ℝ}
    (hK : IsCompact K)
    (hzle : ∀ x, x ∈ K → z ≤ F x)
    (hF : ContinuousOn F K)
    (hdF : ContinuousOn dF K)
    (hexact : ∀ x, x ∈ K → F x = z → G ≤ dF x) :
    ∀ eps > 0, ∃ rho > 0, ∀ x, x ∈ K → F x ≤ z + rho →
      G - eps ≤ dF x := by
  intro eps heps
  by_contra h
  push Not at h
  have hbad : ∀ n : ℕ, ∃ x, x ∈ K ∧
      F x ≤ z + (1 : ℝ) / ((n : ℝ) + 1) ∧ dF x < G - eps := by
    intro n
    exact h ((1 : ℝ) / ((n : ℝ) + 1)) (by positivity)
  choose xs hxsK hxsNear hxsBad using hbad
  obtain ⟨xstar, hxstarK, φ, hφmono, hxlim⟩ := hK.tendsto_subseq hxsK
  have hF_lim : Tendsto (fun k => F (xs (φ k))) atTop (nhds (F xstar)) := by
    have hcwa : ContinuousWithinAt F K xstar := hF xstar hxstarK
    exact hcwa.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Filter.Eventually.of_forall (fun k => hxsK (φ k))⟩)
  have hupper_lim :
      Tendsto (fun k : ℕ => z + (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (nhds z) := by
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add (h0.comp hφmono.tendsto_atTop)
  have hF_to_z : Tendsto (fun k => F (xs (φ k))) atTop (nhds z) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper_lim ?_ ?_
    · intro k
      exact hzle (xs (φ k)) (hxsK (φ k))
    · intro k
      exact hxsNear (φ k)
  have hFx : F xstar = z := tendsto_nhds_unique hF_lim hF_to_z
  have hdF_lim : Tendsto (fun k => dF (xs (φ k))) atTop (nhds (dF xstar)) := by
    have hcwa : ContinuousWithinAt dF K xstar := hdF xstar hxstarK
    exact hcwa.tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hxlim, Filter.Eventually.of_forall (fun k => hxsK (φ k))⟩)
  have hdF_le : dF xstar ≤ G - eps :=
    le_of_tendsto hdF_lim
      (Filter.Eventually.of_forall (fun k => le_of_lt (hxsBad (φ k))))
  have hdF_ge : G ≤ dF xstar := hexact xstar hxstarK hFx
  linarith

end

end ShenWork.Paper3

#print axioms ShenWork.Paper3.compact_near_argmin_lower_of_exact
