import ShenWork.Paper1.Proposition11PositiveErrata

/-!
# The committed critical window supplies the local-moment exponent

For `1 ≤ χ`, the (mis-transcribed) critical window in the committed statement
is narrower than the source-paper window.  In particular it still supplies
the exponent used by the uniformly-local `L^P` iteration in §3.1.
-/

open Real

noncomputable section

namespace ShenWork.Paper1

/-- In the only nonvacuous part of the committed critical window with
`1 ≤ χ`, one necessarily has `m < γ`, and the source-paper division-free
threshold follows. -/
theorem paper1_committed_large_chi_threshold_implies_faithful
    (p : CMParams)
    (hcommitted :
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)))
    (hχ : 1 ≤ p.χ) :
    p.m < p.γ ∧ paper1PositiveCriticalThreshold p := by
  rcases (lt_min_iff.mp hcommitted) with ⟨hfirst, hsecond⟩
  have hmden : 0 < 2 * p.m - 1 := by linarith [p.hm]
  have hγ : 1 < p.γ := by
    rcases p.hγ.eq_or_lt with hγeq | hγlt
    · rw [← hγeq] at hsecond
      norm_num at hsecond
      linarith
    · exact hγlt
  have hγden : 0 < p.γ - 1 := sub_pos.mpr hγ
  have hfirst_mul : p.χ * (2 * p.m - 1) < p.m + p.γ - 1 :=
    (lt_div_iff₀ hmden).mp hfirst
  have hden_le : 2 * p.m - 1 ≤ p.χ * (2 * p.m - 1) := by
    have hprod : 0 ≤ (p.χ - 1) * (2 * p.m - 1) :=
      mul_nonneg (sub_nonneg.mpr hχ) hmden.le
    nlinarith
  have hmγ : p.m < p.γ := by linarith
  have hsecond_mul : p.χ * (p.γ - 1) < p.m + p.γ - 1 :=
    (lt_div_iff₀ hγden).mp hsecond
  have hmarginγ : (p.χ - 1) * (p.γ - 1) < p.m := by
    nlinarith
  have hmarginm_le :
      (p.χ - 1) * (p.m - 1) ≤ (p.χ - 1) * (p.γ - 1) := by
    exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hχ)
  have hmarginm : (p.χ - 1) * (p.m - 1) < p.m :=
    lt_of_le_of_lt hmarginm_le hmarginγ
  refine ⟨hmγ, ?_⟩
  unfold paper1PositiveCriticalThreshold
  constructor <;> nlinarith

/-- Hence there is an exponent in the precise range required by Step 1 of
the large-sensitivity bootstrap. -/
theorem paper1_committed_large_chi_exists_admissible_exponent
    (p : CMParams)
    (hcommitted :
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)))
    (hχ : 1 ≤ p.χ) :
    ∃ P : ℝ, max 1 (max p.m p.γ) < P ∧ P < p.m + p.γ ∧
      p.χ * (P - 1) < P + p.m - 1 := by
  apply
    (paper1PositiveCriticalThreshold_iff_exists_admissible_exponent
      p (zero_le_one.trans hχ)).mp
  exact
    (paper1_committed_large_chi_threshold_implies_faithful
      p hcommitted hχ).2

/-- The committed window actually leaves enough room to choose `P > 2m`.
This permits the final semigroup step to use the fixed conjugate pair
`L²-L²`, whose time singularity is `t⁻³ᐟ⁴`. -/
theorem paper1_committed_large_chi_exists_admissible_exponent_gt_two_m
    (p : CMParams)
    (hcommitted :
      p.χ < min ((p.m + p.γ - 1) / (2 * p.m - 1))
        ((p.m + p.γ - 1) / (p.γ - 1)))
    (hχ : 1 ≤ p.χ) :
    ∃ P : ℝ, max (2 * p.m) p.γ < P ∧ P < p.m + p.γ ∧
      p.χ * (P - 1) < P + p.m - 1 := by
  rcases (lt_min_iff.mp hcommitted) with ⟨hfirst, hsecond⟩
  have hmγ :=
    (paper1_committed_large_chi_threshold_implies_faithful
      p hcommitted hχ).1
  have hmden : 0 < 2 * p.m - 1 := by linarith [p.hm]
  have hγ : 1 < p.γ := lt_of_le_of_lt p.hm hmγ
  have hγden : 0 < p.γ - 1 := sub_pos.mpr hγ
  have hfirst_mul : p.χ * (2 * p.m - 1) < p.m + p.γ - 1 :=
    (lt_div_iff₀ hmden).mp hfirst
  have hsecond_mul : p.χ * (p.γ - 1) < p.m + p.γ - 1 :=
    (lt_div_iff₀ hγden).mp hsecond
  set s : ℝ := max (2 * p.m) p.γ with hs
  have hs_lt : s < p.m + p.γ := by
    rcases le_total (2 * p.m) p.γ with h | h
    · rw [hs, max_eq_right h]
      linarith [p.hm]
    · rw [hs, max_eq_left h]
      linarith
  have hmargin : (p.χ - 1) * (s - 1) < p.m := by
    rcases le_total (2 * p.m) p.γ with h | h
    · rw [hs, max_eq_right h]
      nlinarith
    · rw [hs, max_eq_left h]
      nlinarith
  set D : ℝ := p.m - (p.χ - 1) * (s - 1) with hDdef
  have hD : 0 < D := by rw [hDdef]; linarith
  set eps : ℝ := min ((p.m + p.γ - s) / 2)
    (D / (2 * (1 + p.χ))) with hepsdef
  have heps : 0 < eps := by
    rw [hepsdef]
    apply lt_min
    · linarith
    · positivity
  have heps_left : eps ≤ (p.m + p.γ - s) / 2 := by
    rw [hepsdef]
    exact min_le_left _ _
  have heps_right : eps ≤ D / (2 * (1 + p.χ)) := by
    rw [hepsdef]
    exact min_le_right _ _
  refine ⟨s + eps, by linarith, by linarith, ?_⟩
  have hχ0 : 0 ≤ p.χ := zero_le_one.trans hχ
  have hχeps : p.χ * eps ≤
      p.χ * (D / (2 * (1 + p.χ))) :=
    mul_le_mul_of_nonneg_left heps_right hχ0
  have hhalf : p.χ * (D / (2 * (1 + p.χ))) < D := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hsmall : (p.χ - 1) * eps < D := by
    nlinarith [heps.le, hχeps.trans_lt hhalf]
  rw [hDdef] at hsmall
  nlinarith

section AxiomAudit

#print axioms paper1_committed_large_chi_threshold_implies_faithful
#print axioms paper1_committed_large_chi_exists_admissible_exponent
#print axioms paper1_committed_large_chi_exists_admissible_exponent_gt_two_m

end AxiomAudit

end ShenWork.Paper1
