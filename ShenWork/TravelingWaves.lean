/-
  ShenWork/TravelingWaves.lean
  Section 4: Explicit barrier/profile facts for traveling-wave construction.
-/
import ShenWork.Defs
import ShenWork.Preliminary
import ShenWork.StabilityUniqueness

open Filter Topology

noncomputable section

/-!
The paper-level traveling-wave existence theorem is not currently formalized as
a Lean theorem.  The statements below are only true facts about the logistic
profile used as a barrier/profile, not existence of an `IsTravelingWave`.
-/

theorem logistic_profile_bound_neg_speed (p : CMParams)
    (_hα : p.α ≤ p.m + p.γ - 1) (_hχ : p.χ ≤ 0)
    (c : ℝ) (hc : cStarLower p < c) :
    ∃ F : LogisticProfileFacts (kappa c),
      F.U = logisticProfile (kappa c) ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < max 1 (Real.exp (-kappa c * x))) := by
  have hc2 : 2 < c := lt_of_le_of_lt (cStarLower_ge_two p) hc
  exact logisticProfile_facts_with_exp_bound (kappa_pos_of_two_lt hc2)

theorem logistic_profile_bound_small_pos_speed (p : CMParams)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1 / 2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ F : LogisticProfileFacts (kappa c),
      F.U = logisticProfile (kappa c) ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < max 1 (Real.exp (-kappa c * x))) := by
  exact logistic_profile_small_pos_facts p hα hχ_nn hχ_small c hc

end
