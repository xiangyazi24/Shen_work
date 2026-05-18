/-
  ShenWork/StabilityUniqueness.lean
  Section 5: Stability and uniqueness of traveling waves.
-/
import ShenWork.Defs
import ShenWork.Preliminary
import ShenWork.PDE.TravelingWaveConstruction

open Filter Topology

noncomputable section

/-!
The paper-level stability and uniqueness theorems are not currently formalized
as Lean theorems.  This file only records explicit profile facts that are true
for the logistic barrier profile.
-/

theorem logistic_profile_small_pos_facts (p : CMParams)
    (_hα : p.α = p.m + p.γ - 1)
    (_hχ_nn : 0 ≤ p.χ) (_hχ_small : p.χ < min (1 / 2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ F : LogisticProfileFacts (kappa c),
      F.U = logisticProfile (kappa c) ∧
      (∀ x, 0 < F.U x) ∧
      (∀ x, F.U x < max 1 (Real.exp (-kappa c * x))) := by
  exact logisticProfile_facts_with_exp_bound (kappa_pos_of_two_lt hc)

end
