/-
  ShenWork/StabilityUniqueness.lean
  Section 5: Stability and uniqueness of traveling waves.
-/
import ShenWork.Defs
import ShenWork.Preliminary
import ShenWork.PDE.TravelingWaveConstruction

open Filter Topology

noncomputable section

theorem stability_traveling_wave (p : CMParams)
    (hparam : (p.χ < 0 ∧ p.α ≤ p.m + p.γ - 1) ∨
              (0 ≤ p.χ ∧ p.χ < chiStar p ∧ p.α = p.m + p.γ - 1))
    (c : ℝ) (hc : cStarStar p < c)
    (U V : ℝ → ℝ) (hTW : IsTravelingWave p c U V)
    (hU_diff : ContDiff ℝ 2 U) (hV_diff : ContDiff ℝ 2 V)
    (u₀ : ℝ → ℝ) (hu₀_nn : ∀ x, 0 ≤ u₀ x) :
    ∃ u v : ℝ → ℝ → ℝ,
      IsGlobalClassicalSolution p u v ∧
      (∀ ε > 0, ∃ T, ∀ t x, T ≤ t → |u t x - U (x - c * t)| < ε) :=
  cm_tw_stability p hparam c hc U V hTW hU_diff hV_diff u₀ hu₀_nn

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
