/-
  ShenWork/TravelingWaves.lean
  Section 4: Existence of traveling wave solutions.
-/
import ShenWork.Defs
import ShenWork.Preliminary
import ShenWork.StabilityUniqueness

open Filter Topology

noncomputable section

theorem existence_monotone_traveling_wave_neg (p : CMParams)
    (_hα : p.α ≤ p.m + p.γ - 1) (_hχ : p.χ ≤ 0)
    (c : ℝ) (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ, IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧ (∀ x, U x < max 1 (Real.exp (-kappa c * x))) := by
  have hm_pos : 0 < p.m := lt_of_lt_of_le one_pos p.hm
  have htwo_le_m_inv_add_m : 2 ≤ 1 / p.m + p.m := by
    have hsq : 0 ≤ (p.m - 1) ^ 2 := sq_nonneg (p.m - 1)
    field_simp [ne_of_gt hm_pos]
    nlinarith
  have htwo_le_cStar : 2 ≤ cStarLower p :=
    le_trans htwo_le_m_inv_add_m (le_max_left _ _)
  have hc2 : 2 < c := lt_of_le_of_lt htwo_le_cStar hc
  have hc0 : 0 < c := by linarith
  have hκ : 0 < kappa c := by
    simp only [kappa]
    have hrad_pos : 0 < c ^ 2 - 4 := by nlinarith
    have hsqrt_lt : Real.sqrt (c ^ 2 - 4) < c := by
      have hsq : (Real.sqrt (c ^ 2 - 4)) ^ 2 = c ^ 2 - 4 := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg (c ^ 2 - 4)]
    linarith
  exact traveling_wave_exists_with_exp_bound p c hc0 hκ

theorem existence_traveling_wave_small_pos (p : CMParams)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1/2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ U V : ℝ → ℝ, IsTravelingWave p c U V ∧ (∀ x, 0 < U x) := by
  exact existence_tw_small_pos p hα hχ_nn hχ_small c hc

end
