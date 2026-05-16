/-
  ShenWork/TravelingWaves.lean
  Section 4: Existence of traveling wave solutions.
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

theorem existence_monotone_traveling_wave_neg (p : CMParams)
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0) (c : ℝ) (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ, IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧ (∀ x, U x < max 1 (Real.exp (-kappa c * x))) :=
  cm_tw_exist_neg p hα hχ c hc

theorem existence_traveling_wave_small_pos (p : CMParams)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1/2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ U V : ℝ → ℝ, IsTravelingWave p c U V ∧ (∀ x, 0 < U x) :=
  cm_tw_exist_small_pos p hα hχ_nn hχ_small c hc

end
