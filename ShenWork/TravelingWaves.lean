/-
  ShenWork/TravelingWaves.lean
  Section 4: Existence of traveling wave solutions and proof of Theorem 1.1.
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

variable {p : CMParams} [PDETheory p]

theorem existence_monotone_traveling_wave_neg
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0) (c : ℝ) (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ, IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧ (∀ x, U x < max 1 (Real.exp (-kappa c * x))) :=
  PDETheory.tw_exist_neg hα hχ c hc

theorem existence_traveling_wave_small_pos
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1/2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ U V : ℝ → ℝ, IsTravelingWave p c U V ∧ (∀ x, 0 < U x) :=
  PDETheory.tw_exist_small_pos hα hχ_nn hχ_small c hc

end
