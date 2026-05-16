/-
  ShenWork/TravelingWaves.lean

  Section 4: Existence of traveling wave solutions and proof of Theorem 1.1.
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

/-! ## Theorem 1.1(1): Existence of monotone traveling waves (χ ≤ 0) -/

theorem existence_monotone_traveling_wave_neg (p : CMParams)
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0) (c : ℝ)
    (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x < max 1 (Real.exp (-kappa c * x))) ∧
      (∀ κ₁, kappa c < κ₁ →
        κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1/2) 1) →
        Tendsto (fun x => Real.exp ((κ₁ - kappa c) * x) *
          (U x / Real.exp (-kappa c * x) - 1)) atTop (𝓝 0)) :=
  cm_tw_exist_neg p hα hχ c hc

/-! ## Theorem 1.1(2): Existence of traveling waves (small positive χ) -/

theorem existence_traveling_wave_small_pos (p : CMParams)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1/2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-kappa c * x))) :=
  cm_tw_exist_small_pos p hα hχ_nn hχ_small c hc

end
