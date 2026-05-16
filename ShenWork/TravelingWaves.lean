/-
  ShenWork/TravelingWaves.lean

  Section 4: Existence of traveling wave solutions and proof of Theorem 1.1.
  - §4.1: Super- and sub-solutions
  - §4.2: Monotone traveling waves with negative sensitivity (Theorem 1.1(1))
  - §4.3: Traveling waves with positive sensitivity (Theorem 1.1(2))
-/
import ShenWork.Defs
import ShenWork.Preliminary

open Filter Topology

noncomputable section

/-! ## Theorem 1.1(1): Existence of monotone traveling waves (χ ≤ 0) -/

/-- Theorem 1.1(1): Assume α ≤ m+γ−1 and χ ≤ 0. For any c > c*_{χ,m,γ},
    there is a monotone traveling wave solution connecting (1,1) and (0,0)
    with speed c, satisfying:
    - 0 < U*(x) < max{1, e^{-κx}}
    - U*_x(x) ≤ 0, V*_x(x) ≤ 0
    - Exponential decay rate at +∞. -/
theorem existence_monotone_traveling_wave_neg (p : CMParams)
    (hα : p.α ≤ p.m + p.γ - 1) (hχ : p.χ ≤ 0) (c : ℝ)
    (hc : cStarLower p < c) :
    ∃ U V : ℝ → ℝ,
      IsMonotoneTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x < max 1 (Real.exp (-kappa c * x))) ∧
      -- Exponential decay: for κ < κ₁ < min{(1+α)κ, mκ+1/2, 1},
      -- lim_{x→∞} e^{(κ₁−κ)x} (U*(x)/e^{-κx} − 1) = 0
      (∀ κ₁, kappa c < κ₁ → κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1/2) 1) →
        Tendsto (fun x => Real.exp ((κ₁ - kappa c) * x) * (U x / Real.exp (-kappa c * x) - 1))
          atTop (𝓝 0)) := by
  sorry

/-! ## Theorem 1.1(2): Existence of traveling waves (small positive χ) -/

/-- Theorem 1.1(2): Assume α = m+γ−1 and 0 ≤ χ < min{1/2, χ*}.
    For any c > 2, there is a traveling wave solution connecting (1,1) and (0,0)
    with 0 < U*(x) < min{(1/(1−χ))^{1/α}, e^{-κx}}. -/
theorem existence_traveling_wave_small_pos (p : CMParams)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nn : 0 ≤ p.χ) (hχ_small : p.χ < min (1/2) (chiStar p))
    (c : ℝ) (hc : 2 < c) :
    ∃ U V : ℝ → ℝ,
      IsTravelingWave p c U V ∧
      (∀ x, 0 < U x) ∧
      (∀ x, U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-kappa c * x))) := by
  sorry

end
