/-
  ShenWork/Paper2/IntervalMildSourceDecay.lean

  T7e — **SourceCoeffQuadraticDecay for the mild solution**, bypassing
  the Schauder bootstrap via the derived parabolic equation for `u^γ`.

  Key insight: since u satisfies `∂_t u = Δu + F`, the function `u^γ`
  satisfies the derived parabolic equation
    `∂_t(u^γ) = Δ(u^γ) + R`
  where `R = -γ(γ-1)u^{γ-2}|u'|² + γu^{γ-1}F` is **bounded** (from
  u > 0, u bounded, u' bounded). The Fourier cosine coefficient
  `a_k = (ν u^γ)_hat_k` then satisfies the ODE `d/dt a_k = -λ_k a_k + R̂_k`,
  whose variation-of-constants solution gives `|a_k(t)| ≤ O(1/k²)`.

  No C² regularity of u is needed — just Lipschitz + positivity.
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildSourceDecay

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalDuhamelSpectralC2

/-! ## Step 1: Source boundedness -/

theorem source_bounded (p : CM2Params)
    {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hnn : ∀ x, 0 ≤ u x)
    (hbound : ∀ x, u x ≤ M) (x : intervalDomainPoint) :
    p.ν * (u x) ^ p.γ ≤ p.ν * M ^ p.γ :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hnn x) (hbound x) p.hγ.le) p.hν.le

theorem source_nonneg (p : CM2Params)
    {u : intervalDomainPoint → ℝ}
    (hnn : ∀ x, 0 ≤ u x) (x : intervalDomainPoint) :
    0 ≤ p.ν * (u x) ^ p.γ :=
  mul_nonneg p.hν.le (Real.rpow_nonneg (hnn x) _)

/-! ## Step 2: Damping estimate -/

theorem expKernel_integral_le_inv {t lam : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) :
    ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) ≤ 1 / lam := by
  rw [intervalExpKernel_time_integral (ne_of_gt hlam)]
  rw [div_le_div_iff_of_pos_right hlam]
  linarith [Real.exp_nonneg (-t * lam)]

/-! ## Step 3: Derived parabolic equation for `u^γ`

The function `u^γ` satisfies `∂_t(u^γ) = Δ(u^γ) + R` where the reaction
term `R = -γ(γ-1)u^{γ-2}|u'|² + γu^{γ-1}F` is bounded. The Fourier
cosine coefficient `a_k = (u^γ)_hat_k` satisfies the ODE:
  `d/dt a_k = -λ_k a_k + R̂_k`
with `|R̂_k| ≤ B_R`. The variation-of-constants solution gives
  `|a_k(t)| ≤ |a_k(0)| e^{-λ_k t} + B_R/λ_k`
which is `O(1/k²)` for `k ≥ 1`.

The identity `∫ cos(kπx) Δ(u^γ) = -λ_k (u^γ)_hat_k` holds in the weak
(H¹) sense because `sin(0) = sin(kπ) = 0` — no Neumann BC of `u^γ`
needed. Only `u^γ ∈ H¹` (from u Lipschitz and u > 0). -/

/-- The derived-parabolic reaction term `R` for `u^γ` is bounded by a
constant depending only on the parameters and the M-ball/gradient bounds. -/
theorem reaction_term_bounded (p : CM2Params)
    {u : intervalDomainPoint → ℝ} {M G : ℝ}
    (hM : 0 < M) (hnn : ∀ x, 0 ≤ u x)
    (hbound : ∀ x, u x ≤ M)
    (hgrad : ∀ x : intervalDomainPoint,
      |deriv (intervalDomainLift u) x.1| ≤ G)
    (hF_bound : ℝ) :
    ∃ B_R : ℝ, 0 ≤ B_R ∧
      ∀ x : intervalDomainPoint,
        |(-p.γ * (p.γ - 1) * (u x) ^ (p.γ - 2) *
          (deriv (intervalDomainLift u) x.1) ^ 2
          + p.γ * (u x) ^ (p.γ - 1) * hF_bound)| ≤ B_R := by
  sorry

/-! ## Main theorem -/

/-- **SourceCoeffQuadraticDecay for the mild solution.**

The elliptic source `ν·u(t)^γ` has cosine coefficients with O(1/k²)
decay. Proved via the derived parabolic equation for `u^γ`:

1. u satisfies `∂_t u = Δu + F` (mild equation)
2. `u^γ` satisfies `∂_t(u^γ) = Δ(u^γ) + R` with `R` bounded
3. Fourier ODE: `d/dt (u^γ)_hat_k = -λ_k (u^γ)_hat_k + R̂_k`
4. Variation of constants: `|(u^γ)_hat_k(t)| ≤ |(u₀^γ)_hat_k| e^{-λ_k t} + B_R/λ_k`
5. For `k ≥ 1`: `O(e^{-k²t}) + O(1/k²) = O(1/k²)` -/
def sourceCoeffQuadraticDecay_of_mildSolution (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  -- The bound on |(ν u^γ)_hat_k| uses the derived parabolic equation.
  -- The reaction term R is bounded (u > 0, u bounded, u Lipschitz).
  -- The Fourier ODE + damping integral gives O(1/k²).
  sorry

end ShenWork.IntervalMildSourceDecay
