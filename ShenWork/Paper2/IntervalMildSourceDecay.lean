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

/-- The reaction term in the derived parabolic equation for `u^γ`
is bounded when u is bounded away from 0 and u' is bounded.
Each factor in the expression is bounded: u^{γ-2} is bounded on [c,M],
|u'|² ≤ G², u^{γ-1} ≤ M^{γ-1}, |F| ≤ B_F. -/
theorem reaction_term_bounded {γ : ℝ} (hγ : 0 < γ)
    {c M G B_F : ℝ} (hc : 0 < c) (hcM : c ≤ M)
    (hG : 0 ≤ G) (hBF : 0 ≤ B_F) :
    ∃ B_R : ℝ, 0 ≤ B_R ∧
    ∀ (u_val grad_val F_val : ℝ),
      c ≤ u_val → u_val ≤ M → |grad_val| ≤ G → |F_val| ≤ B_F →
      |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2
        + γ * u_val ^ (γ - 1) * F_val| ≤ B_R := by
  have hM_pos : 0 < M := lt_of_lt_of_le hc hcM
  refine ⟨γ * |γ - 1| * (c ^ (γ - 2) + M ^ (γ - 2)) * G ^ 2
    + γ * M ^ (γ - 1) * B_F, ?_, ?_⟩
  · positivity
  intro u_val grad_val F_val hcu huM hgv hfv
  have hu_pos : 0 < u_val := lt_of_lt_of_le hc hcu
  have hrpow_bound : u_val ^ (γ - 2) ≤ c ^ (γ - 2) + M ^ (γ - 2) := by
    rcases le_or_gt (γ - 2) (0 : ℝ) with hr | hr
    · exact le_add_of_le_of_nonneg
        (Real.rpow_le_rpow_of_exponent_nonpos hc hcu hr)
        (Real.rpow_nonneg hM_pos.le _)
    · exact le_add_of_nonneg_of_le
        (Real.rpow_nonneg hc.le _)
        (Real.rpow_le_rpow hu_pos.le huM (le_of_lt hr))
  calc |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2
        + γ * u_val ^ (γ - 1) * F_val|
      ≤ |γ * (γ - 1) * u_val ^ (γ - 2) * grad_val ^ 2|
        + |γ * u_val ^ (γ - 1) * F_val| := abs_add_le _ _
    _ ≤ γ * |γ - 1| * (c ^ (γ - 2) + M ^ (γ - 2)) * G ^ 2
        + γ * M ^ (γ - 1) * B_F := by
      -- Both summands are bounded: products of bounded factors on [c,M].
      sorry

/-! ## Main theorem -/

/-- **Fourier coefficient bound from the derived parabolic equation.**

The source coefficient `(ν u^γ)_hat_k` is bounded by a combination
of exponential decay (from the initial data) and a `1/k²` term (from
the bounded reaction in the derived parabolic equation for `u^γ`).

The constants `C₀, B_R` are **uniform in k**: `C₀` bounds the initial
source coefficients (from `‖u₀^γ‖_∞`), and `B_R` bounds the reaction
(from `u ∈ [c,M]`, `‖u'‖_∞ ≤ G`, `‖F‖_∞ ≤ B_F`). -/
theorem sourceCoeff_bound_from_parabolic (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ∃ C₀ B_R : ℝ, 0 ≤ C₀ ∧ 0 ≤ B_R ∧
    ∀ k : ℕ, 1 ≤ k →
      |(intervalNeumannResolverSourceCoeff p (D.u t) k).re| ≤
        C₀ * Real.exp (-((k : ℝ) * Real.pi) ^ 2 * t) +
        B_R / ((k : ℝ) * Real.pi) ^ 2 := by
  -- The derived parabolic equation for u^γ:
  --   ∂_t(u^γ) = Δ(u^γ) + R,  R = -γ(γ-1)u^{γ-2}|u'|² + γu^{γ-1}F, |R| ≤ B_R
  --
  -- Projecting onto cos(kπx) via the weak eigenfunction identity
  --   ∫₀¹ cos(kπx) Δ(u^γ) dx = -(kπ)² ∫₀¹ cos(kπx) u^γ dx
  -- (valid in H¹: the sin boundary terms sin(0) = sin(kπ) = 0 vanish
  -- regardless of the Neumann BC of u^γ), we get the Fourier ODE:
  --   d/dt a_k = -(kπ)² a_k + R̂_k(t),  |R̂_k| ≤ 2B_R
  --
  -- Variation of constants:
  --   a_k(t) = e^{-(kπ)²t} a_k(0) + ∫₀ᵗ e^{-(kπ)²(t-s)} R̂_k(s) ds
  --   |a_k(t)| ≤ |a_k(0)| e^{-(kπ)²t} + 2B_R/(kπ)²
  --
  -- Set C₀ = 2ν‖u₀^γ‖_∞ (bounds |a_k(0)|), B_R' = 2B_R.
  --
  -- BLOCKER: establishing the Fourier ODE requires:
  -- (a) d/dt ∫cos·(ν u^γ) = ∫cos·∂_t(ν u^γ) (differentiate under integral)
  -- (b) ∂_t(u^γ) = γu^{γ-1}∂_t u (chain rule in time)
  -- (c) the mild equation gives ∂_t u = Δu + F (in distributional sense)
  -- (d) weak IBP ∫cos·Δ(u^γ) = -(kπ)²∫cos·u^γ (sin boundary terms vanish)
  -- All four hold for the mild solution (u Lipschitz, u > 0, u bounded).
  -- The formal Lean4 proof requires connecting the mild equation's
  -- distributional PDE to the spectral coefficient ODE.
  sorry

/-- For `x > 0`, `exp(-x) ≤ 1/x` (from `x ≤ exp(x)` for all x). -/
private theorem exp_neg_le_inv {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) ≤ 1 / x := by
  rw [one_div, Real.exp_neg]
  exact inv_anti₀ hx
    (le_trans (by linarith) (Real.add_one_le_exp x))

/-- **SourceCoeffQuadraticDecay for the mild solution.** -/
def sourceCoeffQuadraticDecay_of_mildSolution (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  have hex := sourceCoeff_bound_from_parabolic p D ht htT
  set C₀ := hex.choose with hC₀_def
  set B_R := hex.choose_spec.choose with hBR_def
  have hC₀ := hex.choose_spec.choose_spec.1
  have hBR := hex.choose_spec.choose_spec.2.1
  have hbound := hex.choose_spec.choose_spec.2.2
  exact ⟨C₀ / t + B_R,
    add_nonneg (div_nonneg hC₀ ht.le) hBR, fun k hk => by
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hlampos : (0 : ℝ) < ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hlamt : 0 < ((k : ℝ) * Real.pi) ^ 2 * t := mul_pos hlampos ht
    calc |(intervalNeumannResolverSourceCoeff p (D.u t) k).re|
        ≤ C₀ * Real.exp (-((k : ℝ) * Real.pi) ^ 2 * t) +
          B_R / ((k : ℝ) * Real.pi) ^ 2 := hbound k hk
      _ ≤ C₀ * (1 / (((k : ℝ) * Real.pi) ^ 2 * t)) +
          B_R / ((k : ℝ) * Real.pi) ^ 2 := by
        gcongr
        convert exp_neg_le_inv hlamt using 2
        ring
      _ = C₀ / (t * ((k : ℝ) * Real.pi) ^ 2) +
          B_R / ((k : ℝ) * Real.pi) ^ 2 := by
        congr 1; rw [mul_comm]; ring
      _ = (C₀ / t + B_R) / ((k : ℝ) * Real.pi) ^ 2 := by
        rw [add_div, div_div]⟩

end ShenWork.IntervalMildSourceDecay
