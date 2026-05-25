import ShenWork.PDE.IntervalDomainEllipticResolver
import ShenWork.PDE.HeatKernelGradientEstimates
import ShenWork.PDE.IntervalDomainExistence
import Mathlib.Analysis.PSeries

/-!
# Concrete interval-domain Neumann elliptic resolver `R`

This file builds the concrete elliptic Neumann resolver `R` used downstream by
the coupled fixed-point local-existence proof in
`ShenWork.PDE.IntervalDomainExistence` (where `R` appears with signature
`R : (intervalDomainPoint → ℝ) → intervalDomainPoint → ℝ`).

`R u` is the solution `v` of the elliptic Neumann problem

  `−Δ v + p.μ · v = p.ν · u ^ p.γ`   with Neumann boundary conditions,

built spectrally in the cosine basis `1, cos(πx), cos(2πx), …`.  Writing
`â_k` for the `k`-th Neumann cosine coefficient of the source `p.ν · u ^ p.γ`
and `λ_k = unitIntervalNeumannSpectrum.eigenvalue k = k² π²` for the Neumann
eigenvalue, the `k`-th cosine coefficient of `v = R u` is

  `v̂_k = (p.μ + λ_k)⁻¹ · â_k`.

This is *exactly* the diagonal shifted resolvent
`shiftedNeumannResolventCoeff 0 (p.μ : ℂ)` from
`ShenWork.PDE.ResolventEstimate` (with shift `ω = 0` and spectral parameter
`z = p.μ`, since `shiftedNeumannEigenvalue 0 k = λ_k`).  Consequently the L²
Lipschitz estimate for `R` reduces, at the coefficient level, to the already
proven `shiftedNeumannResolventCoeff_l2_norm_lipschitz`.

## What is proved here (0 sorry, 0 axiom)

* `intervalNeumannResolverCoeff` — the resolved cosine coefficient sequence
  `v̂` (complex), and `intervalNeumannResolverR` — the real-valued
  reconstruction `R u : intervalDomainPoint → ℝ` with the demanded signature.
* `intervalNeumannResolverCoeff_elliptic` — the **coefficient-form elliptic
  equation**: `(p.μ + λ_k) · v̂_k = â_k` for every mode `k`.  This is the weak
  / spectral statement of `−Δ v + p.μ v = (source)` that the cosine machinery
  supports (the differential form is recovered mode-by-mode because each
  `cos(kπx)` is a Neumann eigenfunction with `−Δ cos(kπx) = λ_k cos(kπx)`).
* `intervalNeumannResolverCoeff_l2_norm_lipschitz` — the L² Lipschitz bound
  `‖v̂₁ − v̂₂‖₂ ≤ (1/μ) · ‖â₁ − â₂‖₂`, with the resolvent constant `1/p.μ`,
  obtained from `shiftedNeumannResolventCoeff_l2_norm_lipschitz`.

## Sup / pointwise Lipschitz bound (now proved, 0 sorry, 0 axiom)

* `intervalNeumannResolverWeight_sq_summable` — the diagonal resolvent
  multiplier sequence `wₖ = 1/(p.μ + λ_k)` is `ℓ²` (decay `~ 1/k⁴`), proved by
  comparison with the convergent `p`-series `∑ 1/k⁴`.
* `intervalNeumannResolverR_sup_lipschitz` — the bridge from the coefficient
  `ℓ²` Lipschitz bound to a *pointwise / sup* Lipschitz bound on
  `R u : intervalDomainPoint → ℝ`:
  `|R u₁ x − R u₂ x| ≤ sqrt(∑ₖ 1/(p.μ+λ_k)²) · coeffL2Norm(â(u₁) − â(u₂))`.
  This is the cosine-series `ℓ² → L^∞` (absolute-convergence / Cauchy–Schwarz)
  embedding, supplied by the repo's
  `real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq`
  (the same analytic ingredient as the heat-kernel `L² → L^∞` smoothing).  The
  factoring `dₖ·cos(kπx) = ((p.μ+λ_k)dₖ)·(cos(kπx)/(p.μ+λ_k))` turns the first
  factor into the *source* real-part difference (via the coefficient-form
  elliptic identity) and the second into the `ℓ²`-summable weight·cosine.
-/

noncomputable section

open ShenWork.PDE.ResolventEstimate
open ShenWork.Paper3 ShenWork.HeatKernelGradientEstimates ShenWork.IntervalDomain
open scoped BigOperators

namespace ShenWork.PDE

/-- The `k`-th Neumann cosine coefficient of the elliptic source
`p.ν · u ^ p.γ`, viewed as a complex number.  We use the normalized Neumann
cosine coefficient projection `unitIntervalNeumannCosineCoeff` applied to the
lift of `p.ν · u ^ p.γ` to `ℝ → ℂ`. -/
def intervalNeumannResolverSourceCoeff
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  ((unitIntervalNeumannCosineCoeff
      (fun x : ℝ =>
        ((p.ν * intervalDomainLift u x ^ p.γ : ℝ) : ℂ)) k : ℝ) : ℂ)

/-- The resolved cosine coefficient `v̂_k = (p.μ + λ_k)⁻¹ · â_k` of `R u`.

This is the diagonal shifted Neumann resolvent with shift `ω = 0` and spectral
parameter `z = p.μ`, applied to the source coefficient sequence
`intervalNeumannResolverSourceCoeff p u`.  Recall
`shiftedNeumannEigenvalue 0 k = unitIntervalNeumannSpectrum.eigenvalue k = λ_k`,
so the multiplier is `(p.μ + λ_k)⁻¹`. -/
def intervalNeumannResolverCoeff
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  shiftedNeumannResolventCoeff 0 (p.μ : ℂ)
    (intervalNeumannResolverSourceCoeff p u) k

/-- The concrete interval Neumann elliptic resolver `R`.

`R u : intervalDomainPoint → ℝ` is the spectral reconstruction of the elliptic
solution from its resolved cosine coefficients,
`(R u)(x) = ∑' k, (v̂_k).re · cos(k π x)`.  The real part is taken because the
source `p.ν · u ^ p.γ` is real, so all coefficients are real and `R u` is a
real function; using `.re` keeps the codomain `ℝ` as required by the
downstream signature. -/
def intervalNeumannResolverR
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun x =>
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        unitIntervalCosineMode k x.1

/-! ### The coefficient-form elliptic equation -/

/-- `shiftedNeumannEigenvalue 0 k` is the bare Neumann eigenvalue `λ_k`. -/
lemma shiftedNeumannEigenvalue_zero (k : ℕ) :
    shiftedNeumannEigenvalue 0 k = unitIntervalNeumannSpectrum.eigenvalue k := by
  simp [shiftedNeumannEigenvalue]

/-- The denominator `p.μ + λ_k` is nonzero (indeed positive as a real, hence
nonzero as a complex number), so the resolvent multiplier is genuinely
invertible. -/
lemma intervalNeumannResolver_denominator_ne_zero
    (p : CM2Params) (k : ℕ) :
    ((p.μ : ℂ) + (shiftedNeumannEigenvalue 0 k : ℂ)) ≠ 0 := by
  have hpos : 0 < p.μ + shiftedNeumannEigenvalue 0 k := by
    have hlam : 0 ≤ shiftedNeumannEigenvalue 0 k :=
      shiftedNeumannEigenvalue_nonneg (le_refl 0) k
    linarith [p.hμ]
  have hre : ((p.μ : ℂ) + (shiftedNeumannEigenvalue 0 k : ℂ)) =
      ((p.μ + shiftedNeumannEigenvalue 0 k : ℝ) : ℂ) := by
    push_cast; ring
  rw [hre]
  exact_mod_cast (ne_of_gt hpos)

/-- **Coefficient-form elliptic equation.**  For every cosine mode `k`,

  `(p.μ + λ_k) · v̂_k = â_k`,

where `v̂_k = intervalNeumannResolverCoeff p u k` and
`â_k = intervalNeumannResolverSourceCoeff p u k`.  Since `cos(kπx)` is the
`k`-th Neumann eigenfunction with `−Δ cos(kπx) = λ_k cos(kπx)`, this is exactly
the spectral (weak) statement of `−Δ (R u) + p.μ (R u) = p.ν u^γ`. -/
theorem intervalNeumannResolverCoeff_elliptic
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) *
        intervalNeumannResolverCoeff p u k =
      intervalNeumannResolverSourceCoeff p u k := by
  have hne := intervalNeumannResolver_denominator_ne_zero p k
  unfold intervalNeumannResolverCoeff shiftedNeumannResolventCoeff
  rw [← shiftedNeumannEigenvalue_zero k]
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-! ### L² Lipschitz estimate for the resolver coefficients -/

/-- `p.μ`, as a complex spectral parameter, is nonzero and has nonnegative real
part, so the resolvent sector hypotheses are met with `z = p.μ`, `ω = 0`. -/
lemma intervalNeumannResolver_param_sector (p : CM2Params) :
    (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (p.μ : ℂ).re ∧ (p.μ : ℂ) ≠ 0 := by
  refine ⟨le_refl 0, ?_, ?_⟩
  · simp [Complex.ofReal_re]; exact p.hμ.le
  · exact_mod_cast (ne_of_gt p.hμ)

/-- `‖(p.μ : ℂ)‖ = p.μ`. -/
lemma norm_param_eq (p : CM2Params) : ‖(p.μ : ℂ)‖ = p.μ := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos p.hμ]

/-- **L² Lipschitz bound for the resolver coefficient map.**

The resolved-coefficient difference is controlled in coefficient `ℓ²` by the
source-coefficient difference with the resolvent constant `1 / p.μ`:

  `‖v̂(u₁) − v̂(u₂)‖₂ ≤ (1 / p.μ) · ‖â(u₁) − â(u₂)‖₂`.

This is the coefficient-space contraction at the heart of the coupled
fixed-point argument.  It is obtained directly from the already-proven
`shiftedNeumannResolventCoeff_l2_norm_lipschitz`. -/
theorem intervalNeumannResolverCoeff_l2_norm_lipschitz
    (p : CM2Params) (u₁ u₂ : intervalDomainPoint → ℝ)
    (hab : Summable fun k : ℕ =>
      ‖intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k‖ ^ 2) :
    coeffL2Norm
        (fun k : ℕ =>
          intervalNeumannResolverCoeff p u₁ k -
            intervalNeumannResolverCoeff p u₂ k) ≤
      ((1 : ℝ) / p.μ) *
        coeffL2Norm
          (fun k : ℕ =>
            intervalNeumannResolverSourceCoeff p u₁ k -
              intervalNeumannResolverSourceCoeff p u₂ k) := by
  obtain ⟨hω, hzre, hz⟩ := intervalNeumannResolver_param_sector p
  have hbound :=
    shiftedNeumannResolventCoeff_l2_norm_lipschitz
      (ω := (0 : ℝ)) hω (z := (p.μ : ℂ)) hzre hz
      (a := intervalNeumannResolverSourceCoeff p u₁)
      (b := intervalNeumannResolverSourceCoeff p u₂) hab
  -- Rewrite the resolvent multiplier constant `1 / ‖p.μ‖` as `1 / p.μ`.
  rw [norm_param_eq] at hbound
  -- The two `intervalNeumannResolverCoeff` are exactly the
  -- `shiftedNeumannResolventCoeff` applied to the source coefficients.
  simpa [intervalNeumannResolverCoeff] using hbound

/-! ### Sup / pointwise Lipschitz bound for the resolver `R`

The bridge from the coefficient-`ℓ²` Lipschitz bound to a pointwise/sup
Lipschitz bound.  The analytic ingredient is the cosine-series `ℓ² → L^∞`
absolute-convergence (Cauchy–Schwarz) step, supplied here by the repo's
`real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq`. -/

/-- The real "resolver weight" `wₖ = 1 / (p.μ + λ_k)`.  This is the modulus of
the diagonal resolvent multiplier (all data here are real). -/
def intervalNeumannResolverWeight (p : CM2Params) (k : ℕ) : ℝ :=
  1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)

/-- The denominator `p.μ + λ_k` is strictly positive. -/
lemma intervalNeumannResolver_denom_pos (p : CM2Params) (k : ℕ) :
    0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
  have hlam : 0 ≤ unitIntervalNeumannSpectrum.eigenvalue k :=
    unitIntervalNeumannSpectrum_eigenvalue_nonneg k
  linarith [p.hμ]

/-- The resolver weight is nonnegative. -/
lemma intervalNeumannResolverWeight_nonneg (p : CM2Params) (k : ℕ) :
    0 ≤ intervalNeumannResolverWeight p k :=
  le_of_lt (by
    rw [intervalNeumannResolverWeight]
    exact div_pos one_pos (intervalNeumannResolver_denom_pos p k))

/-- **The squared resolver weight is summable** (decay `~ 1/k⁴`).  This is the
genuine `ℓ²`-convergence of the multiplier sequence that powers the
absolute-convergence embedding; proved by comparison with the convergent
`p`-series `∑ 1/k⁴`. -/
lemma intervalNeumannResolverWeight_sq_summable (p : CM2Params) :
    Summable fun k : ℕ => (intervalNeumannResolverWeight p k) ^ 2 := by
  -- It suffices to be summable after dropping the `k = 0` term.
  rw [← summable_nat_add_iff 1]
  -- Eigenvalue identity: `λ_k = k² π²`.
  have hlam : ∀ k : ℕ,
      unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 := by
    intro k
    rfl
  -- Comparison majorant: `(1/π⁴) · 1/(k+1)⁴`.
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmaj : Summable fun k : ℕ =>
      (1 / Real.pi ^ 4) * (1 / ((k : ℝ) + 1) ^ 4) := by
    have hp4 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 4 := by
      have := (Real.summable_one_div_nat_pow (p := 4)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 4) 1).2 this
    exact hp4.mul_left _
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_ hmaj
  intro k
  -- Bound term `(k+1)` by the majorant.
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1) :=
    intervalNeumannResolver_denom_pos p (k + 1)
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- Lower bound the denominator by `((k+1) π)²`.
  have hlow : ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 ≤
      p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1) := by
    rw [hlam (k + 1)]
    push_cast
    nlinarith [p.hμ.le, sq_nonneg ((k : ℝ) + 1), sq_nonneg Real.pi]
  have hbase_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by positivity
  have hweight :
      (intervalNeumannResolverWeight p (k + 1)) ^ 2 ≤
        (1 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2)) ^ 2 := by
    rw [intervalNeumannResolverWeight]
    apply sq_le_sq'
    · have : (0:ℝ) ≤ 1 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) := by positivity
      have h2 : (0:ℝ) ≤ 1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) := by
        positivity
      linarith
    · exact one_div_le_one_div_of_le hbase_pos hlow
  refine hweight.trans (le_of_eq ?_)
  field_simp

/-- The real-part source-coefficient `ℓ²` summability upgrades to full
complex-norm `ℓ²` summability of the source-difference, because the source
coefficients are real (their imaginary part is `0`), so `‖A k‖² = (A k).re²`. -/
lemma intervalNeumannResolverR_source_l2_summable
    (p : CM2Params) (u₁ u₂ : intervalDomainPoint → ℝ)
    (hsrc : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2) :
    Summable fun k : ℕ =>
      ‖intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k‖ ^ 2 := by
  refine hsrc.congr ?_
  intro k
  -- The source coefficients are real (`ofReal`), so the difference is real.
  have him : (intervalNeumannResolverSourceCoeff p u₁ k -
      intervalNeumannResolverSourceCoeff p u₂ k).im = 0 := by
    simp [intervalNeumannResolverSourceCoeff, Complex.sub_im]
  rw [Complex.sq_norm, Complex.normSq_apply, him]
  ring

/-- **Sup / pointwise Lipschitz bound for the elliptic resolver `R`.**

For every interval point `x`,

  `|R u₁ x − R u₂ x| ≤ C · coeffL2Norm(â(u₁) − â(u₂))`,

with constant `C = sqrt (∑ₖ 1/(p.μ + λ_k)²)` — the `ℓ²` norm of the diagonal
resolvent multiplier sequence — and `â = intervalNeumannResolverSourceCoeff`
the cosine coefficients of the source `p.ν · u ^ p.γ`.

The proof is the cosine-series `ℓ² → L^∞` Cauchy–Schwarz embedding: writing the
`k`-th coefficient difference as `dₖ = (v̂₁,k − v̂₂,k).re` and factoring
`dₖ · cos(kπx) = (dₖ · (p.μ + λ_k)) · (cos(kπx) / (p.μ + λ_k))`, the first
factor equals the real part of the *source* coefficient difference (the
coefficient-form elliptic identity), whose `ℓ²` energy is bounded by
`coeffL2Energy(â diff)`, while the second factor is `ℓ²`-summable with energy
`≤ ∑ₖ 1/(p.μ+λ_k)²` (the resolver-weight summability above). -/
theorem intervalNeumannResolverR_sup_lipschitz
    (p : CM2Params) (u₁ u₂ : intervalDomainPoint → ℝ)
    (hsrc : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2)
    (x : intervalDomainPoint)
    (hsum₁ : Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u₁ k).re * unitIntervalCosineMode k x.1)
    (hsum₂ : Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u₂ k).re * unitIntervalCosineMode k x.1) :
    |intervalNeumannResolverR p u₁ x - intervalNeumannResolverR p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
        coeffL2Norm
          (fun k : ℕ =>
            intervalNeumannResolverSourceCoeff p u₁ k -
              intervalNeumannResolverSourceCoeff p u₂ k) := by
  -- Abbreviations.
  set D : ℕ → ℂ := fun k =>
    intervalNeumannResolverCoeff p u₁ k - intervalNeumannResolverCoeff p u₂ k with hD
  set A : ℕ → ℂ := fun k =>
    intervalNeumannResolverSourceCoeff p u₁ k -
      intervalNeumannResolverSourceCoeff p u₂ k with hA
  -- The coefficient-form elliptic identity, subtracted across `u₁, u₂`:
  --   (p.μ + λ_k) · D k = A k.
  have hell : ∀ k : ℕ,
      ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) * D k = A k := by
    intro k
    have h1 := intervalNeumannResolverCoeff_elliptic p u₁ k
    have h2 := intervalNeumannResolverCoeff_elliptic p u₂ k
    simp only [hD, hA]
    rw [mul_sub, h1, h2]
  -- Real-part version of the identity: `(p.μ + λ_k) · (D k).re = (A k).re`.
  have hellRe : ∀ k : ℕ,
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) * (D k).re = (A k).re := by
    intro k
    have hcast :
        ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast; ring
    have hk := congrArg Complex.re (hell k)
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  -- The cosine value factor: `mₖ = cos(kπx) / (p.μ + λ_k)`.
  set m : ℕ → ℝ := fun k =>
    unitIntervalCosineMode k x.1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) with hm
  -- The "energy" factor: `eₖ = (D k).re · (p.μ + λ_k) = (A k).re`.
  set e : ℕ → ℝ := fun k => (A k).re with he
  -- Pointwise rewriting of the summand.
  have hterm : ∀ k : ℕ,
      (D k).re * unitIntervalCosineMode k x.1 = e k * m k := by
    intro k
    have hden : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ≠ 0 :=
      ne_of_gt (intervalNeumannResolver_denom_pos p k)
    simp only [he, hm, ← hellRe k]
    field_simp
  -- Summability of `eₖ²` (= source real-part energy) and `mₖ²` (weight energy).
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := hsrc
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    have hw := intervalNeumannResolverWeight_sq_summable p
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_ hw
    intro k
    have hcos : (unitIntervalCosineMode k x.1) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
    have hweq : (intervalNeumannResolverWeight p k) ^ 2 =
        1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [intervalNeumannResolverWeight]; field_simp
    rw [hweq, hm, div_pow]
    gcongr
  -- The product `eₖ·mₖ` is `ℓ¹`-summable (Cauchy–Schwarz domination).
  have hprod_sum : Summable fun k : ℕ => e k * m k := by
    apply Summable.of_norm
    have hdom : ∀ k : ℕ, ‖e k * m k‖ ≤ (1/2) * (e k)^2 + (1/2) * (m k)^2 := by
      intro k
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (e k), sq_abs (m k), sq_nonneg (|e k| - |m k|)]
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom
      ((he_sq.mul_left (1/2)).add (hm_sq.mul_left (1/2)))
  -- `R u₁ x − R u₂ x = ∑' k, (D k).re · cos(kπx) = ∑' k, e k · m k`.
  have hsum_eq :
      intervalNeumannResolverR p u₁ x - intervalNeumannResolverR p u₂ x =
        ∑' k : ℕ, e k * m k := by
    simp only [intervalNeumannResolverR]
    rw [← hsum₁.tsum_sub hsum₂]
    refine tsum_congr ?_
    intro k
    rw [← hterm k]
    simp only [hD, Complex.sub_re]
    ring
  -- Cauchy–Schwarz.
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) * Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  rw [hsum_eq]
  -- Bound `sqrt(∑ e²) ≤ coeffL2Norm A` and `sqrt(∑ m²) ≤ sqrt(∑ weight²)`.
  have heE : Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_ (intervalNeumannResolverR_source_l2_summable p u₁ u₂ hsrc)
    intro k
    have : (e k) ^ 2 = (A k).re * (A k).re := by rw [he]; ring
    rw [this]
    calc (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW : Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm_sq.tsum_le_tsum ?_ (intervalNeumannResolverWeight_sq_summable p)
    intro k
    have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hcos : (unitIntervalCosineMode k x.1) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
    have hweq : (intervalNeumannResolverWeight p k) ^ 2 =
        1 / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [intervalNeumannResolverWeight]; field_simp
    rw [hweq, hm, div_pow]
    gcongr
  calc |∑' k : ℕ, e k * m k|
      ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) * Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ coeffL2Norm A *
          Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) := by
          exact mul_le_mul heE hmW (Real.sqrt_nonneg _)
            (by rw [coeffL2Norm]; exact Real.sqrt_nonneg _)
    _ = Real.sqrt (∑' k : ℕ, (intervalNeumannResolverWeight p k) ^ 2) *
          coeffL2Norm A := by ring

/-! ### Gradient (spatial-derivative) sup Lipschitz bound for the resolver `R`

The chemotaxis term `u · ∂ₓv / (1 + v)^β` (with `v = R u`) needs control of the
*difference of spatial derivatives* of `R`, not just the values.  Formally,

  `∂ₓ (R u)(x) = ∑' k, (v̂_k).re · ∂ₓ cos(kπx)
              = ∑' k, (v̂_k).re · (−kπ · sin(kπx))`,

using the termwise derivative `unitIntervalCosineMode_hasDerivAt`
(`∂ₓ cos(kπx) = −kπ · sin(kπx)`).  We *define* the gradient as this
termwise-differentiated series — the same modelling choice the repo already
makes for the heat flow, where `unitIntervalCosineHeatGradientValue` is defined
directly as the differentiated series rather than as `deriv` of the value series
(see `ShenWork.PDE.HeatKernelLpEstimates`).  This sidesteps the
interchange-of-`deriv`-and-`tsum` question, which the repo handles separately in
`RegularityBootstrap` under explicit summable-majorant hypotheses.

The derivative-mode weight is `kπ / (p.μ + λ_k)`.  Since `λ_k = k²π²`, for
`k ≥ 1` we have `p.μ + λ_k ≥ k²π²`, hence `(kπ/(p.μ+λ_k))² ≤ 1/(k²π²)`, so the
squared gradient weight is summable by comparison with `∑ 1/k²`.  The same
Cauchy–Schwarz `ℓ² → L^∞` bridge then yields the gradient sup-Lipschitz bound. -/

/-- Spatial derivative of the resolver `R u`, defined as the termwise
differentiated cosine series:
`∂ₓ(R u)(x) = ∑' k, (v̂_k).re · (−kπ · sin(kπx))`. -/
def intervalNeumannResolverRGrad
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    intervalDomainPoint → ℝ :=
  fun x =>
    ∑' k : ℕ,
      (intervalNeumannResolverCoeff p u k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x.1))

/-- The real "gradient resolver weight" `wₖ = kπ / (p.μ + λ_k)`.  This is the
modulus of the diagonal derivative-mode multiplier. -/
def intervalNeumannResolverGradWeight (p : CM2Params) (k : ℕ) : ℝ :=
  ((k : ℝ) * Real.pi) / (p.μ + unitIntervalNeumannSpectrum.eigenvalue k)

/-- The gradient resolver weight is nonnegative. -/
lemma intervalNeumannResolverGradWeight_nonneg (p : CM2Params) (k : ℕ) :
    0 ≤ intervalNeumannResolverGradWeight p k := by
  rw [intervalNeumannResolverGradWeight]
  apply div_nonneg
  · positivity
  · exact (intervalNeumannResolver_denom_pos p k).le

/-- **The squared gradient resolver weight is summable** (decay `~ 1/k²`).
Proved by comparison with the convergent `p`-series `∑ 1/k²`: for `k ≥ 1`,
`p.μ + λ_k ≥ (kπ)²` so `(kπ/(p.μ+λ_k))² ≤ 1/((kπ)²) ≤ (1/π²)·1/k²`. -/
lemma intervalNeumannResolverGradWeight_sq_summable (p : CM2Params) :
    Summable fun k : ℕ => (intervalNeumannResolverGradWeight p k) ^ 2 := by
  -- It suffices to be summable after dropping the `k = 0` term.
  rw [← summable_nat_add_iff 1]
  -- Eigenvalue identity: `λ_k = k² π²`.
  have hlam : ∀ k : ℕ,
      unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 := by
    intro k; rfl
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Comparison majorant: `(1/π²) · 1/(k+1)²`.
  have hmaj : Summable fun k : ℕ =>
      (1 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left _
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_ hmaj
  intro k
  -- Lower bound the denominator by `((k+1) π)²`.
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1) :=
    intervalNeumannResolver_denom_pos p (k + 1)
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlow : ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 ≤
      p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1) := by
    rw [hlam (k + 1)]; push_cast
    nlinarith [p.hμ.le, sq_nonneg ((k : ℝ) + 1), sq_nonneg Real.pi]
  have hbase_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by positivity
  -- Numerator: `(k+1)·π`.
  have hnum_nonneg : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.pi := by positivity
  -- The squared gradient weight at `k+1`, written as a single fraction.
  have hweq : (intervalNeumannResolverGradWeight p (k + 1)) ^ 2 =
      (((k : ℝ) + 1) * Real.pi) ^ 2 /
        (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) ^ 2 := by
    rw [intervalNeumannResolverGradWeight, div_pow]
    norm_num
  rw [hweq]
  -- `(p.μ+λ)² ≥ ((k+1)²π²)²` from `(k+1)²π² ≤ (p.μ+λ)`.
  have hsq : (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) ^ 2 ≤
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) ^ 2 := by
    have := mul_le_mul hlow hlow hbase_pos.le hden_pos.le
    calc (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) ^ 2
        = (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) *
            (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) := by ring
      _ ≤ (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) *
            (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) := this
      _ = (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) ^ 2 := by ring
  rw [div_le_iff₀ (by positivity)]
  -- Goal: `((k+1)π)² ≤ (1/π²·1/(k+1)²) · (p.μ+λ)²`.
  have hpine : (0 : ℝ) < Real.pi ^ 2 := by positivity
  have hk1ne : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  calc (((k : ℝ) + 1) * Real.pi) ^ 2
      = (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) := by ring
    _ = (1 / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) *
          (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) ^ 2 := by
        field_simp
    _ ≤ (1 / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2)) *
          (p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsq; positivity

/-- **Gradient (spatial-derivative) sup / pointwise Lipschitz bound for the
elliptic resolver `R`.**

For every interval point `x`,

  `|∂ₓ(R u₁) x − ∂ₓ(R u₂) x| ≤ C · coeffL2Norm(â(u₁) − â(u₂))`,

with constant `C = sqrt (∑ₖ (kπ/(p.μ + λ_k))²)` — the `ℓ²` norm of the diagonal
*derivative-mode* multiplier sequence — and `â = intervalNeumannResolverSourceCoeff`.

The proof mirrors `intervalNeumannResolverR_sup_lipschitz`: the `k`-th
coefficient difference `dₖ = (v̂₁,k − v̂₂,k).re` times the derivative mode
`−kπ·sin(kπx)` factors as `(dₖ·(p.μ+λ_k)) · (−kπ·sin(kπx)/(p.μ+λ_k))`; the first
factor is the source real-part difference (coefficient-form elliptic identity),
the second is `ℓ²`-summable with energy `≤ ∑ₖ (kπ/(p.μ+λ_k))²`, and Cauchy–Schwarz
closes the bound. -/
theorem intervalNeumannResolverR_grad_sup_lipschitz
    (p : CM2Params) (u₁ u₂ : intervalDomainPoint → ℝ)
    (hsrc : Summable fun k : ℕ =>
      ((intervalNeumannResolverSourceCoeff p u₁ k -
        intervalNeumannResolverSourceCoeff p u₂ k).re) ^ 2)
    (x : intervalDomainPoint)
    (hsum₁ : Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u₁ k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x.1)))
    (hsum₂ : Summable fun k : ℕ =>
      (intervalNeumannResolverCoeff p u₂ k).re *
        (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x.1))) :
    |intervalNeumannResolverRGrad p u₁ x - intervalNeumannResolverRGrad p u₂ x| ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
        coeffL2Norm
          (fun k : ℕ =>
            intervalNeumannResolverSourceCoeff p u₁ k -
              intervalNeumannResolverSourceCoeff p u₂ k) := by
  -- Abbreviations (same as the sup case).
  set D : ℕ → ℂ := fun k =>
    intervalNeumannResolverCoeff p u₁ k - intervalNeumannResolverCoeff p u₂ k with hD
  set A : ℕ → ℂ := fun k =>
    intervalNeumannResolverSourceCoeff p u₁ k -
      intervalNeumannResolverSourceCoeff p u₂ k with hA
  -- Coefficient-form elliptic identity subtracted across `u₁, u₂`.
  have hell : ∀ k : ℕ,
      ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) * D k = A k := by
    intro k
    have h1 := intervalNeumannResolverCoeff_elliptic p u₁ k
    have h2 := intervalNeumannResolverCoeff_elliptic p u₂ k
    simp only [hD, hA]; rw [mul_sub, h1, h2]
  have hellRe : ∀ k : ℕ,
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) * (D k).re = (A k).re := by
    intro k
    have hcast :
        ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast; ring
    have hk := congrArg Complex.re (hell k)
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  -- The derivative-mode value factor:
  --   mₖ = (−kπ·sin(kπx)) / (p.μ + λ_k).
  set m : ℕ → ℝ := fun k =>
    (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x.1)) /
      (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) with hm
  -- The energy factor: eₖ = (A k).re.
  set e : ℕ → ℝ := fun k => (A k).re with he
  -- Pointwise rewriting of the summand.
  have hterm : ∀ k : ℕ,
      (D k).re * (-((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x.1)) =
        e k * m k := by
    intro k
    have hden : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ≠ 0 :=
      ne_of_gt (intervalNeumannResolver_denom_pos p k)
    simp only [he, hm, ← hellRe k]
    field_simp
  -- Summability of `eₖ²` and `mₖ²`.
  have he_sq : Summable fun k : ℕ => (e k) ^ 2 := hsrc
  have hm_sq : Summable fun k : ℕ => (m k) ^ 2 := by
    have hw := intervalNeumannResolverGradWeight_sq_summable p
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) ?_ hw
    intro k
    have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hsin : (Real.sin ((k : ℝ) * Real.pi * x.1)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
    have hgweq : (intervalNeumannResolverGradWeight p k) ^ 2 =
        ((k : ℝ) * Real.pi) ^ 2 /
          (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [intervalNeumannResolverGradWeight, div_pow]
    rw [hgweq, hm, div_pow, mul_pow, neg_pow]
    have hkp : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hnum :
        (-1 : ℝ) ^ 2 * ((k : ℝ) * Real.pi) ^ 2 *
            (Real.sin ((k : ℝ) * Real.pi * x.1)) ^ 2 ≤
          ((k : ℝ) * Real.pi) ^ 2 := by
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      nlinarith [hkp, hsin, sq_nonneg (Real.sin ((k : ℝ) * Real.pi * x.1))]
    gcongr
  -- Product `eₖ·mₖ` is summable.
  have hprod_sum : Summable fun k : ℕ => e k * m k := by
    apply Summable.of_norm
    have hdom : ∀ k : ℕ, ‖e k * m k‖ ≤ (1/2) * (e k)^2 + (1/2) * (m k)^2 := by
      intro k
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (e k), sq_abs (m k), sq_nonneg (|e k| - |m k|)]
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hdom
      ((he_sq.mul_left (1/2)).add (hm_sq.mul_left (1/2)))
  -- ∂ₓR u₁ x − ∂ₓR u₂ x = ∑' eₖ·mₖ.
  have hsum_eq :
      intervalNeumannResolverRGrad p u₁ x - intervalNeumannResolverRGrad p u₂ x =
        ∑' k : ℕ, e k * m k := by
    simp only [intervalNeumannResolverRGrad]
    rw [← hsum₁.tsum_sub hsum₂]
    refine tsum_congr ?_
    intro k
    rw [← hterm k]
    simp only [hD, Complex.sub_re]; ring
  -- Cauchy–Schwarz.
  have hCS :
      |∑' k : ℕ, e k * m k| ≤
        Real.sqrt (∑' k : ℕ, (e k) ^ 2) * Real.sqrt (∑' k : ℕ, (m k) ^ 2) :=
    real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq he_sq hm_sq
  rw [hsum_eq]
  have heE : Real.sqrt (∑' k : ℕ, (e k) ^ 2) ≤ coeffL2Norm A := by
    rw [coeffL2Norm, coeffL2Energy]
    apply Real.sqrt_le_sqrt
    refine he_sq.tsum_le_tsum ?_ (intervalNeumannResolverR_source_l2_summable p u₁ u₂ hsrc)
    intro k
    have : (e k) ^ 2 = (A k).re * (A k).re := by rw [he]; ring
    rw [this]
    calc (A k).re * (A k).re ≤ Complex.normSq (A k) := Complex.re_sq_le_normSq _
      _ = ‖A k‖ ^ 2 := (Complex.sq_norm _).symm
  have hmW : Real.sqrt (∑' k : ℕ, (m k) ^ 2) ≤
      Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) := by
    apply Real.sqrt_le_sqrt
    refine hm_sq.tsum_le_tsum ?_ (intervalNeumannResolverGradWeight_sq_summable p)
    intro k
    have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k :=
      intervalNeumannResolver_denom_pos p k
    have hsin : (Real.sin ((k : ℝ) * Real.pi * x.1)) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
    have hgweq : (intervalNeumannResolverGradWeight p k) ^ 2 =
        ((k : ℝ) * Real.pi) ^ 2 /
          (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) ^ 2 := by
      rw [intervalNeumannResolverGradWeight, div_pow]
    rw [hgweq, hm, div_pow, mul_pow, neg_pow]
    have hkp : (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2 := by positivity
    have hnum :
        (-1 : ℝ) ^ 2 * ((k : ℝ) * Real.pi) ^ 2 *
            (Real.sin ((k : ℝ) * Real.pi * x.1)) ^ 2 ≤
          ((k : ℝ) * Real.pi) ^ 2 := by
      have h1 : (-1 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, one_mul]
      nlinarith [hkp, hsin, sq_nonneg (Real.sin ((k : ℝ) * Real.pi * x.1))]
    gcongr
  calc |∑' k : ℕ, e k * m k|
      ≤ Real.sqrt (∑' k : ℕ, (e k) ^ 2) * Real.sqrt (∑' k : ℕ, (m k) ^ 2) := hCS
    _ ≤ coeffL2Norm A *
          Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) := by
          exact mul_le_mul heE hmW (Real.sqrt_nonneg _)
            (by rw [coeffL2Norm]; exact Real.sqrt_nonneg _)
    _ = Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
          coeffL2Norm A := by ring

end ShenWork.PDE
