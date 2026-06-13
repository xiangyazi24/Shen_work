/-
# Parabolic ∂ₓₓ-Duhamel L∞ estimate — the spectral IBP cancellation (per-mode)

This file formalizes the load-bearing **per-mode spectral integration-by-parts
cancellation** for the second spatial derivative of the Neumann-heat Duhamel term.

The 1D Neumann heat semigroup is diagonal in the cosine basis with multipliers
`e^{-λ_k t}`, `λ_k = (kπ)²`.  The Duhamel term `U(t,x) = ∫₀ᵗ S(t−s) F(s) ds` has
cosine coefficients `Û_k(t) = ∫₀ᵗ e^{-λ_k(t−s)} F̂_k(s) ds`.  The second spatial
derivative brings down `−λ_k`, giving the per-mode quantity

  `D_k(t) := −λ_k ∫₀ᵗ e^{-λ_k(t−s)} F̂_k(s) ds`.

Naively `|D_k| ~ λ_k·(1/λ_k)·sup|F̂_k|`; the worry is that the `λ_k` is unbounded.
But the time integral supplies the missing `1/λ_k`: integrating by parts in `s`
(with `w(s) = e^{-λ_k(t−s)}`, `w'(s) = λ_k e^{-λ_k(t−s)}`),

  `∫₀ᵗ λ_k e^{-λ_k(t−s)} F̂_k(s) ds
     = F̂_k(t) − e^{-λ_k t} F̂_k(0) − ∫₀ᵗ e^{-λ_k(t−s)} F̂_k'(s) ds`,

so

  `D_k(t) = −[ F̂_k(t) − e^{-λ_k t} F̂_k(0) − ∫₀ᵗ e^{-λ_k(t−s)} F̂_k'(s) ds ]`,
  `|D_k(t)| ≤ |F̂_k(t)| + |F̂_k(0)| + (1/λ_k) sup|F̂_k'|
            ≤ 2·Bv_k + (1/λ_k)·Bv'_k`.

**The `λ_k` from `∂ₓₓ` is EXACTLY canceled by the IBP boundary term** — both terms
are genuinely present.  This is the parabolic analog of the committed elliptic
resolver bounded-weight C² (`IntervalResolverPhysicalC2.resolverR_eigenWeighted_le_source`):
the elliptic static weight `1/(μ+λ_k)` is replaced by the time integral's `1/λ_k`.

The Mathlib IBP lemma feeding the cancellation is
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`.

## What is proved (0 sorry, 0 admit, 0 custom axiom, 0 native_decide)

* `parabolicWeight_hasDerivAt` — `∂ₛ e^{-λ(t−s)} = λ·e^{-λ(t−s)}`.
* `parabolic_weight_integral_eq` — `∫₀ᵗ e^{-λ(t−s)} ds = (1 − e^{-λt})/λ`.
* `parabolicDuhamel_ibp` — the spectral IBP identity (boundary term + remainder).
* `parabolicDuhamel_perMode_bound` — `|D_k(t)| ≤ 2·Bv + (1/λ)·Bv'` (load-bearing).
* `parabolicDuhamel_sndDeriv_Linfty_perMode_summable` — `Summable (fun k => |D_k|)`
  from `Summable Bv` + `Summable (Bv'/λ)` (the L∞ majorant bookkeeping).
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory intervalIntegral
open scoped Topology BigOperators

namespace ShenWork.IntervalParabolicDuhamelSecondDerivBoundedWeight

noncomputable section

/-- The parabolic weight `s ↦ e^{-λ(t−s)}`. -/
def parabolicWeight (lam t : ℝ) : ℝ → ℝ := fun s => Real.exp (-(lam * (t - s)))

/-- `∂ₛ e^{-λ(t−s)} = λ·e^{-λ(t−s)}`: differentiating the parabolic weight in `s`
brings down `+λ` (the inner `t−s` gives a sign flip). -/
theorem parabolicWeight_hasDerivAt (lam t s : ℝ) :
    HasDerivAt (parabolicWeight lam t) (lam * parabolicWeight lam t s) s := by
  have hinner : HasDerivAt (fun s : ℝ => -(lam * (t - s))) lam s := by
    have h1 : HasDerivAt (fun s : ℝ => t - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have h2 : HasDerivAt (fun s : ℝ => -(lam * (t - s))) (-(lam * (-1))) s :=
      ((h1.const_mul lam).neg)
    simpa using h2
  have hexp := (Real.hasDerivAt_exp (-(lam * (t - s)))).comp s hinner
  simpa [parabolicWeight, mul_comm] using hexp

/-- `parabolicWeight lam t` is continuous (in `s`). -/
theorem parabolicWeight_continuous (lam t : ℝ) :
    Continuous (parabolicWeight lam t) := by
  unfold parabolicWeight
  exact Real.continuous_exp.comp (by continuity)

/-- On `s ≤ t` (and `0 ≤ lam`), the parabolic weight is `≤ 1`. -/
theorem parabolicWeight_le_one {lam t s : ℝ} (hlam : 0 ≤ lam) (hst : s ≤ t) :
    parabolicWeight lam t s ≤ 1 := by
  unfold parabolicWeight
  rw [Real.exp_le_one_iff]
  have : 0 ≤ lam * (t - s) := mul_nonneg hlam (by linarith)
  linarith

theorem parabolicWeight_nonneg (lam t s : ℝ) : 0 ≤ parabolicWeight lam t s :=
  (Real.exp_pos _).le

/-- `∫₀ᵗ e^{-λ(t−s)} ds = (1 − e^{-λt})/λ` for `λ ≠ 0`.  Computed via FTC with the
antiderivative `s ↦ e^{-λ(t−s)}/λ`. -/
theorem parabolic_weight_integral_eq {lam t : ℝ} (hlam : lam ≠ 0) :
    (∫ s in (0 : ℝ)..t, parabolicWeight lam t s) = (1 - Real.exp (-(lam * t))) / lam := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => parabolicWeight lam t s / lam) (parabolicWeight lam t s) s := by
    intro s _
    have h := (parabolicWeight_hasDerivAt lam t s).div_const lam
    rw [mul_div_cancel_left₀ _ hlam] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((parabolicWeight_continuous lam t).intervalIntegrable _ _)]
  simp [parabolicWeight, sub_div]

/-- **Spectral integration-by-parts identity (per mode).**  For a `C¹` coefficient
`fhat : ℝ → ℝ` with derivative `fhat'`, the eigenvalue-weighted Duhamel integral
satisfies (`0 ≤ t`):

  `∫₀ᵗ λ·e^{-λ(t−s)}·fhat(s) ds
     = fhat(t) − e^{-λt}·fhat(0) − ∫₀ᵗ e^{-λ(t−s)}·fhat'(s) ds`.

The `λ` from `∂ₓₓ` is consumed by `∂ₛ e^{-λ(t−s)} = λ·e^{-λ(t−s)}`; the boundary
term `fhat(t) − e^{-λt}·fhat(0)` is what cancels it.  Fed by Mathlib's
`intervalIntegral.integral_mul_deriv_eq_deriv_mul`. -/
theorem parabolicDuhamel_ibp {lam t : ℝ} {fhat fhat' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt fhat (fhat' s) s)
    (hf'c : Continuous fhat') :
    (∫ s in (0 : ℝ)..t, fhat s * (lam * parabolicWeight lam t s))
      = fhat t * parabolicWeight lam t t - fhat 0 * parabolicWeight lam t 0
        - ∫ s in (0 : ℝ)..t, fhat' s * parabolicWeight lam t s := by
  have hu : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt fhat (fhat' s) s := fun s _ => hf s
  have hv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (parabolicWeight lam t) (lam * parabolicWeight lam t s) s :=
    fun s _ => parabolicWeight_hasDerivAt lam t s
  have hu' : IntervalIntegrable fhat' MeasureTheory.volume 0 t :=
    hf'c.intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun s => lam * parabolicWeight lam t s)
      MeasureTheory.volume 0 t :=
    ((parabolicWeight_continuous lam t).const_mul lam).intervalIntegrable _ _
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'

/-- The per-mode `∂ₓₓ`-Duhamel quantity `D_k(t) = −λ ∫₀ᵗ e^{-λ(t−s)} fhat(s) ds`. -/
def duhamelSecondMode (lam t : ℝ) (fhat : ℝ → ℝ) : ℝ :=
  -(lam * ∫ s in (0 : ℝ)..t, parabolicWeight lam t s * fhat s)

/-- The closed form of `D_k(t)` after IBP: `D_k = −(fhat(t) − e^{-λt} fhat(0) − R)`
where `R = ∫₀ᵗ e^{-λ(t−s)} fhat'(s) ds`. -/
theorem duhamelSecondMode_eq {lam t : ℝ} {fhat fhat' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt fhat (fhat' s) s) (hf'c : Continuous fhat') :
    duhamelSecondMode lam t fhat
      = -(fhat t * parabolicWeight lam t t - fhat 0 * parabolicWeight lam t 0
          - ∫ s in (0 : ℝ)..t, fhat' s * parabolicWeight lam t s) := by
  unfold duhamelSecondMode
  have hbring : (lam * ∫ s in (0 : ℝ)..t, parabolicWeight lam t s * fhat s)
      = ∫ s in (0 : ℝ)..t, fhat s * (lam * parabolicWeight lam t s) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext s; ring
  rw [hbring, parabolicDuhamel_ibp hf hf'c]

/-- **The load-bearing per-mode cancellation bound.**
With `λ > 0`, `0 ≤ t`, sup bounds `|fhat s| ≤ Bv` and `|fhat' s| ≤ Bv'` on `[0,t]`,

  `|D_k(t)| ≤ 2·Bv + (1/λ)·Bv'`.

The `2·Bv` is the IBP boundary term (`|fhat(t)| + e^{-λt}|fhat(0)| ≤ 2·Bv`); the
`(1/λ)·Bv'` is the remainder integral, whose `1/λ` comes from
`∫₀ᵗ e^{-λ(t−s)} ds ≤ 1/λ`.  This is the parabolic analog of the elliptic
`resolverR_eigenWeighted_le_source` (`1/(μ+λ_k)` ↦ `1/λ_k`).  Both terms present:
genuine cancellation, not vacuous. -/
theorem parabolicDuhamel_perMode_bound {lam t Bv Bv' : ℝ} {fhat fhat' : ℝ → ℝ}
    (hlam : 0 < lam) (ht : 0 ≤ t)
    (hf : ∀ s, HasDerivAt fhat (fhat' s) s) (hf'c : Continuous fhat')
    (hBv : ∀ s ∈ Set.Icc (0 : ℝ) t, |fhat s| ≤ Bv)
    (hBv' : ∀ s ∈ Set.Icc (0 : ℝ) t, |fhat' s| ≤ Bv') :
    |duhamelSecondMode lam t fhat| ≤ 2 * Bv + (1 / lam) * Bv' := by
  rw [duhamelSecondMode_eq hf hf'c, abs_neg]
  -- boundary values
  have hwt : parabolicWeight lam t t = 1 := by simp [parabolicWeight]
  have hw0 : parabolicWeight lam t 0 = Real.exp (-(lam * t)) := by simp [parabolicWeight]
  have hBv0 : |fhat 0| ≤ Bv := hBv 0 ⟨le_refl _, ht⟩
  have hBvt : |fhat t| ≤ Bv := hBv t ⟨ht, le_refl _⟩
  have hBv_nonneg : 0 ≤ Bv := le_trans (abs_nonneg _) hBv0
  -- bound the boundary term `|fhat t · 1 − fhat 0 · e^{-λt}| ≤ 2·Bv`
  have hbdry : |fhat t * parabolicWeight lam t t - fhat 0 * parabolicWeight lam t 0|
      ≤ 2 * Bv := by
    rw [hwt, hw0, mul_one]
    refine le_trans (abs_sub _ _) ?_
    have h1 : |fhat t| ≤ Bv := hBvt
    have h2 : |fhat 0 * Real.exp (-(lam * t))| ≤ Bv := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc |fhat 0| * Real.exp (-(lam * t)) ≤ |fhat 0| * 1 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact Real.exp_le_one_iff.mpr
              (by have := mul_nonneg hlam.le ht; linarith)
        _ = |fhat 0| := mul_one _
        _ ≤ Bv := hBv0
    linarith
  -- bound the remainder integral `|∫ fhat' · e^{-λ(t−s)}| ≤ (1/λ)·Bv'`
  have hrem : |∫ s in (0 : ℝ)..t, fhat' s * parabolicWeight lam t s|
      ≤ (1 / lam) * Bv' := by
    have hBv'_nonneg : 0 ≤ Bv' := le_trans (abs_nonneg _) (hBv' 0 ⟨le_refl _, ht⟩)
    have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t,
        |fhat' s * parabolicWeight lam t s| ≤ Bv' * parabolicWeight lam t s := by
      intro s hs
      rw [abs_mul, abs_of_nonneg (parabolicWeight_nonneg lam t s)]
      exact mul_le_mul_of_nonneg_right (hBv' s hs) (parabolicWeight_nonneg lam t s)
    calc |∫ s in (0 : ℝ)..t, fhat' s * parabolicWeight lam t s|
        ≤ ∫ s in (0 : ℝ)..t, |fhat' s * parabolicWeight lam t s| :=
          intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in (0 : ℝ)..t, Bv' * parabolicWeight lam t s :=
          intervalIntegral.integral_mono_on ht
            ((Continuous.intervalIntegrable
                (hf'c.mul (parabolicWeight_continuous lam t)) 0 t).abs)
            (((parabolicWeight_continuous lam t).const_mul Bv').intervalIntegrable 0 t)
            hpt
      _ = Bv' * (1 / lam) * (1 - Real.exp (-(lam * t))) := by
          rw [intervalIntegral.integral_const_mul, parabolic_weight_integral_eq (ne_of_gt hlam)]
          ring
      _ ≤ (1 / lam) * Bv' := by
          have h1 : (1 : ℝ) - Real.exp (-(lam * t)) ≤ 1 := by
            have := Real.exp_pos (-(lam * t)); linarith
          have hlaminv : (0 : ℝ) ≤ 1 / lam := le_of_lt (one_div_pos.mpr hlam)
          have h2 : 0 ≤ Bv' * (1 / lam) := mul_nonneg hBv'_nonneg hlaminv
          have h3 : 0 ≤ (1 : ℝ) - Real.exp (-(lam * t)) := by
            have : Real.exp (-(lam * t)) ≤ 1 :=
              Real.exp_le_one_iff.mpr (by have := mul_nonneg hlam.le ht; linarith)
            linarith
          calc Bv' * (1 / lam) * (1 - Real.exp (-(lam * t)))
              ≤ Bv' * (1 / lam) * 1 := by
                apply mul_le_mul_of_nonneg_left h1 h2
            _ = (1 / lam) * Bv' := by ring
  calc |fhat t * parabolicWeight lam t t - fhat 0 * parabolicWeight lam t 0
          - ∫ s in (0 : ℝ)..t, fhat' s * parabolicWeight lam t s|
      ≤ |fhat t * parabolicWeight lam t t - fhat 0 * parabolicWeight lam t 0|
          + |∫ s in (0 : ℝ)..t, fhat' s * parabolicWeight lam t s| := abs_sub _ _
    _ ≤ 2 * Bv + (1 / lam) * Bv' := by linarith [hbdry, hrem]

/-- **L∞ summation majorant (the bounded-weight series bookkeeping).**
Given per-mode eigenvalues `lam k > 0`, `C¹` coefficient families `fhat k`, sup
bounds `Bv k`, `Bv' k`, and the two honest ℓ¹ inputs

  (i)  `Summable Bv`                       (source ℓ¹ — same as the resolver),
  (ii) `Summable (fun k => Bv' k / lam k)` (`Σ 1/λ_k = 1/6 < ∞` × bounded `Bv'`),

the second-spatial-derivative Duhamel coefficients `D_k(t)` are absolutely summable:
`Summable (fun k => |D_k(t)|)`.  Comparison against `2·Bv k + Bv' k / lam k` via the
per-mode cancellation bound, mirroring `IntervalResolverPhysicalC2`'s
`resolverR_eigenWeighted_summable_of_sourceL1` (`Summable.of_nonneg_of_le`). -/
theorem parabolicDuhamel_sndDeriv_Linfty_perMode_summable
    {t : ℝ} {lam : ℕ → ℝ} {Bv Bv' : ℕ → ℝ} {fhat fhat' : ℕ → ℝ → ℝ}
    (ht : 0 ≤ t) (hlam : ∀ k, 0 < lam k)
    (hf : ∀ k s, HasDerivAt (fhat k) (fhat' k s) s)
    (hf'c : ∀ k, Continuous (fhat' k))
    (hBv : ∀ k s, s ∈ Set.Icc (0 : ℝ) t → |fhat k s| ≤ Bv k)
    (hBv' : ∀ k s, s ∈ Set.Icc (0 : ℝ) t → |fhat' k s| ≤ Bv' k)
    (hsumBv : Summable Bv) (hsumBv' : Summable (fun k => Bv' k / lam k)) :
    Summable (fun k => |duhamelSecondMode (lam k) t (fhat k)|) := by
  have hmaj : Summable (fun k => 2 * Bv k + Bv' k / lam k) :=
    (hsumBv.mul_left 2).add hsumBv'
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmaj
  have hb := parabolicDuhamel_perMode_bound (lam := lam k) (t := t)
    (Bv := Bv k) (Bv' := Bv' k) (fhat := fhat k) (fhat' := fhat' k)
    (hlam k) ht (hf k) (hf'c k) (hBv k) (hBv' k)
  have hrw : (1 / lam k) * Bv' k = Bv' k / lam k := by rw [one_div, inv_mul_eq_div]
  rwa [hrw] at hb

end

end ShenWork.IntervalParabolicDuhamelSecondDerivBoundedWeight
