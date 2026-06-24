import ShenWork.Wiener.EWA.DivergenceDuhamelGain
import ShenWork.Paper2.IntervalHSigmaScale

/-!
# A³ ladder step — windowed divergence-Duhamel weighted-Wiener `+1` gain

This file builds **roadmap lemma 4** of the χ₀<0 positive-time A³ weighted-Wiener
bootstrap: the *ladder step* `TrajA r ⇒ TrajA (r+1)`.  It is the operator-level
`+1` weight-gain consequence of the banked per-mode gain
`ShenWork.EWA.divergence_duhamel_gain_per_mode`, summed over the spectrum with the
`(1+λ_k)^{(σ+1)/2}` weight.

## The documented gap (read from `IntervalChiNegA3Slice.lean`)

The A³ slice machinery (`slice_A3_of_step`, `slice_memHSigma_target_of_step`)
reduces the whole per-slice ladder to a single object:
`UniformBootstrapStep α (cosineCoeffs ut)`, whose SOLE field is

    step : ∀ {σ}, MemHSigma σ (cosineCoeffs ut) → MemHSigma (σ + α) (cosineCoeffs ut)

— the **window-uniform flux envelope** `+α` step (the campaign's isolated crux:
the cos→sin transfer needs a *window-uniform* envelope of the flux derivative one
order beyond the landed factor envelopes, with no unconditional producer — the
"Gronwall-continuation closure" residual).

## The key insight

The divergence-Duhamel leg carries one spatial derivative (`∂ₓ`), and on a
LOCALIZED compact positive-time window `[a,t]` (`0 ≤ a ≤ t`) the banked per-mode
gain delivers exactly the `+1` weight-gain with a UNIFORM constant `Cdiv`
(independent of `σ`, with no `σ < 1` blow-up).  Summing it over `k` with the
`(1+λ_k)^{σ+1}` weight turns a window-uniform `MemHSigma σ` *source* envelope into
a `MemHSigma (σ+1)` *Duhamel* envelope.  That is the `α = 1` realiser of the
`UniformBootstrapStep` field whenever the running solution's cosine coefficients
are presented as a divergence-Duhamel integral of a source carrying a
window-uniform `MemHSigma σ` envelope.

## What is proved here

* `divDuhamelFamily` — the divergence-Duhamel coefficient family
  `D_k = √λ_k · ∫_a^t e^{−(t−s)λ_k} Ŝ_k(s) ds` (the `d = 1` form matching the
  banked per-mode lemma).
* `windowed_divergence_gain_mode_sq` — the per-mode SQUARED `H^{σ+1}` bound,
  obtained by squaring the banked per-mode gain (`r = σ`).
* `windowed_divergence_gain` — **the ladder step**: a window-uniform source
  envelope `Esrc ∈ MemHSigma σ` (`0 ≤ σ`) ⇒ `D ∈ MemHSigma (σ+1)`.  Pure
  comparison-test sum of the banked per-mode bound.
* `uniformBootstrapStep_of_windowed_divergence` — the WIRING shape: if the running
  cosine coefficients are pointwise the `divDuhamelFamily` of a source admitting,
  at EVERY level `σ`, a window-uniform `MemHSigma σ` envelope, the `+1`
  `UniformBootstrapStep` field is discharged.

The precise residual is documented at the end: this discharges
`UniformBootstrapStep 1` *modulo* the per-level window-uniform envelope producer
`Esrc σ` (exactly the campaign's documented "window-uniform flux envelope" — now
reduced from a Gronwall closure to a single summable-envelope obligation, with the
analytic `+1` gain fully banked).

No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.  Lines ≤ 100.
Mathlib v4.29.1.  `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.
-/

open Set Real
open ShenWork.EWA (Cdiv Cdiv_pos divergence_duhamel_gain_per_mode)
open ShenWork.Paper2.HSigmaScale (lam MemHSigma one_add_lam_pos lam_nonneg)

noncomputable section

namespace ShenWork.EWA.A3LadderStep

/-- The divergence-Duhamel coefficient family on the window `[a,t]`:
`D_k = √λ_k · ∫_a^t e^{−(t−s)λ_k} Ŝ_k(s) ds`.  This is the `d = 1` divergence leg
whose per-mode `+1` gain is banked in `divergence_duhamel_gain_per_mode`. -/
def divDuhamelFamily (Ŝ : ℕ → ℝ → ℝ) (t a : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (lam k) * ∫ s in a..t, Real.exp (-((t - s) * lam k)) * Ŝ k s

/-- The absolute divergence-Duhamel coefficient `√λ_k · ∫_a^t e^{−(t−s)λ_k}|Ŝ_k|`,
which dominates `|D_k|`. -/
def divDuhamelAbs (Ŝ : ℕ → ℝ → ℝ) (t a : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (lam k) * ∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s|

/-- `|D_k| ≤ divDuhamelAbs`: the absolute family dominates the signed one.
`√λ_k ≥ 0`, and `|∫ e·Ŝ| ≤ ∫ e·|Ŝ|` by `abs_integral_le_integral_abs` (the
integrand `e·|Ŝ| ≥ 0`). -/
theorem abs_divDuhamel_le (Ŝ : ℕ → ℝ → ℝ) (t a : ℝ) (hat : a ≤ t) (k : ℕ) :
    |divDuhamelFamily Ŝ t a k| ≤ divDuhamelAbs Ŝ t a k := by
  unfold divDuhamelFamily divDuhamelAbs
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc |∫ s in a..t, Real.exp (-((t - s) * lam k)) * Ŝ k s|
      ≤ ∫ s in a..t, |Real.exp (-((t - s) * lam k)) * Ŝ k s| :=
        intervalIntegral.abs_integral_le_integral_abs hat
    _ = ∫ s in a..t, Real.exp (-((t - s) * lam k)) * |Ŝ k s| := by
        apply intervalIntegral.integral_congr; intro s _
        simp only [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]

/-- **Per-mode squared `H^{σ+1}` bound.**  Squaring the banked per-mode gain at
`r = σ`: `(1+λ_k)^{σ+1} · (divDuhamelAbs)² ≤ Cdiv² · (1+λ_k)^σ · (Esrc k)²`. -/
theorem windowed_divergence_gain_mode_sq
    (Ŝ : ℕ → ℝ → ℝ) (Esrc : ℕ → ℝ) (t a σ : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hσ : 0 ≤ σ) (hat : a ≤ t)
    (hŜcont : Continuous (Ŝ k))
    (hbound : ∀ s ∈ Set.uIcc a t, |Ŝ k s| ≤ Esrc k) :
    (1 + lam k) ^ (σ + 1) * (divDuhamelAbs Ŝ t a k) ^ 2
      ≤ Cdiv ^ 2 * ((1 + lam k) ^ σ * (Esrc k) ^ 2) := by
  have hgain := divergence_duhamel_gain_per_mode Ŝ Esrc k σ t a hk hσ hat hŜcont hbound
  -- hgain : (1+λ_k)^{(σ+1)/2} · divDuhamelAbs ≤ Cdiv · (1+λ_k)^{σ/2} · Esrc_k
  have h1pos := one_add_lam_pos k
  have hEsrc_nonneg : 0 ≤ Esrc k :=
    le_trans (abs_nonneg _) (hbound a Set.left_mem_uIcc)
  have hwσ_nonneg : 0 ≤ (1 + lam k) ^ (σ / 2) := Real.rpow_nonneg h1pos.le _
  have habs_nonneg : 0 ≤ divDuhamelAbs Ŝ t a k :=
    le_trans (abs_nonneg _) (abs_divDuhamel_le Ŝ t a hat k)
  -- LHS factors as the square of the gain's LHS.
  have hwL : (1 + lam k) ^ (σ + 1) = ((1 + lam k) ^ ((σ + 1) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast ((1 + lam k) ^ ((σ + 1) / 2)) 2,
      ← Real.rpow_mul h1pos.le]; norm_num
  have hLHS : (1 + lam k) ^ (σ + 1) * (divDuhamelAbs Ŝ t a k) ^ 2
      = ((1 + lam k) ^ ((σ + 1) / 2) * divDuhamelAbs Ŝ t a k) ^ 2 := by
    rw [hwL, mul_pow]
  have hgainLHS_nonneg : 0 ≤ (1 + lam k) ^ ((σ + 1) / 2) * divDuhamelAbs Ŝ t a k :=
    mul_nonneg (Real.rpow_nonneg h1pos.le _) habs_nonneg
  have hsq := pow_le_pow_left₀ hgainLHS_nonneg hgain 2
  rw [hLHS]
  calc ((1 + lam k) ^ ((σ + 1) / 2) * divDuhamelAbs Ŝ t a k) ^ 2
      ≤ (Cdiv * (1 + lam k) ^ (σ / 2) * Esrc k) ^ 2 := hsq
    _ = Cdiv ^ 2 * (((1 + lam k) ^ (σ / 2)) ^ 2 * (Esrc k) ^ 2) := by ring
    _ = Cdiv ^ 2 * ((1 + lam k) ^ σ * (Esrc k) ^ 2) := by
        congr 2
        rw [← Real.rpow_natCast ((1 + lam k) ^ (σ / 2)) 2, ← Real.rpow_mul h1pos.le]
        norm_num

/-- **The ladder step `windowed_divergence_gain` — operator `+1` weight gain.**

Given a source coefficient family `Ŝ` with a window-uniform `MemHSigma σ`
envelope `Esrc` on `[a,t]` (`0 ≤ σ`, `a ≤ t`, each `Ŝ k` continuous), the
divergence-Duhamel family `divDuhamelFamily Ŝ t a` lies in `MemHSigma (σ+1)`.

Proof: per-mode comparison.  For `k ≥ 1`, `(1+λ_k)^{σ+1}(D_k)²` is dominated by
`(1+λ_k)^{σ+1}(divDuhamelAbs)²` (by `abs_divDuhamel_le`) and then by
`Cdiv²·(1+λ_k)^σ(Esrc k)²` (banked, `windowed_divergence_gain_mode_sq`); the `k=0`
term has `λ₀ = 0`, so `√λ₀ = 0` and `D₀ = 0`.  The dominating series is summable
since `Esrc ∈ MemHSigma σ`. -/
theorem windowed_divergence_gain
    (Ŝ : ℕ → ℝ → ℝ) (Esrc : ℕ → ℝ) (t a σ : ℝ)
    (hσ : 0 ≤ σ) (hat : a ≤ t)
    (hŜcont : ∀ k, Continuous (Ŝ k))
    (hEsrc : MemHSigma σ Esrc)
    (hbound : ∀ k, ∀ s ∈ Set.uIcc a t, |Ŝ k s| ≤ Esrc k) :
    MemHSigma (σ + 1) (divDuhamelFamily Ŝ t a) := by
  have hdom : ∀ k, (1 + lam k) ^ (σ + 1) * (divDuhamelFamily Ŝ t a k) ^ 2
      ≤ Cdiv ^ 2 * ((1 + lam k) ^ σ * (Esrc k) ^ 2) := by
    intro k
    have h1pos := one_add_lam_pos k
    have hw_nonneg : 0 ≤ (1 + lam k) ^ (σ + 1) := Real.rpow_nonneg h1pos.le _
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0: λ₀ = 0 ⇒ √λ₀ = 0 ⇒ D₀ = 0; RHS ≥ 0.
      subst hk0
      have hlam0 : lam 0 = 0 := by unfold lam unitIntervalCosineEigenvalue; simp
      have hD0 : divDuhamelFamily Ŝ t a 0 = 0 := by
        unfold divDuhamelFamily; rw [hlam0, Real.sqrt_zero, zero_mul]
      rw [hD0]
      have hEsrc_nn : 0 ≤ Esrc 0 := le_trans (abs_nonneg _) (hbound 0 a Set.left_mem_uIcc)
      have : 0 ≤ Cdiv ^ 2 * ((1 + lam 0) ^ σ * (Esrc 0) ^ 2) := by positivity
      simpa using this
    · -- k ≥ 1: dominate |D_k| by divDuhamelAbs, then banked per-mode bound.
      have habs := abs_divDuhamel_le Ŝ t a hat k
      have hDsq : (divDuhamelFamily Ŝ t a k) ^ 2 ≤ (divDuhamelAbs Ŝ t a k) ^ 2 := by
        rw [← sq_abs (divDuhamelFamily Ŝ t a k)]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      calc (1 + lam k) ^ (σ + 1) * (divDuhamelFamily Ŝ t a k) ^ 2
          ≤ (1 + lam k) ^ (σ + 1) * (divDuhamelAbs Ŝ t a k) ^ 2 :=
            mul_le_mul_of_nonneg_left hDsq hw_nonneg
        _ ≤ Cdiv ^ 2 * ((1 + lam k) ^ σ * (Esrc k) ^ 2) :=
            windowed_divergence_gain_mode_sq Ŝ Esrc t a σ k hkpos hσ hat
              (hŜcont k) (hbound k)
  have hnonneg : ∀ k, 0 ≤ (1 + lam k) ^ (σ + 1) * (divDuhamelFamily Ŝ t a k) ^ 2 := by
    intro k; have := Real.rpow_nonneg (one_add_lam_pos k).le (σ + 1); positivity
  have hsum_env : Summable fun k => Cdiv ^ 2 * ((1 + lam k) ^ σ * (Esrc k) ^ 2) :=
    hEsrc.mul_left _
  exact Summable.of_nonneg_of_le hnonneg hdom hsum_env

/-- **WIRING — the `+1` `UniformBootstrapStep` field, modulo a per-level
window-uniform envelope producer.**

If the running cosine coefficients `c` are pointwise the `divDuhamelFamily` of a
source `Ŝ` that, at EVERY running level `σ`, admits a window-uniform
`MemHSigma σ` envelope `Esrc σ` on `[a,t]`, then the `α = 1`
`UniformBootstrapStep` field `MemHSigma σ c → MemHSigma (σ+1) c` is discharged
(the input `MemHSigma σ c` is not even needed — the envelope producer alone
drives each step, which is exactly the campaign's no-Gronwall observation).

This is the abstract closing form: the analytic `+1` gain is fully banked; the
sole carried obligation is the family `Esrc : ℝ → ℕ → ℝ` of window-uniform
`MemHSigma σ` envelopes — the campaign's documented "window-uniform flux
envelope" crux, now reduced from a Gronwall closure to a summable-envelope
hypothesis. -/
theorem uniformBootstrapStep_of_windowed_divergence
    (c : ℕ → ℝ) (Ŝ : ℕ → ℝ → ℝ) (Esrc : ℝ → ℕ → ℝ) (t a : ℝ)
    (hat : a ≤ t) (hŜcont : ∀ k, Continuous (Ŝ k))
    (hc : ∀ k, c k = divDuhamelFamily Ŝ t a k)
    (henv : ∀ σ, 0 ≤ σ → MemHSigma σ (Esrc σ))
    (hbd : ∀ σ, 0 ≤ σ → ∀ k, ∀ s ∈ Set.uIcc a t, |Ŝ k s| ≤ Esrc σ k)
    {σ : ℝ} (hσ : 0 ≤ σ) (_hin : MemHSigma σ c) :
    MemHSigma (σ + 1) c := by
  have hgain : MemHSigma (σ + 1) (divDuhamelFamily Ŝ t a) :=
    windowed_divergence_gain Ŝ (Esrc σ) t a σ hσ hat hŜcont (henv σ hσ) (hbd σ hσ)
  refine hgain.congr ?_
  intro k; rw [hc k]

section AxiomAudit
#print axioms divDuhamelFamily
#print axioms abs_divDuhamel_le
#print axioms windowed_divergence_gain_mode_sq
#print axioms windowed_divergence_gain
#print axioms uniformBootstrapStep_of_windowed_divergence
end AxiomAudit

end ShenWork.EWA.A3LadderStep
