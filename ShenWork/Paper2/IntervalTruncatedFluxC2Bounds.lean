import Mathlib

/-!
# Truncated chemotaxis flux pointwise C² bounds — the δ-free algebra (Q4354)

The flux is `Q = u·g` with `g = R'·(1+R)^{-β}` (the chemical-gradient factor).
The ChatGPT-verified audit (Q4354) established that the pointwise `C²` bound of
`Q` is **δ-free** — it uses only `1 + R ≥ 1` (from `R ≥ 0`, `β ≥ 0`), never a
lower floor `δ ≤ u`.  What it does need is `u`'s own derivative envelope
(`U₀,U₁,U₂`), because `Q'' = u''g + 2u'g' + ug''` genuinely reads `u'`, `u''`.

This file formalizes the **δ-free algebraic core** as standalone `0`-sorry
lemmas: the product-rule estimates for `Q'` and `Q''` from factor bounds, the
denominator power bound `0 ≤ (1+R)^{-β-j} ≤ 1`, and the first denominator/gradient
factor bounds.  (The `HasDerivAt` derivative tower `denom0→denom1→…` that produces
the derivative expressions is a separate calculus build.)  Self-contained: Mathlib
only.
-/

namespace ShenWork.Paper2.TruncatedFluxC2Bounds

open Real

/-- **Denominator power membership.** For `A ≥ 1` and a nonpositive exponent
`e ≤ 0`, `0 ≤ A^e ≤ 1`.  Applied with `A = 1+R ≥ 1` (from `R ≥ 0`) and
`e ∈ {-β, -β-1, -β-2}` (all `≤ 0` when `β ≥ 0`) — the δ-free denominator floor. -/
theorem rpow_nonpos_mem {A e : ℝ} (hA : 1 ≤ A) (he : e ≤ 0) :
    0 ≤ A ^ e ∧ A ^ e ≤ 1 :=
  ⟨Real.rpow_nonneg (by linarith) e, Real.rpow_le_one_of_one_le_of_nonpos hA he⟩

/-- **First-order product estimate** `|Q'| = |u'g + ug'| ≤ U₁G₀ + U₀G₁`. -/
theorem flux1_abs_le
    {u u' g g' U₀ U₁ G₀ G₁ : ℝ}
    (hu : |u| ≤ U₀) (hu' : |u'| ≤ U₁)
    (hg : |g| ≤ G₀) (hg' : |g'| ≤ G₁) :
    |u' * g + u * g'| ≤ U₁ * G₀ + U₀ * G₁ := by
  have hU₀ : 0 ≤ U₀ := le_trans (abs_nonneg _) hu
  have hU₁ : 0 ≤ U₁ := le_trans (abs_nonneg _) hu'
  have t1 : |u' * g| ≤ U₁ * G₀ := by
    rw [abs_mul]; exact mul_le_mul hu' hg (abs_nonneg _) hU₁
  have t2 : |u * g'| ≤ U₀ * G₁ := by
    rw [abs_mul]; exact mul_le_mul hu hg' (abs_nonneg _) hU₀
  calc |u' * g + u * g'| ≤ |u' * g| + |u * g'| := abs_add_le _ _
    _ ≤ U₁ * G₀ + U₀ * G₁ := by gcongr

/-- **Second-order product estimate** (the core of the flux `C²` bound):
`|Q''| = |u''g + 2u'g' + ug''| ≤ U₂G₀ + 2U₁G₁ + U₀G₂`. -/
theorem flux2_abs_le
    {u u' u'' g g' g'' U₀ U₁ U₂ G₀ G₁ G₂ : ℝ}
    (hu : |u| ≤ U₀) (hu' : |u'| ≤ U₁) (hu'' : |u''| ≤ U₂)
    (hg : |g| ≤ G₀) (hg' : |g'| ≤ G₁) (hg'' : |g''| ≤ G₂) :
    |u'' * g + 2 * u' * g' + u * g''| ≤ U₂ * G₀ + 2 * (U₁ * G₁) + U₀ * G₂ := by
  have hU₀ : 0 ≤ U₀ := le_trans (abs_nonneg _) hu
  have hU₁ : 0 ≤ U₁ := le_trans (abs_nonneg _) hu'
  have hU₂ : 0 ≤ U₂ := le_trans (abs_nonneg _) hu''
  have t1 : |u'' * g| ≤ U₂ * G₀ := by
    rw [abs_mul]; exact mul_le_mul hu'' hg (abs_nonneg _) hU₂
  have t2 : |2 * u' * g'| ≤ 2 * (U₁ * G₁) := by
    have h1 : |2 * u' * g'| = 2 * |u'| * |g'| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h1]
    have hb : |u'| * |g'| ≤ U₁ * G₁ := mul_le_mul hu' hg' (abs_nonneg _) hU₁
    nlinarith [hb, abs_nonneg u', abs_nonneg g']
  have t3 : |u * g''| ≤ U₀ * G₂ := by
    rw [abs_mul]; exact mul_le_mul hu hg'' (abs_nonneg _) hU₀
  calc |u'' * g + 2 * u' * g' + u * g''|
      ≤ |u'' * g + 2 * u' * g'| + |u * g''| := abs_add_le _ _
    _ ≤ (|u'' * g| + |2 * u' * g'|) + |u * g''| := by gcongr; exact abs_add_le _ _
    _ ≤ (U₂ * G₀ + 2 * (U₁ * G₁)) + U₀ * G₂ := by gcongr
    _ = U₂ * G₀ + 2 * (U₁ * G₁) + U₀ * G₂ := by ring

/-- **Chemical-gradient zeroth factor bound** `|g| = |R'·(1+R)^{-β}| ≤ K₁`,
using `0 ≤ (1+R)^{-β} ≤ 1`. -/
theorem chemGrad0_abs_le
    {R' A e K₁ : ℝ} (hA : 1 ≤ A) (he : e ≤ 0) (hR' : |R'| ≤ K₁) :
    |R' * A ^ e| ≤ K₁ := by
  obtain ⟨hp0, hp1⟩ := rpow_nonpos_mem hA he
  have hK₁ : 0 ≤ K₁ := le_trans (abs_nonneg _) hR'
  rw [abs_mul, abs_of_nonneg hp0]
  calc |R'| * A ^ e ≤ K₁ * 1 := by
        apply mul_le_mul hR' hp1 hp0 hK₁
    _ = K₁ := by ring

/-- **First denominator-derivative factor bound** `|h'| = |-β·(1+R)^{-β-1}·R'| ≤ β·K₁`. -/
theorem denom1_abs_le
    {β A R' K₁ : ℝ} (hβ : 0 ≤ β) (hA : 1 ≤ A) (hR' : |R'| ≤ K₁) :
    |(-β) * A ^ (-β - 1) * R'| ≤ β * K₁ := by
  have he : (-β - 1 : ℝ) ≤ 0 := by linarith
  obtain ⟨hp0, hp1⟩ := rpow_nonpos_mem hA he
  have hK₁ : 0 ≤ K₁ := le_trans (abs_nonneg _) hR'
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_nonneg hp0]
  calc β * A ^ (-β - 1) * |R'| ≤ β * 1 * K₁ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hp1 hβ) hR' (abs_nonneg _)
        positivity
    _ = β * K₁ := by ring

/-! ## Constant layer (matching the Q4354 audit's `C²` envelope) -/

/-- `|g| ≤ K`. -/
def chemGradC0 (K : ℝ) : ℝ := K

/-- `|g'| ≤ K + βK²`. -/
def chemGradC1 (β K : ℝ) : ℝ := K + β * K ^ 2

/-- `|g''| ≤ K + 3βK² + β(β+1)K³`. -/
def chemGradC2 (β K : ℝ) : ℝ := K + 3 * β * K ^ 2 + β * (β + 1) * K ^ 3

/-- Pointwise flux `C²` constant `U₂·G₀ + 2U₁·G₁ + U₀·G₂`. -/
def fluxC2PointConst (U₀ U₁ U₂ β K : ℝ) : ℝ :=
  U₂ * chemGradC0 K + 2 * (U₁ * chemGradC1 β K) + U₀ * chemGradC2 β K

/-- Common-`C²`-envelope flux constant `U·(4K + 5βK² + β(β+1)K³)`. -/
def fluxC2CommonConst (U β K : ℝ) : ℝ :=
  U * (4 * K + 5 * β * K ^ 2 + β * (β + 1) * K ^ 3)

/-- The common-envelope constant dominates the pointwise constant when one
`C²` bound `U` controls `U₀,U₁,U₂` (and `K,β ≥ 0`). -/
theorem fluxC2PointConst_le_common
    {U₀ U₁ U₂ U β K : ℝ}
    (h0 : U₀ ≤ U) (h1 : U₁ ≤ U) (h2 : U₂ ≤ U)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hU : 0 ≤ U) :
    fluxC2PointConst U₀ U₁ U₂ β K ≤ fluxC2CommonConst U β K := by
  unfold fluxC2PointConst fluxC2CommonConst chemGradC0 chemGradC1 chemGradC2
  have hK2 : 0 ≤ K ^ 2 := by positivity
  have hK3 : 0 ≤ K ^ 3 := by positivity
  nlinarith [mul_nonneg hβ hK2, mul_nonneg (mul_nonneg hβ (by linarith : (0:ℝ) ≤ β + 1)) hK3,
    h0, h1, h2, hK, hβ, mul_nonneg hβ hK]

/-! ## HasDerivAt derivative towers (Q4363) — produce the denominator/gradient/flux
derivative expressions the algebraic bounds above consume.  The denominator uses the
LEFT disjunct of `HasDerivAt.rpow_const` (`1 + R ≠ 0` from `1 + R ≥ 1`). -/

/-- **Denominator first derivative** `h = (1+R)^{-β}`, `h' = -β·(1+R)^{-β-1}·R'`,
via `HasDerivAt.rpow_const` with `Or.inl (1+R ≠ 0)`. -/
theorem denom0_hasDerivAt
    {β : ℝ} {R R1 : ℝ → ℝ} {x : ℝ}
    (hR0 : HasDerivAt R (R1 x) x) (hden : 1 ≤ 1 + R x) :
    HasDerivAt (fun y => (1 + R y) ^ (-β)) (-β * (1 + R x) ^ (-β - 1) * R1 x) x := by
  have hbase : HasDerivAt (fun y => 1 + R y) (R1 x) x := hR0.const_add 1
  have hbase_pos : (0 : ℝ) < 1 + R x := lt_of_lt_of_le zero_lt_one hden
  have hbase_ne : (1 + R x) ≠ 0 := hbase_pos.ne'
  have h := hbase.rpow_const (p := -β) (Or.inl hbase_ne)
  convert h using 1
  ring

/-- **Denominator second derivative**: `HasDerivAt` of `h' = -β·(1+R)^{-β-1}·R'`
at value `h'' = β(β+1)(1+R)^{-β-2}(R')² - β(1+R)^{-β-1}·R''`. -/
theorem denom1_hasDerivAt
    {β : ℝ} {R R1 R2 : ℝ → ℝ} {x : ℝ}
    (hR0 : HasDerivAt R (R1 x) x) (hR1 : HasDerivAt R1 (R2 x) x)
    (hden : 1 ≤ 1 + R x) :
    HasDerivAt (fun y => -β * (1 + R y) ^ (-β - 1) * R1 y)
      (β * (β + 1) * (1 + R x) ^ (-β - 2) * (R1 x) ^ 2
        - β * (1 + R x) ^ (-β - 1) * R2 x) x := by
  have hbase : HasDerivAt (fun y => 1 + R y) (R1 x) x := hR0.const_add 1
  have hbase_pos : (0 : ℝ) < 1 + R x := lt_of_lt_of_le zero_lt_one hden
  have hbase_ne : (1 + R x) ≠ 0 := hbase_pos.ne'
  have hpow_next := hbase.rpow_const (p := -β - 1) (Or.inl hbase_ne)
  rw [show ((-β - 1) - 1 : ℝ) = -β - 2 from by ring] at hpow_next
  have hstep := (hpow_next.const_mul (-β)).mul hR1
  convert hstep using 1
  ring

/-- **Chemical-gradient first derivative** `g = R'·h`, `g' = R''·h + R'·h'`,
via `HasDerivAt.mul`. -/
theorem chemGrad_hasDerivAt
    {β : ℝ} {R R1 R2 : ℝ → ℝ} {x : ℝ}
    (hR0 : HasDerivAt R (R1 x) x) (hR1 : HasDerivAt R1 (R2 x) x)
    (hden : 1 ≤ 1 + R x) :
    HasDerivAt (fun y => R1 y * (1 + R y) ^ (-β))
      (R2 x * (1 + R x) ^ (-β)
        + R1 x * (-β * (1 + R x) ^ (-β - 1) * R1 x)) x :=
  hR1.mul (denom0_hasDerivAt (β := β) hR0 hden)

/-- **Flux first derivative** `Q = u·g`, `Q' = u'·g + u·g'`, via `HasDerivAt.mul`. -/
theorem flux_hasDerivAt
    {β : ℝ} {u u1 R R1 R2 : ℝ → ℝ} {x : ℝ}
    (hu0 : HasDerivAt u (u1 x) x)
    (hR0 : HasDerivAt R (R1 x) x) (hR1 : HasDerivAt R1 (R2 x) x)
    (hden : 1 ≤ 1 + R x) :
    HasDerivAt (fun y => u y * (R1 y * (1 + R y) ^ (-β)))
      (u1 x * (R1 x * (1 + R x) ^ (-β))
        + u x * (R2 x * (1 + R x) ^ (-β)
            + R1 x * (-β * (1 + R x) ^ (-β - 1) * R1 x))) x :=
  hu0.mul (chemGrad_hasDerivAt (β := β) hR0 hR1 hden)

end ShenWork.Paper2.TruncatedFluxC2Bounds
