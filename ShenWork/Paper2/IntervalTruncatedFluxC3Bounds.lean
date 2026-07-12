import ShenWork.Paper2.IntervalTruncatedFluxC2Bounds

/-!
# Truncated chemotaxis flux pointwise C³ bounds — δ-free (Q4369)

Extends the committed C² bounds (`IntervalTruncatedFluxC2Bounds`) by one derivative
order.  For `Q = u·g`, `g = R'·h`, `h = (1+R)^{-β}`, the confirmed (cqK/Q4371) final
source pass needs one `C³` flux bound.  The third-order Leibniz/Faà di Bruno algebra
is **δ-free** on the flux side (`1+R ≥ 1` floors every denominator power; no `u^{-q}`).

Contents:
* `flux3_abs_le` — the `(1,3,3,1)` third-order Leibniz estimate.  Reused for BOTH the
  outer product `Q''' = u'''g + 3u''g' + 3u'g'' + ug'''` AND the inner
  `g''' = R₄h + 3R₃h' + 3R₂h'' + R₁h'''` (identical shape).
* `hBound2_abs_le`, `hBound3_abs_le` — the new δ-free `|h''|`, `|h'''|` bounds
  (`|h'|` is `denom1_abs_le`, `|h| ≤ 1` is `rpow_nonpos_mem` from the C² file).
* the constant layer `hBound0/1/2/3`, `gBound0/1/2/3`, `fluxC3Bound`.

Hypothesis-taking style (matching the C² file): `R,R',R'',R''',R''''` bounded
(`R∈C⁴`) and `u,u',u'',u'''` bounded are HYPOTHESES; the derivative tower that
supplies them is threaded separately.
-/

namespace ShenWork.Paper2.TruncatedFluxC3Bounds

open Real
open ShenWork.Paper2.TruncatedFluxC2Bounds

/-- `|c·a·b| ≤ c·(A·B)` for `c ≥ 0`, `|a| ≤ A`, `|b| ≤ B`. -/
theorem cterm_le {c a b A B : ℝ} (hc : 0 ≤ c) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    |c * a * b| ≤ c * (A * B) := by
  have hA : 0 ≤ A := le_trans (abs_nonneg _) ha
  have h1 : |c * a * b| = c * (|a| * |b|) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc]; ring
  rw [h1]
  have hb' : |a| * |b| ≤ A * B := mul_le_mul ha hb (abs_nonneg _) hA
  nlinarith [hb', hc]

/-- **Third-order `(1,3,3,1)` Leibniz estimate.**  Serves both
`|Q'''| = |u'''g + 3u''g' + 3u'g'' + ug'''| ≤ U₃G₀ + 3U₂G₁ + 3U₁G₂ + U₀G₃`
and (by relabelling `u_j ↦ R_{j+1}`, `g_j ↦ h_j`) the inner `|g'''|`. -/
theorem flux3_abs_le
    {u u' u'' u''' g g' g'' g''' U₀ U₁ U₂ U₃ G₀ G₁ G₂ G₃ : ℝ}
    (hu : |u| ≤ U₀) (hu' : |u'| ≤ U₁) (hu'' : |u''| ≤ U₂) (hu''' : |u'''| ≤ U₃)
    (hg : |g| ≤ G₀) (hg' : |g'| ≤ G₁) (hg'' : |g''| ≤ G₂) (hg''' : |g'''| ≤ G₃) :
    |u''' * g + 3 * u'' * g' + 3 * u' * g'' + u * g'''|
      ≤ U₃ * G₀ + 3 * (U₂ * G₁) + 3 * (U₁ * G₂) + U₀ * G₃ := by
  have t0 : |u''' * g| ≤ U₃ * G₀ := by
    rw [abs_mul]; exact mul_le_mul hu''' hg (abs_nonneg _) (le_trans (abs_nonneg _) hu''')
  have t1 : |3 * u'' * g'| ≤ 3 * (U₂ * G₁) := cterm_le (by norm_num) hu'' hg'
  have t2 : |3 * u' * g''| ≤ 3 * (U₁ * G₂) := cterm_le (by norm_num) hu' hg''
  have t3 : |u * g'''| ≤ U₀ * G₃ := by
    rw [abs_mul]; exact mul_le_mul hu hg''' (abs_nonneg _) (le_trans (abs_nonneg _) hu)
  calc |u''' * g + 3 * u'' * g' + 3 * u' * g'' + u * g'''|
      ≤ |u''' * g + 3 * u'' * g' + 3 * u' * g''| + |u * g'''| := abs_add_le _ _
    _ ≤ (|u''' * g + 3 * u'' * g'| + |3 * u' * g''|) + |u * g'''| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ((|u''' * g| + |3 * u'' * g'|) + |3 * u' * g''|) + |u * g'''| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ((U₃ * G₀ + 3 * (U₂ * G₁)) + 3 * (U₁ * G₂)) + U₀ * G₃ := by gcongr
    _ = U₃ * G₀ + 3 * (U₂ * G₁) + 3 * (U₁ * G₂) + U₀ * G₃ := by ring

/-- **δ-free `|h''|` bound.**  `h'' = β(β+1)(1+R)^{-β-2}(R')² − β(1+R)^{-β-1}R''`,
`|h''| ≤ β(β+1)R₁² + βR₂`, using `(1+R)^{-β-j} ≤ 1`. -/
theorem hBound2_abs_le
    {β A R' R'' R₁ R₂ : ℝ} (hβ : 0 ≤ β) (hA : 1 ≤ A)
    (hR' : |R'| ≤ R₁) (hR'' : |R''| ≤ R₂) :
    |β * (β + 1) * A ^ (-β - 2) * R' ^ 2 - β * A ^ (-β - 1) * R''|
      ≤ β * (β + 1) * R₁ ^ 2 + β * R₂ := by
  obtain ⟨hp2n, hp2⟩ := rpow_nonpos_mem hA (by linarith : (-β - 2 : ℝ) ≤ 0)
  obtain ⟨hp1n, hp1⟩ := rpow_nonpos_mem hA (by linarith : (-β - 1 : ℝ) ≤ 0)
  have hββ : 0 ≤ β * (β + 1) := mul_nonneg hβ (by linarith)
  have hR₁ : 0 ≤ R₁ := le_trans (abs_nonneg _) hR'
  have hsq : R' ^ 2 ≤ R₁ ^ 2 := by nlinarith [abs_le.mp hR', hR₁]
  have hsq0 : 0 ≤ R' ^ 2 := sq_nonneg _
  -- |term1| ≤ β(β+1)R₁²
  have ht1nn : 0 ≤ β * (β + 1) * A ^ (-β - 2) * R' ^ 2 :=
    mul_nonneg (mul_nonneg hββ hp2n) hsq0
  have ht1 : |β * (β + 1) * A ^ (-β - 2) * R' ^ 2| ≤ β * (β + 1) * R₁ ^ 2 := by
    rw [abs_of_nonneg ht1nn]
    calc β * (β + 1) * A ^ (-β - 2) * R' ^ 2
        ≤ β * (β + 1) * 1 * R₁ ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp2 hββ) hsq hsq0
            (mul_nonneg hββ zero_le_one)
      _ = β * (β + 1) * R₁ ^ 2 := by ring
  -- |term2| ≤ βR₂
  have ht2 : |β * A ^ (-β - 1) * R''| ≤ β * R₂ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg hp1n]
    calc β * A ^ (-β - 1) * |R''|
        ≤ β * 1 * R₂ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp1 hβ) hR'' (abs_nonneg _)
            (mul_nonneg hβ zero_le_one)
      _ = β * R₂ := by ring
  have hstep := abs_add_le (β * (β + 1) * A ^ (-β - 2) * R' ^ 2)
    (-(β * A ^ (-β - 1) * R''))
  rw [← sub_eq_add_neg, abs_neg] at hstep
  calc |β * (β + 1) * A ^ (-β - 2) * R' ^ 2 - β * A ^ (-β - 1) * R''|
      ≤ |β * (β + 1) * A ^ (-β - 2) * R' ^ 2| + |β * A ^ (-β - 1) * R''| := hstep
    _ ≤ β * (β + 1) * R₁ ^ 2 + β * R₂ := by gcongr

/-- **δ-free `|h'''|` bound.**
`h''' = −β(β+1)(β+2)(1+R)^{-β-3}(R')³ + 3β(β+1)(1+R)^{-β-2}R'R'' − β(1+R)^{-β-1}R'''`,
`|h'''| ≤ β(β+1)(β+2)R₁³ + 3β(β+1)R₁R₂ + βR₃`. -/
theorem hBound3_abs_le
    {β A R' R'' R''' R₁ R₂ R₃ : ℝ} (hβ : 0 ≤ β) (hA : 1 ≤ A)
    (hR' : |R'| ≤ R₁) (hR'' : |R''| ≤ R₂) (hR''' : |R'''| ≤ R₃) :
    |(-(β * (β + 1) * (β + 2))) * A ^ (-β - 3) * R' ^ 3
        + 3 * (β * (β + 1)) * A ^ (-β - 2) * (R' * R'')
        - β * A ^ (-β - 1) * R'''|
      ≤ β * (β + 1) * (β + 2) * R₁ ^ 3 + 3 * (β * (β + 1)) * (R₁ * R₂) + β * R₃ := by
  obtain ⟨hp3n, hp3⟩ := rpow_nonpos_mem hA (by linarith : (-β - 3 : ℝ) ≤ 0)
  obtain ⟨hp2n, hp2⟩ := rpow_nonpos_mem hA (by linarith : (-β - 2 : ℝ) ≤ 0)
  obtain ⟨hp1n, hp1⟩ := rpow_nonpos_mem hA (by linarith : (-β - 1 : ℝ) ≤ 0)
  have hββ : 0 ≤ β * (β + 1) := mul_nonneg hβ (by linarith)
  have hβββ : 0 ≤ β * (β + 1) * (β + 2) := mul_nonneg hββ (by linarith)
  have hR₁ : 0 ≤ R₁ := le_trans (abs_nonneg _) hR'
  have hR₂ : 0 ≤ R₂ := le_trans (abs_nonneg _) hR''
  -- |R'|³ ≤ R₁³
  have hcube : |R'| ^ 3 ≤ R₁ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hR' 3
  -- term A: |−β(β+1)(β+2)A^{-β-3}(R')³| = β(β+1)(β+2)·A^{-β-3}·|R'|³ ≤ ·R₁³
  have htA : |(-(β * (β + 1) * (β + 2))) * A ^ (-β - 3) * R' ^ 3|
      ≤ β * (β + 1) * (β + 2) * R₁ ^ 3 := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hβββ, abs_of_nonneg hp3n, abs_pow]
    calc β * (β + 1) * (β + 2) * A ^ (-β - 3) * |R'| ^ 3
        ≤ β * (β + 1) * (β + 2) * 1 * R₁ ^ 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp3 hβββ) hcube (pow_nonneg (abs_nonneg _) 3)
            (mul_nonneg hβββ zero_le_one)
      _ = β * (β + 1) * (β + 2) * R₁ ^ 3 := by ring
  -- term B: |3β(β+1)A^{-β-2}R'R''| ≤ 3β(β+1)R₁R₂
  have htB : |3 * (β * (β + 1)) * A ^ (-β - 2) * (R' * R'')|
      ≤ 3 * (β * (β + 1)) * (R₁ * R₂) := by
    have h3ββ : 0 ≤ 3 * (β * (β + 1)) := by positivity
    rw [abs_mul, abs_mul, abs_of_nonneg h3ββ, abs_of_nonneg hp2n, abs_mul]
    have hRR : |R'| * |R''| ≤ R₁ * R₂ := mul_le_mul hR' hR'' (abs_nonneg _) hR₁
    calc 3 * (β * (β + 1)) * A ^ (-β - 2) * (|R'| * |R''|)
        ≤ 3 * (β * (β + 1)) * 1 * (R₁ * R₂) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp2 h3ββ) hRR
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg h3ββ zero_le_one)
      _ = 3 * (β * (β + 1)) * (R₁ * R₂) := by ring
  -- term C: |βA^{-β-1}R'''| ≤ βR₃
  have htC : |β * A ^ (-β - 1) * R'''| ≤ β * R₃ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, abs_of_nonneg hp1n]
    calc β * A ^ (-β - 1) * |R'''|
        ≤ β * 1 * R₃ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp1 hβ) hR''' (abs_nonneg _)
            (mul_nonneg hβ zero_le_one)
      _ = β * R₃ := by ring
  -- triangle over (A + B) − C
  set tA : ℝ := (-(β * (β + 1) * (β + 2))) * A ^ (-β - 3) * R' ^ 3
  set tB : ℝ := 3 * (β * (β + 1)) * A ^ (-β - 2) * (R' * R'')
  set tC : ℝ := β * A ^ (-β - 1) * R'''
  have hAB := abs_add_le tA tB
  have hsub := abs_add_le (tA + tB) (-tC)
  rw [← sub_eq_add_neg, abs_neg] at hsub
  calc |tA + tB - tC|
      ≤ |tA + tB| + |tC| := hsub
    _ ≤ (|tA| + |tB|) + |tC| := by gcongr
    _ ≤ (β * (β + 1) * (β + 2) * R₁ ^ 3 + 3 * (β * (β + 1)) * (R₁ * R₂)) + β * R₃ := by
        gcongr
    _ = β * (β + 1) * (β + 2) * R₁ ^ 3 + 3 * (β * (β + 1)) * (R₁ * R₂) + β * R₃ := by ring

/-! ## Constant layer (Q4369 §6) -/

/-- `‖h‖ ≤ 1`. -/
def hBound0 : ℝ := 1
/-- `‖h'‖ ≤ βR₁`. -/
def hBound1 (β R₁ : ℝ) : ℝ := β * R₁
/-- `‖h''‖ ≤ β(β+1)R₁² + βR₂`. -/
def hBound2 (β R₁ R₂ : ℝ) : ℝ := β * (β + 1) * R₁ ^ 2 + β * R₂
/-- `‖h'''‖ ≤ β(β+1)(β+2)R₁³ + 3β(β+1)R₁R₂ + βR₃`. -/
def hBound3 (β R₁ R₂ R₃ : ℝ) : ℝ :=
  β * (β + 1) * (β + 2) * R₁ ^ 3 + 3 * (β * (β + 1)) * (R₁ * R₂) + β * R₃

/-- `‖g‖ ≤ R₁H₀`. -/
def gBound0 (R₁ H₀ : ℝ) : ℝ := R₁ * H₀
/-- `‖g'‖ ≤ R₂H₀ + R₁H₁`. -/
def gBound1 (R₁ R₂ H₀ H₁ : ℝ) : ℝ := R₂ * H₀ + R₁ * H₁
/-- `‖g''‖ ≤ R₃H₀ + 2R₂H₁ + R₁H₂`. -/
def gBound2 (R₁ R₂ R₃ H₀ H₁ H₂ : ℝ) : ℝ := R₃ * H₀ + 2 * R₂ * H₁ + R₁ * H₂
/-- `‖g'''‖ ≤ R₄H₀ + 3R₃H₁ + 3R₂H₂ + R₁H₃`. -/
def gBound3 (R₁ R₂ R₃ R₄ H₀ H₁ H₂ H₃ : ℝ) : ℝ :=
  R₄ * H₀ + 3 * R₃ * H₁ + 3 * R₂ * H₂ + R₁ * H₃

/-- Consolidated `C³` flux constant (max over orders `0..3`). -/
def fluxC3Bound (U₀ U₁ U₂ U₃ G₀ G₁ G₂ G₃ : ℝ) : ℝ :=
  max (U₀ * G₀)
    (max (U₁ * G₀ + U₀ * G₁)
      (max (U₂ * G₀ + 2 * (U₁ * G₁) + U₀ * G₂)
        (U₃ * G₀ + 3 * (U₂ * G₁) + 3 * (U₁ * G₂) + U₀ * G₃)))

/-- The third-order term of `fluxC3Bound` dominates `|Q'''|`. -/
theorem flux3_abs_le_fluxC3Bound
    {u u' u'' u''' g g' g'' g''' U₀ U₁ U₂ U₃ G₀ G₁ G₂ G₃ : ℝ}
    (hu : |u| ≤ U₀) (hu' : |u'| ≤ U₁) (hu'' : |u''| ≤ U₂) (hu''' : |u'''| ≤ U₃)
    (hg : |g| ≤ G₀) (hg' : |g'| ≤ G₁) (hg'' : |g''| ≤ G₂) (hg''' : |g'''| ≤ G₃) :
    |u''' * g + 3 * u'' * g' + 3 * u' * g'' + u * g'''|
      ≤ fluxC3Bound U₀ U₁ U₂ U₃ G₀ G₁ G₂ G₃ := by
  refine (flux3_abs_le hu hu' hu'' hu''' hg hg' hg'' hg''').trans ?_
  unfold fluxC3Bound
  exact le_trans (le_refl _) (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

end ShenWork.Paper2.TruncatedFluxC3Bounds
