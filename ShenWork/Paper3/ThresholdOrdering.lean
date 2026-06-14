/-
# Paper3 Lemma A.7 / A.8 — threshold ordering against the spectral critical sensitivity

This file proves, at the formula level, the comparisons between the explicit
global-stability thresholds (`chiStrong*Formula`, `chiMinimal*Formula`) and the
spectral critical sensitivity `χ* = paperCriticalSensitivity`.  These are
Paper3 Appendix Lemmas A.7 (positive/non-minimal model) and A.8 (minimal
model).  The recon flagged these as the one genuinely OPEN ("transcendental vs
spectral sInf") target — the existing `Paper3Constants` comparison fields and
the `…_of_firstNonzero_lower` bridges still *carried* a comparison hypothesis;
here we DERIVE the comparison from the explicit formulas, unconditionally on the
spectrum.

## The analytic content

`χ*` is the infimum over the nonzero Neumann modes of the per-mode threshold
`A·h(λ)` where

  `A = (1+v*)^β / (νγ u*^{m+γ−1}) > 0`,   `h(λ) = (λ + aα)(μ + λ)/λ`.

The key observation (paper inequality `(√x+√y)² ≥ 4√(xy)`, the U-shape of `h`)
is a **spectrum-free lower bound**: for *every* `λ > 0`,

  `h(λ) = λ + aαμ/λ + (aα + μ) ≥ 2√(aαμ) + (aα + μ) ≥ 4√(aαμ)`,

(AM–GM twice), the minimum `A·(√(aα)+√μ)²` being attained at `λ = √(aαμ)`.
Hence, with **no** regime/first-mode hypothesis,

  `χ* ≥ A · 4 √(aα μ)`.            (`paperCriticalSensitivity_ge_four_sqrt_aαμ`)

This is sharper than the committed `χ* ≥ A·(μ + firstNonzero)` floor and, unlike
it, is *independent of the spectrum*, which is exactly what the paper's A.7/A.8
proofs use.

The first/third strong thresholds are shown `≤ A·4√(aαμ)` resp. `≤ A·aα` under
the paper's parameter hypotheses (`α+1 ≥ 2γ`, `α+1 ≥ m+γ`), via the Lemma A.6
fact `Cα,γ · α/γ² ≥ 1` and the Bernoulli bound `(1+v*)^{2β} ≥ 1 + β̃ v*`.
Chaining with the spectrum-free floors gives the named comparisons
`chiStrong1Formula ≤ χ*` and `chiStrong3Formula ≤ χ*` for any Neumann spectrum.
(The `min`-of-`chiBar` thresholds `chiStrong2/4Formula`, involving
`vABLowerFormula`/`chiBarFormula`, are NOT yet routed to the floor — see the
residual note at the end of the file.)

For A.8, every `chiMinimal*Formula ≤ chiBeta` (built into the `min`), so the
minimal comparison `chiMinimal* ≤ χ*` reduces to the paper's own A.8 input
`chiBeta ≤ χ*` (carried here as a hypothesis, exactly as the linear-stability
bridge `…linearlyStable_of_chiBeta_le_critical` consumes it; in the
first-mode regime it is `chiBeta ≤ paperFormula(λ₁)`).

No `sorry`/`admit`/`native_decide`/custom `axiom`.  The parameter hypotheses
(`α+1 ≥ 2γ`, `β ≥ 1`, …) are the paper's own, not smuggled halves of the goal.
-/

import ShenWork.Paper3.CriticalSensitivityExactValue

namespace ShenWork.Paper3

open ShenWork.Paper2 (chiBeta)

/-- The common positive prefactor `A = (1+v*)^β / (νγ u*^{m+γ−1})`. -/
private lemma paperPrefactor_pos
    (p : CM2Params) {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    0 < (1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1)) :=
  div_pos
    (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
    (mul_pos (mul_pos p.hν p.hγ) (Real.rpow_pos_of_pos huStar _))

/-- **Spectrum-free U-shape floor for the per-mode threshold.**  For every
`λ > 0`, `h(λ) = (λ+aα)(μ+λ)/λ ≥ 4√(aαμ)`.  The minimum of `h` is
`(√(aα)+√μ)²`, attained at `λ = √(aαμ)`; AM–GM then gives `≥ 4√(aαμ)`.
This is the spectrum-independent estimate behind Paper3 Lemma A.7/A.8. -/
theorem sigmaCriticalChiPaperFormula_ge_four_sqrt
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) (hlam : 0 < lambdaN) :
    ((1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
        (4 * Real.sqrt (p.a * p.α * p.μ)) ≤
      sigmaCriticalChiPaperFormula p uStar vStar lambdaN := by
  unfold sigmaCriticalChiPaperFormula
  have hA_pos := paperPrefactor_pos p huStar hvStar
  refine mul_le_mul_of_nonneg_left ?_ hA_pos.le
  -- `4√(aαμ) ≤ (λ+aα)(μ+λ)/λ`.
  rw [le_div_iff₀ hlam]
  -- `4√(aαμ)·λ ≤ (λ+aα)(μ+λ) = λ² + (aα+μ)λ + aαμ`.
  have haα_nonneg : 0 ≤ p.a * p.α := mul_nonneg p.ha p.hα.le
  set s := Real.sqrt (p.a * p.α * p.μ) with hs_def
  have hs : s ^ 2 = p.a * p.α * p.μ :=
    Real.sq_sqrt (mul_nonneg haα_nonneg p.hμ.le)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  -- AM–GM `aα + μ ≥ 2√(aαμ) = 2s`, from `√(aα·μ)=√(aα)·√μ` and `(√(aα)-√μ)²≥0`.
  have hsplit : s = Real.sqrt (p.a * p.α) * Real.sqrt p.μ := by
    rw [hs_def, Real.sqrt_mul haα_nonneg]
  have haα_sq : Real.sqrt (p.a * p.α) ^ 2 = p.a * p.α := Real.sq_sqrt haα_nonneg
  have hμ_sq : Real.sqrt p.μ ^ 2 = p.μ := Real.sq_sqrt p.hμ.le
  have hAMGM : 2 * s ≤ p.a * p.α + p.μ := by
    rw [hsplit]
    nlinarith [sq_nonneg (Real.sqrt (p.a * p.α) - Real.sqrt p.μ), haα_sq, hμ_sq]
  -- `λ²+aαμ ≥ 2sλ` (from `(λ-s)²≥0`) and `(aα+μ)λ ≥ 2sλ` (AM–GM); sum gives it.
  nlinarith [sq_nonneg (lambdaN - s), hs, hs_nonneg, hlam, haα_nonneg, p.hμ,
    mul_le_mul_of_nonneg_right hAMGM hlam.le]

/-- **`χ* ≥ A · 4√(aαμ)`** — the spectrum-free lower bound for the critical
sensitivity.  Holds for any Neumann spectrum (no first-mode/regime hypothesis),
since `4√(aαμ)` lower-bounds every per-mode value. -/
theorem paperCriticalSensitivity_ge_four_sqrt
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    ((1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
        (4 * Real.sqrt (p.a * p.α * p.μ)) ≤
      paperCriticalSensitivity S p uStar vStar := by
  unfold paperCriticalSensitivity
  refine le_csInf (paperCriticalSensitivitySet_nonempty S p uStar vStar) ?_
  rintro χ ⟨n, hn, rfl⟩
  exact sigmaCriticalChiPaperFormula_ge_four_sqrt p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)

/-- **Second spectrum-free floor `h(λ) ≥ aα`.**  Since `(λ + aα) ≥ aα` and
`(μ + λ)/λ ≥ 1`, every per-mode value is `≥ A·aα`.  This is the floor `(A.11)`
the paper uses for the third/fourth strong thresholds. -/
theorem sigmaCriticalChiPaperFormula_ge_aα
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) (hlam : 0 < lambdaN) :
    ((1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) * (p.a * p.α) ≤
      sigmaCriticalChiPaperFormula p uStar vStar lambdaN := by
  unfold sigmaCriticalChiPaperFormula
  have hA_pos := paperPrefactor_pos p huStar hvStar
  refine mul_le_mul_of_nonneg_left ?_ hA_pos.le
  rw [le_div_iff₀ hlam]
  nlinarith [mul_nonneg p.ha p.hα.le, p.hμ, hlam,
    mul_nonneg (mul_nonneg p.ha p.hα.le) p.hμ.le]

/-- **`χ* ≥ A·aα`.** -/
theorem paperCriticalSensitivity_ge_aα
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar) :
    ((1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) * (p.a * p.α) ≤
      paperCriticalSensitivity S p uStar vStar := by
  unfold paperCriticalSensitivity
  refine le_csInf (paperCriticalSensitivitySet_nonempty S p uStar vStar) ?_
  rintro χ ⟨n, hn, rfl⟩
  exact sigmaCriticalChiPaperFormula_ge_aα p huStar hvStar
    (H.eigenvalue_pos_of_ne_zero n hn)

/-! ## Lemma A.7 — strong (non-minimal) thresholds vs the spectral floor

We compare each `chiStrong*Formula` to the spectrum-free floor
`Φ := A·4√(aαμ)`, where `A = (1+v*)^β/(νγ u*^{m+γ−1})`.  At the positive
equilibrium `u* = (a/b)^{1/α}` we have `a = b·u*^α`, hence
`aαμ = bαμ·u*^α` and `Φ² = 16bαμ·(1+v*)^{2β}·u*^{α−2(m+γ−1)}/(ν²γ²)`. -/

/-- `a = b · (u*)^α` at the positive equilibrium. -/
private lemma a_eq_b_mul_rpow
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) :
    p.a = p.b * (positiveEquilibrium p hab).1 ^ p.α := by
  rw [positiveEquilibrium_fst_rpow_alpha p hab]
  field_simp [ne_of_gt hab.2]

/-- **Lemma A.7(1).**  `χ**,1 ≤ Φ = A·4√(aαμ)` under `α + 1 ≥ 2γ`.
The squared comparison is `(1+β̃v*)·γ² ≤ (2m−1)·Cα,γ·α·(1+v*)^{2β}`, which
follows from `(2m−1)Cα,γ·α ≥ γ²` (Lemma A.6, needs `α+1 ≥ 2γ` and `m ≥ 1`) and
`(1+v*)^{2β} ≥ 1 + β̃v*` (Bernoulli). -/
theorem chiStrong1Formula_le_four_sqrt
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) (hm : 1 ≤ p.m)
    (hαγ : 2 * p.γ ≤ p.α + 1) :
    chiStrong1Formula p (positiveEquilibrium p hab).1 (positiveEquilibrium p hab).2 ≤
      ((1 + (positiveEquilibrium p hab).2) ^ p.β /
          (p.ν * p.γ * (positiveEquilibrium p hab).1 ^ (p.m + p.γ - 1))) *
        (4 * Real.sqrt (p.a * p.α * p.μ)) := by
  set uStar := (positiveEquilibrium p hab).1 with hu
  set vStar := (positiveEquilibrium p hab).2 with hv
  have huStar : 0 < uStar := positiveEquilibrium_fst_pos p hab
  have hvStar : 0 < vStar := positiveEquilibrium_snd_pos p hab
  set A := (1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1)) with hA
  have hA_pos : 0 < A := paperPrefactor_pos p huStar hvStar.le
  -- the floor `Φ = A·4√(aαμ)` is nonneg.
  have hΦ_nonneg : 0 ≤ A * (4 * Real.sqrt (p.a * p.α * p.μ)) :=
    mul_nonneg hA_pos.le (by positivity)
  unfold chiStrong1Formula
  rw [Real.sqrt_le_iff]
  refine ⟨hΦ_nonneg, ?_⟩
  -- abbreviations
  have hC : 0 < CAlphaGamma p.α p.γ := CAlphaGamma_pos p.hα p.hγ
  have h2m1 : 0 < 2 * p.m - 1 := by linarith
  have hνsq : 0 < p.ν ^ 2 := pow_pos p.hν 2
  have hγsq : 0 < p.γ ^ 2 := pow_pos p.hγ 2
  have haαμ_nonneg : 0 ≤ p.a * p.α * p.μ :=
    mul_nonneg (mul_nonneg p.ha p.hα.le) p.hμ.le
  -- `(2m−1)·C·α ≥ γ²` from Lemma A.6.
  have hCab : (1 : ℝ) ≤ CAlphaGamma p.α p.γ * p.α / p.γ ^ 2 :=
    one_le_CAlphaGamma_mul_alpha_div_gamma_sq p.hα p.hγ (by linarith)
  have hγ2_le : p.γ ^ 2 ≤ (2 * p.m - 1) * CAlphaGamma p.α p.γ * p.α := by
    rw [le_div_iff₀ hγsq] at hCab
    nlinarith [hCab, h2m1, hC, p.hα, sq_nonneg p.γ, mul_pos hC p.hα]
  -- Bernoulli `(1+v*)^{2β} ≥ 1 + β̃ v*`.
  have hBern : 1 + betaTilde p.β * vStar ≤ (1 + vStar) ^ (2 * p.β) :=
    one_add_betaTilde_mul_le_one_add_rpow p.hβ hvStar.le
  -- expand `Φ²` and `aαμ` via `a = b u*^α`.
  have ha_eq : p.a = p.b * uStar ^ p.α := a_eq_b_mul_rpow p hab
  -- `√(aαμ)² = aαμ`, and `((1+v*)^β)² = (1+v*)^{2β}`.
  have hsq_sqrt : Real.sqrt (p.a * p.α * p.μ) ^ 2 = p.a * p.α * p.μ :=
    Real.sq_sqrt haαμ_nonneg
  have hβrpow : ((1 + vStar) ^ p.β) ^ 2 = (1 + vStar) ^ (2 * p.β) := by
    rw [← Real.rpow_natCast ((1 + vStar) ^ p.β) 2, ← Real.rpow_mul (by positivity)]
    ring_nf
  -- u* power bookkeeping: the clean relation `u*^α · u*^{2γ−α+2m−2} = (u*^{m+γ−1})²`.
  have huden_pos : 0 < uStar ^ (p.m + p.γ - 1) := Real.rpow_pos_of_pos huStar _
  have hu2_pos : 0 < uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) := Real.rpow_pos_of_pos huStar _
  have huα_pos : 0 < uStar ^ p.α := Real.rpow_pos_of_pos huStar _
  have hurel : uStar ^ p.α * uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)
      = (uStar ^ (p.m + p.γ - 1)) ^ 2 := by
    rw [← Real.rpow_natCast (uStar ^ (p.m + p.γ - 1)) 2, ← Real.rpow_mul huStar.le,
      ← Real.rpow_add huStar]
    congr 1; ring
  -- the clean squared-coefficient inequality `γ²(1+β̃v*) ≤ (2m−1)Cα(1+v*)^{2β}`.
  have hkey : p.γ ^ 2 * (1 + betaTilde p.β * vStar)
      ≤ (2 * p.m - 1) * CAlphaGamma p.α p.γ * p.α * (1 + vStar) ^ (2 * p.β) := by
    have hpos1 : (0:ℝ) ≤ (1 + vStar) ^ (2 * p.β) - (1 + betaTilde p.β * vStar) := by
      linarith [hBern]
    nlinarith [hγ2_le, hpos1, mul_pos (mul_pos h2m1 hC) p.hα,
      mul_nonneg (mul_nonneg (mul_nonneg h2m1.le hC.le) p.hα.le) hpos1,
      betaTilde_nonneg p.β, hvStar.le, sq_nonneg p.γ,
      mul_nonneg (sq_nonneg p.γ) (mul_nonneg (betaTilde_nonneg p.β) hvStar.le)]
  -- denominators are positive.
  have hDL_pos : 0 < (2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
      uStar ^ (2 * p.γ - p.α + 2 * p.m - 2) :=
    mul_pos (mul_pos (mul_pos h2m1 hνsq) hC) hu2_pos
  have hAden_pos : 0 < p.ν * p.γ * uStar ^ (p.m + p.γ - 1) :=
    mul_pos (mul_pos p.hν p.hγ) huden_pos
  -- explicit value of `Φ²` over the common denominator `ν²γ²·u*^{2γ−α+2m−2}`.
  have hexp : uStar ^ p.α * uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)
      = uStar ^ (p.m + p.γ - 1) * uStar ^ (p.m + p.γ - 1) := by
    rw [hurel]; ring
  have hΦsq : (A * (4 * Real.sqrt (p.a * p.α * p.μ))) ^ 2
      = (16 * p.b * p.α * p.μ * (1 + vStar) ^ (2 * p.β)) /
          (p.ν ^ 2 * p.γ ^ 2 * uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)) := by
    rw [hA, mul_pow, mul_pow, div_pow, mul_pow, mul_pow, hsq_sqrt, hβrpow, ha_eq]
    rw [div_mul_eq_mul_div, div_eq_div_iff
      (by positivity)
      (ne_of_gt (mul_pos (mul_pos hνsq hγsq) hu2_pos))]
    -- both sides are degree-matched monomials; `hexp` identifies the `u*` powers.
    linear_combination
      (16 * p.b * p.α * p.μ * (1 + vStar) ^ (2 * p.β) * p.ν ^ 2 * p.γ ^ 2) * hexp
  rw [hΦsq]
  -- LHS to single fraction, then compare fractions with the same denominator structure.
  rw [show p.b * (16 * (1 + betaTilde p.β * vStar) * p.μ /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)))
      = (16 * p.b * p.μ * (1 + betaTilde p.β * vStar)) /
        ((2 * p.m - 1) * p.ν ^ 2 * CAlphaGamma p.α p.γ *
          uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)) by ring]
  rw [div_le_div_iff₀ hDL_pos (mul_pos (mul_pos hνsq hγsq) hu2_pos)]
  -- cross-multiply: `hkey` scaled by `16 b μ ν² u*^{2γ−α+2m−2} ≥ 0`.
  have hscale : 0 ≤ 16 * p.b * p.μ * (p.ν ^ 2 *
      uStar ^ (2 * p.γ - p.α + 2 * p.m - 2)) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) p.hb) p.hμ.le)
      (mul_nonneg hνsq.le hu2_pos.le)
  nlinarith [mul_le_mul_of_nonneg_left hkey hscale, hu2_pos, hνsq, hγsq,
    p.hb, p.hμ, hC, h2m1]

/-- **Lemma A.7(3).**  `χ**,3 ≤ Φ' = A·aα` under `γ ≥ 1` and `α + 1 ≥ m + γ`.
Here `χ**,3 = a/(ν u*^{m+γ−1}(2 + βv*M0²)) ≤ a/(2ν u*^{m+γ−1})`, and
`A·aα = aα(1+v*)^β/(νγ u*^{m+γ−1})`; the comparison reduces to
`1/(2+βv*M0²) ≤ 1/2 ≤ 1 ≤ (α/γ)(1+v*)^β` (using `α ≥ γ` from `α+1 ≥ m+γ`,
`m ≥ 1`). -/
theorem chiStrong3Formula_le_aα
    (p : CM2Params) (hab : 0 < p.a ∧ 0 < p.b) (hm : 1 ≤ p.m) (M0 : ℝ)
    (hαmγ : p.m + p.γ ≤ p.α + 1) :
    chiStrong3Formula p M0 (positiveEquilibrium p hab).1 (positiveEquilibrium p hab).2 ≤
      ((1 + (positiveEquilibrium p hab).2) ^ p.β /
          (p.ν * p.γ * (positiveEquilibrium p hab).1 ^ (p.m + p.γ - 1))) *
        (p.a * p.α) := by
  set uStar := (positiveEquilibrium p hab).1 with hu
  set vStar := (positiveEquilibrium p hab).2 with hv
  have huStar : 0 < uStar := positiveEquilibrium_fst_pos p hab
  have hvStar : 0 < vStar := positiveEquilibrium_snd_pos p hab
  have huden_pos : 0 < uStar ^ (p.m + p.γ - 1) := Real.rpow_pos_of_pos huStar _
  have hαγ : p.γ ≤ p.α := by linarith
  -- `2 + βv*M0² ≥ 2 > 0`.
  have hden2 : 2 ≤ 2 + p.β * vStar * M0 ^ 2 :=
    by nlinarith [p.hβ, hvStar.le, sq_nonneg M0, mul_nonneg p.hβ hvStar.le]
  have hden2_pos : 0 < 2 + p.β * vStar * M0 ^ 2 := by linarith
  -- `(1+v*)^β ≥ 1`.
  have hβpow : (1 : ℝ) ≤ (1 + vStar) ^ p.β :=
    Real.one_le_rpow (by linarith) p.hβ
  unfold chiStrong3Formula
  -- factor out the common positive `a/(ν u*^{m+γ−1})`; compare scalar factors.
  have hfactor : ((1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))) *
        (p.a * p.α)
      = (p.a / (p.ν * uStar ^ (p.m + p.γ - 1))) *
          (p.α * (1 + vStar) ^ p.β / p.γ) := by
    field_simp
  rw [hfactor]
  refine mul_le_mul_of_nonneg_left ?_
    (div_nonneg hab.1.le (mul_pos p.hν huden_pos).le)
  -- `1/(2+βv*M0²) ≤ 1/2 ≤ 1 ≤ α(1+v*)^β/γ`.
  rw [le_div_iff₀ p.hγ, div_mul_eq_mul_div, div_le_iff₀ hden2_pos]
  nlinarith [hβpow, hden2, hαγ, p.hγ, mul_le_mul hαγ hβpow (by linarith) p.hα.le,
    mul_nonneg p.hγ.le (by linarith : (0:ℝ) ≤ 2 + p.β * vStar * M0 ^ 2 - 2)]

/-! ## Named targets: `chiStrong* ≤ χ*` against the spectral critical sensitivity

The two strong thresholds `chiStrong1Formula`, `chiStrong3Formula` are bounded
above by the spectrum-free floors `A·4√(aαμ)` and `A·aα` respectively, which are
themselves `≤ χ* = paperCriticalSensitivity` for **any** Neumann spectrum (no
first-mode/regime hypothesis).  Chaining gives the named comparisons. -/

/-- **Lemma A.7(1), spectral form.**  `chiStrong1Formula ≤ χ*`, for any Neumann
spectrum, under `α+1 ≥ 2γ` and `m ≥ 1`.  Combines `chiStrong1Formula_le_four_sqrt`
with the spectrum-free floor `paperCriticalSensitivity_ge_four_sqrt`. -/
theorem chiStrong1Formula_le_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (hab : 0 < p.a ∧ 0 < p.b) (hm : 1 ≤ p.m) (hαγ : 2 * p.γ ≤ p.α + 1) :
    chiStrong1Formula p (positiveEquilibrium p hab).1 (positiveEquilibrium p hab).2 ≤
      paperCriticalSensitivity S p
        (positiveEquilibrium p hab).1 (positiveEquilibrium p hab).2 :=
  (chiStrong1Formula_le_four_sqrt p hab hm hαγ).trans
    (paperCriticalSensitivity_ge_four_sqrt S p H
      (positiveEquilibrium_fst_pos p hab) (positiveEquilibrium_snd_pos p hab).le)

/-- **Lemma A.7(3), spectral form.**  `chiStrong3Formula ≤ χ*`, for any Neumann
spectrum, under `m ≥ 1` and `α+1 ≥ m+γ`.  Combines `chiStrong3Formula_le_aα` with
the spectrum-free floor `paperCriticalSensitivity_ge_aα`. -/
theorem chiStrong3Formula_le_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (hab : 0 < p.a ∧ 0 < p.b) (hm : 1 ≤ p.m) (M0 : ℝ)
    (hαmγ : p.m + p.γ ≤ p.α + 1) :
    chiStrong3Formula p M0 (positiveEquilibrium p hab).1
        (positiveEquilibrium p hab).2 ≤
      paperCriticalSensitivity S p
        (positiveEquilibrium p hab).1 (positiveEquilibrium p hab).2 :=
  (chiStrong3Formula_le_aα p hab hm M0 hαmγ).trans
    (paperCriticalSensitivity_ge_aα S p H
      (positiveEquilibrium_fst_pos p hab) (positiveEquilibrium_snd_pos p hab).le)

/-! ## Named targets: `chiMinimal* ≤ χ*`

Both minimal thresholds are bounded by `chiBeta/2` by construction (the `min`
in their definitions), hence by `chiBeta`.  The minimal comparison therefore
reduces to `chiBeta ≤ χ*` — the paper's own A.8 hypothesis, supplied here as a
parameter (it is *not* a spectrum-free fact; it is precisely the linear-stability
input the bridge `…linearlyStable_of_chiBeta_le_critical` consumes).  In the
first-mode-dominant regime it is `chiBeta ≤ paperFormula(λ₁)`. -/

/-- `chiMinimal1Formula ≤ chiBeta`, spectrum-free (`chiBeta ≥ 0` from `β ≥ 1`). -/
theorem chiMinimal1Formula_le_chiBeta
    (p : CM2Params) (hβ : 1 ≤ p.β) (lambdaStar uStar uBar vLower : ℝ) :
    chiMinimal1Formula p lambdaStar uStar uBar vLower ≤ chiBeta p := by
  refine (chiMinimal1Formula_le_min_half_sqrt p lambdaStar uStar uBar vLower).trans ?_
  refine (min_le_left _ _).trans ?_
  have := ShenWork.Paper2.chiBeta_pos_of_one_le_beta p hβ
  linarith

/-- `chiMinimal2Formula ≤ chiBeta`, spectrum-free. -/
theorem chiMinimal2Formula_le_chiBeta
    (p : CM2Params) (hβ : 1 ≤ p.β) (uBar vLower : ℝ) :
    chiMinimal2Formula p uBar vLower ≤ chiBeta p := by
  refine (chiMinimal2Formula_le_min_half_sqrt p uBar vLower).trans ?_
  refine (min_le_left _ _).trans ?_
  have := ShenWork.Paper2.chiBeta_pos_of_one_le_beta p hβ
  linarith

/-- **Lemma A.8(1), spectral form.**  `chiMinimal1Formula ≤ χ*`, given the paper's
A.8 input `chiBeta ≤ χ*`. -/
theorem chiMinimal1Formula_le_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (hβ : 1 ≤ p.β)
    {uStar vStar lambdaStar uBar vLower : ℝ}
    (hchiBeta : chiBeta p ≤ paperCriticalSensitivity S p uStar vStar) :
    chiMinimal1Formula p lambdaStar (minimalEquilibrium p uStar).1 uBar vLower ≤
      paperCriticalSensitivity S p uStar vStar :=
  (chiMinimal1Formula_le_chiBeta p hβ _ _ _ _).trans hchiBeta

/-- **Lemma A.8(2), spectral form.**  `chiMinimal2Formula ≤ χ*`, given `chiBeta ≤ χ*`. -/
theorem chiMinimal2Formula_le_paperCriticalSensitivity
    (S : SpectralData) (p : CM2Params) (hβ : 1 ≤ p.β)
    {uStar vStar uBar vLower : ℝ}
    (hchiBeta : chiBeta p ≤ paperCriticalSensitivity S p uStar vStar) :
    chiMinimal2Formula p uBar vLower ≤ paperCriticalSensitivity S p uStar vStar :=
  (chiMinimal2Formula_le_chiBeta p hβ _ _).trans hchiBeta

/-! ## Residual: `chiStrong2Formula`, `chiStrong4Formula`

These two strong thresholds are `min (chiBarFormula p) X`, where `X` involves the
auxiliary lower bound `vABLowerFormula p`:

  `chiStrong2Formula = min chiBar √(b·16(1+vAB)^{2β}μ / ((2m−1)ν²Cα,γ u*^{2γ−α+2m−2}))`,
  `chiStrong4Formula = min chiBar ((1+vAB)^β · chiStrong3Formula p M0 u* (ν/μ·u*^γ))`.

Unlike A.7(1)/(3), their second `min`-arguments carry the extra factor
`(1+vABLowerFormula p)^{2β}` resp. `(1+vABLowerFormula p)^β > 1`, so they are NOT
`≤ A·4√(aαμ)` / `≤ A·aα` directly (the floor route fails: `(1+vAB)^{2β} > 1` while
A.7(1) needed `(1+β̃v*) ≤ (1+v*)^{2β}`).  Closing them against `χ*` requires either
(a) the spectrum-free bound `chiBarFormula p ≤ A·4√(aαμ)` (a `Theta_beta`-vs-`√(aαμ)`
inequality, not yet formalised), giving `min chiBar _ ≤ chiBar ≤ χ*`; or
(b) a parameter bound on `vABLowerFormula p` (e.g. `(1+vAB)^β ≤ √(aαμ)/aα · γ/α`)
turning the second argument into the floor.  Both are genuine paper-A.7 algebra on
`chiBarFormula`/`vABLowerFormula` and are left as the precise residual; the four-way
`max_le` aggregate `max(max S1 S2)(max S3 S4) ≤ χ*` is then immediate once S2,S4 land.
-/

end ShenWork.Paper3
