/-
# Exact value of the Paper3 critical sensitivity `χ*` (Remark 2.1, formula level)

`paperCriticalSensitivity S p uStar vStar = sInf {paperFormula(λ_n) : n ≠ 0}` is the
infimum over the nonzero Neumann modes of the explicit per-mode threshold

  `paperFormula(λ) = A · (λ + aα)(μ + λ)/λ`,   `A = (1+vStar)^β / (νγ uStar^{m+γ−1}) > 0`.

The `λ`-dependent factor `h(λ) = (λ + aα)(μ + λ)/λ = λ + aαμ/λ + (μ + aα)` is
**U-shaped**, with a unique minimum at `λ = √(aαμ)` and monotone increasing on
`[√(aαμ), ∞)`.  Consequently, when the **first nonzero mode is already past the
minimum** — the natural regime `aαμ ≤ firstNonzero²` — the infimum over the discrete
modes is attained at the first mode, so

  `χ* = paperFormula(λ₁)`   (exactly).

This file proves that exact value, replacing the prior crude two-sided bounds
(`paperCriticalSensitivity_le_mode_one` / `…_ge_firstNonzero_lower`, which leave a
gap `A·(μ+firstNonzero) ≤ χ* ≤ paperFormula(λ₁)`) by an exact formula — addressing
the THEOREM_STATUS Remark 2.1 item "replace constants-package comparison fields by
exact formula proofs".  Self-contained, formula/spectral level; no dependence on
solution existence.

No `sorry`/`admit`/custom `axiom`.  The regime hypothesis `aαμ ≤ firstNonzero²` is a
genuine parameter condition (it is *why* the first mode is the minimiser — if it
fails the infimum can sit at a higher mode), not a smuggled half of the conclusion.
-/

import ShenWork.Paper3.Statements

namespace ShenWork.Paper3

/-- **Monotonicity of the per-mode threshold past the U-shape minimum.**  The
explicit per-mode value `paperFormula(λ)` is increasing in `λ` whenever the product
`λ₁·λ₂` of two arguments is at least `aαμ` (which holds in particular for
`λ₁, λ₂ ≥ √(aαμ)`).  Algebraically, with `h(λ) = (λ+aα)(μ+λ)/λ`,

  `h(λ₂) − h(λ₁) = (λ₂ − λ₁)·(λ₁λ₂ − aαμ)/(λ₁λ₂) ≥ 0`. -/
theorem sigmaCriticalChiPaperFormula_le_of_firstMode_dominant
    (p : CM2Params) {uStar vStar lambda₁ lambda₂ : ℝ}
    (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hlam1 : 0 < lambda₁) (hlam2 : 0 < lambda₂) (hle : lambda₁ ≤ lambda₂)
    (hprod : p.a * p.α * p.μ ≤ lambda₁ * lambda₂) :
    sigmaCriticalChiPaperFormula p uStar vStar lambda₁ ≤
      sigmaCriticalChiPaperFormula p uStar vStar lambda₂ := by
  unfold sigmaCriticalChiPaperFormula
  -- the common positive prefactor `A`.
  have hA_pos :
      0 < (1 + vStar) ^ p.β / (p.ν * p.γ * uStar ^ (p.m + p.γ - 1)) :=
    div_pos
      (Real.rpow_pos_of_pos (by linarith : 0 < 1 + vStar) _)
      (mul_pos (mul_pos p.hν p.hγ) (Real.rpow_pos_of_pos huStar _))
  refine mul_le_mul_of_nonneg_left ?_ hA_pos.le
  -- reduce the `h(λ₁) ≤ h(λ₂)` quotient inequality to a polynomial one.
  rw [div_le_div_iff₀ hlam1 hlam2]
  -- `(λ₁+aα)(μ+λ₁)·λ₂ ≤ (λ₂+aα)(μ+λ₂)·λ₁`, difference `= (λ₂−λ₁)(λ₁λ₂−aαμ) ≥ 0`.
  nlinarith [mul_nonneg (sub_nonneg.2 hle) (sub_nonneg.2 hprod), hlam1, hlam2,
    mul_nonneg p.ha p.hα.le, p.hμ]

/-- **Exact value of `χ*` in the first-mode-dominant regime.**  When the first
nonzero mode realises the spectral floor (`eigenvalue 1 = firstNonzero`, true for the
unit-interval spectrum) and lies past the U-shape minimum (`aαμ ≤ firstNonzero²`),
the critical sensitivity equals the first-mode threshold exactly:

  `paperCriticalSensitivity = sigmaCriticalChiPaperFormula(eigenvalue 1)`.

This is sharp: it closes the gap between the prior upper bound
`paperCriticalSensitivity_le_mode_one` and lower bound
`paperCriticalSensitivity_ge_firstNonzero_lower`. -/
theorem paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hmode1 : S.eigenvalue 1 = S.firstNonzero)
    (hregime : p.a * p.α * p.μ ≤ S.firstNonzero ^ 2) :
    paperCriticalSensitivity S p uStar vStar =
      sigmaCriticalChiPaperFormula p uStar vStar (S.eigenvalue 1) := by
  refine le_antisymm
    (paperCriticalSensitivity_le_mode_one S p H huStar hvStar) ?_
  -- lower bound: `paperFormula(λ₁)` is a lower bound for the whole mode set.
  unfold paperCriticalSensitivity
  refine le_csInf (paperCriticalSensitivitySet_nonempty S p uStar vStar) ?_
  rintro χ ⟨n, hn, rfl⟩
  -- `paperFormula(λ₁) ≤ paperFormula(λ_n)` by monotonicity past the U-min.
  have hlam1_pos : 0 < S.eigenvalue 1 := H.eigenvalue_pos_of_ne_zero 1 one_ne_zero
  have hlamn_pos : 0 < S.eigenvalue n := H.eigenvalue_pos_of_ne_zero n hn
  have hlam1_le_lamn : S.eigenvalue 1 ≤ S.eigenvalue n := by
    rw [hmode1]; exact H.firstNonzero_le_eigenvalue n hn
  have hprod : p.a * p.α * p.μ ≤ S.eigenvalue 1 * S.eigenvalue n := by
    have hfn_le_lamn : S.firstNonzero ≤ S.eigenvalue n :=
      H.firstNonzero_le_eigenvalue n hn
    have hsq : S.firstNonzero ^ 2 ≤ S.eigenvalue 1 * S.eigenvalue n := by
      rw [hmode1, sq]
      exact mul_le_mul_of_nonneg_left hfn_le_lamn H.firstNonzero_pos.le
    linarith
  exact sigmaCriticalChiPaperFormula_le_of_firstMode_dominant p huStar hvStar
    hlam1_pos hlamn_pos hlam1_le_lamn hprod

/-- **`χ*` at the positive constant equilibrium, exact value (first-mode regime).** -/
theorem paperCriticalSensitivity_positiveEquilibrium_eq_mode_one_of_firstMode_dominant
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    (ha : 0 < p.a) (hb : 0 < p.b)
    (hmode1 : S.eigenvalue 1 = S.firstNonzero)
    (hregime : p.a * p.α * p.μ ≤ S.firstNonzero ^ 2) :
    paperCriticalSensitivity S p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2 =
      sigmaCriticalChiPaperFormula p
        (positiveEquilibrium p ⟨ha, hb⟩).1
        (positiveEquilibrium p ⟨ha, hb⟩).2
        (S.eigenvalue 1) :=
  paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant S p H
    (positiveEquilibrium_fst_pos p ⟨ha, hb⟩)
    (positiveEquilibrium_snd_pos p ⟨ha, hb⟩).le hmode1 hregime

/-- **`χ*` at the minimal constant equilibrium, exact value (first-mode regime).** -/
theorem paperCriticalSensitivity_minimalEquilibrium_eq_mode_one_of_firstMode_dominant
    (S : SpectralData) (p : CM2Params) (H : HasNeumannSpectrum S)
    {uStar : ℝ} (huStar : 0 < uStar)
    (hmode1 : S.eigenvalue 1 = S.firstNonzero)
    (hregime : p.a * p.α * p.μ ≤ S.firstNonzero ^ 2) :
    paperCriticalSensitivity S p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 =
      sigmaCriticalChiPaperFormula p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2
        (S.eigenvalue 1) :=
  paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant S p H
    (by simpa [minimalEquilibrium_fst_eq] using huStar)
    (minimalEquilibrium_snd_pos p huStar).le hmode1 hregime

/-- **Exact `χ*` for the concrete unit-interval Neumann spectrum.**  Here
`eigenvalue 1 = π² = firstNonzero`, so the first-mode-realisation hypothesis is
automatic and the regime condition is the explicit `aαμ ≤ π⁴`. -/
theorem paperCriticalSensitivity_unitInterval_eq_mode_one
    (p : CM2Params) {uStar vStar : ℝ} (huStar : 0 < uStar) (hvStar : 0 ≤ vStar)
    (hregime : p.a * p.α * p.μ ≤ (Real.pi ^ 2) ^ 2) :
    paperCriticalSensitivity unitIntervalNeumannSpectrum p uStar vStar =
      sigmaCriticalChiPaperFormula p uStar vStar
        (unitIntervalNeumannSpectrum.eigenvalue 1) := by
  refine paperCriticalSensitivity_eq_mode_one_of_firstMode_dominant
    unitIntervalNeumannSpectrum p unitIntervalNeumannSpectrum_hasNeumannSpectrum
    huStar hvStar ?_ ?_
  · simp [unitIntervalNeumannSpectrum]
  · simpa [unitIntervalNeumannSpectrum] using hregime

end ShenWork.Paper3
