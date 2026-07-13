import ShenWork.Paper3.ThresholdOrdering
import Mathlib.Analysis.MeanInequalities

/-! # The minimal-model half-threshold lies below the spectral threshold -/

namespace ShenWork.Paper3

open ShenWork.Paper2

noncomputable section

/-- The elementary coefficient inequality used in Lemma A.8. -/
private theorem two_beta_sub_one_le_youngCoefficient
    {beta : ℝ} (hbeta : 1 ≤ beta) :
    2 * beta - 1 ≤ beta * (beta / (beta - 1)) ^ (beta - 1) := by
  rcases eq_or_lt_of_le hbeta with rfl | hbeta
  · norm_num
  have hbeta0 : 0 < beta := lt_trans zero_lt_one hbeta
  have hsub0 : 0 < beta - 1 := sub_pos.mpr hbeta
  let q : ℝ := (beta - 1) / beta
  have hq0 : 0 < q := div_pos hsub0 hbeta0
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hbeta0]
    linarith
  have hweight0 : 0 ≤ 1 / beta := by positivity
  have hweights : q + 1 / beta = 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  have hqplus0 : 0 ≤ 1 + q := by linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hq0.le hweight0 hq0.le hqplus0 hweights
  have harith : q * q + (1 / beta) * (1 + q) = 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  rw [harith] at hamgm
  have hleft0 : 0 ≤ q ^ q * (1 + q) ^ (1 / beta) :=
    mul_nonneg (Real.rpow_nonneg hq0.le _) (Real.rpow_nonneg hqplus0 _)
  have hraised := Real.rpow_le_rpow hleft0 hamgm hbeta0.le
  have hqmul : q * beta = beta - 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
  have hinvmul : (1 / beta) * beta = 1 := by
    field_simp [hbeta0.ne']
  have hpower :
      (q ^ q * (1 + q) ^ (1 / beta)) ^ beta =
        q ^ (beta - 1) * (1 + q) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hq0.le _)
        (Real.rpow_nonneg hqplus0 _),
      ← Real.rpow_mul hq0.le, ← Real.rpow_mul hqplus0,
      hqmul, hinvmul, Real.rpow_one]
  have hqbound : q ^ (beta - 1) * (1 + q) ≤ 1 := by
    rw [hpower] at hraised
    simpa using hraised
  have hqpow0 : 0 < q ^ (beta - 1) := Real.rpow_pos_of_pos hq0 _
  have hratio : 1 + q ≤ (q ^ (beta - 1))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hqpow0]
    simpa [mul_comm] using hqbound
  have hbase : beta / (beta - 1) = q⁻¹ := by
    dsimp [q]
    field_simp [hbeta0.ne', hsub0.ne']
  have hcoef : 1 + q ≤ (beta / (beta - 1)) ^ (beta - 1) := by
    rw [hbase, Real.inv_rpow hq0.le]
    exact hratio
  have hidentity : beta * (1 + q) = 2 * beta - 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  rw [← hidentity]
  exact mul_le_mul_of_nonneg_left hcoef hbeta0.le

/-- For `beta ≥ 1`, the coefficient occurring in the minimal threshold obeys
`(2 beta - 1) v ≤ (1+v)^beta` for every nonnegative signal level. -/
theorem two_beta_sub_one_mul_le_one_add_rpow
    {beta v : ℝ} (hbeta : 1 ≤ beta) (hv : 0 ≤ v) :
    (2 * beta - 1) * v ≤ (1 + v) ^ beta := by
  rcases eq_or_lt_of_le hbeta with rfl | hbeta
  · norm_num
  have hbeta0 : 0 < beta := lt_trans zero_lt_one hbeta
  have hsub0 : 0 < beta - 1 := sub_pos.mpr hbeta
  let q : ℝ := (beta - 1) / beta
  have hq0 : 0 < q := div_pos hsub0 hbeta0
  have hweight0 : 0 ≤ 1 / beta := by positivity
  have hweights : q + 1 / beta = 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
    ring
  have hpone0 : 0 ≤ beta / (beta - 1) := (div_pos hbeta0 hsub0).le
  have hptwo0 : 0 ≤ beta * v := mul_nonneg hbeta0.le hv
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hq0.le hweight0 hpone0 hptwo0 hweights
  have harith :
      q * (beta / (beta - 1)) + (1 / beta) * (beta * v) = 1 + v := by
    dsimp [q]
    field_simp [hbeta0.ne', hsub0.ne']
  rw [harith] at hamgm
  have hleft0 :
      0 ≤ (beta / (beta - 1)) ^ q * (beta * v) ^ (1 / beta) :=
    mul_nonneg (Real.rpow_nonneg hpone0 _ ) (Real.rpow_nonneg hptwo0 _)
  have hraised := Real.rpow_le_rpow hleft0 hamgm hbeta0.le
  have hqmul : q * beta = beta - 1 := by
    dsimp [q]
    field_simp [hbeta0.ne']
  have hinvmul : (1 / beta) * beta = 1 := by
    field_simp [hbeta0.ne']
  have hpower :
      ((beta / (beta - 1)) ^ q * (beta * v) ^ (1 / beta)) ^ beta =
        (beta / (beta - 1)) ^ (beta - 1) * (beta * v) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hpone0 _)
        (Real.rpow_nonneg hptwo0 _),
      ← Real.rpow_mul hpone0, ← Real.rpow_mul hptwo0,
      hqmul, hinvmul, Real.rpow_one]
  have hyoung :
      (beta / (beta - 1)) ^ (beta - 1) * (beta * v) ≤
        (1 + v) ^ beta := by
    rw [hpower] at hraised
    exact hraised
  have hcoef := two_beta_sub_one_le_youngCoefficient hbeta.le
  have hscaled := mul_le_mul_of_nonneg_right hcoef hv
  calc
    (2 * beta - 1) * v ≤
        (beta * (beta / (beta - 1)) ^ (beta - 1)) * v := hscaled
    _ = (beta / (beta - 1)) ^ (beta - 1) * (beta * v) := by ring
    _ ≤ (1 + v) ^ beta := hyoung

/-- On the one-dimensional minimal branch, the half-threshold appearing in
Lemma A.8 lies below the actual discrete critical sensitivity.  The factor
`1 / 2` is essential: the corresponding statement with `chiBeta p` in place
of `chiBeta p / 2` is not the paper's comparison. -/
theorem chiBeta_half_le_paperCriticalSensitivity_minimal_unitInterval
    (p : CM2Params) {uStar : ℝ}
    (hN : p.N = 1) (hm : p.m = 1)
    (hbeta : 1 ≤ p.β) (huStar : 0 < uStar) :
    chiBeta p / 2 ≤
      paperCriticalSensitivity unitIntervalNeumannSpectrum p
        (minimalEquilibrium p uStar).1
        (minimalEquilibrium p uStar).2 := by
  let vStar := (minimalEquilibrium p uStar).2
  have hvStar : 0 < vStar := by
    simpa [vStar] using minimalEquilibrium_snd_pos p huStar
  have hnum : 0 ≤ 2 * p.β - 1 := by linarith
  have hdenEq :
      max (2 : ℝ) (p.γ * (p.N : ℝ)) = max 2 p.γ := by
    rw [hN]
    norm_num
  have hmaxPos : 0 < max (2 : ℝ) p.γ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hhalf : chiBeta p / 2 ≤ (2 * p.β - 1) / p.γ := by
    have hdiv :
        (2 * p.β - 1) / max 2 p.γ ≤
          (2 * p.β - 1) / p.γ :=
      div_le_div_of_nonneg_left hnum p.hγ (le_max_right _ _)
    rw [chiBeta, hdenEq]
    calc
      (2 * (2 * p.β - 1) / max 2 p.γ) / 2 =
          (2 * p.β - 1) / max 2 p.γ := by
            field_simp [ne_of_gt hmaxPos]
      _ ≤ (2 * p.β - 1) / p.γ := hdiv
  have hyoung :
      (2 * p.β - 1) * vStar ≤ (1 + vStar) ^ p.β :=
    two_beta_sub_one_mul_le_one_add_rpow hbeta hvStar.le
  have hratio :
      (2 * p.β - 1) / p.γ ≤
        (1 + vStar) ^ p.β / (p.γ * vStar) := by
    have hden : 0 < p.γ * vStar := mul_pos p.hγ hvStar
    calc
      (2 * p.β - 1) / p.γ =
          ((2 * p.β - 1) * vStar) / (p.γ * vStar) := by
            field_simp [ne_of_gt p.hγ, ne_of_gt hvStar]
      _ ≤ (1 + vStar) ^ p.β / (p.γ * vStar) :=
        (div_le_div_iff_of_pos_right hden).2 hyoung
  let A : ℝ :=
    (1 + vStar) ^ p.β /
      (p.ν * p.γ * uStar ^ (p.m + p.γ - 1))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (Real.rpow_nonneg (by linarith [hvStar]) _)
      (mul_pos (mul_pos p.hν p.hγ)
        (Real.rpow_pos_of_pos huStar _)).le
  have hratioEq :
      (1 + vStar) ^ p.β / (p.γ * vStar) = A * p.μ := by
    have hpow : uStar ^ (p.m + p.γ - 1) = uStar ^ p.γ := by
      rw [hm]
      ring_nf
    have hvrel : p.μ * vStar = p.ν * uStar ^ p.γ := by
      simpa [vStar, minimalEquilibrium_fst_eq] using
        minimalEquilibrium_elliptic_relation p uStar
    have hvEq : vStar = p.ν * uStar ^ p.γ / p.μ := by
      apply (eq_div_iff (ne_of_gt p.hμ)).2
      nlinarith [hvrel]
    dsimp [A]
    rw [hpow, hvEq]
    field_simp [ne_of_gt p.hμ, ne_of_gt p.hν, ne_of_gt p.hγ,
      ne_of_gt (Real.rpow_pos_of_pos huStar p.γ)]
  have hcritical :=
    paperCriticalSensitivity_minimalEquilibrium_ge_firstNonzero_lower
      unitIntervalNeumannSpectrum p
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar
  have hAstep :
      A * p.μ ≤ A * (p.μ + unitIntervalNeumannSpectrum.firstNonzero) := by
    exact mul_le_mul_of_nonneg_left
      (by linarith [unitIntervalNeumannSpectrum_hasNeumannSpectrum.firstNonzero_pos]) hA
  calc
    chiBeta p / 2 ≤ (2 * p.β - 1) / p.γ := hhalf
    _ ≤ (1 + vStar) ^ p.β / (p.γ * vStar) := hratio
    _ = A * p.μ := hratioEq
    _ ≤ A * (p.μ + unitIntervalNeumannSpectrum.firstNonzero) := hAstep
    _ ≤ paperCriticalSensitivity unitIntervalNeumannSpectrum p
          (minimalEquilibrium p uStar).1
          (minimalEquilibrium p uStar).2 := by
      simpa [A, vStar, minimalEquilibrium_fst_eq] using hcritical

/-- Both explicit minimal thresholds are bounded by `chiBeta / 2`, exactly as
they are defined in `(2.22)` and `(2.23)`. -/
theorem MinimalGlobalStabilityFormulaCondition.chi_lt_chiBeta_half
    {p : CM2Params} {uStar uBar vLower : ℝ}
    (h : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower) :
    p.χ₀ < chiBeta p / 2 := by
  rcases h with h | h
  · exact h.2.trans_le
      ((chiMinimal1Formula_le_min_half_sqrt
        p 1 uStar uBar vLower).trans (min_le_left _ _))
  · exact h.2.2.trans_le
      ((chiMinimal2Formula_le_min_half_sqrt
        p uBar vLower).trans (min_le_left _ _))

/-- The paper's two minimal formula branches imply the actual discrete
linear-stability condition on the one-dimensional Neumann interval. -/
theorem MinimalGlobalStabilityFormulaCondition.linearlyStable_unitInterval
    (p : CM2Params) {uStar uBar vLower : ℝ}
    (hN : p.N = 1) (hm : p.m = 1)
    (hbeta : 1 ≤ p.β) (huStar : 0 < uStar)
    (h : MinimalGlobalStabilityFormulaCondition p uStar uBar vLower) :
    let eq := minimalEquilibrium p uStar
    LinearlyStable unitIntervalNeumannSpectrum p eq.1 eq.2 := by
  exact
    minimalEquilibrium_linearlyStable_of_chi_lt_paperCriticalSensitivity_neumann
      unitIntervalNeumannSpectrum p
      unitIntervalNeumannSpectrum_hasNeumannSpectrum huStar
      (h.chi_lt_chiBeta_half.trans_le
        (chiBeta_half_le_paperCriticalSensitivity_minimal_unitInterval
          p hN hm hbeta huStar))

#print axioms two_beta_sub_one_mul_le_one_add_rpow
#print axioms
  chiBeta_half_le_paperCriticalSensitivity_minimal_unitInterval
#print axioms MinimalGlobalStabilityFormulaCondition.chi_lt_chiBeta_half
#print axioms MinimalGlobalStabilityFormulaCondition.linearlyStable_unitInterval

end

end ShenWork.Paper3
