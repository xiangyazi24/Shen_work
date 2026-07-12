/-
  Uniform spectral-gap extraction for the Paper3 unit-interval linearization.

  Modewise strict negativity is not by itself a numerical gap on an arbitrary
  spectrum.  On the unit interval, however, the eigenvalues tend to infinity
  and the chemotactic multiplier stays bounded.  Thus all sufficiently high
  modes lie below `-1`; the remaining finite set has a positive minimum gap.
-/
import ShenWork.Paper3.EventualExponentialStability
import ShenWork.PDE.SectorialOperator

namespace ShenWork.Paper3

open ShenWork.PDE.SectorialOperator

noncomputable section

/-- A finite family of strictly negative nonzero modes admits a uniform
positive gap. -/
private theorem finite_nonzero_uniform_gap
    (f : ℕ → ℝ) (hneg : ∀ n : ℕ, n ≠ 0 → f n < 0) :
    ∀ N : ℕ, ∃ rate > 0, ∀ n : ℕ, n < N → n ≠ 0 → f n ≤ -rate := by
  intro N
  induction N with
  | zero =>
      exact ⟨1, one_pos, by intro n hn; omega⟩
  | succ N ih =>
      rcases ih with ⟨rate, hrate, hfinite⟩
      by_cases hN0 : N = 0
      · refine ⟨rate, hrate, ?_⟩
        intro n hn hne
        have hn0 : n = 0 := by omega
        exact False.elim (hne hn0)
      · let nextRate : ℝ := min rate (-f N)
        have hnext : 0 < nextRate := by
          exact lt_min hrate (neg_pos.mpr (hneg N hN0))
        refine ⟨nextRate, hnext, ?_⟩
        intro n hn hne
        have hnle : n ≤ N := Nat.lt_succ_iff.mp hn
        rcases eq_or_lt_of_le hnle with hEq | hlt
        · subst n
          have hle : nextRate ≤ -f N := min_le_right _ _
          linarith
        · have hmode := hfinite n hlt hne
          have hle : nextRate ≤ rate := min_le_left _ _
          linarith

/-- Rewrite the chemotactic contribution as a bounded scalar coefficient
times `lambda / (mu + lambda)`. -/
private theorem sigma_eq_bounded_multiplier
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN) :
    sigma p uStar vStar lambdaN =
      -lambdaN +
        (p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
            (1 + vStar) ^ p.β) *
          (lambdaN / (p.μ + lambdaN)) -
        p.a * p.α := by
  have hvpow : 0 < (1 + vStar) ^ p.β :=
    Real.rpow_pos_of_pos (by linarith) _
  have hmul : 0 < p.μ + lambdaN := by linarith [p.hμ]
  unfold sigma
  field_simp [ne_of_gt hvpow, ne_of_gt hmul]

/-- The non-diffusive part of every nonnegative mode is bounded uniformly in
the eigenvalue. -/
private theorem sigma_le_neg_lambda_add_abs_multiplier
    (p : CM2Params) {uStar vStar lambdaN : ℝ}
    (hvStar : 0 ≤ vStar) (hlambda : 0 ≤ lambdaN) :
    sigma p uStar vStar lambdaN ≤
      -lambdaN +
        |p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
          (1 + vStar) ^ p.β| := by
  let A : ℝ :=
    p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
      (1 + vStar) ^ p.β
  let r : ℝ := lambdaN / (p.μ + lambdaN)
  have hden : 0 < p.μ + lambdaN := by linarith [p.hμ]
  have hr0 : 0 ≤ r := div_nonneg hlambda hden.le
  have hr1 : r ≤ 1 := by
    dsimp [r]
    exact (div_le_one hden).2 (by linarith [p.hμ])
  have hAr : A * r ≤ |A| := by
    calc
      A * r ≤ |A| * r :=
        mul_le_mul_of_nonneg_right (le_abs_self A) hr0
      _ ≤ |A| * 1 := mul_le_mul_of_nonneg_left hr1 (abs_nonneg A)
      _ = |A| := mul_one _
  rw [sigma_eq_bounded_multiplier p hvStar hlambda]
  change -lambdaN + A * r - p.a * p.α ≤ -lambdaN + |A|
  have hdamp : 0 ≤ p.a * p.α := mul_nonneg p.ha p.hα.le
  linarith

/-- Modewise stability on the unit interval yields a positive uniform gap on
all nonzero modes.  This is the new linear extraction needed by the nonlinear
Duhamel argument. -/
theorem unitIntervalLinearMassSpectralGap_of_linearlyStable
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar) :
    ∃ rate > 0,
      UnitIntervalLinearMassSpectralGap p uStar vStar rate := by
  let A : ℝ :=
    p.χ₀ * p.ν * p.γ * uStar ^ (p.m + p.γ - 1) /
      (1 + vStar) ^ p.β
  have hpiSqPos : 0 < Real.pi ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt Real.pi_pos)
  obtain ⟨N, hN⟩ := exists_nat_gt ((|A| + 1) / (Real.pi ^ 2))
  have hAN : |A| + 1 < (N : ℝ) * Real.pi ^ 2 := by
    exact (div_lt_iff₀ hpiSqPos).mp hN
  have hNpos : 0 < N := by
    by_contra hnot
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    norm_num at hAN
    linarith [abs_nonneg A]
  have htail :
      ∀ n : ℕ, N ≤ n →
        unitIntervalLinearizedGrowth p uStar vStar n ≤ -1 := by
    intro n hn
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hNnMul :
        (N : ℝ) * Real.pi ^ 2 ≤ (n : ℝ) * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right hNn hpiSqPos.le
    have hAn : |A| + 1 < (n : ℝ) * Real.pi ^ 2 :=
      lt_of_lt_of_le hAN hNnMul
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_lt_of_le hNpos hn))
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have hsqpi :
        (n : ℝ) * Real.pi ^ 2 ≤ (n : ℝ) ^ 2 * Real.pi ^ 2 :=
      mul_le_mul_of_nonneg_right hnsq hpiSqPos.le
    have hlambda : |A| + 1 ≤ unitIntervalNeumannSpectrum.eigenvalue n := by
      dsimp [unitIntervalNeumannSpectrum]
      exact (le_of_lt hAn).trans hsqpi
    have hsigma :=
      sigma_le_neg_lambda_add_abs_multiplier p (uStar := uStar) heq.v_nonneg
        (unitIntervalNeumannSpectrum_hasNeumannSpectrum.eigenvalue_nonneg n)
    change unitIntervalLinearizedGrowth p uStar vStar n ≤ -1
    change sigma p uStar vStar
      (unitIntervalNeumannSpectrum.eigenvalue n) ≤ -1
    change |A| + 1 ≤ unitIntervalNeumannSpectrum.eigenvalue n at hlambda
    change sigma p uStar vStar
      (unitIntervalNeumannSpectrum.eigenvalue n) ≤
        -unitIntervalNeumannSpectrum.eigenvalue n + |A| at hsigma
    linarith
  rcases finite_nonzero_uniform_gap
      (unitIntervalLinearizedGrowth p uStar vStar) hstable N with
    ⟨finiteRate, hfiniteRate, hfinite⟩
  let rate : ℝ := min finiteRate 1
  have hrate : 0 < rate := lt_min hfiniteRate one_pos
  refine ⟨rate, hrate, hrate, ?_⟩
  intro n hn0
  by_cases hnN : n < N
  · have hmode := hfinite n hnN hn0
    have hrle : rate ≤ finiteRate := min_le_left _ _
    linarith
  · have hmode := htail n (Nat.le_of_not_gt hnN)
    have hrle : rate ≤ 1 := min_le_right _ _
    linarith

/-- In the positive-logistic branch, adding the zero-mode damping `a*alpha`
to the extracted nonzero gap yields a full spectral gap. -/
theorem unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hstable : LinearlyStable unitIntervalNeumannSpectrum p uStar vStar)
    (ha : 0 < p.a) :
    ∃ rate > 0, UnitIntervalLinearSpectralGap p uStar vStar rate := by
  rcases unitIntervalLinearMassSpectralGap_of_linearlyStable p heq hstable with
    ⟨nonzeroRate, hnonzeroRate, hnonzeroGap⟩
  let rate : ℝ := min nonzeroRate (p.a * p.α)
  have hdamp : 0 < p.a * p.α := mul_pos ha p.hα
  have hrate : 0 < rate := lt_min hnonzeroRate hdamp
  refine ⟨rate, hrate, hrate, ?_⟩
  intro n
  by_cases hn0 : n = 0
  · subst n
    have hrle : rate ≤ p.a * p.α := min_le_right _ _
    simpa [unitIntervalLinearizedGrowth, unitIntervalNeumannSpectrum, sigma]
      using (neg_le_neg hrle)
  · have hmode := hnonzeroGap.2 n hn0
    have hrle : rate ≤ nonzeroRate := min_le_left _ _
    linarith

#print axioms unitIntervalLinearMassSpectralGap_of_linearlyStable
#print axioms unitIntervalLinearSpectralGap_of_linearlyStable_of_a_pos

end

end ShenWork.Paper3
