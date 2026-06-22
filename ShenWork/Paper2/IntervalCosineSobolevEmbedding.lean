/-
  ShenWork/Paper2/IntervalCosineSobolevEmbedding.lean

  WALL-C — the cosine-Sobolev → classical-smoothness embedding for the Neumann
  cosine scale on `[0,1]`.

  The fractional cosine Sobolev space `H^σ` (Brick 2 of the parabolic bootstrap,
  `ShenWork.Paper2.HSigmaScale.MemHSigma σ b := Summable (1+λ_k)^σ (b_k)²`,
  `λ_k = (kπ)²`) embeds into classical `C²` once `σ > 5/2`:

    `MemHSigma σ b`, `σ > 5/2`  ⟹  `x ↦ ∑'ₙ bₙ cos(nπx) ∈ C²`.

  Mechanism (the Sobolev-embedding inequality, coefficient form): the
  Cauchy–Schwarz / AM–GM estimate against the σ-weight gives the
  eigenvalue-weighted ℓ¹ control

    `Σ λ_n |b_n| ≤ ½ Σ (1+λ_n)^σ b_n² + ½ Σ λ_n²/(1+λ_n)^σ < ∞`,

  the second factor being summable exactly because `λ_n²/(1+λ_n)^σ ~ n^{4-2σ}` and
  `4 - 2σ < -1 ⟺ σ > 5/2`.  The eigenvalue-weighted ℓ¹ bound is the precise
  hypothesis `∑ λ_n|b_n| < ∞` consumed by the already-formalised termwise
  twice-differentiation engine `cosineCoeffSeries_contDiff_two`
  (`ShenWork.PDE.IntervalDuhamelClosedC2`), which carries the uniform
  convergence of the 0th/1st/2nd differentiated cosine series.  Thus WALL-C is,
  after that engine, a pure weighted-summability fact, proved here.

  Integer specialisation: `MemHSigma 3 b ⟹ C²` (the `H³ ↪ C²` step the bootstrap
  aims for; `3 > 5/2`).

  No `sorry`, no `admit`, no `native_decide`, no custom `axiom`.  New file only.
-/
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalHSigmaScale
import Mathlib.Analysis.PSeries

open Real
open ShenWork.Paper2.HSigmaScale
open ShenWork.CosineSpectrum (cosineMode)

noncomputable section

namespace ShenWork.Paper2.IntervalCosineSobolevEmbedding

/-- **σ-tail summability.**  For `σ > 5/2` the dual weight `λ_n²/(1+λ_n)^σ` is
summable: it is dominated, for `n ≥ 1`, by `π^{4-2σ} · n^{4-2σ}` with
`4 - 2σ < -1`, so the `p`-series criterion applies. -/
theorem dualWeight_summable {σ : ℝ} (hσ : 5 / 2 < σ) :
    Summable fun n : ℕ => (lam n) ^ 2 / (1 + lam n) ^ σ := by
  have hsummaj : Summable fun n : ℕ => Real.pi ^ (4 - 2 * σ) * (n : ℝ) ^ (4 - 2 * σ) := by
    apply Summable.mul_left
    exact summable_nat_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsummaj
  · have := one_add_lam_pos n; have := lam_nonneg n; positivity
  · have hlamval : lam n = ((n : ℝ) * Real.pi) ^ 2 := by
      unfold lam unitIntervalCosineEigenvalue; ring
    have hlamnn := lam_nonneg n
    have h1pos := one_add_lam_pos n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : lam 0 = 0 := by rw [hlamval]; simp
      rw [h0]; simp; positivity
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnpipos : (0 : ℝ) < (n : ℝ) * Real.pi := by positivity
      have hlampos : 0 < lam n := by rw [hlamval]; positivity
      have hbase : (lam n) ^ σ ≤ (1 + lam n) ^ σ :=
        Real.rpow_le_rpow hlamnn (by linarith) (by linarith)
      have step1 : (lam n) ^ 2 / (1 + lam n) ^ σ ≤ (lam n) ^ 2 / (lam n) ^ σ :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hbase
      have hsq : (lam n) ^ 2 = (lam n) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hdiv : (lam n) ^ (2 : ℝ) / (lam n) ^ σ = (lam n) ^ (2 - σ) := by
        rw [← Real.rpow_sub hlampos]
      have hrw : (lam n) ^ (2 - σ) = ((n : ℝ) * Real.pi) ^ (4 - 2 * σ) := by
        rw [hlamval, ← Real.rpow_natCast (((n : ℝ) * Real.pi)) 2,
            ← Real.rpow_mul (le_of_lt hnpipos)]
        ring_nf
      have hsplit : ((n : ℝ) * Real.pi) ^ (4 - 2 * σ)
          = (n : ℝ) ^ (4 - 2 * σ) * Real.pi ^ (4 - 2 * σ) := by
        rw [Real.mul_rpow (le_of_lt hnpos) (le_of_lt Real.pi_pos)]
      calc (lam n) ^ 2 / (1 + lam n) ^ σ ≤ (lam n) ^ 2 / (lam n) ^ σ := step1
        _ = (lam n) ^ (2 - σ) := by rw [hsq, hdiv]
        _ = (n : ℝ) ^ (4 - 2 * σ) * Real.pi ^ (4 - 2 * σ) := by rw [hrw, hsplit]
        _ = Real.pi ^ (4 - 2 * σ) * (n : ℝ) ^ (4 - 2 * σ) := by ring

/-- **Per-mode Sobolev-embedding (AM–GM) bound.**  `λ_n |b_n|` is bounded by the
half-sum of the `H^σ` summand `(1+λ_n)^σ b_n²` and the dual weight
`λ_n²/(1+λ_n)^σ`, whose geometric mean is exactly `λ_n |b_n|`. -/
theorem eigenvalue_abs_mode_le (σ : ℝ) (b : ℕ → ℝ) (n : ℕ) :
    lam n * |b n| ≤
      ((1 + lam n) ^ σ * (b n) ^ 2 + (lam n) ^ 2 / (1 + lam n) ^ σ) / 2 := by
  have h1pos := one_add_lam_pos n
  have hlamnn := lam_nonneg n
  set A : ℝ := (1 + lam n) ^ σ * (b n) ^ 2 with hA
  set C : ℝ := (lam n) ^ 2 / (1 + lam n) ^ σ with hC
  have hApos : 0 ≤ A := by rw [hA]; have := Real.rpow_nonneg h1pos.le σ; positivity
  have hCpos : 0 ≤ C := by rw [hC]; have := Real.rpow_pos_of_pos h1pos σ; positivity
  have hAC : A * C = (lam n * |b n|) ^ 2 := by
    rw [hA, hC]
    have hrne : (1 + lam n) ^ σ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h1pos σ)
    rw [mul_pow, sq_abs]
    field_simp
  have hT : 0 ≤ lam n * |b n| := by positivity
  nlinarith [sq_nonneg (A - C), hApos, hCpos, hAC, hT, sq_nonneg (lam n * |b n|)]

/-- **WALL-C, summability core (the Sobolev-embedding inequality, ℓ¹ form).**
If `b ∈ H^σ` with `σ > 5/2`, then the eigenvalue-weighted absolute series
`∑ λ_n |b_n|` converges.  This is exactly the hypothesis that the termwise
twice-differentiation engine `cosineCoeffSeries_contDiff_two` consumes. -/
theorem memHSigma_summable_eigenvalue_abs {σ : ℝ} (hσ : 5 / 2 < σ) {b : ℕ → ℝ}
    (hb : MemHSigma σ b) :
    Summable fun n => unitIntervalCosineEigenvalue n * |b n| := by
  have hmaj : Summable fun n : ℕ =>
      ((1 + lam n) ^ σ * (b n) ^ 2 + (lam n) ^ 2 / (1 + lam n) ^ σ) / 2 := by
    have h1 : Summable fun n : ℕ => (1 + lam n) ^ σ * (b n) ^ 2 := hb
    have h2 := dualWeight_summable hσ
    exact ((h1.add h2).div_const 2)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have := lam_nonneg n; positivity
  · exact eigenvalue_abs_mode_le σ b n

/-- **WALL-C (ambient form).**  `MemHSigma σ b` with `σ > 5/2` ⟹ the cosine
series `x ↦ ∑'ₙ bₙ cos(nπx)` is `ContDiff ℝ 2` on all of `ℝ`. -/
theorem memHSigma_contDiff_two {σ : ℝ} (hσ : 5 / 2 < σ) {b : ℕ → ℝ}
    (hb : MemHSigma σ b) :
    ContDiff ℝ 2 (fun x => ∑' n, b n * cosineMode n x) :=
  ShenWork.IntervalDuhamelClosedC2.cosineCoeffSeries_contDiff_two
    (memHSigma_summable_eigenvalue_abs hσ hb)

/-- **WALL-C (closed-domain form).**  `MemHSigma σ b`, `σ > 5/2` ⟹ the cosine
series is `ContDiffOn ℝ 2` on the closed interval `[0,1]`. -/
theorem memHSigma_contDiffOn_two {σ : ℝ} (hσ : 5 / 2 < σ) {b : ℕ → ℝ}
    (hb : MemHSigma σ b) :
    ContDiffOn ℝ 2 (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1) :=
  (memHSigma_contDiff_two hσ hb).contDiffOn

/-- **WALL-C (interior form).**  The same `C²` regularity on the open interval
`(0,1)` — the slice regularity `IterateSourceTimeData.sliceC2` /
`hchemFourier_of_chemDiv_C2Neumann` consume. -/
theorem memHSigma_contDiffOn_two_Ioo {σ : ℝ} (hσ : 5 / 2 < σ) {b : ℕ → ℝ}
    (hb : MemHSigma σ b) :
    ContDiffOn ℝ 2 (fun x => ∑' n, b n * cosineMode n x) (Set.Ioo (0 : ℝ) 1) :=
  (memHSigma_contDiffOn_two hσ hb).mono Set.Ioo_subset_Icc_self

/-- **WALL-C, integer specialisation `H³ ↪ C²`.**  The clean target the parabolic
bootstrap aims for (six half-steps): `MemHSigma 3 b ⟹ C²` on `[0,1]`. -/
theorem memHSigma_contDiffOn_two_of_memHSigma_three {b : ℕ → ℝ}
    (hb : MemHSigma 3 b) :
    ContDiffOn ℝ 2 (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1) :=
  memHSigma_contDiffOn_two (by norm_num) hb

#print axioms dualWeight_summable
#print axioms eigenvalue_abs_mode_le
#print axioms memHSigma_summable_eigenvalue_abs
#print axioms memHSigma_contDiff_two
#print axioms memHSigma_contDiffOn_two
#print axioms memHSigma_contDiffOn_two_Ioo
#print axioms memHSigma_contDiffOn_two_of_memHSigma_three

end ShenWork.Paper2.IntervalCosineSobolevEmbedding
