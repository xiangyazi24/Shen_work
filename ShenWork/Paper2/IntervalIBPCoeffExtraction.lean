/-
# Higher-order IBP cosine-coefficient decay `|f̂ₙ| ≤ M/(nπ)^{2j}`

This file generalizes the `C²`-Neumann quadratic decay
`ShenWork.IntervalCosineCoeffDecay.cosineCoeff_decay` (`|f̂ₙ| ≤ M/(nπ)²`) to
arbitrary even order `2j` by **iterating the eigenfunction integration-by-parts
identity** `intervalCosineLaplacianCoeff_eq_of_contDiffOn`:

  `∫₀¹ cos(nπx) · (deriv (deriv g)) x dx = −(nπ)² · ∫₀¹ cos(nπx) · g x dx`.

Set up a *Neumann tower* `g : ℕ → (ℝ → ℝ)` with `g (i+1) = deriv (deriv (g i))`,
each `g i` being `C²` on `[0,1]` with genuine Neumann data on `deriv (g i)`.  A
finite induction over `j` then gives

  `∫₀¹ cos(nπx) · (g j) x dx = (−(nπ)²)^j · ∫₀¹ cos(nπx) · (g 0) x dx`,

so `Iₙ(g 0) = (−(nπ)²)^{-j} · Iₙ(g j)` and, when the top coefficient is bounded by
`M`, `|Iₙ(g 0)| ≤ M / (nπ)^{2j}`.  Packaged in the normalized `cosineCoeffs`, this
feeds the eigen-cube source tail (`SourceEigenCubeTailFields`, needing
`(nπ)^6 · |coeffₙ| ≤ C`, i.e. the `j = 3` / order-`6` case) UNCONDITIONALLY from
spatial smoothness.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.Paper2.IntervalMildPicardRegularity

open MeasureTheory intervalIntegral
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalMildPicardRegularity (cosineCoeffs_eq_factor_mul_integral)
open scoped Topology

namespace ShenWork.IntervalIBPCoeffExtraction

noncomputable section

/-- Abbreviation: the raw cosine integral `Iₙ(f) = ∫₀¹ cos(nπx) · f(x) dx`. -/
def rawCoeff (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x

/-- A **Neumann tower**: a sequence of functions `g i` (`g 0 = f`,
`g (i+1) = deriv (deriv (g i))`) such that each level `g i` (for `i < j`) is `C²`
on `[0,1]` with genuine Neumann data on `deriv (g i)`. -/
structure NeumannTower (g : ℕ → ℝ → ℝ) (j : ℕ) : Prop where
  step : ∀ i, i < j → g (i + 1) = deriv (deriv (g i))
  contDiff : ∀ i, i < j → ContDiffOn ℝ 2 (g i) (Set.Icc (0 : ℝ) 1)
  tend0 : ∀ i, i < j →
    Filter.Tendsto (deriv (g i)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
  tend1 : ∀ i, i < j →
    Filter.Tendsto (deriv (g i)) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  bc0 : ∀ i, i < j → deriv (g i) 0 = 0
  bc1 : ∀ i, i < j → deriv (g i) 1 = 0

/-- **Single eigenfunction IBP step**, recast on `rawCoeff`:
`Iₙ(g (i+1)) = −(nπ)² · Iₙ(g i)` whenever `g i` is `C²`-Neumann and
`g (i+1) = deriv (deriv (g i))`. -/
theorem rawCoeff_step (n : ℕ) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {i : ℕ} (hi : i < j) :
    rawCoeff n (g (i + 1)) = -((n : ℝ) * Real.pi) ^ 2 * rawCoeff n (g i) := by
  unfold rawCoeff
  rw [H.step i hi]
  exact intervalCosineLaplacianCoeff_eq_of_contDiffOn n (H.contDiff i hi)
    (H.tend0 i hi) (H.tend1 i hi) (H.bc0 i hi) (H.bc1 i hi)

/-- **IBP iteration**: after `j` levels,
`Iₙ(g j) = (−(nπ)²)^j · Iₙ(g 0)`. -/
theorem rawCoeff_iterate (n : ℕ) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) :
    rawCoeff n (g j) = (-((n : ℝ) * Real.pi) ^ 2) ^ j * rawCoeff n (g 0) := by
  induction j with
  | zero => simp
  | succ m ih =>
    -- Restrict the tower to its first `m` levels.
    have Hm : NeumannTower g m :=
      { step := fun i hi => H.step i (hi.trans (Nat.lt_succ_self m))
        contDiff := fun i hi => H.contDiff i (hi.trans (Nat.lt_succ_self m))
        tend0 := fun i hi => H.tend0 i (hi.trans (Nat.lt_succ_self m))
        tend1 := fun i hi => H.tend1 i (hi.trans (Nat.lt_succ_self m))
        bc0 := fun i hi => H.bc0 i (hi.trans (Nat.lt_succ_self m))
        bc1 := fun i hi => H.bc1 i (hi.trans (Nat.lt_succ_self m)) }
    have hstep := rawCoeff_step n H (Nat.lt_succ_self m)
    rw [hstep, ih Hm, pow_succ]
    ring

/-- **Higher-order raw-coefficient decay.**  For a Neumann tower of depth `j`
(so `g 0` is `C^{2j}`-Neumann), with the top-level coefficient bounded by `M`,
the base coefficient decays as `|Iₙ(g 0)| ≤ M / (nπ)^{2j}` for `n ≥ 1`. -/
theorem rawCoeff_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |rawCoeff n (g 0)| ≤ M / ((n : ℝ) * Real.pi) ^ (2 * j) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnpi_pos : (0 : ℝ) < (n : ℝ) * Real.pi := mul_pos hnpos Real.pi_pos
  have hbase_pos : (0 : ℝ) < ((n : ℝ) * Real.pi) ^ 2 := by positivity
  have hpow_pos : (0 : ℝ) < ((n : ℝ) * Real.pi) ^ (2 * j) := by positivity
  -- From the iteration, solve for the base coefficient.
  have hit := rawCoeff_iterate n H
  -- `Iₙ(g 0) = Iₙ(g j) / (−(nπ)²)^j`.
  have hcoef_ne : ((-((n : ℝ) * Real.pi) ^ 2) ^ j) ≠ 0 := by
    apply pow_ne_zero
    simp only [ne_eq, neg_eq_zero]
    exact ne_of_gt hbase_pos
  have hbase : rawCoeff n (g 0)
      = rawCoeff n (g j) / (-((n : ℝ) * Real.pi) ^ 2) ^ j := by
    rw [hit]; field_simp
  rw [hbase, abs_div]
  -- `|(−(nπ)²)^j| = (nπ)^{2j}`.
  have habs : |(-((n : ℝ) * Real.pi) ^ 2) ^ j| = ((n : ℝ) * Real.pi) ^ (2 * j) := by
    rw [abs_pow, abs_neg, abs_of_pos hbase_pos, ← pow_mul, Nat.mul_comm]
  rw [habs]
  exact div_le_div_of_nonneg_right hM hpow_pos.le

/-- **Higher-order normalized cosine-coefficient decay.**

The packaged form on `cosineCoeffs` (the normalized Neumann coefficient, factor `2`
on positive modes): for a Neumann tower of depth `j` with top coefficient bounded
by `M`, and `n ≥ 1`,

  `|cosineCoeffs (g 0) n| ≤ 2 M / (nπ)^{2j}`.

With `j = 3` (order `6`) this delivers `(nπ)^6 · |cosineCoeffs (g 0) n| ≤ 2 M`, the
exact eigen-cube source-tail bound (`SourceEigenCubeTailFields.sourceCube`) from
spatial `C^6`-Neumann smoothness. -/
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow_pos : (0 : ℝ) < ((n : ℝ) * Real.pi) ^ (2 * j) := by positivity
  rw [cosineCoeffs_eq_factor_mul_integral, if_neg (by omega : n ≠ 0)]
  change |2 * rawCoeff n (g 0)| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hdecay := rawCoeff_decay n hn H hM
  calc 2 * |rawCoeff n (g 0)|
      ≤ 2 * (M / ((n : ℝ) * Real.pi) ^ (2 * j)) := by
        apply mul_le_mul_of_nonneg_left hdecay (by norm_num)
    _ = 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j) := by ring

end

end ShenWork.IntervalIBPCoeffExtraction
