/-
# Eigen-cube source SUMMABILITY from source spatial-`C⁸` regularity (weight-three input)

`ShenWork.Paper2.SourceC6Representative.sourceEigenCubeTailFields_of_weightThree`
discharges the source-representative half of the χ₀<0 close but TAKES, as honest input,
summable envelopes `Esrc`/`Eadot` dominating the eigen-**cube** weight

  `λₙ³ · |L.aC s n|`   and   `λₙ³ · |L.srcC.adot s n|`     (`λₙ = (nπ)²`, so `λₙ³ = (nπ)^6`).

This file DERIVES those envelopes (and hence the eigen-cube SUMMABILITY) from the
source's spatial **`C⁸`-Neumann** regularity, via the committed higher-order IBP
coefficient decay at depth `j = 4`:

  `|cosineCoeffs f n| ≤ 2M/(nπ)^8`   ⇒   `λₙ³ · |cosineCoeffs f n| ≤ 2M/(nπ)^2`,

and `Summable (fun n => 2M/(nπ)^2)` (a `p = 2` series, `n = 0` term `= 0` in `ℝ`).

The regularity is supplied by the depth-`4` Neumann tower
`ShenWork.Paper2.NeumannTowerOfC8.neumannTower_four_of_contDiff_eight` (built from a
*global* `C⁸` representative, one level above the committed depth-`3` tower), and the
decay by the *generic* `ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay` at
`j = 4`.  Non-circular: the source `C⁸` regularity comes from the iterate climb, not
from the tail being derived here.

The producer `sourceEigenCubeTailFields_of_sourceC8` feeds the resulting envelopes into
`sourceEigenCubeTailFields_of_weightThree`, discharging its weight-three input from
honest source-`C⁸` data only.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalNeumannTowerOfC8
import ShenWork.Paper2.IntervalSourceC6Representative
import Mathlib.Analysis.PSeries

open Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower rawCoeff cosineCoeffs_decay)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.NeumannTowerOfC6 (gTower gTower_zero)
open ShenWork.Paper2.NeumannTowerOfC8 (neumannTower_four_of_contDiff_eight)
open ShenWork.Paper2.SourceRepresentative (higherNeumannCompatibility_of_doublyEven)
open ShenWork.Paper2.SourceC6Representative
  (doublyEven_cosineSeries l1_of_eigenCube_summable eigenCube_summable_of_bound
    abs_rawCoeff_le cosineCoeffs_eq_two_rawCoeff one_le_eigenvalue
    sourceEigenCubeTailFields_of_weightThree)

noncomputable section

namespace ShenWork.Paper2.EigenCubeSummability

/-- The eigen-cube envelope `E n = 2M/(nπ)²`.  Nonneg (for `M ≥ 0`), summable (`p = 2`),
and the `n = 0` term is `2M/0 = 0` in `ℝ`. -/
def cubeEnvelope (M : ℝ) (n : ℕ) : ℝ := 2 * M / ((n : ℝ) * Real.pi) ^ 2

theorem cubeEnvelope_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ cubeEnvelope M n := by
  unfold cubeEnvelope; positivity

/-- `Summable (cubeEnvelope M)`: it is `(2M/π²) · (1/n²)`, a convergent `p = 2` series. -/
theorem cubeEnvelope_summable (M : ℝ) : Summable (cubeEnvelope M) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have hscaled := hbase.mul_left (2 * M / Real.pi ^ 2)
  refine hscaled.congr (fun n => ?_)
  unfold cubeEnvelope
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hnpi : ((n : ℝ) * Real.pi) ^ 2 = (n : ℝ) ^ 2 * Real.pi ^ 2 := by ring
    rw [hnpi]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hpi0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

/-- **Per-mode eigen-cube bound from a depth-`4` Neumann tower.**

If the spatial function `f` has a depth-`4` Neumann tower `g` with `g 0 = f` and top
coefficient bounded by `M`, then for `n ≥ 1` the eigen-cube weight of the normalized
cosine coefficient is dominated by the envelope:

  `λₙ · (λₙ · (λₙ · |cosineCoeffs f n|)) ≤ cubeEnvelope M n = 2M/(nπ)²`.

This is the `j = 4` IBP decay `|cosineCoeffs f n| ≤ 2M/(nπ)^8` multiplied by
`λₙ³ = (nπ)^6`. -/
theorem eigenCube_envelope_bound_of_tower
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} (hg0 : g 0 = f)
    (H : NeumannTower g 4) {M : ℝ} (hM : ∀ n, 1 ≤ n → |rawCoeff n (g 4)| ≤ M)
    {n : ℕ} (hn : 1 ≤ n) :
    unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |cosineCoeffs f n|))
      ≤ cubeEnvelope M n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnpi : (0 : ℝ) < (n : ℝ) * Real.pi := mul_pos hnpos Real.pi_pos
  -- `j = 4` IBP decay on `cosineCoeffs`.
  have hdecay := cosineCoeffs_decay n hn H (hM n hn)
  rw [hg0] at hdecay
  -- Collapse the nested-eigenvalue LHS to `(nπ)^6 · |coeff|`.
  have hcube : unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |cosineCoeffs f n|))
      = ((n : ℝ) * Real.pi) ^ 6 * |cosineCoeffs f n| := by
    unfold unitIntervalCosineEigenvalue; ring
  rw [hcube]
  -- Multiply the decay by `(nπ)^6 ≥ 0`.
  have hpow6 : (0 : ℝ) ≤ ((n : ℝ) * Real.pi) ^ 6 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdecay hpow6
  refine le_trans hmul (le_of_eq ?_)
  -- `(nπ)^6 · (2M/(nπ)^8) = 2M/(nπ)^2 = cubeEnvelope M n`.
  unfold cubeEnvelope
  rw [show (2 * 4 : ℕ) = 8 from rfl]
  have hne : ((n : ℝ) * Real.pi) ≠ 0 := ne_of_gt hnpi
  rw [show (8 : ℕ) = 6 + 2 from rfl, pow_add]
  field_simp

/-- **Eigen-cube envelope domination for the FULL coefficient family.**

For a coefficient family `a : ℝ → ℕ → ℝ` whose `s`-slices are the normalized cosine
coefficients of depth-`4`-Neumann-tower spatial representatives with a uniform top
bound `M`, the eigen-cube weight is dominated, for *every* `n` (the `n = 0` mode is
free because `λ₀ = 0`), by the summable envelope `cubeEnvelope M`. -/
theorem eigenCube_envelope_full
    {a : ℝ → ℕ → ℝ} {g : ℝ → ℕ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hCoeff : ∀ s, 0 ≤ s → ∀ n, a s n = cosineCoeffs (g s 0) n)
    (hTower : ∀ s, 0 ≤ s → NeumannTower (g s) 4)
    (hTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (g s 4)| ≤ M) :
    ∀ s, 0 ≤ s → ∀ n, unitIntervalCosineEigenvalue n *
      (unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |a s n|))
      ≤ cubeEnvelope M n := by
  intro s hs n
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- `n = 0`: `λ₀ = (0·π)² = 0`, so the cube weight is `0 ≤ cubeEnvelope M 0`.
    subst hn0
    have hlam0 : unitIntervalCosineEigenvalue 0 = 0 := by
      unfold unitIntervalCosineEigenvalue; simp
    rw [hlam0]
    simp only [zero_mul, mul_zero]
    exact cubeEnvelope_nonneg hM 0
  · rw [hCoeff s hs n]
    exact eigenCube_envelope_bound_of_tower (rfl) (hTower s hs) (hTop s hs) hn1

/-- **The per-restart eigen-cube source tail from honest source-`C⁸`-Neumann regularity.**

From spatial representatives `fSrc`/`fAdot : ℝ → ℝ → ℝ` of the source / time-derivative
coefficient families `L.aC` / `L.srcC.adot` that are **globally `C⁸`** with their odd
derivatives `∂ₓ`, `∂ₓ³`, `∂ₓ⁵`, `∂ₓ⁷` vanishing at the endpoints (the cosine / no-flux
parity), plus a uniform sup-bound `M`/`Mdot` on the top tower coefficient
`rawCoeff n (∂ₓ⁸ ·)`, we DERIVE the eigen-cube envelopes (`cubeEnvelope M`/`cubeEnvelope
Mdot`, summable `p = 2` series) and feed them into
`sourceEigenCubeTailFields_of_weightThree`.

This discharges the weight-three input of
`ShenWork.Paper2.SourceC6Representative.sourceEigenCubeTailFields_of_weightThree` from
source spatial-`C⁸` data only — non-circular (the `C⁸` comes from the iterate climb, not
from the tail being produced here). -/
theorem sourceEigenCubeTailFields_of_sourceC8
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T σ : ℝ}
    (L : LocalRestart p u T σ)
    {fSrc fAdot : ℝ → ℝ → ℝ} {M Mdot : ℝ}
    (hM : 0 ≤ M) (hMdot : 0 ≤ Mdot)
    -- source: `C⁸` representative, cosine-coeff identification, Neumann data, top bound:
    (hSrcCoeff : ∀ s, 0 ≤ s → ∀ n, L.aC s n = cosineCoeffs (fSrc s) n)
    (hSrcCD8 : ∀ s, 0 ≤ s → ContDiff ℝ (8 : ℕ) (fSrc s))
    (hSrcN0 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fSrc s) i) 0 = 0)
    (hSrcN1 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fSrc s) i) 1 = 0)
    (hSrcTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fSrc s) 4)| ≤ M)
    -- time derivative: `C⁸` representative, identification, Neumann data, top bound:
    (hAdotCoeff : ∀ s, 0 ≤ s → ∀ n, L.srcC.adot s n = cosineCoeffs (fAdot s) n)
    (hAdotCD8 : ∀ s, 0 ≤ s → ContDiff ℝ (8 : ℕ) (fAdot s))
    (hAdotN0 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fAdot s) i) 0 = 0)
    (hAdotN1 : ∀ s, 0 ≤ s → ∀ i, i < 4 → deriv (gTower (fAdot s) i) 1 = 0)
    (hAdotTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fAdot s) 4)| ≤ Mdot)
    -- zero-mode bounds (the tower is silent on `n = 0`):
    {C0 C0dot : ℝ} (hC0 : 0 ≤ C0) (hC0dot : 0 ≤ C0dot)
    (hSrcZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (hAdotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot) :
    ShenWork.Paper2.ChiNegSourceTail.SourceEigenCubeTailFields
      L C0 (2 * (∑' m, cubeEnvelope M m)) C0dot (2 * (∑' m, cubeEnvelope Mdot m)) := by
  -- Depth-`4` Neumann towers `gTower (fSrc s)` / `gTower (fAdot s)` from the `C⁸` reps.
  have hSrcTower : ∀ s, 0 ≤ s → NeumannTower (gTower (fSrc s)) 4 := fun s hs =>
    neumannTower_four_of_contDiff_eight (hSrcCD8 s hs) (hSrcN0 s hs) (hSrcN1 s hs)
  have hAdotTower : ∀ s, 0 ≤ s → NeumannTower (gTower (fAdot s)) 4 := fun s hs =>
    neumannTower_four_of_contDiff_eight (hAdotCD8 s hs) (hAdotN0 s hs) (hAdotN1 s hs)
  -- Eigen-cube envelope domination from the depth-`4` towers (j = 4 IBP decay).
  have hSrcEnv := eigenCube_envelope_full (a := L.aC) (g := fun s => gTower (fSrc s)) hM
    (fun s hs n => by simp only [gTower_zero]; exact hSrcCoeff s hs n) hSrcTower hSrcTop
  have hAdotEnv := eigenCube_envelope_full (a := L.srcC.adot)
    (g := fun s => gTower (fAdot s)) hMdot
    (fun s hs n => by simp only [gTower_zero]; exact hAdotCoeff s hs n) hAdotTower hAdotTop
  -- Feed the summable envelopes into the weight-three producer.
  exact sourceEigenCubeTailFields_of_weightThree L
    (cubeEnvelope_nonneg hM) (cubeEnvelope_summable M) hSrcEnv
    (cubeEnvelope_nonneg hMdot) (cubeEnvelope_summable Mdot) hAdotEnv
    hC0 hC0dot hSrcZero hAdotZero

#print axioms sourceEigenCubeTailFields_of_sourceC8

end ShenWork.Paper2.EigenCubeSummability
