/-
# Bridge: `SourceEigenCubeTailFields` from spatial Neumann towers

The eigen-cube source tail (`ShenWork.Paper2.ChiNegSourceTail.SourceEigenCubeTailFields`)
asks, for the concrete source `L.aC` and its time derivative `L.srcC.adot`, the
pointwise bounds

  `|L.aC s 0| ≤ C0`,  `λₙ³ · |L.aC s n| ≤ C`   (n ≥ 1),
  `|L.srcC.adot s 0| ≤ C0dot`,  `λₙ³ · |L.srcC.adot s n| ≤ Cdot`   (n ≥ 1),

with `λₙ = unitIntervalCosineEigenvalue n = (nπ)²`, so `λₙ³ = (nπ)^6 = (nπ)^{2·3}`.

The IBP coefficient-extraction lemma
`ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay` gives, for a depth-`j`
Neumann tower `g` of a spatial function `g 0` with top coefficient bounded by `M`,

  `|cosineCoeffs (g 0) n| ≤ 2 M / (nπ)^{2j}`   (n ≥ 1).

At `j = 3` this is exactly `(nπ)^6 · |cosineCoeffs (g 0) n| ≤ 2 M`, i.e.
`λₙ³ · |cosineCoeffs (g 0) n| ≤ 2 M` — the eigen-cube `sourceCube` bound with `C := 2 M`.

This file builds `SourceEigenCubeTailFields_of_neumannTower`, taking the depth-`3`
Neumann tower data for the spatial source `L.aC s` and its time derivative
`L.srcC.adot s` (the honest `C⁶`-Neumann spatial regularity of the source, supplied
by a later climb-instantiation lane) as the bridge's HYPOTHESES, and producing
`SourceEigenCubeTailFields`.  No `sorry`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalChiNegSourceTail
import ShenWork.Paper2.IntervalIBPCoeffExtraction

open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower rawCoeff cosineCoeffs_decay)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

namespace ShenWork.Paper2.EigenCubeTailFromTower

noncomputable section

variable {p : CM2Params}
variable {u : ℝ → ShenWork.IntervalDomain.intervalDomainPoint → ℝ}
variable {T σ : ℝ}

/-- `λₙ³ = (nπ)^{2·3} = (nπ)^6`, the algebraic identity converting the eigen-cube
weight into the IBP decay denominator.  Both sides are defeq up to `pow` reshaping. -/
theorem eigenCube_eq_pow (n : ℕ) :
    unitIntervalCosineEigenvalue n ^ (3 : ℕ)
      = ((n : ℝ) * Real.pi) ^ (2 * 3) := by
  unfold unitIntervalCosineEigenvalue
  rw [← pow_mul]

/-- **Per-mode bridge.**  If the spatial function `f` has a depth-`3` Neumann tower
`g` with `g 0 = f` and top coefficient bounded by `M`, then the normalized cosine
coefficient of `f` satisfies the eigen-cube bound `λₙ³ · |cosineCoeffs f n| ≤ 2 M`
for `n ≥ 1`. -/
theorem eigenCube_bound_of_tower
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} (hg0 : g 0 = f)
    (H : NeumannTower g 3) {M : ℝ} (hM : ∀ n, 1 ≤ n → |rawCoeff n (g 3)| ≤ M)
    {n : ℕ} (hn : 1 ≤ n) :
    unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |cosineCoeffs f n| ≤ 2 * M := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow_pos : (0 : ℝ) < ((n : ℝ) * Real.pi) ^ (2 * 3) := by positivity
  have hdecay := cosineCoeffs_decay n hn H (hM n hn)
  rw [hg0] at hdecay
  rw [eigenCube_eq_pow]
  -- `(nπ)^6 · |coeff| ≤ (nπ)^6 · (2M/(nπ)^6) = 2M`.
  have := mul_le_mul_of_nonneg_left hdecay hpow_pos.le
  calc ((n : ℝ) * Real.pi) ^ (2 * 3) * |cosineCoeffs f n|
      ≤ ((n : ℝ) * Real.pi) ^ (2 * 3) * (2 * M / ((n : ℝ) * Real.pi) ^ (2 * 3)) :=
        this
    _ = 2 * M := by field_simp

/-- **The bridge.**  From depth-`3` Neumann tower data for the spatial source `L.aC s`
and its time derivative `L.srcC.adot s` (the source's `C⁶`-Neumann spatial regularity,
honest hypotheses here), plus the zero-mode bounds, produce
`SourceEigenCubeTailFields` with cube constants `C := 2 M`, `Cdot := 2 Mdot`.

* `aC`/`adot` cube fields come from `eigenCube_bound_of_tower` (j = 3).
* `aC`/`adot` zero-mode fields are supplied directly as hypotheses.

`gSrc s`/`gAdot s` are the towers, `hSrc0`/`hAdot0` identify the base level with the
source coefficient as a `cosineCoeffs`, `hSrcTop`/`hAdotTop` bound the top coefficient. -/
theorem SourceEigenCubeTailFields_of_neumannTower
    (L : LocalRestart p u T σ)
    {fSrc fAdot : ℝ → ℝ → ℝ}
    {gSrc gAdot : ℝ → ℕ → ℝ → ℝ}
    {C0 C0dot M Mdot : ℝ}
    (hC0 : 0 ≤ C0) (hC0dot : 0 ≤ C0dot)
    -- source coefficient is the normalized cosine coefficient of `fSrc s`:
    (hSrcCoeff : ∀ s, 0 ≤ s → ∀ n, L.aC s n = cosineCoeffs (fSrc s) n)
    (hSrc0Base : ∀ s, gSrc s 0 = fSrc s)
    (hSrcTower : ∀ s, 0 ≤ s → NeumannTower (gSrc s) 3)
    (hSrcTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gSrc s 3)| ≤ M)
    -- time-derivative coefficient is the normalized cosine coefficient of `fAdot s`:
    (hAdotCoeff : ∀ s, 0 ≤ s → ∀ n, L.srcC.adot s n = cosineCoeffs (fAdot s) n)
    (hAdot0Base : ∀ s, gAdot s 0 = fAdot s)
    (hAdotTower : ∀ s, 0 ≤ s → NeumannTower (gAdot s) 3)
    (hAdotTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gAdot s 3)| ≤ Mdot)
    -- zero-mode bounds (honest hypotheses; the j-tower is silent on n = 0):
    (hSrcZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (hAdotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot) :
    ShenWork.Paper2.ChiNegSourceTail.SourceEigenCubeTailFields
      L C0 (2 * M) C0dot (2 * Mdot) where
  hC := le_max_of_le_left hC0
  hCdot := le_max_of_le_left hC0dot
  sourceZero := hSrcZero
  sourceCube := fun s hs n hn => by
    rw [hSrcCoeff s hs n]
    exact eigenCube_bound_of_tower (hSrc0Base s) (hSrcTower s hs)
      (hSrcTop s hs) hn
  adotZero := hAdotZero
  adotCube := fun s hs n hn => by
    rw [hAdotCoeff s hs n]
    exact eigenCube_bound_of_tower (hAdot0Base s) (hAdotTower s hs)
      (hAdotTop s hs) hn

end

end ShenWork.Paper2.EigenCubeTailFromTower
