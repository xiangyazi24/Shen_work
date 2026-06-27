# Q1045 / cron1 — NeumannTower / higher-depth IBP audit

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

Yes, the repo now has a **generic finite-depth `NeumannTower` infrastructure** for arbitrary depth `j`, plus arbitrary-`j` coefficient decay. It is not located in `IntervalSourceDecayQuantitative.lean`; it is in:

```text
ShenWork/Paper2/IntervalIBPCoeffExtraction.lean
```

The key declarations are:

```lean
ShenWork.IntervalIBPCoeffExtraction.NeumannTower
ShenWork.IntervalIBPCoeffExtraction.rawCoeff_step
ShenWork.IntervalIBPCoeffExtraction.rawCoeff_iterate
ShenWork.IntervalIBPCoeffExtraction.rawCoeff_decay
ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay
```

The arbitrary-depth theorem is:

```lean
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

So the generic IBP part exists for any finite `j`, provided a `NeumannTower g j` and a top-coefficient bound are supplied.

However, the repo does **not** yet have a fully generic producer

```text
ContDiff ℝ (2*j) f + odd-Neumann boundary chain up to depth j
  ⟹ ∃ g, g 0 = f ∧ NeumannTower g j
```

for arbitrary symbolic `j`. Instead, it has concrete producers for depth 3 and depth 4:

```lean
-- ShenWork/Paper2/IntervalNeumannTowerOfC6.lean
ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six

-- ShenWork/Paper2/IntervalNeumannTowerOfC8.lean
ShenWork.Paper2.NeumannTowerOfC8.neumannTower_four_of_contDiff_eight
```

Those are enough for the current DuhamelSourceTimeC2Coeff/eigen-tail tasks, but they are not a fully arbitrary-depth constructor.

## What `IntervalSourceDecayQuantitative.lean` contains

The requested file:

```text
ShenWork/PDE/IntervalSourceDecayQuantitative.lean
```

contains the older quantitative weak-H2 Neumann bound. It does **not** define `NeumannTower`, `intervalWeakH4Neumann`, or a depth-j tower.

Its main theorem is:

```lean
ShenWork.IntervalSourceDecayQuantitative.intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
```

with shape:

```lean
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB : (∫ x in (0:ℝ)..1, |hf.secondDeriv x|) ≤ B) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2
```

This is depth `j = 1` in the `NeumannTower` language: two spatial derivatives, quadratic decay. The file also has:

```lean
ShenWork.IntervalSourceDecayQuantitative.weak_laplacianCoeff_abs_le_of_bound
```

which is the quantitative bound on the top weak-Laplacian cosine integral.

I found no declarations named:

```text
intervalWeakH4Neumann
intervalWeakH6Neumann
```

by repo search. Higher-order decay is handled by `NeumannTower`, not by `intervalWeakH4Neumann` / `intervalWeakH6Neumann` structures.

## 1. Does a generic NeumannTower exist at arbitrary depth?

Yes, at the IBP extraction level.

File:

```text
ShenWork/Paper2/IntervalIBPCoeffExtraction.lean
```

Core structure:

```lean
structure NeumannTower (g : ℕ → ℝ → ℝ) (j : ℕ) : Prop where
  step : ∀ i, i < j → g (i + 1) = deriv (deriv (g i))
  contDiff : ∀ i, i < j → ContDiffOn ℝ 2 (g i) (Set.Icc (0 : ℝ) 1)
  tend0 : ∀ i, i < j →
    Filter.Tendsto (deriv (g i)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)
  tend1 : ∀ i, i < j →
    Filter.Tendsto (deriv (g i)) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  bc0 : ∀ i, i < j → deriv (g i) 0 = 0
  bc1 : ∀ i, i < j → deriv (g i) 1 = 0
```

Arbitrary-depth decay theorem:

```lean
theorem rawCoeff_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |rawCoeff n (g 0)| ≤ M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

Normalized coefficient form:

```lean
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

Therefore:

```text
NeumannTower depth j + top raw coefficient bound
  ⟹ |cosineCoeffs (g 0) n| ≤ 2M / (nπ)^(2j).
```

The gap is not IBP iteration. The gap is producing the tower and top bound for the concrete nonlinear source.

## 2. If only depth 2 existed, what would need to be added for depth 3?

The premise is outdated: depth 3 already exists.

File:

```text
ShenWork/Paper2/IntervalNeumannTowerOfC6.lean
```

Key definitions/theorems:

```lean
ShenWork.Paper2.NeumannTowerOfC6.gTower
ShenWork.Paper2.NeumannTowerOfC6.gTower_step
ShenWork.Paper2.NeumannTowerOfC6.deriv_gTower
ShenWork.Paper2.NeumannTowerOfC6.contDiff_gTower
ShenWork.Paper2.NeumannTowerOfC6.continuous_deriv_gTower
ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six
```

The producer is:

```lean
theorem neumannTower_three_of_contDiff_six
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    ∃ g, g 0 = f ∧ NeumannTower g 3
```

Here:

```lean
def gTower (f : ℝ → ℝ) (i : ℕ) : ℝ → ℝ := deriv^[2 * i] f
```

So for depth 3 one needs exactly:

```text
f ∈ C⁶ globally,
∂ₓ f(0)=∂ₓ f(1)=0,
∂ₓ³ f(0)=∂ₓ³ f(1)=0,
∂ₓ⁵ f(0)=∂ₓ⁵ f(1)=0,
plus a top raw coefficient bound for ∂ₓ⁶ f.
```

The bridge from depth 3 tower to eigen-cube pointwise bounds is in:

```text
ShenWork/Paper2/IntervalEigenCubeTailFromTower.lean
```

The exact bridge theorem is:

```lean
ShenWork.Paper2.EigenCubeTailFromTower.SourceEigenCubeTailFields_of_neumannTower
```

and the per-mode lemma is:

```lean
ShenWork.Paper2.EigenCubeTailFromTower.eigenCube_bound_of_tower
```

with content:

```text
depth-3 tower + top raw coefficient bound
  ⟹ λ_n^3 * |cosineCoeffs f n| ≤ 2M  for n ≥ 1.
```

For `DuhamelSourceTimeC2Coeff`, the field `sourceEigenSqEnvelope` only needs λ² summability, not a λ³ pointwise bound. Depth 3 is enough:

```text
|c_n| ≤ 2M / (nπ)^6
λ_n² |c_n| = (nπ)^4 |c_n| ≤ 2M / (nπ)^2,
```

and `∑ 1/n²` converges. The repo has the generic `cosineCoeffs_decay` needed for this; it just does not appear to have a dedicated theorem named exactly `sourceEigenSqEnvelope_of_neumannTower_three`. That would be a small wrapper around `cosineCoeffs_decay` at `j = 3` plus the p-series summability lemma.

The repo also has depth 4:

```text
ShenWork/Paper2/IntervalNeumannTowerOfC8.lean
```

```lean
ShenWork.Paper2.NeumannTowerOfC8.neumannTower_four_of_contDiff_eight
```

This produces a depth-4 tower from global C8 plus odd derivatives through order 7 vanishing at endpoints. It is used for eigen-cube **summability** in:

```text
ShenWork/Paper2/IntervalEigenCubeSummability.lean
```

with:

```lean
ShenWork.Paper2.EigenCubeSummability.cubeEnvelope
ShenWork.Paper2.EigenCubeSummability.cubeEnvelope_summable
ShenWork.Paper2.EigenCubeSummability.eigenCube_envelope_bound_of_tower
ShenWork.Paper2.EigenCubeSummability.eigenCube_envelope_full
ShenWork.Paper2.EigenCubeSummability.sourceEigenCubeTailFields_of_sourceC8
```

This file explains the stronger fact:

```text
C8 / depth 4 gives |c_n| ≤ 2M/(nπ)^8,
therefore λ_n^3 |c_n| ≤ 2M/(nπ)^2,
which is summable.
```

## 3. Does the repo have C6 Neumann regularity for `ν·u^γ`, with `u = S(t)u₀`?

Mathematically, yes: at positive time the heat Level0 profile is smooth, and with positivity the nonlinear source is smooth.

In the repo, the answer is more precise:

### What exists for the heat semigroup itself

Files:

```text
ShenWork/Paper2/IntervalCD6HeatSmoothness.lean
ShenWork/Paper2/IntervalSpatialC6Certificate.lean
ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean
```

Theorems:

```lean
ShenWork.Paper2.CD6HeatSmoothness.unitIntervalCosineHeatValue_contDiff_seven
ShenWork.Paper2.SpatialC6Certificate.unitIntervalCosineHeatValue_contDiff_six
ShenWork.Paper2.SpatialC6Certificate.intervalDomainLift_contDiffOn_six_of_eqOn_heatValue
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_contDiff_four
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

So the linear heat representative has at least C6/C7 spatial regularity in committed code.

### What exists for source C6 representatives

Files:

```text
ShenWork/Paper2/IntervalSourceC6Representative.lean
ShenWork/Paper2/IntervalChiNegUnconditionalClose.lean
```

Theorems:

```lean
ShenWork.Paper2.SourceC6Representative.sourceEigenCubeTailFields_of_weightThree
ShenWork.Paper2.ChiNegUnconditionalClose.sourceEigenCubeTailFields_of_sourceRegularity
ShenWork.Paper2.ChiNegUnconditionalClose.neumannTower_gTower_three_of_contDiff_six
```

These do not directly prove from first principles that

```text
x ↦ ν * (S(t)u₀ x)^γ
```

is C6-Neumann. Instead:

* `sourceEigenCubeTailFields_of_sourceRegularity` takes smooth C6 representatives `fSrc` / `fAdot`, coefficient identifications, odd-derivative Neumann vanishing, and top coefficient bounds as hypotheses, then derives `SourceEigenCubeTailFields`.
* `sourceEigenCubeTailFields_of_weightThree` builds C6 cosine-series representatives from an already-supplied eigen-cube summability input (`DuhamelSourceSpatialWeightThree` / weight-three envelope). That is a useful non-sorry bridge, but it is not the same as deriving C6 of the concrete nonlinear source from heat smoothing.

### What exists for the concrete chemDiv / source path

The concrete path currently wired from smooth inputs is mostly C2/H2:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

Key theorem:

```lean
ShenWork.Paper2.ChemDivSpatialC2.chemDivSource_weakH2_of_cosineRep
```

It produces:

```lean
IntervalWeakH2Neumann (chemDivLift p u v)
```

from global C4 cosine representatives for `u` and `v`. That is a depth-1 weak-H2 object, feeding quadratic decay.

The concrete physical source time C2 file:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

has:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiff
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_bound
ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
```

This is time-C2/source-envelope infrastructure, not a C6-Neumann spatial tower for `ν·(S(t)u₀)^γ`.

Therefore, for the concrete nonlinear Level0 source, the repo’s directly wired regularity is still essentially the C2/H2 lane (`chemDivSource_weakH2_of_cosineRep`) plus newer abstract/high-order tower bridges. I did not find a theorem of the form:

```lean
-- not found under this name/shape
heatLevel0_powerSource_neumannTower_three
heatLevel0_powerSource_contDiff_six_neumann
sourceTimeCoeff_C6Neumann_of_heatLevel0
```

or any `intervalWeakH4Neumann` / `intervalWeakH6Neumann` structure.

## Practical conclusion for `DuhamelSourceTimeC2Coeff`

For `DuhamelSourceTimeC2Coeff`, depth 3 is the right minimum if you want λ²-summable envelopes from spatial IBP:

```text
j = 3 gives |c_k| ≤ C/(kπ)^6,
λ_k² |c_k| ≤ C/(kπ)^2,
∑ λ_k² |c_k| < ∞.
```

The repo has the generic theorem to prove this (`IntervalIBPCoeffExtraction.cosineCoeffs_decay`) and a C6-to-depth3 tower producer (`NeumannTowerOfC6.neumannTower_three_of_contDiff_six`). What still must be supplied for the heat Level0 nonlinear source is the concrete C6-Neumann representative package:

```text
ContDiff ℝ 6 fSrc,
odd derivative boundary chain through orders 1, 3, 5,
top raw coefficient / L1 bound for ∂ₓ⁶ fSrc,
coefficient identification a_k = cosineCoeffs fSrc k,
and the same for adot.
```

The repo’s depth-4/C8 route (`IntervalEigenCubeSummability.lean`) is stronger and is used when one needs eigen-cube **summable** envelopes (`λ³|c_k| ≤ C/(kπ)^2`). For plain `DuhamelSourceTimeC2Coeff` λ² summability, depth 3 should suffice.

## Lean-facing wrapper that is still missing

The natural small wrapper for the C2Coeff route would be:

```lean
import ShenWork.Paper2.IntervalIBPCoeffExtraction
import Mathlib.Analysis.PSeries

open ShenWork.IntervalIBPCoeffExtraction
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2.MissingC2CoeffDepth3Wrapper

/-- Suggested wrapper: depth-3 Neumann tower gives a summable λ² envelope.
This is not claiming to be committed under this exact name; it is the next small
lemma to add for `DuhamelSourceTimeC2Coeff`. -/
theorem sourceEigenSq_summable_of_neumannTower_three
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} (hg0 : g 0 = f)
    (H : NeumannTower g 3) {M : ℝ} (hM : 0 ≤ M)
    (hTop : ∀ n, 1 ≤ n → |rawCoeff n (g 3)| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |cosineCoeffs f n|)) := by
  -- Proof route:
  -- * n = 0 is zero because λ₀ = 0.
  -- * for n ≥ 1, use `cosineCoeffs_decay n hn H (hTop n hn)` at j = 3.
  -- * multiply by λ² = (nπ)^4 to get ≤ 2M / (nπ)^2.
  -- * conclude by the p = 2 series.
  sorry

end ShenWork.Paper2.MissingC2CoeffDepth3Wrapper
```

## Bottom line

1. **Generic depth-j IBP exists**: `IntervalIBPCoeffExtraction.NeumannTower` plus `cosineCoeffs_decay` works for arbitrary finite `j`.
2. **Depth 3 is already implemented** from C6 data: `IntervalNeumannTowerOfC6.neumannTower_three_of_contDiff_six`. Depth 4 from C8 also exists.
3. **Concrete nonlinear Level0 C6-Neumann regularity is not fully wired as a direct theorem from `u = S(t)u₀`**. The repo has heat C6/C7, source C6/C8 representative bridges, and tower/eigen-tail bridges; but the current concrete chemDiv/source path that starts from heat Level0 still visibly bottoms out at C2/H2 unless the high-order source representative hypotheses/envelopes are supplied.
