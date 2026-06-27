# Q1041 (cron2/cron1) — depth-`j` IBP for nonlinear source coefficients

Static repo inspection only; I did **not** run Lean.

I read and searched:

- `ShenWork/PDE/IntervalSourceDecayQuantitative.lean`
- searches for `H6Neumann`, `WeakH6`, `sextic`, `sixth cosineCoeff`, `depth-3`, `NeumannTower`
- `ShenWork/Paper2/IntervalIBPCoeffExtraction.lean`
- `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean`
- `ShenWork/Paper2/IntervalEigenCubeTailFromTower.lean`
- `ShenWork/Paper2/IntervalNeumannTowerOfC8.lean`
- `ShenWork/Paper2/IntervalEigenCubeSummability.lean`
- `ShenWork/Paper2/IntervalChiNegUnconditionalClose.lean`
- `ShenWork/Paper2/IntervalSourceRepresentative.lean`
- `ShenWork/Paper2/IntervalSourceC6Representative.lean`

## Executive verdict

Yes and no, depending on what exactly is meant.

1. **Inside `IntervalSourceDecayQuantitative.lean` only**, the repo has depth-1 and depth-2:
   - `intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound`
   - `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound`
   - `intervalWeakH4Neumann_eigenvalue_L1_summable`

   It does **not** have a theorem named `intervalWeakH6Neumann_cosineCoeff_sextic_decay_of_bound` there.

2. **Elsewhere in the repo**, the repo already has a stronger and more general infrastructure:
   - a generic arbitrary-depth `NeumannTower` and `cosineCoeffs_decay` theorem in
     `IntervalIBPCoeffExtraction.lean`;
   - a depth-3 / C⁶ producer `neumannTower_three_of_contDiff_six` in
     `IntervalNeumannTowerOfC6.lean`;
   - a depth-3 bridge `eigenCube_bound_of_tower` and
     `SourceEigenCubeTailFields_of_neumannTower` in `IntervalEigenCubeTailFromTower.lean`;
   - a higher depth-4 / C⁸ summability route in `IntervalNeumannTowerOfC8.lean` and
     `IntervalEigenCubeSummability.lean`.

So the repo does have **generic depth-`j` IBP**, and it has a committed depth-3 route.  It is just **not packaged under the old `IntervalSourceDecayQuantitative` H6/sextic naming**.

The remaining question is whether the repo already instantiates that route specifically for the Level0 nonlinear source

```lean
x ↦ p.ν * (S(t)u₀ x) ^ p.γ
```

and its time derivative.  I did **not** find a single Level0 theorem proving this specialization automatically.  Existing depth-3/C6 theorems take smooth representative data (`fSrc`, `fAdot`, coefficient-identification, Neumann parity, top raw-coefficient bounds) as hypotheses.  Thus the IBP/tower machinery exists; the Level0 nonlinear-source C⁶/C⁸ representative instantiation still appears to be the missing analytic wiring.

## What `IntervalSourceDecayQuantitative.lean` has

The file has the quantitative H² theorem:

```lean
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB : (∫ x in (0:ℝ)..1, |hf.secondDeriv x|) ≤ B) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2
```

and the depth-2 / H⁴ theorem:

```lean
theorem intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv)
    {B₂ : ℝ} (hB₂ : (∫ x in (0:ℝ)..1, |hf''.secondDeriv x|) ≤ B₂) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B₂ / ((k : ℝ) * Real.pi) ^ 4
```

and the λ¹ summability theorem:

```lean
theorem intervalWeakH4Neumann_eigenvalue_L1_summable
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f)
    (hf'' : IntervalWeakH2Neumann hf.secondDeriv) :
    Summable (fun k : ℕ => unitIntervalCosineEigenvalue k * |cosineCoeffs f k|)
```

That file stops at depth 2.  It does not contain an H6/sextic theorem.

## Generic arbitrary-depth IBP already exists

`ShenWork/Paper2/IntervalIBPCoeffExtraction.lean` defines:

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

and proves the arbitrary-depth decay theorem:

```lean
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

This is exactly the generic depth-`j` IBP theorem.  To get sextic decay, instantiate `j := 3`.

There is also the raw coefficient version:

```lean
theorem rawCoeff_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |rawCoeff n (g 0)| ≤ M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

So the repo does not need a hand-written copy of the H4 proof to get H6; it already has the generic theorem.

## Depth-3 / C⁶ producer already exists

`ShenWork/Paper2/IntervalNeumannTowerOfC6.lean` provides:

```lean
def gTower (f : ℝ → ℝ) (i : ℕ) : ℝ → ℝ := deriv^[2 * i] f
```

and:

```lean
theorem neumannTower_three_of_contDiff_six
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    ∃ g, g 0 = f ∧ NeumannTower g 3
```

So once a source representative `f` is globally `C⁶` and has odd derivatives `∂ₓ f`, `∂ₓ³ f`, `∂ₓ⁵ f` vanishing at both endpoints, the repo can build the depth-3 Neumann tower.

`ShenWork/Paper2/IntervalChiNegUnconditionalClose.lean` exposes a non-existential version:

```lean
theorem neumannTower_gTower_three_of_contDiff_six
    {f : ℝ → ℝ} (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 3
```

This is the most convenient form for downstream use.

## Depth-3 bridge to eigen-cube bounds already exists

`ShenWork/Paper2/IntervalEigenCubeTailFromTower.lean` proves:

```lean
theorem eigenCube_bound_of_tower
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} (hg0 : g 0 = f)
    (H : NeumannTower g 3) {M : ℝ} (hM : ∀ n, 1 ≤ n → |rawCoeff n (g 3)| ≤ M)
    {n : ℕ} (hn : 1 ≤ n) :
    unitIntervalCosineEigenvalue n ^ (3 : ℕ) * |cosineCoeffs f n| ≤ 2 * M
```

This is `j = 3` converted into the eigen-cube boundedness form:

```text
λₙ³ · |coeffₙ| ≤ constant.
```

It also packages the source and time-derivative cases into:

```lean
theorem SourceEigenCubeTailFields_of_neumannTower
    (L : LocalRestart p u T σ)
    ...
    (hSrcTower : ∀ s, 0 ≤ s → NeumannTower (gSrc s) 3)
    ...
    (hAdotTower : ∀ s, 0 ≤ s → NeumannTower (gAdot s) 3)
    ... :
    ShenWork.Paper2.ChiNegSourceTail.SourceEigenCubeTailFields
      L C0 (2 * M) C0dot (2 * Mdot)
```

This is committed and 0-sorry by file header.

## C⁶ source-regularity bridge exists, but as hypotheses

`IntervalChiNegUnconditionalClose.lean` gives:

```lean
theorem sourceEigenCubeTailFields_of_sourceRegularity
    (L : LocalRestart p u T σ)
    {fSrc fAdot : ℝ → ℝ → ℝ} {C0 C0dot M Mdot : ℝ}
    (hC0 : 0 ≤ C0) (hC0dot : 0 ≤ C0dot)
    (hSrcCoeff : ∀ s, 0 ≤ s → ∀ n, L.aC s n = cosineCoeffs (fSrc s) n)
    (hSrcCD6 : ∀ s, 0 ≤ s → ContDiff ℝ (6 : ℕ) (fSrc s))
    (hSrcN0 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fSrc s) i) 0 = 0)
    (hSrcN1 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fSrc s) i) 1 = 0)
    (hSrcTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fSrc s) 3)| ≤ M)
    (hAdotCoeff : ∀ s, 0 ≤ s → ∀ n, L.srcC.adot s n = cosineCoeffs (fAdot s) n)
    (hAdotCD6 : ∀ s, 0 ≤ s → ContDiff ℝ (6 : ℕ) (fAdot s))
    (hAdotN0 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fAdot s) i) 0 = 0)
    (hAdotN1 : ∀ s, 0 ≤ s → ∀ i, i < 3 → deriv (gTower (fAdot s) i) 1 = 0)
    (hAdotTop : ∀ s, 0 ≤ s → ∀ n, 1 ≤ n → |rawCoeff n (gTower (fAdot s) 3)| ≤ Mdot)
    (hSrcZero : ∀ s, 0 ≤ s → |L.aC s 0| ≤ C0)
    (hAdotZero : ∀ s, 0 ≤ s → |L.srcC.adot s 0| ≤ C0dot) :
    SourceEigenCubeTailFields L C0 (2 * M) C0dot (2 * Mdot)
```

This is a strong bridge: given `C⁶` representatives for the source and its time derivative, it derives the depth-3 tail package.  But it does **not** itself prove that the Level0 nonlinear heat source `ν·(S(t)u₀)^γ` has such a representative.

## Higher parity compatibility exists

`IntervalSourceRepresentative.lean` proves the Neumann odd-derivative compatibility from double-even parity:

```lean
theorem higherNeumannCompatibility_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) :
    (∀ i, i < 3 → deriv (gTower f i) 0 = 0) ∧
      (∀ i, i < 3 → deriv (gTower f i) 1 = 0)
```

So the boundary-compatibility part of C⁶ Neumann data is already handled abstractly by parity.  For a Neumann cosine-series source representative, the odd derivatives vanish automatically.

## There is also a depth-4 / C⁸ route

`IntervalNeumannTowerOfC8.lean` provides:

```lean
theorem neumannTower_four_of_contDiff_eight
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (8 : ℕ) f)
    (hN0 : ∀ i, i < 4 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 4 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 4
```

`IntervalEigenCubeSummability.lean` derives summable eigen-cube envelopes from C⁸:

```lean
theorem sourceEigenCubeTailFields_of_sourceC8
    ...
    (hSrcCD8 : ∀ s, 0 ≤ s → ContDiff ℝ (8 : ℕ) (fSrc s))
    ... :
    SourceEigenCubeTailFields ...
```

This is stronger than the depth-3 bounded-cube route: it gives eigen-cube **summability** via `|coeff| ≤ C/(nπ)^8`, so `λ³ |coeff| ≤ C/(nπ)^2`.

For Q1034's λ² summability, C⁶/depth 3 is enough; for λ³ summability, C⁸/depth 4 is the route already packaged.

## Does the repo already have the exact depth-3 λ²-summability theorem?

I found the generic ingredients, but not a theorem with exactly this likely name:

```lean
intervalWeakH6Neumann_eigenvalueSq_L1_summable
```

or:

```lean
neumannTower_three_eigenvalueSq_summable
```

However it is straightforward to build from committed pieces:

1. use `cosineCoeffs_decay` with `j := 3`:

```lean
|cosineCoeffs (g 0) n| ≤ 2*M / ((n:ℝ)*Real.pi)^6
```

2. multiply by `λ_n^2 = ((n:ℝ)*Real.pi)^4`:

```lean
λ_n * (λ_n * |cosineCoeffs (g 0) n|)
  ≤ 2*M / ((n:ℝ)*Real.pi)^2
```

3. compare with the `p = 2` series.

A theorem skeleton:

```lean
import ShenWork.Paper2.IntervalIBPCoeffExtraction
import Mathlib.Analysis.PSeries

open ShenWork.IntervalIBPCoeffExtraction
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.Paper2.Level0SourceDecay

/-- Depth-3 Neumann tower gives λ²-summability of the base cosine coefficients. -/
theorem eigenSq_summable_of_neumannTower_three
    {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} (hg0 : g 0 = f)
    (H : NeumannTower g 3) {M : ℝ}
    (hM : ∀ n, 1 ≤ n → |rawCoeff n (g 3)| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n *
        (unitIntervalCosineEigenvalue n * |cosineCoeffs f n|)) := by
  -- n=0 term vanishes. For n≥1, use `cosineCoeffs_decay n hn H (hM n hn)`.
  -- Then λ² = (nπ)^4 and denominator = (nπ)^6, leaving `2*M/(nπ)^2`.
  -- Compare with `(2*M/π^2) * (1/(n:ℝ)^2)`.
  sorry

end ShenWork.Paper2.Level0SourceDecay
```

This is not new analysis; it is algebra and p-series comparison.

## What is still needed for the nonlinear Level0 source?

For the actual source

```lean
srcSlice p (conjugatePicardIter p u₀ 0) t x
  = p.ν * intervalDomainLift (conjugatePicardIter p u₀ 0 t) x ^ p.γ
```

one still needs a theorem producing the `C⁶` Neumann representative data, uniformly on the positive time window, for:

1. the source itself;
2. its time derivative if filling `adot`/time-C² coefficient packages.

The expected theorem shape:

```lean
theorem level0_srcSlice_C6_neumann
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c T M₀ : ℝ}
    (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hpos : ∀ t ∈ Icc c T, ∀ x ∈ Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x) :
    ∃ fSrc : ℝ → ℝ → ℝ,
      -- coefficient identity
      (∀ t ∈ Icc c T, ∀ n,
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) n t = cosineCoeffs (fSrc t) n) ∧
      -- C6 representative
      (∀ t ∈ Icc c T, ContDiff ℝ (6:ℕ) (fSrc t)) ∧
      -- double-even / odd-deriv Neumann chain
      (∀ t ∈ Icc c T, ∀ i, i < 3,
        deriv (gTower (fSrc t) i) 0 = 0) ∧
      (∀ t ∈ Icc c T, ∀ i, i < 3,
        deriv (gTower (fSrc t) i) 1 = 0) ∧
      -- top coefficient/sup bound
      (∃ M, 0 ≤ M ∧ ∀ t ∈ Icc c T, ∀ n, 1 ≤ n,
        |rawCoeff n (gTower (fSrc t) 3)| ≤ M)
```

For `DuhamelSourceTimeC2Coeff`, one also needs the analogous package for the time-derivative coefficient family (`adot`) and probably the second time derivative depending on how the local source `a` is defined.

Mathematically, heat smoothing at `t ≥ c > 0` should give this.  But I did not find a committed Level0-specific theorem that assembles it for `ν·(S(t)u₀)^γ`.

## Answer to the specific questions

### Does a depth-3 version exist?

Yes, functionally.  Not in `IntervalSourceDecayQuantitative.lean` under an H6/sextic theorem name, but the repo has:

```lean
ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay
```

with arbitrary `j`, and:

```lean
ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six
ShenWork.Paper2.EigenCubeTailFromTower.eigenCube_bound_of_tower
ShenWork.Paper2.EigenCubeTailFromTower.SourceEigenCubeTailFields_of_neumannTower
ShenWork.Paper2.ChiNegUnconditionalClose.sourceEigenCubeTailFields_of_sourceRegularity
```

These cover the depth-3/C6 story.

### If not in `IntervalSourceDecayQuantitative`, what is needed to build it from existing depth-2?

Do not build it from the depth-2 theorem.  Use the generic `NeumannTower` and `cosineCoeffs_decay` theorem.  The depth-2 theorem is now a special case of the generic route.

The data needed is:

```lean
g : ℕ → ℝ → ℝ
hg0 : g 0 = f
H : NeumannTower g 3
hTop : ∀ n, 1 ≤ n → |rawCoeff n (g 3)| ≤ M
```

or, from a single `C⁶` representative:

```lean
hf : ContDiff ℝ (6:ℕ) f
hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0
hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0
hTop : ∀ n, 1 ≤ n → |rawCoeff n (gTower f 3)| ≤ M
```

Then call `neumannTower_gTower_three_of_contDiff_six` or `neumannTower_three_of_contDiff_six`, and feed it to `cosineCoeffs_decay` with `j=3`.

### Is there a generic `NeumannTower` at arbitrary depth?

Yes:

```lean
ShenWork.IntervalIBPCoeffExtraction.NeumannTower
```

is generic in `j : ℕ`, and the core decay theorem:

```lean
ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay
```

is also generic in `j`.

What is not generic is the producer from `ContDiff ℝ (2*j)` plus odd-derivative boundary vanish into `NeumannTower`.  The repo has fixed producers for `j=3` (`C⁶`) and `j=4` (`C⁸`):

```lean
neumannTower_three_of_contDiff_six
neumannTower_four_of_contDiff_eight
```

No arbitrary-`j` `neumannTower_of_contDiff_even` producer was found.

## Bottom line

The depth-3 IBP machinery exists.  The old `IntervalSourceDecayQuantitative` file is no longer the whole story.  The remaining missing piece for Q1034/Level0 is not “write generic depth-3 IBP”; it is “instantiate the C⁶ Neumann source representative data for `ν·(S(t)u₀)^γ` and its relevant time-derivative slices, with uniform top raw-coefficient bounds on the positive time window.”
