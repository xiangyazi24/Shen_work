# Q660 / cron1: NeumannTower construction helpers

## Verdict

Yes, the repo has a real `NeumannTower` infrastructure and construction helpers, but the existing helper layer is aimed at **depth 3 / C⁶** and **depth 4 / C⁸**, not a dedicated depth-1 constructor for the power source `ν * u^γ`.

For your immediate goal, the reusable pieces are:

```lean
ShenWork.IntervalIBPCoeffExtraction.NeumannTower
ShenWork.Paper2.NeumannTowerOfC6.gTower
ShenWork.Paper2.NeumannTowerOfC6.gTower_step
ShenWork.Paper2.NeumannTowerOfC6.deriv_gTower
ShenWork.Paper2.NeumannTowerOfC6.contDiff_gTower
ShenWork.Paper2.NeumannTowerOfC6.continuous_deriv_gTower
ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six
ShenWork.Paper2.NeumannTowerOfC8.neumannTower_four_of_contDiff_eight
ShenWork.Paper2.ChiNegUnconditionalClose.neumannTower_gTower_three_of_contDiff_six
```

I did **not** find a theorem named `neumannTower_of...`, nor a depth-1 helper specialized to

```lean
fun x => p.ν * intervalDomainLift u x ^ p.γ
```

or to `u = heat semigroup` / `conjugatePicardIter ... 0`.

## Important shape mismatch

The repo's `NeumannTower g j` structure does **not** require `ContDiff ℝ 2 (g j)` at the top level.  It requires the tower fields only for `i < j`:

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

Location:

- `ShenWork/Paper2/IntervalIBPCoeffExtraction.lean:45-56`

So for `j = 1`, the structure only asks for C²/Neumann data of `g 0`, plus the step `g 1 = deriv (deriv (g 0))`.  It does **not** ask for `ContDiff ℝ 2 (g 1)` or Neumann data for `g 1`.

If you want the stronger package you described — both `g 0` and `g 1` are C²-Neumann — that is strictly more than `NeumannTower g 1` in the current structure.  You can either carry those as extra fields, or build a depth-2 tower by also defining `g 2 = deriv (deriv (g 1))` and providing the `i = 1` step/BCs.

## Core IBP consumer API

`IntervalIBPCoeffExtraction.lean` gives the coefficient-extraction engine:

```lean
theorem rawCoeff_step (n : ℕ) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {i : ℕ} (hi : i < j) :
    rawCoeff n (g (i + 1)) = -((n : ℝ) * Real.pi) ^ 2 * rawCoeff n (g i)
```

```lean
theorem rawCoeff_iterate (n : ℕ) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) :
    rawCoeff n (g j) = (-((n : ℝ) * Real.pi) ^ 2) ^ j * rawCoeff n (g 0)
```

```lean
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n) {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ} (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤ 2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

Locations:

- `rawCoeff_step`: `ShenWork/Paper2/IntervalIBPCoeffExtraction.lean:61-67`
- `rawCoeff_iterate`: `ShenWork/Paper2/IntervalIBPCoeffExtraction.lean:71-87`
- `cosineCoeffs_decay`: `ShenWork/Paper2/IntervalIBPCoeffExtraction.lean:127-139`

For your depth-1 case, `cosineCoeffs_decay` with `j = 1` gives the quadratic decay bound for `g 0` from a bound on the raw coefficient of `g 1`.

## Generic even-derivative tower helper

`IntervalNeumannTowerOfC6.lean` defines the reusable even-derivative tower:

```lean
/-- The even-derivative tower of `f`: `gTower f i = ∂ₓ^{2i} f`. -/
def gTower (f : ℝ → ℝ) (i : ℕ) : ℝ → ℝ := deriv^[2 * i] f
```

with the key equations:

```lean
theorem gTower_zero (f : ℝ → ℝ) : gTower f 0 = f

theorem gTower_step (f : ℝ → ℝ) (i : ℕ) :
    gTower f (i + 1) = deriv (deriv (gTower f i))

theorem deriv_gTower (f : ℝ → ℝ) (i : ℕ) :
    deriv (gTower f i) = deriv^[2 * i + 1] f
```

Locations:

- `gTower`: `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:36-37`
- `gTower_zero`: `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:39-40`
- `gTower_step`: `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:42-48`
- `deriv_gTower`: `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:50-55`

It also has regularity helpers:

```lean
theorem contDiff_gTower {f : ℝ → ℝ} {i : ℕ} (hf : ContDiff ℝ (2 + 2 * i : ℕ) f) :
    ContDiff ℝ 2 (gTower f i)

theorem continuous_deriv_gTower {f : ℝ → ℝ} {i : ℕ}
    (hf : ContDiff ℝ (2 * i + 1 : ℕ) f) :
    Continuous (deriv (gTower f i))
```

Locations:

- `contDiff_gTower`: `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:57-61`
- `continuous_deriv_gTower`: `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:63-71`

These are exactly the low-level helpers you want for a custom depth-1 tower.

## Existing high-depth constructors

### Depth 3 from global C⁶

`IntervalNeumannTowerOfC6.lean` has:

```lean
theorem neumannTower_three_of_contDiff_six
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    ∃ g, g 0 = f ∧ NeumannTower g 3
```

Location:

- `ShenWork/Paper2/IntervalNeumannTowerOfC6.lean:77-82`

### Depth 4 from global C⁸

`IntervalNeumannTowerOfC8.lean` has:

```lean
theorem neumannTower_four_of_contDiff_eight
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (8 : ℕ) f)
    (hN0 : ∀ i, i < 4 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 4 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 4
```

Location:

- `ShenWork/Paper2/IntervalNeumannTowerOfC8.lean:39-44`

### Explicit depth-3 witness on `gTower f`

`IntervalChiNegUnconditionalClose.lean` exposes the C⁶ constructor in a more convenient non-existential form:

```lean
theorem neumannTower_gTower_three_of_contDiff_six
    {f : ℝ → ℝ} (hf : ContDiff ℝ (6 : ℕ) f)
    (hN0 : ∀ i, i < 3 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 3 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 3
```

Location:

- `ShenWork/Paper2/IntervalChiNegUnconditionalClose.lean:58-62`

This is probably the best pattern to copy for a custom depth-1 helper.

## Parity helpers for boundary conditions

`IntervalSourceRepresentative.lean` has the doubly-even parity infrastructure.  The key packaged theorem is:

```lean
theorem higherNeumannCompatibility_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) :
    (∀ i, i < 3 → deriv (gTower f i) 0 = 0) ∧
      (∀ i, i < 3 → deriv (gTower f i) 1 = 0)
```

Location:

- `ShenWork/Paper2/IntervalSourceRepresentative.lean:126-131`

It is depth-3-shaped, but for depth 1 you can use it and restrict to `i < 1`, or use the simpler pointwise lemmas:

```lean
theorem gTower_deriv_zero_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) (i : ℕ) :
    deriv (gTower f i) 0 = 0

theorem gTower_deriv_one_of_doublyEven
    {f : ℝ → ℝ} (hf : DoublyEven f) (i : ℕ) :
    deriv (gTower f i) 1 = 0
```

Locations:

- `gTower_deriv_zero_of_doublyEven`: `ShenWork/Paper2/IntervalSourceRepresentative.lean:104-108`
- `gTower_deriv_one_of_doublyEven`: `ShenWork/Paper2/IntervalSourceRepresentative.lean:113-117`

For the heat semigroup cosine representative, doubly-even parity is likely the clean way to discharge the endpoint `deriv(g i)(0/1)=0` facts.

## Suggested depth-1 helper to add

I found no existing theorem with this exact shape, but it should be a small specialization of the C⁶/C⁸ pattern:

```lean
import ShenWork.Paper2.IntervalNeumannTowerOfC6

open Set Filter Topology
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower)
open ShenWork.Paper2.NeumannTowerOfC6
  (gTower gTower_step contDiff_gTower continuous_deriv_gTower)

namespace ShenWork.Paper2.NeumannTowerOfC6

noncomputable section

/-- Depth-1 Neumann tower from global C² plus endpoint Neumann data. -/
theorem neumannTower_gTower_one_of_contDiff_two
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (2 : ℕ) f)
    (hN0 : deriv f 0 = 0)
    (hN1 : deriv f 1 = 0) :
    NeumannTower (gTower f) 1 := by
  have hcd0 : ContDiff ℝ 2 (gTower f 0) := by
    simpa using hf
  have hcont0 : Continuous (deriv (gTower f 0)) := by
    have h1 : ContDiff ℝ (1 : ℕ) f := hf.of_le (by norm_num)
    simpa [gTower] using (continuous_deriv_gTower (f := f) (i := 0) h1)
  refine
    { step := fun i hi => ?_
      contDiff := fun i hi => ?_
      tend0 := fun i hi => ?_
      tend1 := fun i hi => ?_
      bc0 := fun i hi => ?_
      bc1 := fun i hi => ?_ }
  · have hi0 : i = 0 := Nat.eq_zero_of_lt_succ hi
    subst i
    exact gTower_step f 0
  · have hi0 : i = 0 := Nat.eq_zero_of_lt_succ hi
    subst i
    exact hcd0.contDiffOn
  · have hi0 : i = 0 := Nat.eq_zero_of_lt_succ hi
    subst i
    have hT : Tendsto (deriv (gTower f 0)) (nhds 0)
        (nhds (deriv (gTower f 0) 0)) := hcont0.continuousAt
    simpa [gTower, hN0] using hT.mono_left nhdsWithin_le_nhds
  · have hi0 : i = 0 := Nat.eq_zero_of_lt_succ hi
    subst i
    have hT : Tendsto (deriv (gTower f 0)) (nhds 1)
        (nhds (deriv (gTower f 0) 1)) := hcont0.continuousAt
    simpa [gTower, hN1] using hT.mono_left nhdsWithin_le_nhds
  · have hi0 : i = 0 := Nat.eq_zero_of_lt_succ hi
    subst i
    simpa [gTower] using hN0
  · have hi0 : i = 0 := Nat.eq_zero_of_lt_succ hi
    subst i
    simpa [gTower] using hN1

end
end ShenWork.Paper2.NeumannTowerOfC6
```

If you also need `ContDiff ℝ 2 (gTower f 1)`, prove separately from `hf4 : ContDiff ℝ (4 : ℕ) f` using:

```lean
have hg1C2 : ContDiff ℝ 2 (gTower f 1) :=
  contDiff_gTower (f := f) (i := 1) (hf4.of_le (by norm_num))
```

For your intended `f = fun x => p.ν * u x ^ p.γ`, with `u = S(s)u₀` and `s > 0`, this suggests a clean two-step plan:

1. build the global smooth representative `f` and prove `ContDiff ℝ 4 f` plus endpoint Neumann data for `f` (and, if needed, for `gTower f 1`);
2. feed `hf.of_le` and the endpoint BCs into the depth-1 helper above, while using `contDiff_gTower` for the extra `g 1` C² fact.
