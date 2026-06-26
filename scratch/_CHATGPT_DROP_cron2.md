# Q679 (cron2): quartic decay of cosine coefficients for C⁴ Neumann functions

Static repo inspection only; I did not run a Lean build.

## Executive verdict

Yes, the repo already has the **general iterated IBP engine** you want.  It is not named `depth_2` or `iterated_decay`, but it is present as:

```lean
ShenWork.IntervalIBPCoeffExtraction.cosineCoeffs_decay
```

in

```text
ShenWork/Paper2/IntervalIBPCoeffExtraction.lean
```

It proves the arbitrary-depth statement:

```lean
theorem cosineCoeffs_decay (n : ℕ) (hn : 1 ≤ n)
    {g : ℕ → ℝ → ℝ} {j : ℕ}
    (H : NeumannTower g j) {M : ℝ}
    (hM : |rawCoeff n (g j)| ≤ M) :
    |cosineCoeffs (g 0) n| ≤
      2 * M / ((n : ℝ) * Real.pi) ^ (2 * j)
```

So for quartic decay, set `j := 2`.  If `g 0 = f`, `g 1 = f''`, `g 2 = f''''`, and you can bound

```lean
|rawCoeff k (g 2)| ≤ B
```

then the existing theorem gives exactly

```lean
|cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 4
```

for `k ≥ 1`.

## Existing infrastructure found

### 1. `IntervalWeakH2Neumann` gives only the one-step/quadratic form

The quantitative one-round theorem is in `ShenWork/PDE/IntervalSourceDecayQuantitative.lean`:

```lean
theorem intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound
    {f : ℝ → ℝ} (hf : IntervalWeakH2Neumann f) {B : ℝ}
    (hB : (∫ x in (0:ℝ)..1, |hf.secondDeriv x|) ≤ B) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 2
```

This is a good theorem, but it is not the cleanest way to get quartic decay in this repo, because the arbitrary-depth IBP theorem already exists.

### 2. `NeumannTower` is the repo’s intended iteration abstraction

`IntervalIBPCoeffExtraction.lean` defines:

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

The engine then proves:

```lean
rawCoeff_step
rawCoeff_iterate
rawCoeff_decay
cosineCoeffs_decay
```

The file header says explicitly that it generalizes the `C²` Neumann quadratic decay to arbitrary even order `2j` by iterating the eigenfunction integration-by-parts identity.

### 3. There are C6/C8 tower producers, but I did not find a C4/depth-2 wrapper

The repo has:

```lean
ShenWork.Paper2.NeumannTowerOfC6.neumannTower_three_of_contDiff_six
ShenWork.Paper2.NeumannTowerOfC8.neumannTower_four_of_contDiff_eight
```

in:

```text
ShenWork/Paper2/IntervalNeumannTowerOfC6.lean
ShenWork/Paper2/IntervalNeumannTowerOfC8.lean
```

The C6 file defines the reusable even-derivative tower:

```lean
def gTower (f : ℝ → ℝ) (i : ℕ) : ℝ → ℝ := deriv^[2 * i] f
```

with helpers:

```lean
gTower_zero
gTower_step
deriv_gTower
contDiff_gTower
continuous_deriv_gTower
```

The C8 file reuses these.  I did **not** find a named:

```lean
neumannTower_two_of_contDiff_four
```

or a dedicated quartic-decay theorem.  But adding one should be a very small clone/specialization of the C6 producer.

## Cleanest build

Add a lightweight C4 wrapper, probably in a new file such as:

```text
ShenWork/Paper2/IntervalNeumannTowerOfC4.lean
```

or directly in the file where you need the estimate.

### Step 1: depth-2 tower from C4 + Neumann chain

Reuse `gTower` from `IntervalNeumannTowerOfC6.lean`:

```lean
import ShenWork.Paper2.IntervalNeumannTowerOfC6

open Set Filter Topology
open ShenWork.IntervalIBPCoeffExtraction (NeumannTower)
open ShenWork.Paper2.NeumannTowerOfC6
  (gTower gTower_zero gTower_step deriv_gTower contDiff_gTower continuous_deriv_gTower)

namespace ShenWork.Paper2.NeumannTowerOfC4

noncomputable section

theorem neumannTower_two_of_contDiff_four
    {f : ℝ → ℝ}
    (hf : ContDiff ℝ (4 : ℕ) f)
    (hN0 : ∀ i, i < 2 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 2 → deriv (gTower f i) 1 = 0) :
    NeumannTower (gTower f) 2 := by
  have hcd : ∀ i, i < 2 → ContDiff ℝ 2 (gTower f i) := by
    intro i hi
    refine contDiff_gTower (hf.of_le ?_)
    have : (2 + 2 * i : ℕ) ≤ 4 := by omega
    exact_mod_cast this
  have hcont : ∀ i, i < 2 → Continuous (deriv (gTower f i)) := by
    intro i hi
    refine continuous_deriv_gTower (hf.of_le ?_)
    have : (2 * i + 1 : ℕ) ≤ 4 := by omega
    exact_mod_cast this
  refine
    { step := fun i _ => gTower_step f i
      contDiff := fun i hi => (hcd i hi).contDiffOn
      tend0 := fun i hi => ?_
      tend1 := fun i hi => ?_
      bc0 := hN0
      bc1 := hN1 }
  · have hc := (hcont i hi).continuousAt (x := (0 : ℝ))
    have hT : Tendsto (deriv (gTower f i)) (nhds 0)
        (nhds (deriv (gTower f i) 0)) := hc
    rw [hN0 i hi] at hT
    exact hT.mono_left nhdsWithin_le_nhds
  · have hc := (hcont i hi).continuousAt (x := (1 : ℝ))
    have hT : Tendsto (deriv (gTower f i)) (nhds 1)
        (nhds (deriv (gTower f i) 1)) := hc
    rw [hN1 i hi] at hT
    exact hT.mono_left nhdsWithin_le_nhds

end

end ShenWork.Paper2.NeumannTowerOfC4
```

The boundary hypotheses mean:

- `i = 0`: `deriv (gTower f 0) = f'`, so `f'(0)=f'(1)=0`.
- `i = 1`: `deriv (gTower f 1) = (f'')' = f'''`, so `f'''(0)=f'''(1)=0`.

This matches your C4 Neumann assumptions exactly.

### Step 2: quartic coefficient decay wrapper

If you have a uniform bound on the top raw coefficient:

```lean
hM : ∀ k, 1 ≤ k → |rawCoeff k (gTower f 2)| ≤ M
```

then the wrapper is just:

```lean
import ShenWork.Paper2.IntervalIBPCoeffExtraction
import ShenWork.Paper2.IntervalNeumannTowerOfC4

open ShenWork.IntervalIBPCoeffExtraction (rawCoeff cosineCoeffs_decay)
open ShenWork.Paper2.NeumannTowerOfC6 (gTower gTower_zero)
open ShenWork.Paper2.NeumannTowerOfC4 (neumannTower_two_of_contDiff_four)

theorem cosineCoeffs_quartic_decay_of_contDiff_four
    {f : ℝ → ℝ} {M : ℝ}
    (hf : ContDiff ℝ (4 : ℕ) f)
    (hN0 : ∀ i, i < 2 → deriv (gTower f i) 0 = 0)
    (hN1 : ∀ i, i < 2 → deriv (gTower f i) 1 = 0)
    (hM : ∀ k, 1 ≤ k → |rawCoeff k (gTower f 2)| ≤ M) :
    ∀ k : ℕ, 1 ≤ k →
      |cosineCoeffs f k| ≤ 2 * M / ((k : ℝ) * Real.pi) ^ 4 := by
  intro k hk
  have H := neumannTower_two_of_contDiff_four hf hN0 hN1
  have hdecay := cosineCoeffs_decay k hk H (hM k hk)
  simpa [gTower_zero, show (2 * 2 : ℕ) = 4 by norm_num] using hdecay
```

This is the cleanest exact answer to the requested estimate.

### Step 3: if your bound is an L¹ bound on `f''''`

Usually you will have something like:

```lean
hB : (∫ x in (0:ℝ)..1, |gTower f 2 x|) ≤ B
```

Then prove the top raw coefficient bound by `|cos| ≤ 1`:

```lean
have hTop : ∀ k, 1 ≤ k → |rawCoeff k (gTower f 2)| ≤ B := by
  intro k hk
  unfold rawCoeff
  -- use `intervalIntegral.abs_integral_le_integral_abs`
  -- then `|cos * gTower f 2| ≤ |gTower f 2|`
  -- then `hB`
```

The resulting quartic bound is:

```lean
|cosineCoeffs f k| ≤ 2 * B / ((k : ℝ) * Real.pi) ^ 4
```

This matches the constant pattern of the weak-H² theorem: one normalized coefficient factor `2`, and two IBP steps.

## About the proposed “iterate `IntervalWeakH2Neumann`” route

Your proposed argument is mathematically sound:

1. Build `IntervalWeakH2Neumann f` with `secondDeriv = f''`.
2. Build `IntervalWeakH2Neumann f''` with `secondDeriv = f''''`.
3. Apply quadratic decay to `f''`:

   ```lean
   |cosineCoeffs f'' k| ≤ 2B / (kπ)^2
   ```

4. Use the weak-laplacian identity for `f`:

   ```lean
   cosineCoeffs f'' k = -((k:ℝ) * Real.pi)^2 * cosineCoeffs f k
   ```

   for `k ≥ 1`, up to the same positive-mode normalization factor, which cancels.

5. Divide by `(kπ)^2` to get quartic decay.

But in this repo, the `NeumannTower` abstraction is already exactly this iteration packaged generically.  Using it avoids duplicating raw-coefficient/normalization algebra and should be much shorter.

## Existing “higher-depth” examples to copy

For code style, copy these files:

```text
ShenWork/Paper2/IntervalNeumannTowerOfC6.lean
ShenWork/Paper2/IntervalNeumannTowerOfC8.lean
ShenWork/Paper2/IntervalEigenCubeTailFromTower.lean
ShenWork/Paper2/IntervalEigenCubeSummability.lean
```

The `IntervalEigenCubeTailFromTower.lean` file is especially useful because it shows how to consume `cosineCoeffs_decay` and convert an IBP denominator into eigenvalue-weighted bounds.  Its depth is `j = 3`; your quartic estimate is just `j = 2`.

## Search-result summary

Requested searches:

```text
IntervalWeakH2Neumann
NeumannTower
depth_2
iterated_decay
contDiff_four
cosineCoeffs_decay
```

Findings:

- `IntervalWeakH2Neumann`: one-step weak-H² machinery exists in `IntervalMildSourceDecayHelper.lean` and quantitative explicit-constant decay in `IntervalSourceDecayQuantitative.lean`.
- `NeumannTower`: the arbitrary-depth iteration abstraction exists in `IntervalIBPCoeffExtraction.lean`.
- `cosineCoeffs_decay`: landed arbitrary-depth normalized coefficient decay theorem, exactly the right tool.
- `depth_2` / `iterated_decay`: no direct hits.
- C6/C8 tower producers exist; no C4/depth-2 producer found.

## Bottom line

Do **not** build this by manually iterating `IntervalWeakH2Neumann` unless you specifically need that interface.  The clean repo-native fix is:

1. add `neumannTower_two_of_contDiff_four` as a small C4 clone of the C6/C8 producers;
2. call `IntervalIBPCoeffExtraction.cosineCoeffs_decay` with `j = 2`;
3. prove the top-level raw coefficient bound from either `∫ |f''''| ≤ B` or a sup bound on `f''''`.
