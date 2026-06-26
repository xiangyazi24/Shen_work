# Q788 / cron1: smoothRightCutoff derivative-bound search

Repo inspected: xiangyazi24/Shen_work
Mathlib inspected: leanprover-community/mathlib4 v4.29.1
Branch written: chatgpt-scratch

Question: for the sub-sorry in `IntervalHeatSemigroupHighRegularity.lean`, prove/bank

  exists B, 0 <= B and forall t,
    norm (iteratedFDeriv Real k (smoothRightCutoff c' c) t) <= B

with k = 0 by range [0,1], and k >= 1 by continuity + compact support / compact interval.

## Search verdict

I did **not** find repo lemmas named like:

  smoothRightCutoff_le_one
  smoothRightCutoff_range
  smoothRightCutoff_support
  smoothRightCutoff_hasCompactSupport

The repo currently has only the basic one-sided cutoff API in

  ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean

namely:

```lean
def smoothRightCutoff (c' c : Real) : Real -> Real :=
  fun t => Real.smoothTransition ((c - c')^{-1} * (t - c'))

theorem smoothRightCutoff_contDiff :
  ContDiff Real (2 : ENat) (smoothRightCutoff c' c)

theorem smoothRightCutoff_eq_zero_of_le :
  c' < c -> t <= c' -> smoothRightCutoff c' c t = 0

theorem smoothRightCutoff_eq_one_of_ge :
  c' < c -> c <= t -> smoothRightCutoff c' c t = 1

theorem smoothRightCutoff_eventually_eq_one :
  c' < c -> c < s -> smoothRightCutoff c' c = eventuallyEq (nhds s) (fun _ => 1)
```

So: no named `smoothRightCutoff_le_one` was found, but it is a one-liner from Mathlib:

```lean
theorem smoothRightCutoff_nonneg (c' c t : Real) :
    0 <= smoothRightCutoff c' c t := by
  unfold smoothRightCutoff
  exact Real.smoothTransition.nonneg _

theorem smoothRightCutoff_le_one (c' c t : Real) :
    smoothRightCutoff c' c t <= 1 := by
  unfold smoothRightCutoff
  exact Real.smoothTransition.le_one _
```

This matches the existing k = 0 branch in `IntervalHeatSemigroupHighRegularity.lean`, which unfolds `smoothRightCutoff` and uses:

  Real.smoothTransition.nonneg
  Real.smoothTransition.le_one

## Current sub-sorry location

On `main`, `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` has the private theorem:

```lean
private theorem smoothRightCutoff_iteratedFDeriv_bound_exists
    (c' c : Real) (k : Nat) (hk : (k : ENat) <= 2) :
    exists B : Real, 0 <= B and
      forall t : Real,
        norm (iteratedFDeriv Real k (smoothRightCutoff c' c) t) <= B := by
  rcases Nat.eq_zero_or_pos k with rfl | _hk_pos
  · -- k = 0: implemented
  · -- k >= 1: sorry
```

The implemented k = 0 branch returns B = 1 and uses `norm_iteratedFDeriv_zero`, `Real.smoothTransition.nonneg`, and `Real.smoothTransition.le_one`.

The k >= 1 branch comment says the derivative is continuous and supported inside `[c', c]`, but the current comment also mentions `HasCompactSupport.iteratedFDeriv`; that theorem exists, but it is **not directly applicable to `smoothRightCutoff` itself**, because `smoothRightCutoff` is eventually 1 on the right and therefore is not compactly supported.

## Mathlib facts found

### 1. HasCompactSupport.iteratedFDeriv exists

In Mathlib v4.29.1:

```lean
theorem HasCompactSupport.iteratedFDeriv
    (hf : HasCompactSupport f) (n : Nat) :
    HasCompactSupport (iteratedFDeriv k n f)
```

Also nearby:

```lean
theorem Filter.EventuallyEq.iteratedFDeriv
    (h : f1 = eventuallyEq (nhds x) f2) (n : Nat) :
    iteratedFDeriv k n f1 = eventuallyEq (nhds x) iteratedFDeriv k n f2
```

The first theorem propagates compact support from the original function. It helps for the two-sided restart cutoff, but **not** for the one-sided `smoothRightCutoff`.

### 2. Positive iterated derivative of a constant is zero

Mathlib has:

```lean
theorem iteratedFDeriv_const_of_ne {n : Nat} (hn : n != 0) (c : F) :
    iteratedFDeriv k n (fun _ : E => c) = 0
```

and the successor form:

```lean
theorem iteratedFDeriv_succ_const (n : Nat) (c : F) :
    iteratedFDeriv k (n + 1) (fun _ : E => c) = 0
```

This is exactly what is needed after `Filter.EventuallyEq.iteratedFDeriv` reduces the cutoff to a local constant.

### 3. Compact boundedness options

Mathlib has both:

```lean
IsCompact.exists_bound_of_continuousOn
```

for bounding a continuous function on a compact set, and:

```lean
Continuous.bounded_above_of_compact_support
```

for bounding a continuous compactly supported function globally.

For this one-sided cutoff, the compact-interval route is probably cleaner than constructing a `HasCompactSupport` object for the derivative field.

## Recommended route for k >= 1

Use a padded compact interval, e.g.

```lean
K := Set.Icc (c' - 1) (c + 1)
```

This avoids needing to prove behavior exactly at `c'` and `c`: endpoints lie inside K, and outside K one is strictly in a constant region.

Sketch:

```lean
have hcont : Continuous
    (fun t : Real => iteratedFDeriv Real k (smoothRightCutoff c' c) t) :=
  smoothRightCutoff_contDiff.continuous_iteratedFDeriv hk

have hnorm_cont : ContinuousOn
    (fun t : Real => norm (iteratedFDeriv Real k (smoothRightCutoff c' c) t))
    (Set.Icc (c' - 1) (c + 1)) :=
  hcont.norm.continuousOn

obtain <B0, hB0> :=
  isCompact_Icc.exists_bound_of_continuousOn hnorm_cont
```

Then for arbitrary `t`:

```lean
by_cases ht : t in Set.Icc (c' - 1) (c + 1)
· exact (hB0 t ht).trans (le_max_left B0 0)
· -- outside padded compact, t < c' or c < t
  -- prove local eventual equality to constant 0 or 1, then positive-order derivative is zero
```

For the left side, add the missing local lemma:

```lean
theorem smoothRightCutoff_eventually_eq_zero {c' c s : Real}
    (hc : c' < c) (hs : s < c') :
    smoothRightCutoff c' c = eventuallyEq (nhds s) (fun _ : Real => 0) := by
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact smoothRightCutoff_eq_zero_of_le hc (le_of_lt ht)
```

For the right side, use the existing:

```lean
smoothRightCutoff_eventually_eq_one hc hs
```

Then:

```lean
have hlocD := Filter.EventuallyEq.iteratedFDeriv Real hloc k
have hD_eq_at_t := hlocD.eq_of_nhds
-- rewrite by hD_eq_at_t, then use iteratedFDeriv_const_of_ne hk_ne 0 or 1
```

Because `k >= 1`, `iteratedFDeriv_const_of_ne` closes the constant derivative side.

Finally return:

```lean
<max B0 0, le_max_right B0 0, ...>
```

## Alternative: derivative-field compact support

If you really want the exact support statement, prove directly:

```lean
HasCompactSupport
  (fun t => iteratedFDeriv Real k (smoothRightCutoff c' c) t)
```

by showing its support is contained in `Set.Icc c' c`. Do **not** try to use

```lean
(HasCompactSupport smoothRightCutoff).iteratedFDeriv k
```

because the premise is false.

The direct support proof uses the same local-constant logic:

- if `t < c'`, the cutoff is locally equal to 0;
- if `c < t`, the cutoff is locally equal to 1;
- positive iterated derivatives of constants are zero.

Then apply:

```lean
hcont.bounded_above_of_compact_support hDerivCompactSupport
```

## Bottom line

- No repo `smoothRightCutoff_le_one`/`range`/`support` lemma was found.
- Add `smoothRightCutoff_le_one` and `smoothRightCutoff_nonneg` as one-liners if desired.
- `HasCompactSupport.iteratedFDeriv` exists in Mathlib, but it does not apply to one-sided `smoothRightCutoff` because the cutoff itself is not compactly supported.
- For the sub-sorry, the robust route is: bound the continuous derivative on a padded compact interval `[c' - 1, c + 1]`, and outside that interval use local equality to constants plus `Filter.EventuallyEq.iteratedFDeriv` and `iteratedFDeriv_const_of_ne`.
