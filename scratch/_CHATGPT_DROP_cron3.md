# Q1305 (cron3): global positivity of even period-2 cosine series

## Findings

`ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` lines 636--691 contain a local hand-rolled reduction:

1. get symmetry facts for a cosine/resolver lift;
2. derive period-2 and subtraction-by-2 facts;
3. reduce arbitrary `x` to `y = x - 2 * round (x / 2)` with `|y| ∈ Icc 0 1`;
4. use evenness to replace `y` by `|y|`;
5. apply positivity/nonnegativity on `Icc 0 1`.

There is an existing **resolver-specific** reusable lemma in

```text
ShenWork/Paper2/IntervalResolverHighRegularity.lean
```

namely:

```lean
theorem intervalResolverLiftR_nonneg_of_nonneg_on_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalResolverLiftR p u x)
    (x : ℝ) :
    0 ≤ intervalResolverLiftR p u x := by
```

and the strict `1 + V` corollary:

```lean
theorem intervalResolverLiftR_one_add_pos_of_nonneg_on_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hnn : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalResolverLiftR p u x)
    (x : ℝ) :
    (0 : ℝ) < 1 + intervalResolverLiftR p u x :=
```

These are useful for `intervalResolverLiftR`, but not directly for a generic `U_cos`.  For `U_cos`, use the generic helper below.  It is the same idea, but cleaner than the local `round` proof: use `Function.Periodic.sub_int_mul_eq` and `floor` to reduce `x` to `r ∈ [0,2)`, then use evenness + period to reflect `r > 1` into `2-r ∈ [0,1]`.

## Generic helper

```lean
import Mathlib

open Set

noncomputable section

/-- Global strict positivity from strict positivity on `[0,1]`, evenness,
and period `2`.  This is the generic version of the symmetry/periodicity
reduction used locally in `IntervalConjugateLevel0BFormSourceOn.lean`. -/
theorem positive_everywhere_of_even_periodic_pos_on_Icc
    {F : ℝ → ℝ}
    (heven : ∀ z : ℝ, F (-z) = F z)
    (hperiodic : Function.Periodic F (2 : ℝ))
    (hpos : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < F z) :
    ∀ z : ℝ, 0 < F z := by
  intro x
  set n : ℤ := ⌊x / 2⌋ with hn
  set r : ℝ := x - (n : ℝ) * 2 with hr
  have hxr : F x = F r := by
    show F x = F (x - (n : ℝ) * 2)
    exact (hperiodic.sub_int_mul_eq n).symm
  have hr_lo : 0 ≤ r := by
    have hn_le : (n : ℝ) ≤ x / 2 := by
      simpa [hn] using Int.floor_le (x / 2)
    rw [hr]
    nlinarith
  have hr_hi : r < 2 := by
    have hx_lt : x / 2 < (n : ℝ) + 1 := by
      simpa [hn] using Int.lt_floor_add_one (x / 2)
    rw [hr]
    nlinarith
  rw [hxr]
  by_cases hr1 : r ≤ 1
  · exact hpos r ⟨hr_lo, hr1⟩
  · have hr1lt : 1 < r := lt_of_not_ge hr1
    have hreflect : F r = F (2 - r) := by
      calc
        F r = F (-r) := (heven r).symm
        _ = F (-r + 2) := (hperiodic (-r)).symm
        _ = F (2 - r) := by
          have harg : -r + 2 = 2 - r := by ring
          rw [harg]
    rw [hreflect]
    exact hpos (2 - r) ⟨by linarith, by linarith⟩

/-- Same helper with period supplied in the raw form usually produced for cosine
series, `∀ z, F (z + 2) = F z`. -/
theorem positive_everywhere_of_even_period_two_pos_on_Icc
    {F : ℝ → ℝ}
    (heven : ∀ z : ℝ, F (-z) = F z)
    (hperiod : ∀ z : ℝ, F (z + 2) = F z)
    (hpos : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < F z) :
    ∀ z : ℝ, 0 < F z :=
  positive_everywhere_of_even_periodic_pos_on_Icc heven
    (show Function.Periodic F (2 : ℝ) from hperiod) hpos
```

## How to use for `U_cos`

If the local facts are:

```lean
have hU_even : ∀ z : ℝ, U_cos (-z) = U_cos z := by
  ...

have hU_periodic : ∀ z : ℝ, U_cos (z + 2) = U_cos z := by
  ...

have hU_pos_Icc : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < U_cos z := by
  ...
```

then the global positivity proof is just:

```lean
have hU_pos_global : ∀ z : ℝ, 0 < U_cos z :=
  positive_everywhere_of_even_period_two_pos_on_Icc
    hU_even hU_periodic hU_pos_Icc
```

If instead the cosine-series facts you already have are evenness plus reflection about `1`, derive period-2 exactly as in the target-file pattern:

```lean
have hU_periodic : ∀ z : ℝ, U_cos (z + 2) = U_cos z := fun z => by
  have h1 : U_cos (z + 2) = U_cos (2 - (-z)) := by
    congr 1
    ring
  rw [h1, hU_reflect, hU_even]
```

Then apply the helper above.

## Best existing lemma to point to

For resolver lifts, use the existing lemma directly:

```lean
ShenWork.Paper2.IntervalResolverHighRegularity
  .intervalResolverLiftR_nonneg_of_nonneg_on_Icc
```

For a generic heat/cosine series `U_cos`, I did not find an existing repo-level generic lemma; the helper above is the reusable abstraction of the same argument.
