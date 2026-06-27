# Q1293 (cron2) — global positivity pattern for `U_cos`

Static GitHub-connector inspection only. I did **not** run Lean locally.

## The exact pattern in the file

The relevant block is the `hU_pos_all` pattern.  In the current indexed file it appears in the `hf''_H2` construction, right after `hU_even` and `hU_symm1` have been built.

The ingredients are:

```lean
hU_even  : ∀ x, U_cos (-x) = U_cos x
hU_symm1 : ∀ x, U_cos (2 - x) = U_cos x
```

and first a period-2 fact is derived:

```lean
have hU_period_fun : Function.Periodic U_cos 2 := by
  intro x; show U_cos (x + 2) = U_cos x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)
```

Then the code proves positivity on `[0,1]`:

```lean
have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
  intro y hy
  rw [← hU_agree y hy]
  exact hpos_w y hy
```

In the original per-slice use, `hpos_w` was obtained from the window hypothesis:

```lean
have hpos_w : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    0 < intervalDomainLift w x :=
  _hpos s hs
```

So the old source of positivity is:

```lean
_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x
```

The global positivity reduction then proceeds as follows:

```lean
have hU_pos_all : ∀ x, 0 < U_cos x := by
  have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
    intro y hy
    rw [← hU_agree y hy]
    exact hpos_w y hy
  intro x
  -- Step 1: reduce to [0,∞) using evenness
  have hx_abs : U_cos x = U_cos |x| := by
    by_cases h : 0 ≤ x
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]
      exact (hU_even x).symm
  rw [hx_abs]
  -- Step 2: reduce |x| to [0,2) using period 2
  set n := ⌊|x| / 2⌋ with hn_def
  set r := |x| - n * 2 with hr_def
  have hrV : U_cos |x| = U_cos r :=
    (hU_period_fun.sub_int_mul_eq n).symm
  have hr_lo : 0 ≤ r := by
    have := Int.floor_le (|x| / 2)
    linarith
  have hr_hi : r < 2 := by
    have := Int.lt_floor_add_one (|x| / 2)
    linarith
  rw [hrV]
  -- Step 3: if r ∈ [0,1], done; if r ∈ (1,2), use symmetry about 1
  by_cases hr1 : r ≤ 1
  · exact hU_pos_Icc r ⟨hr_lo, hr1⟩
  · push_neg at hr1
    have : U_cos r = U_cos (2 - r) := (hU_symm1 r).symm
    rw [this]
    exact hU_pos_Icc (2 - r) ⟨by linarith, by linarith⟩
```

That is the exact mechanism:

1. prove positivity on `[0,1]`;
2. use evenness to replace `x` by `|x|`;
3. use period 2 to reduce `|x|` to `r = |x| - 2⌊|x|/2⌋ ∈ [0,2)`;
4. if `r ≤ 1`, use the `[0,1]` positivity;
5. if `1 < r < 2`, reflect by `x ↦ 2 - x` to land in `[0,1]`.

## For a different `r` not necessarily in `Icc c T`

Do **not** try to use `_hpos r`; that requires `r ∈ Icc c T` and fails for the local ball near `T`.

Instead, replace only the `[0,1]` seed:

```lean
have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := ...
```

Everything after that — the evenness/period-2/reflection reduction — is unchanged.

For a positive time `r` with

```lean
hr_pos' : 0 < r
```

and

```lean
U_cos x = ∑' k,
  (Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) * cosineMode k x
```

use the heat-semigroup positivity theorem to build positivity on `[0,1]`.

The exact primitive is:

```lean
ShenWork.IntervalSemigroupConeAtoms.intervalFullSemigroupOperator_pos
```

with signature:

```lean
theorem intervalFullSemigroupOperator_pos
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    {y₀ : ℝ} (hy₀ : y₀ ∈ Set.Icc (0 : ℝ) 1) (hf_pos : 0 < f y₀)
    (x : ℝ) :
    0 < intervalFullSemigroupOperator t f x
```

There is also a convenient wrapper:

```lean
ShenWork.Paper2.BFormPositiveDatumNegPart
  .intervalFullSemigroupOperator_pos_of_nonneg_nonzero
```

with signature:

```lean
theorem intervalFullSemigroupOperator_pos_of_nonneg_nonzero
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
    (hf_pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀)
    (x : ℝ) :
    0 < intervalFullSemigroupOperator t f x
```

## Drop-in pattern for arbitrary positive `r`

Assume you have already derived:

```lean
hLift_cont : ContinuousOn (intervalDomainLift u₀) (Icc (0 : ℝ) 1)
hLift_nonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y
hLift_pos_somewhere : ∃ y₀ ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift u₀ y₀
```

Then for any `r > 0`, define:

```lean
have hheat_pos_global : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
    0 < intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  intro r hr x
  exact ShenWork.Paper2.BFormPositiveDatumNegPart
    .intervalFullSemigroupOperator_pos_of_nonneg_nonzero
      hr hLift_cont hLift_nonneg hLift_pos_somewhere x
```

Now in the local `r` block:

```lean
set w := conjugatePicardIter p u₀ 0 r with hw_def

set U_cos := fun x => ∑' k,
  (Real.exp (-r * unitIntervalCosineEigenvalue k) * heatCoeff u₀ k) *
    cosineMode k x with hU_cos_def

have hU_agree : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x = U_cos x :=
  fun x hx => ShenWork.IntervalPicardIterateRepresentation.hagree_zero
    p u₀ hr_pos' _hu₀_cont _hu₀_bound hx

-- Positivity on [0,1], using heat positivity instead of `_hpos r`.
have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
  intro y hy
  rw [← hU_agree y hy]
  simp only [conjugatePicardIter, intervalDomainLift, dif_pos hy]
  exact hheat_pos_global r hr_pos' y
```

Then paste the existing global-reduction block unchanged:

```lean
have hU_period_fun : Function.Periodic U_cos 2 := by
  intro x
  show U_cos (x + 2) = U_cos x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)

have hU_pos_all : ∀ x, 0 < U_cos x := by
  intro x
  have hx_abs : U_cos x = U_cos |x| := by
    by_cases h : 0 ≤ x
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]
      exact (hU_even x).symm
  rw [hx_abs]
  set n := ⌊|x| / 2⌋ with hn_def
  set q := |x| - n * 2 with hq_def
  have hqU : U_cos |x| = U_cos q :=
    (hU_period_fun.sub_int_mul_eq n).symm
  have hq_lo : 0 ≤ q := by
    have := Int.floor_le (|x| / 2)
    linarith
  have hq_hi : q < 2 := by
    have := Int.lt_floor_add_one (|x| / 2)
    linarith
  rw [hqU]
  by_cases hq1 : q ≤ 1
  · exact hU_pos_Icc q ⟨hq_lo, hq1⟩
  · push_neg at hq1
    have : U_cos q = U_cos (2 - q) := (hU_symm1 q).symm
    rw [this]
    exact hU_pos_Icc (2 - q) ⟨by linarith, by linarith⟩
```

## How to get `hLift_pos_somewhere` under the current hypotheses

In `level0_chemDiv_timeDerivData`, the available hypotheses are:

```lean
_hu₀_cont : Continuous u₀
_hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x
_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x
```

Use `_hpos` only at `σ = c` to prove `u₀` is positive somewhere.  Since `_hcT : c ≤ T`, we have `c ∈ Icc c T`.  If `intervalDomainLift u₀` were zero on `[0,1]`, then `S(c)u₀` would be zero, contradicting `_hpos c`.

Skeleton:

```lean
have hLift_cont : ContinuousOn (intervalDomainLift u₀) (Icc (0 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  have hrestr : Set.restrict (Icc (0 : ℝ) 1) (intervalDomainLift u₀) = u₀ := by
    funext ⟨z, hz⟩
    show intervalDomainLift u₀ z = u₀ ⟨z, hz⟩
    rw [intervalDomainLift, dif_pos hz]
  rw [hrestr]
  exact _hu₀_cont

have hLift_nonneg : ∀ y ∈ Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y := by
  intro y hy
  rw [intervalDomainLift, dif_pos hy]
  exact _hu₀_nonneg ⟨y, hy⟩

have hLift_pos_somewhere : ∃ y₀ ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift u₀ y₀ := by
  by_contra hnone
  push_neg at hnone
  have hzero_lift : ∀ y ∈ Icc (0 : ℝ) 1, intervalDomainLift u₀ y = 0 := by
    intro y hy
    exact le_antisymm (not_lt.mp (hnone y hy)) (hLift_nonneg y hy)
  have hhalf : ((1 : ℝ) / 2) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hSc_pos :
      0 < intervalFullSemigroupOperator c (intervalDomainLift u₀) ((1 : ℝ) / 2) := by
    have h := _hpos c ⟨le_rfl, _hcT⟩ ((1 : ℝ) / 2) hhalf
    simpa [conjugatePicardIter, intervalDomainLift, hhalf] using h
  have hSc_zero :
      intervalFullSemigroupOperator c (intervalDomainLift u₀) ((1 : ℝ) / 2) = 0 := by
    unfold intervalFullSemigroupOperator
    have hzero_ae :
        (fun y => intervalNeumannFullKernel c ((1 : ℝ) / 2) y * intervalDomainLift u₀ y)
          =ᵐ[intervalMeasure 1] fun _ => 0 := by
      unfold intervalMeasure intervalSet
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun y hy => by
        rw [hzero_lift y hy, mul_zero]
    rw [integral_congr_ae hzero_ae]
    simp
  rw [hSc_zero] at hSc_pos
  exact (lt_irrefl (0 : ℝ) hSc_pos).elim
```

After that, the `hheat_pos_global` block above gives positivity for every positive `r`, with no need for `r ∈ Icc c T`.

## Bottom line

The old pattern uses `_hpos` only to get `hU_pos_Icc`; the global part is pure symmetry:

```text
[0,1] positivity + evenness + period 2 + reflection about 1 ⇒ positivity on all ℝ.
```

For a different `r`, keep the symmetry block exactly the same.  Replace the `[0,1]` seed with:

```lean
rw [← hU_agree y hy]
simp [conjugatePicardIter, intervalDomainLift, dif_pos hy]
exact hheat_pos_global r hr_pos' y
```

where `hheat_pos_global` is obtained from `intervalFullSemigroupOperator_pos` / `intervalFullSemigroupOperator_pos_of_nonneg_nonzero` applied to the initial datum.
