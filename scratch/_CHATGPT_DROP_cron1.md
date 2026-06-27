# Q1308 / cron1 — reusable cosine positivity reduction

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

I did **not** find an existing generic helper named like

```lean
cosineSeriesPositive_of_Icc
heatSemigroup_cosine_pos_all
```

or a general theorem of the form

```lean
(∀ y ∈ Icc (0 : ℝ) 1, 0 < f y) → (∀ x : ℝ, 0 < f x)
```

that abstracts only the symmetry/periodicity argument for an arbitrary real-valued `f`.

What exists are **specialized all-real-line reductions** for heat/resolver cosine syntheses:

1. `ShenWork.EWA.cosineHeatValue_ge_floor_all`
   in
   ```text
   ShenWork/Wiener/EWA/HeatFloor.lean
   ```
   It proves the heat cosine value floor for all `x : ℝ` from a global source floor.  The final step is exactly the period-2 plus evenness reduction to `[0,1]`.

2. `ShenWork.EWA.cosineHeatValue_ge_floor_Icc_all`
   in
   ```text
   ShenWork/Wiener/EWA/HeatFloorIcc.lean
   ```
   This is the closest existing named theorem to your desired pattern, but it is specialized to `unitIntervalCosineHeatValue t (cosineCoeffs u₀)` and proves a `δ ≤ ...` floor, not arbitrary positivity of a function.

3. `ShenWork.EWA.resolverSynthesis_nonneg_all`
   in
   ```text
   ShenWork/Wiener/EWA/SourceResolverFloor.lean
   ```
   This proves nonnegativity of a resolver cosine synthesis for all real `x`, again by the same period-2/evenness reduction.

The local block in

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

around the `V` positivity/nonnegativity step is **not currently factored out**; it repeats the argument locally:

- derive `V (z + 2) = V z`,
- derive `V (z - 2) = V z`,
- build integer shifts `V (z + 2*m) = V z`,
- choose `m₀ := round (x / 2)`,
- set `y := x - 2*m₀`,
- show `|y| ∈ Icc 0 1`,
- use evenness to replace `V y` by `V |y|`,
- apply interval-domain nonnegativity.

For your current `U_cos` use case, the existing local code already has the right ingredients:

```lean
have hU_period_fun : Function.Periodic U_cos 2 := by
  intro x; show U_cos (x + 2) = U_cos x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by congr 1; exact cosineMode_add_two' k x)

have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
  intro y hy
  rw [← hU_agree y hy]
  exact hpos_w y hy
```

and `hU_even : ∀ x, U_cos (-x) = U_cos x` is already in scope.  So the clean reusable abstraction is a small generic lemma.

## Recommended reusable helper

This is the helper I would extract.  It uses only:

- evenness,
- period `2`,
- positivity on `Icc 0 1`.

It does **not** need cosine-specific APIs except for how the caller proves `heven` and `hperiod`.

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open Set

noncomputable section

namespace ShenWork.Paper2

/-- Reduce positivity of an even period-`2` real function to the fundamental interval
`[0,1]`.

This is the reusable skeleton currently duplicated by the heat/resolver floor proofs and
by the local `U_cos`/`V_cos` blocks in `IntervalConjugateLevel0BFormSourceOn.lean`.

The proof first sends `x` to `|x|`, then subtracts an integral multiple of `2` to land
in `[0,2)`, and finally reflects the part in `(1,2)` back into `[0,1]`.  The reflection
`f (2 - r) = f r` is derived from evenness plus period `2`.
-/
theorem pos_all_of_pos_Icc01_even_periodic_two {f : ℝ → ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hperiod : Function.Periodic f 2)
    (hpos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < f y) :
    ∀ x : ℝ, 0 < f x := by
  have hreflect : ∀ z : ℝ, f (2 - z) = f z := by
    intro z
    calc
      f (2 - z) = f (-z + 2) := by congr 1; ring
      _ = f (-z) := hperiod (-z)
      _ = f z := heven z
  intro x
  -- Step 1: reduce to `[0,∞)` by evenness.
  have hx_abs : f x = f |x| := by
    by_cases h : 0 ≤ x
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]
      exact (heven x).symm
  rw [hx_abs]
  -- Step 2: reduce `|x|` to `[0,2)` by subtracting an integral period.
  set n : ℤ := ⌊|x| / 2⌋ with hn_def
  set r : ℝ := |x| - n * 2 with hr_def
  have hrV : f |x| = f r :=
    (hperiod.sub_int_mul_eq n).symm
  have hr_lo : 0 ≤ r := by
    have := Int.floor_le (|x| / 2)
    linarith
  have hr_hi : r < 2 := by
    have := Int.lt_floor_add_one (|x| / 2)
    linarith
  rw [hrV]
  -- Step 3: if `r ≤ 1`, use the interval positivity.  Otherwise reflect across `1`.
  by_cases hr1 : r ≤ 1
  · exact hpos_Icc r ⟨hr_lo, hr1⟩
  · push_neg at hr1
    rw [← hreflect r]
    exact hpos_Icc (2 - r) ⟨by linarith, by linarith⟩

end ShenWork.Paper2
```

## Use it at the current `U_cos` site

Inside `IntervalConjugateLevel0BFormSourceOn.lean`, the local block can collapse to:

```lean
have hU_period_fun : Function.Periodic U_cos 2 := by
  intro x
  show U_cos (x + 2) = U_cos x
  simp only [hU_cos_def]
  exact tsum_congr (fun k => by
    congr 1
    exact cosineMode_add_two' k x)

have hU_pos_all : ∀ x, 0 < U_cos x := by
  have hU_pos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < U_cos y := by
    intro y hy
    rw [← hU_agree y hy]
    exact hpos_w y hy
  exact ShenWork.Paper2.pos_all_of_pos_Icc01_even_periodic_two
    hU_even hU_period_fun hU_pos_Icc
```

This is strictly cleaner than the current local `floor`/`r` block, and it should also be usable for any future cosine synthesis once you prove `Function.Periodic f 2` and evenness.

## If you want the exact round-based variant

The `V` block uses `round (x / 2)` rather than `floor (|x| / 2)`.  A second helper matching that block exactly would take an integer-shift theorem directly:

```lean
theorem pos_all_of_pos_Icc01_even_intShift_two {f : ℝ → ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hshift : ∀ (m : ℤ) (z : ℝ), f (z + 2 * m) = f z)
    (hpos_Icc : ∀ y ∈ Icc (0 : ℝ) 1, 0 < f y) :
    ∀ x : ℝ, 0 < f x := by
  intro x
  set m₀ : ℤ := round (x / 2)
  set y : ℝ := x - 2 * m₀
  have hxy : f x = f y := by
    rw [show x = y + 2 * m₀ from by simp [y]]
    exact hshift m₀ y
  have hyabs : |y| ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact abs_nonneg _
    · have hround : |x / 2 - m₀| ≤ 1 / 2 := abs_sub_round (x / 2)
      rw [show y = 2 * (x / 2 - m₀) from by simp [y]; ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hround]
  have hy : f y = f |y| := by
    by_cases hnn : 0 ≤ y
    · rw [abs_of_nonneg hnn]
    · rw [not_le] at hnn
      rw [abs_of_neg hnn, ← heven]
  rw [hxy, hy]
  exact hpos_Icc |y| hyabs
```

This variant matches lines 636--691 of `IntervalConjugateLevel0BFormSourceOn.lean` more closely, but the `Function.Periodic`/`floor` helper is usually the nicer one for `U_cos`, because you already have `hU_period_fun : Function.Periodic U_cos 2`.

## Bottom line

There is **no currently reusable generic helper** for arbitrary `U_cos` positivity.  The closest reusable named theorems are specialized:

```lean
ShenWork.EWA.cosineHeatValue_ge_floor_all
ShenWork.EWA.cosineHeatValue_ge_floor_Icc_all
ShenWork.EWA.resolverSynthesis_nonneg_all
```

For the present proof, add/extract `pos_all_of_pos_Icc01_even_periodic_two` and replace the local `hU_pos_all` derivation with a one-line call.  The same reduction skeleton can also eliminate future copies of the `round`/`abs` period-2 argument.

No local `lake build` was run; this drop was produced through the GitHub connector only.
