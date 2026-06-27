# Q1304 (cron2) — level-0 `conjugatePicardIter` lift equals the heat semigroup

Static GitHub-connector inspection only. I did **not** run Lean locally.

## The exact definitional facts

`conjugatePicardIter` is defined in `ShenWork/Paper2/IntervalConjugatePicard.lean` as:

```lean
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x
```

So at level `0`,

```lean
conjugatePicardIter p u₀ 0 r ⟨x, hx⟩
```

reduces definitionally to

```lean
intervalFullSemigroupOperator r (intervalDomainLift u₀) x
```

The only other step is unfolding `intervalDomainLift` at `x ∈ Icc 0 1`, so it selects the subtype value rather than the outside-zero branch.

## Minimal local proof

Inside `IntervalConjugateLevel0BFormSourceOn.lean`, with the file’s existing opens, this should be the proof you want:

```lean
have hlevel0_lift_eq : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  intro x hx
  simp [intervalDomainLift, conjugatePicardIter, hx]
```

This is the intended one-liner.  The `hx` discharges the `dif_pos` branch in `intervalDomainLift`; `conjugatePicardIter` unfolds the `0` case.

## If `simp` does not unfold enough

Use the slightly more explicit variant:

```lean
have hlevel0_lift_eq : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  intro x hx
  unfold intervalDomainLift
  simp [hx, conjugatePicardIter]
```

If the if-condition in `intervalDomainLift` is phrased through `intervalSet 1` rather than literally `Icc 0 1`, use:

```lean
have hlevel0_lift_eq : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  intro x hx
  unfold intervalDomainLift
  simp [ShenWork.IntervalDomain.intervalSet, hx, conjugatePicardIter]
```

## Pointwise form

For a single `x` and `hx : x ∈ Icc (0 : ℝ) 1`:

```lean
have hx_level0_lift_eq :
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  simp [intervalDomainLift, conjugatePicardIter, hx]
```

or the fully explicit proof:

```lean
have hx_level0_lift_eq :
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  unfold intervalDomainLift
  simp [hx, conjugatePicardIter]
```

## Using it for positivity

This is the bridge you need before applying heat-semigroup positivity:

```lean
have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x := by
  intro x hx
  rw [hlevel0_lift_eq x hx]
  exact hheat_pos_global r hr_pos' x
```

where `hheat_pos_global` has shape:

```lean
hheat_pos_global : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
  0 < intervalFullSemigroupOperator r (intervalDomainLift u₀) x
```

## Bottom line

Yes: on `x ∈ Icc 0 1`, this is definitional.  Use:

```lean
simp [intervalDomainLift, conjugatePicardIter, hx]
```

and add `ShenWork.IntervalDomain.intervalSet` to the simp list only if the lift’s guard is not syntactically the same as `Icc 0 1` in your local goal.
