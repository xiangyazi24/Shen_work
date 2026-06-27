# Q1326 (cron2) — exact level-0 lift/semigroup equality

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Target

In `IntervalConjugateLevel0BFormSourceOn.lean`, for

```lean
hx : x ∈ Icc (0 : ℝ) 1
```

you want:

```lean
intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
  intervalFullSemigroupOperator r (intervalDomainLift u₀) x
```

This is definitional: level `0` of `conjugatePicardIter` is the heat semigroup, and `intervalDomainLift` on `x ∈ [0,1]` selects the subtype value.

## Exact local proof

Use this first:

```lean
have hlevel0_lift_eq : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  intro x hx
  simp [intervalDomainLift, ShenWork.IntervalDomain.intervalSet,
    conjugatePicardIter, hx]
```

If the local namespace does not expose `conjugatePicardIter`, use the fully qualified name:

```lean
have hlevel0_lift_eq : ∀ x ∈ Icc (0 : ℝ) 1,
    intervalDomainLift (ShenWork.IntervalConjugatePicard.conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  intro x hx
  simp [intervalDomainLift, ShenWork.IntervalDomain.intervalSet,
    ShenWork.IntervalConjugatePicard.conjugatePicardIter, hx]
```

## Pointwise version

For a fixed `x` and `hx`:

```lean
have hx_level0_lift_eq :
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  simp [intervalDomainLift, ShenWork.IntervalDomain.intervalSet,
    conjugatePicardIter, hx]
```

## More explicit version, if `simp` needs help

This version spells out the two definitional reductions:

```lean
have hx_level0_lift_eq :
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  unfold intervalDomainLift
  simp [ShenWork.IntervalDomain.intervalSet, hx,
    conjugatePicardIter]
```

If Lean still leaves a subtype coercion, this fully explicit variant should close it:

```lean
have hx_level0_lift_eq :
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  unfold intervalDomainLift
  rw [dif_pos hx]
  change (conjugatePicardIter p u₀ 0 r) ⟨x, hx⟩ =
    intervalFullSemigroupOperator r (intervalDomainLift u₀) x
  simp [conjugatePicardIter]
```

If the guard is `intervalSet 1` rather than literally `Icc 0 1`, use:

```lean
have hx_intervalSet : x ∈ ShenWork.IntervalDomain.intervalSet 1 := by
  simpa [ShenWork.IntervalDomain.intervalSet] using hx

have hx_level0_lift_eq :
    intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
      intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  unfold intervalDomainLift
  rw [dif_pos hx_intervalSet]
  change (conjugatePicardIter p u₀ 0 r) ⟨x, hx_intervalSet⟩ =
    intervalFullSemigroupOperator r (intervalDomainLift u₀) x
  simp [conjugatePicardIter]
```

## Direct use in the positivity proof

For the `hpos_w` bridge:

```lean
have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x := by
  intro x hx
  rw [hlevel0_lift_eq x hx]
  exact hheat_pos_global r hr_pos' x
```

or inline:

```lean
have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x := by
  intro x hx
  have hx_eq :
      intervalDomainLift (conjugatePicardIter p u₀ 0 r) x =
        intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
    simp [intervalDomainLift, ShenWork.IntervalDomain.intervalSet,
      conjugatePicardIter, hx]
  rw [hx_eq]
  exact hheat_pos_global r hr_pos' x
```

## Bottom line

The shortest robust proof is:

```lean
by
  intro x hx
  simp [intervalDomainLift, ShenWork.IntervalDomain.intervalSet,
    conjugatePicardIter, hx]
```

and the most explicit proof is:

```lean
by
  unfold intervalDomainLift
  rw [dif_pos hx]
  change (conjugatePicardIter p u₀ 0 r) ⟨x, hx⟩ =
    intervalFullSemigroupOperator r (intervalDomainLift u₀) x
  simp [conjugatePicardIter]
```

Use the `intervalSet` version if the `dif_pos` guard is not syntactically the same as `hx`.
