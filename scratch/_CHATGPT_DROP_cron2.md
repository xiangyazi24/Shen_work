# Q1289 (cron2) — positivity hypotheses around `hV_C4` / line 1086

Static GitHub-connector inspection only. I did **not** run Lean locally.

## What `_hpos` actually is

In `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, the relevant theorem is:

```lean
theorem level0_chemDiv_timeDerivData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (_hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x) :
    ...
```

So `_hpos` is **not global**.  It is exactly a strict positive floor for the level-0 heat profile only on the closed time window:

```lean
σ ∈ Icc c T
```

and spatially on `[0,1]`.

There is also a global initial nonnegativity hypothesis:

```lean
_hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x
```

There is **no** hypothesis named `hfloor` in this target file/theorem.  A search for `hfloor` did not find a usable local hypothesis in `IntervalConjugateLevel0BFormSourceOn.lean`.

There is also the upper bound:

```lean
_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M
```

but it is also only windowed over `Icc c T`.

## Why `_hpos` does not directly apply at line 1088

In the local slab proof, the code picks

```lean
δ = min 1 (s / 2)
```

and later has

```lean
r ∈ Metric.ball s δ
hr_pos' : 0 < r
```

The chosen ball only ensures `r > s / 2 > 0`.  It does **not** ensure `r ≤ T`, and near the right endpoint `s = T`, no ordinary `𝓝 s` ball can stay inside `Iic T`.  Thus the term

```lean
_hpos r ?hr_mem_Icc
```

cannot be filled from the ball membership.  This is the exact obstacle: `_hpos` is a window floor, while the `HasDerivAt`/local-chain-rule field is being built on an open ball in all of `ℝ`.

## The good news: the existing hypotheses can still give global positive-time heat positivity

Although `_hpos` is windowed, the theorem also carries enough data to derive a **positive-somewhere initial datum**, then use the existing strict heat positivity theorem for every `r > 0`.

The relevant existing theorem is imported through

```lean
import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier
```

and has the shape:

```lean
ShenWork.Paper2.BFormPositiveDatumNegPart
  .intervalFullSemigroupOperator_pos_of_nonneg_nonzero
```

Its assumptions are:

```lean
{t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
(hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
(hf_nonneg : ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f y)
(hf_pos_somewhere : ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < f y₀)
(x : ℝ) :
0 < intervalFullSemigroupOperator t f x
```

For `f = intervalDomainLift u₀`, the first two are available from `_hu₀_cont` and `_hu₀_nonneg`.  The “positive somewhere” fact is not an explicit hypothesis, but it follows from `_hpos` at `σ = c` because `c ∈ Icc c T` by `_hcT` and because the heat profile at time `c` is strictly positive.  If `intervalDomainLift u₀` were zero everywhere on `[0,1]`, then `S(c)u₀` would be zero, contradicting `_hpos c ⟨le_rfl, _hcT⟩`.

So the right local fix at line 1088 is **not** to use `_hpos r`; instead derive a reusable global positive-time heat lemma:

```lean
have hheat_pos_global : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
    0 < intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
  ...
```

Then for

```lean
w := conjugatePicardIter p u₀ 0 r
```

you get the needed local floor:

```lean
have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
    0 < intervalDomainLift w x := by
  intro x hx
  simp only [w, conjugatePicardIter, intervalDomainLift, dif_pos hx]
  exact hheat_pos_global r hr_pos' x
```

This works for all `r > 0`, including `r > T`, so it bypasses the window mismatch.

## Lean skeleton for the reusable global heat positivity fact

This is the code shape I would insert near the start of `level0_chemDiv_timeDerivData`, before `hlocal_slab`, or inside the local proof before the `hV_C4` branch.

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

  have hheat_pos_global : ∀ r : ℝ, 0 < r → ∀ x : ℝ,
      0 < intervalFullSemigroupOperator r (intervalDomainLift u₀) x := by
    intro r hr x
    exact ShenWork.Paper2.BFormPositiveDatumNegPart
      .intervalFullSemigroupOperator_pos_of_nonneg_nonzero
        hr hLift_cont hLift_nonneg hLift_pos_somewhere x
```

Then at the `hV_C4` positivity point:

```lean
      have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
          0 < intervalDomainLift (conjugatePicardIter p u₀ 0 r) x := by
        intro x hx
        simp only [conjugatePicardIter, intervalDomainLift, dif_pos hx]
        exact hheat_pos_global r hr_pos' x
```

or, if `w` has already been set:

```lean
      have hpos_w : ∀ x ∈ Icc (0 : ℝ) 1,
          0 < intervalDomainLift w x := by
        intro x hx
        simp only [w, conjugatePicardIter, intervalDomainLift, dif_pos hx]
        exact hheat_pos_global r hr_pos' x
```

## Bottom line

* `_hpos` is the window floor:

```lean
∀ σ ∈ Icc c T, ∀ x ∈ Icc 0 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x
```

* `_hu₀_nonneg` is a global nonnegativity hypothesis on the initial datum:

```lean
∀ x : intervalDomainPoint, 0 ≤ u₀ x
```

* There is no `hfloor` hypothesis in the relevant theorem.

* Do **not** try to prove `r ∈ Icc c T` from `r ∈ Metric.ball s δ`; it is false at the right endpoint.

* The intended way out is to use `_hpos` once, at `σ = c`, only to prove that `u₀` is positive somewhere, then combine `_hu₀_nonneg` and `_hu₀_cont` with the existing strict positivity theorem for the full heat semigroup.  That gives positivity for every `r > 0`, including the `r` in the neighborhood ball around `s`.
