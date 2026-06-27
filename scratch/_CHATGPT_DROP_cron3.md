# Q1238 (cron3): `ContinuousOn (srcSlice p u s) (Icc 0 1)`

## Verdict

There is **no public repo lemma named** `continuousOn_srcSlice` that directly fills this goal.

The reusable API is the generic Mathlib/Lean theorem:

```lean
ContinuousOn.rpow_const
```

followed by multiplication by the constant `p.ν`:

```lean
continuousOn_const.mul (...)
```

The closest exact repo proof is a **private** helper in
`ShenWork/Wiener/EWA/SourcePerSliceClose.lean`:

```lean
private theorem powerSource_continuousOn_Icc ... :
  ContinuousOn (fun x => p.ν * (intervalDomainLift (realSlice u_star s) x) ^ p.γ)
    (Icc (0 : ℝ) 1) := by
  have hcont : ContinuousOn (intervalDomainLift (realSlice u_star s)) (Icc (0 : ℝ) 1) := ...
  exact continuousOn_const.mul (hcont.rpow_const (fun x _ => Or.inr p.hγ.le))
```

Because it is `private`, you cannot call it outside that file. But its body is exactly the pattern to copy.

The source slice itself is defined in `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean` as:

```lean
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ
```

## Direct proof to use

If you already have:

```lean
hlift : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1)
hpos  : ∀ x ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift (u s) x
```

then the proof is:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)

noncomputable section

example {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hlift : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1))
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < intervalDomainLift (u s) x) :
    ContinuousOn (srcSlice p u s) (Icc (0 : ℝ) 1) := by
  unfold srcSlice
  exact continuousOn_const.mul
    (hlift.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx))))
```

Since `p.hγ : 0 < p.γ`, for **continuity only** you can also use the nonnegative-exponent branch and avoid strict positivity:

```lean
import ShenWork.PDE.IntervalPhysicalSourceTimeC2Concrete

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice)

noncomputable section

example {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hlift : ContinuousOn (intervalDomainLift (u s)) (Icc (0 : ℝ) 1)) :
    ContinuousOn (srcSlice p u s) (Icc (0 : ℝ) 1) := by
  unfold srcSlice
  exact continuousOn_const.mul
    (hlift.rpow_const (fun _ _ => Or.inr p.hγ.le))
```

The strict-positive version is better if the next proof also differentiates through `rpow`; the nonnegative-exponent version is enough for `ContinuousOn`.

## If the goal is not unfolded

In a `FlooredSourceTimeData.d0` proof, the goal may mention `srcSlice p u s` without reducing. Use `simpa` instead of `unfold` if preferred:

```lean
have hsrc_cont : ContinuousOn (srcSlice p u s) (Icc (0 : ℝ) 1) := by
  have hpow : ContinuousOn
      (fun x => intervalDomainLift (u s) x ^ p.γ) (Icc (0 : ℝ) 1) :=
    hlift.rpow_const (fun x hx => Or.inl (ne_of_gt (hpos x hx)))
  simpa [ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcSlice] using
    continuousOn_const.mul hpow
```

or, without using `hpos`:

```lean
have hsrc_cont : ContinuousOn (srcSlice p u s) (Icc (0 : ℝ) 1) := by
  have hpow : ContinuousOn
      (fun x => intervalDomainLift (u s) x ^ p.γ) (Icc (0 : ℝ) 1) :=
    hlift.rpow_const (fun _ _ => Or.inr p.hγ.le)
  simpa [ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcSlice] using
    continuousOn_const.mul hpow
```

## Product-slab analogue

The same pattern is used in `IntervalPicardLevel0SourceTimeC1On.lean` inside
`heatSourceDot_jointContinuousOn`:

```lean
have hpow : ContinuousOn
    (fun q : ℝ × ℝ =>
      (intervalDomainLift (picardIter p u₀ 0 q.1) q.2) ^ p.α)
    (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1) := by
  apply ContinuousOn.rpow_const hprofile
  intro q hq
  obtain ⟨hσ, hx⟩ := Set.mem_prod.mp hq
  exact Or.inl (ne_of_gt (hpos q.1 hσ q.2 hx))
```

So the answer is: **use `ContinuousOn.rpow_const`; no public `srcSlice`-specific lemma is needed.**
