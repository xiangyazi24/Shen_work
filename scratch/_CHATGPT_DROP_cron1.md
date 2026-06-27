# Q1239 / cron1 — `srcSlice1` joint continuity on a closed slab

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Search result

I searched for both requested shapes:

```text
srcSlice1_continuousOn
ContinuousOn uncurry srcSlice1
srcSlice1
```

What I found:

* I did **not** find a named theorem `srcSlice1_continuousOn`.
* `srcSlice1` is defined in:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

as

```lean
def srcSlice1 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (du : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * du t x
```

* The same file already has the consumer field in `IterateSourceTimeData.time1`:

```lean
ContinuousOn (Function.uncurry (srcSlice1 p u du))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
```

* The in-repo proof pattern exists, but it is not factored under the name you want.  The closest pattern is the usual:

```lean
hprofile_joint.rpow_const ...
```

followed by product/constant continuity.  For example, `IntervalPicardSourceTimeC1OnRecursion.lean` proves continuity of a source-derivative expression using `rpow_const` on the positive lifted profile and then closes by multiplying continuous factors.  On `main`, `IntervalHeatSemigroupFlooredSourceTimeData.lean` also has an inline `d0`/`srcSlice1` continuity proof of exactly this algebraic form.

## Recommended lemma

Add this lemma in the namespace where `srcSlice1` is defined, ideally immediately after `srcSlice1` in:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

The proof is pure continuity algebra: continuity of the lifted profile gives continuity of the power by `rpow_const`; positivity supplies the nonzero-base side-condition for `rpow_const`; then multiply by the continuous `du` factor and the two constants `p.ν`, `p.γ`.

The positivity hypothesis must be on the same **closed** slab as the conclusion.  If you only have positivity on `Ioo (0:ℝ) 1`, that is enough for an interior slab, but not for this exact `Icc c T ×ˢ Icc 0 1` target unless you separately prove endpoint positivity or use a different theorem that exploits a positive exponent.

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

/-- Joint continuity of the first source time-derivative slice from joint
continuity of the lifted iterate and of the time derivative `du`, under
positivity of the lifted iterate on the same closed slab.

This is the direct abstraction of

`srcSlice1 p u du t x = p.ν * p.γ * (lift (u t) x) ^ (p.γ - 1) * du t x`.
-/
theorem srcSlice1_continuousOn_of_posOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du : ℝ → ℝ → ℝ}
    {c T : ℝ}
    (hlift : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hdu : ContinuousOn (Function.uncurry du)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hpos : ∀ q ∈ Icc c T ×ˢ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u q.1) q.2) :
    ContinuousOn (Function.uncurry (srcSlice1 p u du))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  have hpow1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    hlift.rpow_const (fun q hq => Or.inl (ne_of_gt (hpos q hq)))
  simpa [srcSlice1, Function.uncurry] using
    (continuousOn_const.mul continuousOn_const).mul (hpow1.mul hdu)

/-- Same continuity lemma, but with slab positivity written in separated
`time`/`space` form.  This is usually the most convenient form in the PDE files. -/
theorem srcSlice1_continuousOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du : ℝ → ℝ → ℝ}
    {c T : ℝ}
    (hlift : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hdu : ContinuousOn (Function.uncurry du)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hpos : ∀ t ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) x) :
    ContinuousOn (Function.uncurry (srcSlice1 p u du))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  refine srcSlice1_continuousOn_of_posOn
    (p := p) (u := u) (du := du) (c := c) (T := T) hlift hdu ?_
  intro q hq
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  exact hpos q.1 ht q.2 hx

end ShenWork.IntervalFlooredSourceTimeDataIterate
```

If this is inserted directly into `ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean`, do **not** keep the self-import line.  The import line above is for a standalone scratch/check file.

## How to use it in the slab proof

Given a local slab

```lean
K = Icc c T ×ˢ Icc (0 : ℝ) 1
```

and hypotheses

```lean
hlift : ContinuousOn
  (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
  (Icc c T ×ˢ Icc (0 : ℝ) 1)

hdu : ContinuousOn (Function.uncurry du)
  (Icc c T ×ˢ Icc (0 : ℝ) 1)

hpos : ∀ t ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (u t) x
```

close the target by:

```lean
exact srcSlice1_continuousOn
  (p := p) (u := u) (du := du) (c := c) (T := T)
  hlift hdu hpos
```

If your continuity hypothesis for the lifted profile is stated with `Function.uncurry`, first normalize it:

```lean
have hlift' : ContinuousOn
    (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
    (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  simpa [Function.uncurry] using hlift
```

If your positivity is already q-shaped, use the `_of_posOn` lemma directly:

```lean
exact srcSlice1_continuousOn_of_posOn
  (p := p) (u := u) (du := du) (c := c) (T := T)
  hlift hdu hpos
```

## Why this is the right side-condition

The only nontrivial side condition is the real-power continuity side-condition.  For

```lean
(fun q : ℝ × ℝ => (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1))
```

`rpow_const` asks for a nonzero base at every point of the continuity set, or a separate positive-exponent route.  Since the exponent is `p.γ - 1` and may not be known positive in the local proof, the robust route is:

```lean
Or.inl (ne_of_gt (hpos q hq))
```

That is exactly why the lemma assumes strict positivity of `lift(u)` on the slab.

## Heat-level call shape

For the heat semigroup base case, the proof context often has a positive lower time endpoint `hc : 0 < c` and a floor of the form

```lean
hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Icc (0:ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x
```

Then instantiate the separated positivity argument as:

```lean
have hsrc1_joint : ContinuousOn
    (Function.uncurry
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)))
    (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  refine srcSlice1_continuousOn
    (p := p) (u := conjugatePicardIter p u₀ 0) (du := heatDu u₀)
    (c := c) (T := T)
    hprofile hdu_joint ?_
  intro t ht x hx
  exact hfloor t (lt_of_lt_of_le hc ht.1) x hx
```

This removes the duplicated inline proof of `srcSlice1` continuity and makes `IterateSourceTimeData.time1` easier to fill.

## Build note

I did not run a local `lake build`; this task was completed through the GitHub connector only.  The theorem body above is aligned with the existing in-repo `rpow_const`/product-continuity pattern and with the inline `srcSlice1` continuity proof already present on `main`.
