# Q1250 (cron2) — `srcSlice2` joint continuity on a slab

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Answer

I did **not** find an existing reusable lemma named `srcSlice2_jointContinuousOn`, nor did the `srcSlice2.*continuousOn`/`srcSlice2 continuousOn` search reveal a generic continuity helper.

What exists now is:

1. `srcSlice2` is defined in:

   ```text
   ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
   ```

   with the concrete formula

   ```lean
   def srcSlice2 (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
       (du d2u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
     p.ν * p.γ * (p.γ - 1) * (intervalDomainLift (u t) x) ^ (p.γ - 1 - 1)
         * (du t x) ^ (2 : ℕ)
       + p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * d2u t x
   ```

2. There is a pointwise derivative lemma:

   ```lean
   theorem hasDerivAt_srcSlice1
       {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
       {t x : ℝ} (hpos : 0 < intervalDomainLift (u t) x)
       (hdu : HasDerivAt (fun r => intervalDomainLift (u r) x) (du t x) t)
       (hd2u : HasDerivAt (fun r => du r x) (d2u t x) t) :
       HasDerivAt (fun r => srcSlice1 p u du r x) (srcSlice2 p u du d2u t x) t
   ```

3. `IterateSourceTimeData.time2` currently **assumes** the desired joint continuity field:

   ```lean
   ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
     (Icc (τ - δ) (τ + δ) ×ˢ Icc (0:ℝ) 1)
   ```

4. The heat-semigroup base file has `d1` still as a `sorry`, and its comments identify the same third sub-obligation: joint `ContinuousOn` of `s₂ = srcSlice2` on a positive-time slab.

So the answer is: **no committed generic lemma appears to exist; add one.**

## Recommended lemma

The clean helper should not be tied to intervals. Prove it on an arbitrary set `s : Set (ℝ × ℝ)`, then specialize it to slabs. Since `Real.rpow` continuity uses nonzero/positive base hypotheses, the helper should take positivity on the whole set where continuity is requested.

Drop this near `srcSlice2`/`hasDerivAt_srcSlice1` in `ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean`.

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

/-- Joint continuity of the second source-time derivative slice from joint
continuity of the lifted iterate, `du`, and `d2u`, under positivity of the lifted
iterate on the set.  This is the reusable algebraic continuity lemma behind the
`FlooredSourceTimeData.d1` continuity field. -/
theorem srcSlice2_jointContinuousOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    {s : Set (ℝ × ℝ)}
    (hu : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) s)
    (hdu : ContinuousOn (Function.uncurry du) s)
    (hd2u : ContinuousOn (Function.uncurry d2u) s)
    (hpos : ∀ q ∈ s, 0 < intervalDomainLift (u q.1) q.2) :
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u)) s := by
  have hpowγm2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1 - 1)) s :=
    hu.rpow_const (fun q hq => Or.inl (ne_of_gt (hpos q hq)))
  have hpowγm1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1)) s :=
    hu.rpow_const (fun q hq => Or.inl (ne_of_gt (hpos q hq)))
  have hdu' : ContinuousOn (fun q : ℝ × ℝ => du q.1 q.2) s := by
    simpa [Function.uncurry] using hdu
  have hd2u' : ContinuousOn (fun q : ℝ × ℝ => d2u q.1 q.2) s := by
    simpa [Function.uncurry] using hd2u
  have hdu2 : ContinuousOn
      (fun q : ℝ × ℝ => (du q.1 q.2) ^ (2 : ℕ)) s :=
    hdu'.pow (2 : ℕ)
  have hc1 : ContinuousOn
      (fun _ : ℝ × ℝ => p.ν * p.γ * (p.γ - 1)) s :=
    continuousOn_const
  have hc2 : ContinuousOn
      (fun _ : ℝ × ℝ => p.ν * p.γ) s :=
    continuousOn_const
  have hterm1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ * (p.γ - 1) *
          (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1 - 1) *
          (du q.1 q.2) ^ (2 : ℕ)) s := by
    simpa [mul_assoc] using (hc1.mul hpowγm2).mul hdu2
  have hterm2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        p.ν * p.γ *
          (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1) *
          d2u q.1 q.2) s := by
    simpa [mul_assoc] using (hc2.mul hpowγm1).mul hd2u'
  simpa [srcSlice2, Function.uncurry] using hterm1.add hterm2

/-- Slab-specialized wrapper for `srcSlice2_jointContinuousOn`. -/
theorem srcSlice2_jointContinuousOn_slab
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {du d2u : ℝ → ℝ → ℝ}
    {c T : ℝ}
    (hu : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hdu : ContinuousOn (Function.uncurry du)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hd2u : ContinuousOn (Function.uncurry d2u)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hpos : ∀ t ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u t) x) :
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  exact srcSlice2_jointContinuousOn
    (s := Icc c T ×ˢ Icc (0 : ℝ) 1) hu hdu hd2u
    (by
      intro q hq
      rcases mem_prod.mp hq with ⟨ht, hx⟩
      exact hpos q.1 ht q.2 hx)

end ShenWork.IntervalFlooredSourceTimeDataIterate
```

## How I would use it for `FlooredSourceTimeData.d1`

Given a slab `Icc c T ×ˢ Icc 0 1`, with

```lean
hprofile : ContinuousOn
  (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
hdu_joint : ContinuousOn (Function.uncurry du)
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
hd2u_joint : ContinuousOn (Function.uncurry d2u)
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
hpos_slab : ∀ t ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (u t) x
```

then the desired field is just

```lean
have hs2_joint : ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
    (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
  srcSlice2_jointContinuousOn_slab
    (p := p) (u := u) (du := du) (d2u := d2u)
    (c := c) (T := T)
    hprofile hdu_joint hd2u_joint hpos_slab
```

For the local `τ, δ` version inside `d1`, instantiate `c := τ - δ` and `T := τ + δ`.

## Caveat

The existing `IterateSourceTimeData.floor` field in `IntervalFlooredSourceTimeDataIterate.lean` is only stated on `x ∈ Ioo 0 1`, while the desired continuity field is on `Icc 0 1`. The generic `rpow_const` continuity proof above needs positivity/nonzero of the lifted base on the **whole continuity set**. Therefore, for the slab lemma as stated, you need positivity on `Icc 0 1` (as the heat-semigroup base file's `hfloor` already assumes), or you need a separate endpoint argument if your only floor datum is interior positivity.

## Bottom line

Use a new helper. The existing code has the derivative algebra (`hasDerivAt_srcSlice1`) and has the continuity obligation packaged as a field, but it does not appear to have a reusable `srcSlice2_jointContinuousOn` lemma yet.
