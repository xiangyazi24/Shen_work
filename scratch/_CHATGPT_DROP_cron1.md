# Q1265 / cron1 — `srcSlice2` joint continuity on a positive-time slab

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Target

You want a reusable proof of

```lean
ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

from joint continuity of

```lean
fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2
Function.uncurry du
Function.uncurry d2u
```

on the slab, plus strict positivity of the lifted profile on that same slab.

The theorem belongs naturally in:

```text
ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean
```

right after `srcSlice2`, or after the existing `hasDerivAt_srcSlice1` theorem.  The proof is pure continuity algebra: two `rpow_const` calls for `lift^(γ-2)` and `lift^(γ-1)`, `hdu.pow 2` for `du²`, then `.mul` and `.add`.

## Full Lean proof

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

noncomputable section

namespace ShenWork.IntervalFlooredSourceTimeDataIterate

/-- Joint continuity of the second source time-derivative slice from joint
continuity of the lifted iterate, `du`, and `d2u`, under positivity of the
lifted iterate on the same closed slab.

This is exactly the continuity algebra for

`srcSlice2 p u du d2u t x`
`= ν·γ·(γ-1)·lift(u t x)^(γ-2)·du(t,x)^2`
`  + ν·γ·lift(u t x)^(γ-1)·d2u(t,x)`.
-/
theorem srcSlice2_continuousOn_of_posOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {du d2u : ℝ → ℝ → ℝ} {c T : ℝ}
    (hlift : ContinuousOn
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hdu : ContinuousOn (Function.uncurry du)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hd2u : ContinuousOn (Function.uncurry d2u)
      (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hpos : ∀ q ∈ Icc c T ×ˢ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (u q.1) q.2) :
    ContinuousOn (Function.uncurry (srcSlice2 p u du d2u))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  have hdu' : ContinuousOn
      (fun q : ℝ × ℝ => du q.1 q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hdu
  have hd2u' : ContinuousOn
      (fun q : ℝ × ℝ => d2u q.1 q.2)
      (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
    simpa [Function.uncurry] using hd2u
  have hpow2 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1 - 1))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    hlift.rpow_const (fun q hq => Or.inl (ne_of_gt (hpos q hq)))
  have hpow1 : ContinuousOn
      (fun q : ℝ × ℝ =>
        (intervalDomainLift (u q.1) q.2) ^ (p.γ - 1))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    hlift.rpow_const (fun q hq => Or.inl (ne_of_gt (hpos q hq)))
  have hdu_sq : ContinuousOn
      (fun q : ℝ × ℝ => (du q.1 q.2) ^ (2 : ℕ))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    hdu'.pow 2
  simpa [srcSlice2, Function.uncurry] using
    ((((continuousOn_const.mul continuousOn_const).mul continuousOn_const).mul
      hpow2).mul hdu_sq).add
    (((continuousOn_const.mul continuousOn_const).mul hpow1).mul hd2u')

/-- Same `srcSlice2` joint continuity lemma, with slab positivity written in
separated time/space form.  This is usually the most convenient form in PDE
slab proofs. -/
theorem srcSlice2_continuousOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {du d2u : ℝ → ℝ → ℝ} {c T : ℝ}
    (hlift : ContinuousOn
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
  refine srcSlice2_continuousOn_of_posOn
    (p := p) (u := u) (du := du) (d2u := d2u)
    (c := c) (T := T) hlift hdu hd2u ?_
  intro q hq
  obtain ⟨ht, hx⟩ := Set.mem_prod.mp hq
  exact hpos q.1 ht q.2 hx

end ShenWork.IntervalFlooredSourceTimeDataIterate
```

If inserted directly into `ShenWork/PDE/IntervalFlooredSourceTimeDataIterate.lean`, do **not** keep the self-import line.  The rest can be pasted after the `srcSlice2` definition or after the derivative lemmas.

## Direct use in the positive heat slab

For the existing heat-semigroup `d1` slab, after you have:

```lean
hprofile : ContinuousOn
  (fun q : ℝ × ℝ =>
    intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

hdu_joint : ContinuousOn
  (fun q : ℝ × ℝ => heatDu u₀ q.1 q.2)
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)

hd2u_joint : ContinuousOn
  (fun q : ℝ × ℝ => heatD2u u₀ q.1 q.2)
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

close the `srcSlice2` continuity goal by normalizing the `du`/`d2u` continuity inputs into `Function.uncurry` form:

```lean
have hdu_uncurry : ContinuousOn (Function.uncurry (heatDu u₀))
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  simpa [Function.uncurry] using hdu_joint
have hd2u_uncurry : ContinuousOn (Function.uncurry (heatD2u u₀))
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) := by
  simpa [Function.uncurry] using hd2u_joint

exact ShenWork.IntervalFlooredSourceTimeDataIterate.srcSlice2_continuousOn
  (p := p)
  (u := conjugatePicardIter p u₀ 0)
  (du := heatDu u₀)
  (d2u := heatD2u u₀)
  (c := τ - δ) (T := τ + δ)
  hprofile hdu_uncurry hd2u_uncurry
  (by
    intro s hs x hx
    exact hfloor s (lt_of_lt_of_le hleft hs.1) x hx)
```

The inline proof currently visible in the heat semigroup file has the same algebraic shape:

```lean
have hpow2 : ContinuousOn
    (fun q : ℝ × ℝ =>
      (intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2) ^ (p.γ - 1 - 1))
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
  hprofile.rpow_const (fun q hq => by
    obtain ⟨hσ, hx⟩ := mem_prod.mp hq
    exact Or.inl (ne_of_gt (hfloor q.1 (lt_of_lt_of_le hleft hσ.1) q.2 hx)))
have hdu_sq : ContinuousOn
    (fun q : ℝ × ℝ => (heatDu u₀ q.1 q.2) ^ (2 : ℕ))
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
  hdu_joint.pow 2
have hd2u_joint : ContinuousOn
    (fun q : ℝ × ℝ => heatD2u u₀ q.1 q.2)
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1) :=
  heatD2u_jointContinuousOn hleft _hu₀_bound
simpa [srcSlice2, Function.uncurry] using
  ((((continuousOn_const.mul continuousOn_const).mul continuousOn_const).mul
    hpow2).mul hdu_sq).add
  (((continuousOn_const.mul continuousOn_const).mul hpow1).mul hd2u_joint)
```

The reusable lemma above removes that duplication and only asks for the three joint-continuity inputs plus slab positivity.

## Notes

* The positivity hypothesis is needed only for the two `rpow_const` side conditions.  It supplies `Or.inl (ne_of_gt ...)` at every point of the closed slab.
* The square on `du` is handled by `hdu'.pow 2`; no derivative data is needed for this continuity lemma.
* This drop was produced via the GitHub connector only; no local `lake build` was run.
