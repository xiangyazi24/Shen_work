# Q825 (cron2) — from pointwise `ContDiffAt` to `ContinuousOn` for 2A-core

Static Mathlib/repo inspection only; I did not run a local Lean build.

## Short answer

Mathlib has the direct global/on-set lemmas:

```lean
theorem ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s

theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f

theorem ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s

theorem ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x
```

I did **not** find a separately named theorem like `ContDiffAt_forall_to_ContinuousOn`.  But you do not need one: `ContinuousOn f S` is definitionally the pointwise `ContinuousWithinAt` statement, and `ContinuousAt.continuousWithinAt` bridges from the pointwise `ContDiffAt` result.

For a closed rectangle/set `S`, if you have pointwise global-at regularity,

```lean
hΦ : ∀ q ∈ S, ContDiffAt ℝ 2 Φ q
```

then the bridge is just:

```lean
have hΦ_cont : ContinuousOn Φ S := by
  intro q hq
  exact (hΦ q hq).continuousAt.continuousWithinAt
```

That is the bridge you want for 2A-core.

## If you can package the proof as `ContDiffOn`

If instead you can prove:

```lean
hΦ : ContDiffOn ℝ 1 Φ S
```

or even

```lean
hΦ : ContDiffOn ℝ 0 Φ S
```

then use Mathlib’s direct theorem:

```lean
exact hΦ.continuousOn
```

For a global `ContDiff` proof:

```lean
hΦ : ContDiff ℝ 1 Φ
```

you can use either:

```lean
exact hΦ.contDiffOn.continuousOn
```

or:

```lean
exact hΦ.continuous.continuousOn
```

The first route is often better in this codebase because the calculus facts are already phrased in the `ContDiff*` API.

## Recommended shape for sub-sorry 2A-core

Let

```lean
R : Set (ℝ × ℝ) := Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1
Φ : ℝ × ℝ → ℝ := fun q => deriv (chemFluxFun β (U q.1) (V q.1)) q.2
```

or whatever the exact unfolded smooth-flux-derivative expression is.

If the local chain-rule work gives:

```lean
hΦ_at : ∀ q ∈ R, ContDiffAt ℝ 0 Φ q
-- or `ContDiffAt ℝ 1 Φ q`, or `ContDiffAt ℝ 2 Φ q`
```

then close the `ContinuousOn` goal by:

```lean
exact fun q hq => (hΦ_at q hq).continuousAt.continuousWithinAt
```

If the local chain-rule work gives `ContDiffAt ℝ 1` or `ContDiffAt ℝ 2`, no `of_le` is needed because `ContDiffAt.continuousAt` works for any order `n`.

If your proof naturally produces a within-at statement on the rectangle,

```lean
hΦ_within : ∀ q ∈ R, ContDiffWithinAt ℝ 0 Φ R q
```

then use the even more direct within-at route:

```lean
exact fun q hq => (hΦ_within q hq).continuousWithinAt
```

## Why this fits `[c,T] × [0,1]`

The fact that the goal is `ContinuousOn` on the closed rectangle is not a problem.  You do **not** need the rectangle to be open.  A `ContDiffAt` proof at every point of the rectangle is stronger than what `ContinuousOn` asks for, including at boundary points.  At a boundary point, `ContinuousAt Φ q` immediately implies `ContinuousWithinAt Φ R q`.

So the strategy is:

```text
joint C² U and V
  → pointwise ContDiffAt / local C¹ of the rational flux expression Φ
  → ContDiffAt.continuousAt at each q
  → ContinuousAt.continuousWithinAt
  → ContinuousOn Φ R
```

For this sub-sorry, the last bridge should not be the hard part; it is a three-line proof.

## Relevant Mathlib locations checked

Mathlib source checked:

```text
leanprover-community/mathlib4 @ 11b908e5cdd941b2d54b1b2ab55d069f5d8281d4
Mathlib/Analysis/Calculus/ContDiff/Defs.lean
Mathlib/Topology/ContinuousOn.lean
```

Useful facts found:

```lean
-- ContDiffWithinAt gives ContinuousWithinAt
theorem ContDiffWithinAt.continuousWithinAt
    (h : ContDiffWithinAt 𝕜 n f s x) : ContinuousWithinAt f s x

-- ContDiffOn gives ContinuousOn
theorem ContDiffOn.continuousOn
    (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s

-- ContDiffAt gives ContinuousAt
theorem ContDiffAt.continuousAt
    (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x

-- Global ContDiff can be restricted to any set
theorem ContDiff.contDiffOn
    (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s

-- Global ContDiff gives Continuous
theorem ContDiff.continuous
    (h : ContDiff 𝕜 n f) : Continuous f
```

And `ContinuousOn` is used as the pointwise-within statement:

```lean
theorem ContinuousOn.continuousWithinAt (hf : ContinuousOn f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  hf x hx
```

So the pointwise proof by `intro q hq` is idiomatic.
