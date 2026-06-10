## 1. A2/A3 core verdict

**VIABLE.** No analytic gap in the uniform-convergence argument.

From `PicardConvFacts`, the constants `K`, `C₀`, the ball bounds, nonnegativity, and geometric tail are all horizon-uniform in `s`. The bundle has

```lean
hgeom : ∀ n t, 0 < t → t ≤ T → ∀ x,
  |picardIter ... (n+1) t x - picardIter ... n t x| ≤ K^n * C₀
```

with `K`, `C₀` independent of `t`. fileciteturn136file0L77-L95

Then the same proof as `picardIter_logisticCoeff_tendsto_limit_of_facts` gives, uniformly for `s ∈ [a', τ]`,

\[
\left|
\widehat{L(u_n(s))}_k-\widehat{L(u(s))}_k
\right|
\le
2\,L_c\,\frac{K^n C_0}{1-K}.
\]

`Lc` is supplied by `logisticLifted_slice_dist_le`, whose hypotheses are exactly ball + nonnegativity for the two slices. fileciteturn136file0L1-L16

Lean caveat: the coefficient-distance lemma also needs spatial `ContinuousOn` of the two source slices. That is not a circular issue: for iterates use the given per-iterate slice/source continuity, and for the limit use `D.hcont` plus the logistic-composition lemma. Once that is included, A2 gives `TendstoUniformlyOn`; A3 is the standard uniform-limit-of-continuous-functions argument.

So the conditional glue theorem should take:

```lean
hcoeff_iter_cont :
  ∀ n k, ContinuousOn
    (fun s => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
    (Set.Icc a' τ)
```

or the stronger global/per-window version from the tower projection. Then A2/A3 closes.

---

## 2. A4/A5 glue at `0` and interior windows

**VIABLE.** No topological obstruction.

At `0`, use the proved

```lean
patchedSlice_timeContinuousAt_zero
```

and transfer to coefficients by the same `2`-Lipschitz coefficient estimate + logistic slice Lipschitz route already documented in `IntervalPicardLimitBddHcontP`. fileciteturn124file0L92-L117 fileciteturn132file0L20-L30

For `s₀ ∈ (0, τ]`, use the window `[s₀/2, τ]`. It is a relative neighborhood of `s₀` inside `Set.Icc 0 τ`. In Lean, prove something like:

```lean
have hWmem :
    Set.Icc (s₀ / 2) τ ∈ 𝓝[Set.Icc (0:ℝ) τ] s₀ := by
  rw [mem_nhdsWithin_iff]
  refine ⟨Set.Ioi (s₀ / 2), Ioi_mem_nhds ?_, ?_⟩
  · linarith
  · intro x hx
    rcases hx with ⟨hxhalf, hxIcc⟩
    exact ⟨le_of_lt hxhalf, hxIcc.2⟩
```

Then convert continuity within the window to continuity within `Icc 0 τ` either with the appropriate `ContinuousWithinAt` “eventual subset” lemma, or manually from `Tendsto` using `hWmem`. The manual proof is only a few filter lines: because points of `𝓝[Icc 0 τ] s₀` are eventually in `Icc (s₀/2) τ`, the window-continuity filter suffices.

So A5 is safe.

---

## 3. Stage C homogeneous sum

**VIABLE.** The direct exponential-difference estimate is the cleaner route.

You only have an `ℓ∞` coefficient bound

\[
|c_k(u(\tau))|\le 2M,
\]

so you need heat damping. The required majorant is

\[
2M\,\lambda_k e^{-(\tau/2)\lambda_k}.
\]

The repo already has the exact summability theorem:

```lean
unitIntervalCosineEigenvalue_mul_exp_summable
```

for positive time. fileciteturn71file0L41-L47

For the scalar bound, prove a small lemma:

```lean
lemma exp_neg_mul_sub_le
    {a b c λ : ℝ}
    (hc : 0 ≤ c) (ha : c ≤ a) (hb : c ≤ b) (hλ : 0 ≤ λ) :
    |Real.exp (-a * λ) - Real.exp (-b * λ)|
      ≤ λ * |a - b| * Real.exp (-c * λ)
```

The easiest proof is by cases `a ≤ b`. For `a ≤ b`,

\[
e^{-a\lambda}-e^{-b\lambda}
=
e^{-a\lambda}\left(1-e^{-(b-a)\lambda}\right)
\le
e^{-a\lambda}(b-a)\lambda,
\]

using \(1-e^{-x}\le x\) for \(x\ge0\). The other case is symmetric. Since `c ≤ min a b`, the exponential factor is bounded by `exp (-c*λ)`.

This avoids MVT machinery. If you prefer MVT, it also works, but the elementary `1 - exp(-x) ≤ x` proof is usually less brittle in Lean.

---

## 4. Stage C Duhamel part

**VIABLE with the common-interval split stated carefully.** Your cancellation is sound.

Let

```lean
x := s - τ
y := s₀ - τ
m := min x y
```

The Duhamel coefficient difference splits into:

1. common interval `[0, m]`;
2. one short tail `[m, x]` or `[m, y]`.

For the tail,

\[
\left|\int_m^x e^{-(x-r)\lambda_k} a(r,k)\,dr\right|
\le
|x-y|\,env(k),
\]

since the kernel is bounded by `1`.

For the common interval,

\[
\left|
e^{-(x-r)\lambda_k}-e^{-(y-r)\lambda_k}
\right|
\le
\lambda_k |x-y| e^{-(m-r)\lambda_k}.
\]

Then

\[
\lambda_k |x-y|\int_0^m e^{-(m-r)\lambda_k}\,dr
=
|x-y|\,(1-e^{-m\lambda_k})
\le
|x-y|.
\]

So the common interval is also bounded by

\[
|x-y|\,env(k).
\]

Hence common + tail is bounded by at most

\[
2|s-s₀|\,env(k)
\]

or `3|s-s₀| env(k)` if you keep a conservative case-split constant. Since `env(τ)` is summable from `DuhamelSourceBddOn.henv_summable`, this is exactly the ℓ¹ majorant needed. The `DuhamelSourceBddOn` structure supplies per-compact envelopes on `[a', τ]`. fileciteturn134file0L83-L93

Lean detail: do not hardcode the common interval as `[0, s₀-τ]`; use `[0, min (s-τ) (s₀-τ)]` and then case-split `s ≤ s₀` / `s₀ ≤ s`.

---

## 5. Final per-stage verdicts

| Piece | Verdict | Lean-level fix |
|---|---:|---|
| **A2/A3** | **VIABLE** | Add/assume per-iterate coefficient continuity on windows; include spatial source continuity inputs when proving the uniform coefficient convergence bound. |
| **A4/A5** | **VIABLE** | Use `patchedSlice_timeContinuousAt_zero`; for interiors, show `Icc (s₀/2) τ ∈ 𝓝[Icc 0 τ] s₀` and transport `ContinuousWithinAt` by eventual membership. |
| **C homogeneous** | **VIABLE** | Use direct exponential-difference bound and `unitIntervalCosineEigenvalue_mul_exp_summable (τ/2)`. |
| **C Duhamel** | **VIABLE** | Split into common interval `[0, min x y]` plus short tail; the `λ` from the exponential difference cancels against `∫ e^{-λ·}` to give `env(k)`. |
| **Wiring into `mildSlice_restart_bound`** | **VIABLE** | Build non-circular `hcontP` first, feed `duhamelSourceBddOn_of_iterates`, then call `picardLimitRestart_general_of_subtypeCont`; convert EqOn lift identities to subtype values by `simp [intervalDomainLift, y.2]`. |

Bottom line: the proposed circle break is sound. The only precision changes are: make A1 a hypothesis or source-package projection, and in Stage C prove the Duhamel common-interval estimate with the `min` split rather than treating everything as a short tail.