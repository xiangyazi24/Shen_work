# Q739 / cron1: smooth cutoff search for `heatSemigroup_jointContDiff_two`

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

Yes, the repo already has the cutoff machinery needed for the pattern, but not exactly under the name or exact properties in the prompt.

* I found **no repo-local hits** for `SmoothBumpFunction` or `smoothBump`.
* The one-sided cutoff matching “zero to the left, one to the right” is:

```lean
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff
```

It is defined in `ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean` as:

```lean
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))
```

The available lemmas are:

```lean
smoothRightCutoff_contDiff :
  ContDiff ℝ (2 : ℕ∞) (smoothRightCutoff c' c)

smoothRightCutoff_eq_zero_of_le
  (hc : c' < c) (ht : t ≤ c') :
  smoothRightCutoff c' c t = 0

smoothRightCutoff_eq_one_of_ge
  (hc : c' < c) (ht : c ≤ t) :
  smoothRightCutoff c' c t = 1

smoothRightCutoff_eventually_eq_one
  (hc : c' < c) (hs : c < s) :
  smoothRightCutoff c' c =ᶠ[𝓝 s] fun _ : ℝ => 1
```

So, with `c' = c / 2`, `hc : c / 2 < c` follows from `0 < c`, and the cutoff is zero on `(-∞, c/2]` and one on `[c, ∞)`. This matches “support in `[c/2, ∞)`” in the weak support sense: the function is zero to the left of `c/2`.

However, `smoothRightCutoff (c/2) c` is **not compactly supported**. A function equal to `1` on all `[c, ∞)` cannot have compact support. I did not find a `HasCompactSupport` lemma for `smoothRightCutoff`.

## Compact cutoff already used by the resolver files

The compactly supported cutoff is the two-sided one in `ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean`:

```lean
def restartSmoothCutoff (offset s : ℝ) : ℝ → ℝ :=
  fun t =>
    smoothRightCutoff (restartCutoffLeftOuter offset s)
        (restartCutoffLeft offset s) t *
      smoothRightCutoff (-(restartCutoffRightOuter offset s))
        (-(restartCutoffRight offset s)) (-t)
```

It is supported in the compact slab

```lean
Icc (restartCutoffLeftOuter offset s) (restartCutoffRightOuter offset s)
```

and is equal to `1` near `s`, not on all `[c, ∞)`.

Useful lemmas found there:

```lean
restartSmoothCutoff_contDiff :
  ContDiff ℝ (2 : ℕ∞) (restartSmoothCutoff offset s)

restartSmoothCutoff_eventually_eq_one
  (hτ : 0 < s - offset) :
  restartSmoothCutoff offset s =ᶠ[𝓝 s] fun _ : ℝ => 1

restartSmoothCutoff_eq_zero_of_le_left
  (hτ : 0 < s - offset)
  (ht : t ≤ restartCutoffLeftOuter offset s) :
  restartSmoothCutoff offset s t = 0

restartSmoothCutoff_eq_zero_of_right_le
  (hτ : 0 < s - offset)
  (ht : restartCutoffRightOuter offset s ≤ t) :
  restartSmoothCutoff offset s t = 0

restartSmoothCutoff_eq_one_of_mem_core
  (hτ : 0 < s - offset)
  (ht_left : restartCutoffLeft offset s ≤ t)
  (ht_right : t ≤ restartCutoffRight offset s) :
  restartSmoothCutoff offset s t = 1

restartSmoothCutoff_hasCompactSupport
  (hτ : 0 < s - offset) :
  HasCompactSupport (restartSmoothCutoff offset s)

restartCutoffDerivMajorant_spec
  (hτ : 0 < s - offset)
  (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) (t : ℝ) :
  ‖iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t‖ ≤
    restartCutoffDerivMajorant offset s hτ k
```

This is the stronger reusable cutoff if the proof wants compact support and automatic bounded derivatives.

## Generic cutoff theorem in `IntervalResolverSpectralJointC2Cutoff.lean`

The generic theorem is:

```lean
theorem resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (φ : ℝ → ℝ) (gradTerm : ℕ → ℝ × ℝ → ℝ)
    (vValue vGrad : ℕ → ℕ → ℝ)
    ... :
    ResolverSpectralJointC2At a₀ a offset s x
```

Its important hypotheses are:

```lean
hφ_one : φ =ᶠ[𝓝 s] fun _ : ℝ => 1

hValueTerm :
  ∀ n : ℕ,
    ContDiff ℝ (2 : ℕ∞) (cutoffValueTerm φ a₀ a offset n)

hValueSumm :
  ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vValue k)

hValueBound :
  ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
    ‖iteratedFDeriv ℝ k (cutoffValueTerm φ a₀ a offset n) q‖ ≤
      vValue k n

hGradTerm :
  ∀ n : ℕ, ContDiff ℝ (2 : ℕ∞) (cutoffGradTerm φ gradTerm n)

hGradSumm :
  ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vGrad k)

hGradBound :
  ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
    ‖iteratedFDeriv ℝ k (cutoffGradTerm φ gradTerm n) q‖ ≤
      vGrad k n

hGradEq :
  resolverSpectralGradSeries a₀ a offset =ᶠ[𝓝 (s, x)]
    fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q
```

The proof then does exactly the advertised pattern:

1. Pulls `hφ_one` back to `(s, x)` via `continuous_fst.continuousAt`.
2. Applies `contDiff_tsum` to the cutoff value series.
3. Applies `contDiff_tsum` to the cutoff gradient series.
4. Uses eventual equality of `φ q.1 = 1` to identify the cutoff series with the original local series near `(s, x)`.
5. Returns `ContDiffAt` via `congr_of_eventuallyEq`.

## Leibniz helper lemmas already present

`ShenWork/PDE/IntervalResolverSpectralJointC2CutoffBounds.lean` packages the `norm_iteratedFDeriv_mul_le` step:

```lean
cutoffValueTerm_leibniz_bound
cutoffGradTerm_leibniz_bound
```

These are resolver-specific, but the pattern is reusable. The same file also has useful projection bounds:

```lean
norm_iteratedFDeriv_comp_fst_le
norm_iteratedFDeriv_comp_snd_le
```

## Concrete instantiation used by the resolver proof

The final concrete theorem is in `IntervalResolverSpectralJointC2Concrete.lean`:

```lean
theorem resolverSpectralJointC2At_of_restartSmoothCutoff
    {a₀ : ℕ → ℝ} {M : ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (hτ : 0 < s - offset) (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC2Coeff a) :
    ResolverSpectralJointC2At a₀ a offset s x :=
  resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    (φ := restartSmoothCutoff offset s)
    (gradTerm := resolverSpectralConcreteGradTerm a₀ a offset)
    (vValue := concreteRestartValueMajorant a₀ src offset s hτ)
    (vGrad := concreteRestartGradMajorant a₀ src offset s hτ)
    ...
```

The concrete proof supplies:

```lean
restartSmoothCutoff_eventually_eq_one hτ
cutoffValueTerm_restartSmoothCutoff_contDiff src
concreteRestartValueMajorant_summable hτ ha₀ src
cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src
cutoffGradTerm_restartSmoothCutoff_contDiff src
concreteRestartGradMajorant_summable hτ ha₀ src
cutoffGradTerm_restartSmoothCutoff_iteratedFDeriv_bound hτ src
resolverSpectralGradSeries_eventuallyEq_concreteGradTerm hτ ha₀ src
```

So the actual hypotheses for the concrete cutoff instantiation are:

```lean
hτ   : 0 < s - offset
ha₀  : ∀ n, |a₀ n| ≤ M
src  : DuhamelSourceTimeC2Coeff a
```

The cutoff-specific hypothesis is just `hτ : 0 < s - offset`.

## Application note for `heatSemigroup_jointContDiff_two`

The current theorem in `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` claims global

```lean
ContDiff ℝ 2 (fun q : ℝ × ℝ => ∑' k, exp(-q.1 * λ_k) * â_k * cos(kπq.2))
```

from `hc : 0 < c`, and the sorry comment itself says the global uniform bound fails outside the slab `t ≥ c`.

The cutoff pattern proves a **local** statement, i.e. `ContDiffAt` near `(s₀, x₀)` with `s₀ > c`, not the global uncutoff `ContDiff` statement as currently written.

Best reuse options:

1. For a one-sided positive-time cutoff, use

```lean
φ := smoothRightCutoff (c / 2) c
```

This gives `φ = 0` on `t ≤ c/2` and `φ = 1` on `t ≥ c`; it is not compactly supported, but `φ(t) * exp(-t λ_n)` is globally bounded by the positive-time exponential tail plus a compact transition interval.

2. For the closest existing compact-support pattern, use a local two-sided cutoff around the target time:

```lean
φ := restartSmoothCutoff c s₀
```

with hypothesis

```lean
hτ : 0 < s₀ - c
```

This gives compact support, bounded cutoff derivatives via `restartCutoffDerivMajorant_spec`, and `φ =ᶠ[𝓝 s₀] 1` via `restartSmoothCutoff_eventually_eq_one hτ`. Then prove the cutoff heat series is `ContDiff ℝ 2` by `contDiff_tsum`, and transfer to the original heat series by eventual equality near `(s₀, x₀)`.

If the goal remains the global theorem `heatSemigroup_jointContDiff_two` as currently stated, the cutoff argument does not close that exact statement. It should instead close or replace the downstream local theorem:

```lean
heatSemigroup_jointContDiffAt_two
```

or the global theorem should be refactored into a slab/local statement.
