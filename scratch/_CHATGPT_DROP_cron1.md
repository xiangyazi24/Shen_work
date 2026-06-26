# Q769 / cron1: support-aware cutoff left endpoint check

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

Yes, for the **value** of the one-sided cutoff:

```lean
φ := smoothRightCutoff (c / 2) c
```

repo theorem

```lean
smoothRightCutoff_eq_zero_of_le
```

does give:

```lean
φ t = 0
```

for every

```lean
t ≤ c / 2
```

provided

```lean
hc : 0 < c
```

because `c / 2 < c` follows by `linarith`.

The direct instantiation is:

```lean
have hc_half : c / 2 < c := by linarith [hc]
have hφ_zero : smoothRightCutoff (c / 2) c t = 0 :=
  smoothRightCutoff_eq_zero_of_le (c' := c / 2) (c := c) hc_half ht
```

So the cutoff is **exactly zero on the closed half-line** `(-∞, c/2]`, not merely approaching zero.

## Where this is defined

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

Definition/comment:

```lean
/-- Smooth right cutoff equal to `0` on `(-∞, c']` and `1` on `[c, ∞)`. -/
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))
```

Relevant lemmas:

```lean
theorem smoothRightCutoff_eq_zero_of_le {c' c t : ℝ} (hc : c' < c)
    (ht : t ≤ c') :
    smoothRightCutoff c' c t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.2 (sub_pos.2 hc).le) (sub_nonpos.2 ht)
```

```lean
theorem smoothRightCutoff_eq_one_of_ge {c' c t : ℝ} (hc : c' < c)
    (ht : c ≤ t) :
    smoothRightCutoff c' c t = 1
```

```lean
theorem smoothRightCutoff_eventually_eq_one {c' c s : ℝ}
    (hc : c' < c) (hs : c < s) :
    smoothRightCutoff c' c =ᶠ[𝓝 s] fun _ : ℝ => 1
```

## Important nuance: values vs. derivatives

The statement

```text
φ(t) = 0 for t ≤ c/2
```

is directly proved by `smoothRightCutoff_eq_zero_of_le`.

The stronger statement

```text
all derivatives of φ are 0 for t ≤ c/2
```

is **not directly provided** by that theorem.

What is immediately easy in Lean is the strict-left version:

```lean
if ht : t < c / 2 then
  smoothRightCutoff (c / 2) c =ᶠ[𝓝 t] fun _ : ℝ => 0
```

because `{u | u < c/2}` is an open neighborhood of `t`, and on that neighborhood the `≤` lemma applies. Then:

```lean
Filter.EventuallyEq.iteratedFDeriv
```

can show:

```lean
iteratedFDeriv ℝ k (smoothRightCutoff (c / 2) c) t = 0
```

for all `k` when `t < c / 2`.

At the endpoint

```lean
t = c / 2
```

there is no full neighborhood of `t` on which the cutoff is identically zero; the transition begins immediately to the right. Mathematically, because `Real.smoothTransition` is smooth and flat on the left side, its derivatives at the endpoint should be zero, but the repo does **not** appear to have a ready-made lemma that says:

```lean
iteratedFDeriv ℝ k (smoothRightCutoff (c / 2) c) (c / 2) = 0
```

Searches for `smoothRightCutoff iteratedFDeriv zero_of_le` only found the cutoff files, not a derivative-vanishing theorem.

## Consequence for the support-aware proof

Do not split the proof as:

```lean
q.1 ≤ c / 2  -- all derivatives of G vanish
```

unless you first add/prove the endpoint derivative-flatness lemma.

A safer split is:

```lean
by_cases hleft : q.1 < c / 2
```

### Case 1: `q.1 < c / 2`

Here, `G = smoothRightCutoff (c/2) c ∘ fst` is locally equal to `0`, so every iterated derivative of `G` is zero. This is exactly the easy `EventuallyEq.iteratedFDeriv` route.

### Case 2: `¬ q.1 < c / 2`, hence `c / 2 ≤ q.1`

Here the heat factor has the desired exponential tail:

```lean
Real.exp (-q.1 * λ_n) ≤ Real.exp (-(c / 2) * λ_n)
```

because `0 ≤ λ_n` and `c/2 ≤ q.1`.

In this case, do **not** need derivative-zero at the endpoint. Use boundedness of the cutoff derivatives instead. For that, the repo currently has a bound-majorant pattern for `restartSmoothCutoff`, but not for `smoothRightCutoff`. So either:

1. add a `smoothRightCutoffDerivMajorant_spec`; or
2. prove a local `∃ C, ∀ t, ‖iteratedFDeriv ℝ i (smoothRightCutoff (c/2) c) t‖ ≤ C` directly for `i ≤ 2`.

This avoids the endpoint issue completely: the endpoint `q.1 = c/2` belongs to the positive-time-tail case and is handled by bounded cutoff derivatives plus the equality

```lean
exp (-(c / 2) * λ_n)
```

for the heat factor.

## Recommended product-bound split

For the Leibniz summands after

```lean
norm_iteratedFDeriv_mul_le hG hH q hk'
```

use:

```lean
by_cases hleft : q.1 < c / 2
```

* If `hleft`, prove the whole product derivative is zero by local equality of the product `G * H` to `0`. This avoids even needing separate derivative facts for `G`.
* If `¬ hleft`, have:

  ```lean
  have hq_ge : c / 2 ≤ q.1 := le_of_not_gt hleft
  ```

  and use the exponential bound for `H`, together with a cutoff-derivative bound for `G`.

This is cleaner than trying to prove `all derivatives of G are zero for t ≤ c/2`.

## If you still want derivative-zero on the left

The strict-left lemma should be easy to add:

```lean
theorem smoothRightCutoff_iteratedFDeriv_eq_zero_of_lt
    {c' c t : ℝ} (hc : c' < c) (ht : t < c') (k : ℕ) :
    iteratedFDeriv ℝ k (smoothRightCutoff c' c) t = 0 := by
  have hzero : smoothRightCutoff c' c =ᶠ[𝓝 t] fun _ : ℝ => 0 := by
    filter_upwards [(isOpen_lt continuous_id continuous_const).mem_nhds ht] with u hu
    exact smoothRightCutoff_eq_zero_of_le hc (le_of_lt hu)
  have hderiv := Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hzero k
  simpa using hderiv.self_of_nhds
```

For the composed version `G q = smoothRightCutoff (c/2) c q.1`, use the open neighborhood

```lean
{p : ℝ × ℝ | p.1 < c / 2}
```

and the same eventual-equality pattern. The repo already uses this exact style for the compact restart cutoff in:

```lean
cutoffValueTerm_restartSmoothCutoff_iteratedFDeriv_eq_zero_of_left
```

in `IntervalResolverSpectralJointC2Concrete.lean`.

## Bottom line

* `smoothRightCutoff_eq_zero_of_le` **does** give exact value zero for `φ(t)` at all `t ≤ c/2`.
* It does **not**, by itself, give derivative-zero at the endpoint `t = c/2`.
* For Lean, prefer splitting on `q.1 < c/2` versus `c/2 ≤ q.1`; use local-zero on the strict-left case and exponential decay on the complement.
* This avoids needing a delicate endpoint-flatness lemma for `smoothRightCutoff`.
