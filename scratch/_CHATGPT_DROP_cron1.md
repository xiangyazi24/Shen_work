# Q765 / cron1: factor bounds for `cutoffHeatTerm_iteratedFDeriv_bound`

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

The repo has the projection/Leibniz machinery you want, but it does **not** currently have a ready-made derivative majorant for the one-sided cutoff

```lean
smoothRightCutoff (c / 2) c
```

It has that majorant only for the two-sided compact cutoff:

```lean
restartSmoothCutoff offset s
```

Also, the requested independent global H-factor bound

```lean
∀ q, ‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤ bound_H j n
```

with a positive-time exponential tail such as `exp (-(c/2) λ_n)` is false for `heatTerm` alone, because `heatTerm` grows like `exp (-t λ_n)` as `t → -∞`. The proof of `cutoffHeatTerm_iteratedFDeriv_bound` should be **support-aware**: bound each Leibniz summand

```lean
‖D^i G q‖ * ‖D^(k-i) H q‖
```

using the fact that `D^i G q` or `G q` vanishes outside the relevant positive-time/transition region.

## Search results

### Found: `restartCutoffDerivMajorant_spec`

Location:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Concrete.lean
```

Relevant definitions/theorems:

```lean
theorem restartSmoothCutoff_iteratedFDeriv_bound_exists
    {offset s : ℝ} (hτ : 0 < s - offset)
    (k : ℕ) (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t‖ ≤ C
```

```lean
noncomputable def restartCutoffDerivMajorant
    (offset s : ℝ) (hτ : 0 < s - offset) (k : ℕ) : ℝ :=
  if hk : (k : ℕ∞) ≤ (2 : ℕ∞) then
    Classical.choose
      (restartSmoothCutoff_iteratedFDeriv_bound_exists
        (offset := offset) (s := s) hτ k hk)
  else 0
```

```lean
theorem restartCutoffDerivMajorant_spec
    {offset s : ℝ} (hτ : 0 < s - offset) {k : ℕ}
    (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (restartSmoothCutoff offset s) t‖ ≤
      restartCutoffDerivMajorant offset s hτ k
```

This is good reusable infrastructure, but it is for `restartSmoothCutoff`, not for `smoothRightCutoff`.

### Found: `smoothRightCutoff` basic lemmas, but no derivative majorant

Location:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

Found lemmas:

```lean
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))
```

```lean
theorem smoothRightCutoff_contDiff {c' c : ℝ} :
    ContDiff ℝ (2 : ℕ∞) (smoothRightCutoff c' c)
```

```lean
theorem smoothRightCutoff_eq_zero_of_le {c' c t : ℝ} (hc : c' < c)
    (ht : t ≤ c') :
    smoothRightCutoff c' c t = 0
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

Searches for `smoothRightCutoff.*deriv.*bound`, `smoothTransition bound iteratedFDeriv`, and related terms did not reveal a repo theorem of the form:

```lean
∀ t, ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤ C
```

or a named `smoothRightCutoffDerivMajorant`.

### Found: projection helpers

Location:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2CutoffBounds.lean
```

The exact projection helpers exist:

```lean
theorem norm_iteratedFDeriv_comp_fst_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.1) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.1‖
```

```lean
theorem norm_iteratedFDeriv_comp_snd_le
    {g : ℝ → ℝ} {N : WithTop ℕ∞} (hg : ContDiff ℝ N g)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) (q : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => g q.2) q‖ ≤
      ‖iteratedFDeriv ℝ k g q.2‖
```

Same file also has the resolver-side Leibniz wrappers:

```lean
cutoffValueTerm_leibniz_bound
cutoffGradTerm_leibniz_bound
```

For the current heat proof, the raw Mathlib lemma is already used:

```lean
norm_iteratedFDeriv_mul_le hG hH q hk'
```

but the projection helpers are still useful for reducing `G = φ ∘ fst` and the cosine part of `H` to one-dimensional bounds.

## Existing template for the H factor

A very relevant template is in:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

It defines separated joint terms:

```lean
def boundedWeightJointTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * cosineMode n q.2
```

and proves:

```lean
theorem boundedWeightJointTerm_iteratedFDeriv_le
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ} {n k : ℕ} {q : ℝ × ℝ}
    (hc : ContDiff ℝ (2 : ℕ∞) (c n)) (hk : (k : ℕ∞) ≤ (2 : ℕ∞))
    (hBt : ∀ i, i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) q.1‖ ≤ Bt i n) :
    ‖iteratedFDeriv ℝ k (boundedWeightJointTerm c n) q‖ ≤
      boundedWeightJointMajorant Bt k n
```

This theorem already does exactly the mixed `(t,x)` Leibniz/projection work:

* uses `norm_iteratedFDeriv_mul_le`,
* projects the time coefficient via `norm_iteratedFDeriv_comp_fst_le`,
* projects the cosine factor via `norm_iteratedFDeriv_comp_snd_le`,
* bounds the cosine derivatives by `cosineMode_iteratedFDeriv_bound`.

For the heat term, one could set:

```lean
cHeat : ℕ → ℝ → ℝ :=
  fun n t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n
```

Then:

```lean
heatTerm u₀ n = boundedWeightJointTerm cHeat n
```

The missing heat-specific piece would be a coefficient derivative bound for `cHeat n`, **under the condition `q.1 ≥ c/2`**:

```lean
‖iteratedFDeriv ℝ i (cHeat n) q.1‖ ≤
  unitIntervalCosineEigenvalue n ^ i * M₀ *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

This is true only in the positive-time region `q.1 ≥ c/2`; it is not true globally.

## Important correction: the H factor has no global q-independent bound

For `n > 0` and a nonzero coefficient, the value term itself satisfies:

```lean
heatTerm u₀ n (t, x)
  = Real.exp (-t * unitIntervalCosineEigenvalue n) * â_n * cosineMode n x
```

As `t → -∞`, `Real.exp (-t * λ_n)` grows without bound. Therefore no global bound of the form

```lean
∀ q, ‖iteratedFDeriv ℝ j (heatTerm u₀ n) q‖ ≤
  C_j * λ_n^j * M₀ * exp (-(c/2) * λ_n)
```

can hold for `H` alone.

The cutoff proof must use the support/constant-region behavior of `G`:

* if `q.1 ≤ c/2`, then `G q = 0`; for positive derivative orders, `D^i G q` should also vanish because the cutoff is locally constant zero to the left;
* if `q.1 ≥ c`, then `G q = 1`; for positive derivative orders, `D^i G q` should vanish because the cutoff is locally constant one to the right;
* if `c/2 ≤ q.1 ≤ c`, then `H` is bounded by the positive-time tail `exp (-(c/2) λ_n)`, and `D^i G` is bounded because this is a compact transition region.

So the target should be a product-term bound, not two completely independent global factor bounds.

## What is missing for G

There is no one-sided analogue of:

```lean
restartCutoffDerivMajorant_spec
```

for:

```lean
smoothRightCutoff (c / 2) c
```

A useful local addition would be something like:

```lean
noncomputable def smoothRightCutoffDerivMajorant
    (c' c : ℝ) (hc : c' < c) (k : ℕ) : ℝ := ...
```

with:

```lean
theorem smoothRightCutoffDerivMajorant_nonneg ... :
  0 ≤ smoothRightCutoffDerivMajorant c' c hc k
```

```lean
theorem smoothRightCutoffDerivMajorant_spec
    (hc : c' < c) (hk : (k : ℕ∞) ≤ (2 : ℕ∞)) (t : ℝ) :
  ‖iteratedFDeriv ℝ k (smoothRightCutoff c' c) t‖ ≤
    smoothRightCutoffDerivMajorant c' c hc k
```

For `k = 0`, use the range of `Real.smoothTransition` (`nonneg` and `le_one`) to get bound `1`. The repo uses these Mathlib lemmas in `IntervalTimeSoftClamp.lean` for the related soft-clamp profile:

```lean
Real.smoothTransition.nonneg
Real.smoothTransition.le_one
```

For `k > 0`, prove compact support of the derivative using local constancy of `smoothRightCutoff` outside `[c', c]`, then copy the pattern from:

```lean
restartSmoothCutoff_iteratedFDeriv_bound_exists
```

namely:

```lean
have hcont : Continuous
    (fun t => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) :=
  smoothRightCutoff_contDiff.continuous_iteratedFDeriv ...

have hcomp : HasCompactSupport
    (fun t => iteratedFDeriv ℝ k (smoothRightCutoff c' c) t) := ...

rcases hcont.bounded_above_of_compact_support hcomp with ⟨C, hC⟩
```

The support proof for `k > 0` should use eventual equality to the constants `0` and `1` on the left/right, then `Filter.EventuallyEq.iteratedFDeriv` to show the derivative is zero off the transition interval.

## What to use for H

Use the resolver physical-term template rather than proving a custom mixed-partial bound from scratch.

Suggested helper shape:

```lean
def heatCoeffTime (u₀ : intervalDomainPoint → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun t => Real.exp (-t * unitIntervalCosineEigenvalue n) *
    cosineCoeffs (intervalDomainLift u₀) n
```

Then prove:

```lean
heatTerm u₀ n =
  ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm
    (fun n t => heatCoeffTime u₀ n t) n
```

and reuse:

```lean
boundedWeightJointTerm_iteratedFDeriv_le
```

with a region-local `hBt` when `q.1 ≥ c/2`.

For spatial cosine bounds, the repo already has:

```lean
cosineMode_iteratedFDeriv_bound
```

in `IntervalResolverSpectralJointC2Concrete.lean`:

```lean
theorem cosineMode_iteratedFDeriv_bound
    (n m : ℕ) (y : ℝ) (hm : m ≤ 2) :
    ‖iteratedFDeriv ℝ m (cosineMode n) y‖ ≤ valueCosWeight m n
```

There is also a more general older cosine bound in:

```text
ShenWork/Paper2/IntervalCD6CosineModeBounds.lean
```

```lean
theorem unitIntervalCosineMode_iteratedFDeriv_bound
    (k n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (unitIntervalCosineMode n) x‖ ≤
      |(n : ℝ) * Real.pi| ^ k
```

## Recommended proof plan for the current sorry

Avoid trying to prove standalone global `H` bounds. After `norm_iteratedFDeriv_mul_le`, prove each summand by cases on `q.1`:

```lean
by_cases hleft : q.1 ≤ c / 2
```

* In the left region, show the Leibniz summand is zero:
  * for `i = 0`, `G q = 0` by `smoothRightCutoff_eq_zero_of_le`;
  * for `i > 0`, use local constancy of `G` near `q` and `EventuallyEq.iteratedFDeriv` to show `iteratedFDeriv i G q = 0`.

Then in the complement `c/2 < q.1`, split:

```lean
by_cases hright : c ≤ q.1
```

* In the right region, for `i = 0`, use `‖G q‖ = 1` and the positive-time `H` bound with `q.1 ≥ c`; for `i > 0`, show `D^i G q = 0` by local constancy one.
* In the transition region `c/2 < q.1 < c`, use:
  * `smoothRightCutoffDerivMajorant_spec` once added for `G`, or a local compact-transition bound;
  * the positive-time `H` bound with `q.1 ≥ c/2`.

This matches the current mathematical comment but fixes the formal issue: `H` is not globally bounded; only the Leibniz products are globally bounded because the cutoff kills or localizes the bad negative-time region.

## Bottom line

* `restartCutoffDerivMajorant_spec` exists and is useful as a pattern, but only for `restartSmoothCutoff`.
* No direct derivative majorant for `smoothRightCutoff` currently exists.
* `norm_iteratedFDeriv_comp_fst_le` and `norm_iteratedFDeriv_comp_snd_le` exist exactly where expected.
* `boundedWeightJointTerm_iteratedFDeriv_le` is the best existing pattern for the H mixed `(t,x)` derivative bound.
* The current proof should be adjusted from independent global `G` and `H` bounds to support-aware Leibniz summand bounds.
