# Q678 / cron1: Mathlib lemma for polynomial × exponential decay summability

## Verdict

The Mathlib lemma you want is:

```lean
Real.summable_pow_mul_exp_neg_nat_mul
```

Exact signature in Mathlib:

```lean
lemma summable_pow_mul_exp_neg_nat_mul (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun n : ℕ ↦ n ^ k * exp (-r * n)
```

Location:

- `Mathlib/Analysis/SpecialFunctions/Exp.lean:178-182`

There is **not** a direct `exp (-α * n^2)` lemma in the form I found.  The standard route is exactly what `Shen_work` already does: reduce the Gaussian tail to a linear exponential tail using

```lean
(n : ℝ) ≤ (n : ℝ)^2
```

for `n : ℕ`, then apply `Real.summable_pow_mul_exp_neg_nat_mul`.

## Existing `Shen_work` pattern

`ShenWork/Paper2/IntervalCD6Tail.lean` has a private helper doing precisely this for arbitrary natural eigenvalue powers:

```lean
private theorem eigenvalue_pow_mul_exp_summable
    (m : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n ^ m *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < τ * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi ^ (2 * m) * ((n : ℝ) ^ (2 * m) *
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ)))) := by
    simpa [mul_assoc] using
      (Real.summable_pow_mul_exp_neg_nat_mul (2 * m) hc).mul_left
        (Real.pi ^ (2 * m))
  ...
```

Location:

- `ShenWork/Paper2/IntervalCD6Tail.lean:17-28`

The comparison part later proves

```lean
Real.exp (-τ * unitIntervalCosineEigenvalue n)
  ≤ Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ))
```

from

```lean
(n : ℝ) ≤ (n : ℝ)^2
```

and `unitIntervalCosineEigenvalue n = (n : ℝ)^2 * Real.pi^2`.

Location:

- `ShenWork/Paper2/IntervalCD6Tail.lean:34-65`

So the repo-local pattern is already a template for your proof.

## Other related Mathlib lemma

Immediately above the polynomial-times-exponential lemma, Mathlib also has:

```lean
lemma summable_exp_nat_mul_iff {a : ℝ} :
    Summable (fun n : ℕ ↦ exp (n * a)) ↔ a < 0
```

and

```lean
lemma summable_exp_nat_mul_of_ge {c : ℝ} (hc : c < 0) {f : ℕ → ℝ} (hf : ∀ i, i ≤ f i) :
    Summable fun i : ℕ ↦ exp (c * f i)
```

Locations:

- `Mathlib/Analysis/SpecialFunctions/Exp.lean:163-176`

These help for pure exponential tails.  For polynomial times exponential, `Real.summable_pow_mul_exp_neg_nat_mul` is the one to use.

## Proof route for your `MemHSigma` lemma

Target:

```lean
MemHSigma σ a :=
  Summable (fun k => (1 + ((k : ℝ) * Real.pi)^2)^σ * (a k)^2)
```

Assume:

```lean
hσ : 0 ≤ σ
hα : 0 < α
hC : 0 ≤ C
ha : ∀ k, |a k| ≤ C * Real.exp (-α * (k : ℝ)^2)
```

Then:

```lean
(a k)^2 ≤ C^2 * Real.exp (-(2 * α) * (k : ℝ)^2)
```

because squaring `exp (-α k²)` gives `exp (-2α k²)`.

For the polynomial weight, choose a natural `m` with `σ ≤ m`, e.g. via Archimedean ceiling.  Since the base is at least `1`,

```lean
(1 + ((k : ℝ) * Real.pi)^2)^σ ≤
  (1 + ((k : ℝ) * Real.pi)^2)^m
```

Then bound the integer-power weight by a constant multiple of a natural polynomial in `k`, for example something like

```lean
(1 + ((k : ℝ) * Real.pi)^2)^m ≤ A * ((k : ℝ) + 1)^(2*m)
```

or reindex/tail-split and use `k^(2*m)` for `k ≥ 1`.

Finally compare

```lean
((k : ℝ) + 1)^(2*m) * Real.exp (-(2*α) * (k : ℝ)^2)
```

or its tail reindex to a constant multiple of

```lean
(k : ℝ)^N * Real.exp (-r * (k : ℝ))
```

with `r > 0`, and apply:

```lean
Real.summable_pow_mul_exp_neg_nat_mul N hr
```

## Minimal Lean skeleton

For the Gaussian-to-linear-exponential part, copy this style from `IntervalCD6Tail`:

```lean
have hc : 0 < (2 * α) := by positivity
have hbase : Summable (fun n : ℕ =>
    (n : ℝ)^N * Real.exp (-(2 * α) * (n : ℝ))) := by
  simpa [mul_assoc] using
    Real.summable_pow_mul_exp_neg_nat_mul N hc

refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hbase
· positivity
· have hn_sq_ge : (n : ℝ) ≤ (n : ℝ)^2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst n; norm_num
    · exact le_self_pow₀ (by exact_mod_cast hn) (by norm_num)
  have hexp_le :
      Real.exp (-(2 * α) * (n : ℝ)^2) ≤
        Real.exp (-(2 * α) * (n : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * α) hn_sq_ge]
  -- finish by multiplying by the polynomial bound with nonnegative factors
```

The exact `nlinarith` line may need sign care.  The repo pattern avoids ambiguity by writing the exponent as `-(τ * Real.pi^2) * (n : ℝ)` and proving the exponential comparison with `Real.exp_le_exp.mpr`; see `IntervalCD6Tail.lean:43-48`.

## Bottom line

Use:

```lean
Real.summable_pow_mul_exp_neg_nat_mul
```

There is no need to invent a p-series proof.  The cleanest `Shen_work` implementation is to factor your argument into two lemmas:

```lean
theorem summable_poly_mul_exp_neg_sq
    (N : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => (n : ℝ)^N * Real.exp (-α * (n : ℝ)^2))
```

proved by comparison to `Real.summable_pow_mul_exp_neg_nat_mul N hα`, then:

```lean
theorem memHSigma_of_exp_sq_bound
    {σ α C : ℝ} (hσ : 0 ≤ σ) (hα : 0 < α) (hC : 0 ≤ C)
    {a : ℕ → ℝ}
    (ha : ∀ k, |a k| ≤ C * Real.exp (-α * (k : ℝ)^2)) :
    MemHSigma σ a
```

using a natural `N` large enough to dominate the real-power Sobolev weight.
