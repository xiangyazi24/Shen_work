# Q799 / cron1: heatTerm derivative majorant constant

Repo inspected: xiangyazi24/Shen_work
Branch written: chatgpt-scratch

## Question

For the last sorry in `heatTerm_iteratedFDeriv_global_bound`, the desired bound is currently shaped like

```lean
norm (iteratedFDeriv Real j (heatTerm u0 n) q) <=
  (1 + unitIntervalCosineEigenvalue n) ^ j * M0 *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n)
```

under `j <= 2` and `c / 2 <= q.1`.

But by Leibniz, the separated heat term produces a binomial sum, so the missing constant should be `2^j` (or coarsely `4`, since `j <= 2`). Should the majorant be changed?

## Verdict

Yes. The raw heat-term bound as stated without a binomial constant is too tight for the planned Leibniz proof. The safe repair is to include either

```lean
(2 : Real) ^ j
```

or the uniform coarse constant

```lean
4
```

in the heat-term bound and in the downstream `cutoffHeatMajorant`.

The cleanest precise version is:

```lean
norm (iteratedFDeriv Real j (heatTerm u0 n) q) <=
  (2 : Real) ^ j *
    ((1 + unitIntervalCosineEigenvalue n) ^ j * M0 *
      Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))
```

For the cutoff proof, the heat-term derivative order is `k - i`, so the corresponding cutoff majorant should be:

```lean
( sum i in range (k + 1),
    choose k i * Phi i * (2 : Real) ^ (k - i) ) *
  ((1 + lambda n) ^ k * M0 * exp (-(c / 2) * lambda n))
```

where `Phi i` is the bound for the `i`-th derivative of `smoothRightCutoff (c/2) c`.

A simpler, slightly coarser option is:

```lean
4 *
  ( sum i in range (k + 1), choose k i * Phi i ) *
  ((1 + lambda n) ^ k * M0 * exp (-(c / 2) * lambda n))
```

This is probably easiest to thread through the existing proof. Summability is unchanged: it is just `mul_left` by a finite constant.

## Why the factor is needed

Write

```text
lambda_n = unitIntervalCosineEigenvalue n
A_n(t) = exp(-t * lambda_n) * ahat_n
B_n(x) = cosineMode n x
heatTerm u0 n (t,x) = A_n(t) * B_n(x)
```

The joint Leibniz estimate gives

```text
||D^j(A_n o fst * B_n o snd)||
  <= sum_{i <= j} choose(j,i) * ||D^i(A_n o fst)|| * ||D^(j-i)(B_n o snd)||.
```

For `t >= c/2`, the time factor is bounded by

```text
||D^i A_n(t)|| <= lambda_n^i * M0 * exp(-(c/2) * lambda_n)
```

and the spatial cosine factor is bounded by `valueCosWeight (j-i) n`.

For orders up to 2,

```text
valueCosWeight 0 n = 1
valueCosWeight 1 n = |n*pi|
valueCosWeight 2 n = lambda_n
```

and each is bounded by `(1 + lambda_n)^(j-i)` at the corresponding order. Also

```text
lambda_n^i <= (1 + lambda_n)^i.
```

Thus each binomial summand is bounded by

```text
choose(j,i) * (1 + lambda_n)^j * M0 * exp(...)
```

and summing gives

```text
sum_i choose(j,i) = 2^j.
```

So the natural bound is `2^j * (1 + lambda_n)^j * M0 * exp(...)`, not just `(1 + lambda_n)^j * M0 * exp(...)`.

## Current file shape

In `IntervalHeatSemigroupHighRegularity.lean`, the comment already recognizes the binomial factor:

```text
sum C(j,i) * ... = 2^j * (1 + lambda_n)^j
```

but the theorem statement still returns the no-factor RHS. That mismatch is the blocker.

Also, the current `cutoffHeatMajorant` is shaped like

```lean
( sum i in range (k + 1), choose k i * Phi i ) *
  ((1 + lambda n)^k * M0 * exp(...))
```

so if the heat-term lemma is corrected to include `2^(k-i)` or `4`, the majorant must be enlarged accordingly.

## Recommended patch

Use the coarse constant `4` unless you want a sharper lemma.

1. Change `heatTerm_iteratedFDeriv_global_bound` to:

```lean
norm (iteratedFDeriv Real j (heatTerm u0 n) q) <=
  4 * ((1 + unitIntervalCosineEigenvalue n) ^ j * M0 *
    Real.exp (-(c / 2) * unitIntervalCosineEigenvalue n))
```

2. Change `cutoffHeatMajorant` to multiply the old majorant by `4`, e.g.

```lean
4 *
  (sum i in Finset.range (k + 1), choose k i * Phi i) *
  ((1 + unitIntervalCosineEigenvalue n) ^ k * M0 * exp(...))
```

or place the `4` inside each summand.

3. `cutoffHeatMajorant_summable` should remain essentially the same:

```lean
(one_add_eigenvalue_pow_mul_exp_summable k (half_pos hc) hM0).mul_left _
```

with the larger finite constant.

4. In the cutoff proof, when applying the heat-term bound to order `k - i`, use the coarse inequality

```lean
(1 + lambda_n)^(k - i) <= (1 + lambda_n)^k
```

and carry the `4` through by nonnegativity.

## Alternative sharper patch

If you prefer exact constants, use:

```lean
(2 : Real) ^ j * ((1 + lambda_n)^j * M0 * exp(...))
```

for `heatTerm_iteratedFDeriv_global_bound`, and define:

```lean
cutoffHeatMajorant ... :=
  (sum i in range (k + 1),
    choose k i * Phi i * (2 : Real) ^ (k - i)) * base k n
```

This matches the actual Leibniz split. It is a little more bookkeeping but still summable by the same one-line `mul_left` pattern.

## Bottom line

The proposed correction is right: the no-factor heat-term bound should be enlarged. For `j <= 2`, adding a constant `4` is enough and is the least invasive way to unblock the sorry. If you use the sharper route, add `(2 : Real) ^ j` to the heat-term lemma and `(2 : Real) ^ (k - i)` in the cutoff majorant sum.
