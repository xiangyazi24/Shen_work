# Q1471 (cron1) -- bounded-weight majorants and summability

Repository: `xiangyazi24/Shen_work`
Branch: `chatgpt-scratch`
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method

Connector-only repository search. I did not run Lean locally and did not edit Lean source.

As in the immediately preceding cron drops, direct fetch of `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` at `chatgpt-scratch` returned 404, but GitHub code search exposed the indexed snapshot:

```text
7db6d8e4b01d279823281613bb824200483faddd
```

The names below are from that snapshot. This report is committed to `chatgpt-scratch`.

## Definitions found

The definitions are in:

```lean
import ShenWork.PDE.IntervalResolverJointC2Physical
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete
```

The value series term is:

```lean
def boundedWeightJointTerm (c : Nat -> Real -> Real) (n : Nat) : Real × Real -> Real :=
  fun q => c n q.1 * cosineMode n q.2
```

The value majorant is:

```lean
def boundedWeightJointMajorant (Bt : Nat -> Nat -> Real) (k n : Nat) : Real :=
  sum i in Finset.range (k + 1),
    (Nat.choose k i : Real) * Bt i n * valueCosWeight (k - i) n
```

The gradient series term is:

```lean
def boundedWeightJointGradTerm (c : Nat -> Real -> Real) (n : Nat) : Real × Real -> Real :=
  fun q => c n q.1 * deriv (cosineMode n) q.2
```

The gradient majorant is:

```lean
def boundedWeightJointGradMajorant (Bt : Nat -> Nat -> Real) (k n : Nat) : Real :=
  sum i in Finset.range (k + 1),
    (Nat.choose k i : Real) * Bt i n * gradCosWeight (k - i) n
```

The spatial weights are in `IntervalResolverSpectralJointC2Concrete`:

```lean
def valueCosWeight (m n : Nat) : Real :=
  match m with
  | 0 => 1
  | 1 => abs ((n : Real) * Real.pi)
  | _ => unitIntervalCosineEigenvalue n

def gradCosWeight (m n : Nat) : Real :=
  match m with
  | 0 => abs ((n : Real) * Real.pi)
  | 1 => unitIntervalCosineEigenvalue n
  | _ => abs ((n : Real) * Real.pi) * unitIntervalCosineEigenvalue n
```

So `boundedWeightJointMajorant Bt m n` is exactly the Leibniz majorant for the joint order-`m` derivative of `c_n(t) cos(n pi x)`: choose `i` time derivatives on `c_n`, and `m-i` spatial derivatives on the cosine.

Likewise `boundedWeightJointGradMajorant Bt m n` is the same Leibniz majorant after the extra spatial derivative in `deriv (cosineMode n)`.

## What summability means concretely

In `IntervalHeatSemigroupHighRegularity.lean`, the two sorry goals are fed to

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
```

with

```lean
Bt i k = intervalNeumannResolverWeight p k * builtEs H i k
```

where

```lean
intervalNeumannResolverWeight p k = 1 / (p.mu + lambda_k)
```

and `builtEs` is:

```lean
def builtEs (H : FlooredSourceTimeData p u s1 s2) (i k : Nat) : Real :=
  if hi : i <= 2 then
    if k = 0 then Classical.choose (H.zerothBound i hi)
    else Classical.choose (H.laplBound i hi) / (((k : Real) * Real.pi) ^ 2)
  else 0
```

Thus for every fixed joint derivative order `m <= 2`, the value goal is:

```lean
Summable (fun n =>
  sum i in range (m+1), choose(m,i) *
    (w_n * Es_i(n)) * valueCosWeight (m-i) n)
```

and the gradient goal is:

```lean
Summable (fun n =>
  sum i in range (m+1), choose(m,i) *
    (w_n * Es_i(n)) * gradCosWeight (m-i) n)
```

Zero mode `n = 0` is harmless: it is one term, and most gradient spatial weights vanish at `n=0`. The real question is the tail `n >= 1`.

Let

```text
freq_n = abs ((n : Real) * pi)
lambda_n = freq_n^2
w_n = 1 / (mu + lambda_n)
Es_i(n) <= M_i / freq_n^2   for n >= 1
```

Useful existing lemmas:

```lean
ShenWork.IntervalResolverJointC2PhysicalConcrete.eigenvalue_mul_resolverWeight_le_one
ShenWork.IntervalResolverJointC2PhysicalConcrete.resolverWeight_le_inv_mu
ShenWork.IntervalResolverJointC2PhysicalConcrete.valueCosWeight_one_mul_resolverWeight_le
```

For a clean proof one should also add a sharper frequency-weight lemma, since the existing `valueCosWeight_one_mul_resolverWeight_le` is too crude for summability:

```lean
-- suggested lemma, for n >= 1
abs ((n : Real) * Real.pi) * intervalNeumannResolverWeight p n
  <= 1 / abs ((n : Real) * Real.pi)
```

because `mu + freq^2 >= freq^2`.

## Value summability: should be provable from `(k*pi)^-2`

For `m <= 2`, the possible value spatial weights are only:

```text
1, freq_n, lambda_n
```

The three tail estimates are:

```text
w_n * Es_i(n) * 1        <= C / freq_n^2
w_n * Es_i(n) * freq_n   <= C / freq_n^3
w_n * Es_i(n) * lambda_n <= C / freq_n^2
```

The last estimate uses `lambda_n * w_n <= 1`. Therefore each value summand is bounded by a constant multiple of `1 / freq_n^2`, hence by a constant multiple of `1 / n^2`. Since the sum over `i <= m` is finite, `boundedWeightJointMajorant (w*Es) m` is summable for every `m <= 2`.

Skeleton:

```lean
-- For each fixed m <= 2:
apply Summable.of_nonneg_of_le
  (fun n => by positivity / use nonneg lemmas)
  (fun n => by
    -- split n = 0 and n >= 1
    -- unfold boundedWeightJointMajorant
    -- bound the finite sum by C_m * reciprocalSquareTerm n
    -- use:
    --   lambda_n * w_n <= 1
    --   w_n <= 1 / mu
    --   freq_n * w_n <= 1 / freq_n  (new lemma)
    --   builtEs H i n <= M_i / freq_n^2 for n >= 1)
  (reciprocalSquareTerm_summable.mul_left C_m)
```

## Gradient summability: the `m = 2` case is not covered by only `(k*pi)^-2`

For the gradient majorant, the possible spatial weights are:

```text
freq_n, lambda_n, freq_n * lambda_n
```

For `m = 0` and `m = 1`, `(k*pi)^-2` is enough:

```text
w_n * Es_i(n) * freq_n   <= C / freq_n^3
w_n * Es_i(n) * lambda_n <= C / freq_n^2
```

But for `m = 2`, the `i = 0` term contains

```text
w_n * Es_0(n) * (freq_n * lambda_n)
```

Using `lambda_n * w_n <= 1`, this is only

```text
<= Es_0(n) * freq_n <= C / freq_n
```

and `sum 1/n` diverges. More directly,

```text
w_n * (M / freq_n^2) * (freq_n * lambda_n)
  = M * freq_n * lambda_n / ((mu + lambda_n) * freq_n^2)
  ~ M / freq_n.
```

So the current `(k*pi)^-2` envelope is enough for `value_summable`, but not enough for `grad_summable` at joint order `m = 2` under this generic absolute-majorant assembler.

This means the comment in `IntervalHeatSemigroupHighRegularity.lean` saying the gradient case is "same with an extra eigenvalue factor absorbed by `(k*pi)^-2` decay" is too optimistic for the `m=2, i=0` gradient term. The extra gradient derivative leaves one uncancelled frequency.

## Consequences / patch choices

There are three honest options.

### Option A: strengthen the source envelope for gradient `m = 2`

Require enough decay for the `i = 0` source coefficients so that

```text
Summable (fun n => freq_n * Es_0(n))
```

For example `Es_0(n) = O(freq_n^(-3))` is enough. This would come from a stronger spatial regularity/IBP package for the zeroth source slice, not just closed `C^2` Neumann.

### Option B: weaken the gradient target

If the downstream FAC lane only needs fewer joint derivatives of `grad v`, then change the gradient assembler target from joint `C^2` of `grad v` to joint `C^1` where appropriate. For gradient orders `m <= 1`, the current `(k*pi)^-2` envelope is enough.

### Option C: use a non-absolute/oscillatory argument

The current theorem `boundedWeightJointGradSeries_contDiff_two` is based on `contDiff_tsum` with a nonnegative summable majorant. Under that theorem, the `1/freq_n` obstruction is real. Avoiding it would require a different convergence theorem using cancellation of sine/cosine series, not the existing bounded-majorant route.

## Recommendation

Do not try to prove both sorrys from only the existing `builtEs` `(k*pi)^-2` envelope.

Prove `value_summable` from the present data. For `grad_summable`, either strengthen the source-side envelope (at least enough to prove `Summable (fun n => freq_n * Es 0 n)`) or weaken the claimed gradient joint regularity. As the repo currently defines the majorant, `grad_summable` for `m = 2` is not a mechanical consequence of `FlooredSourceTimeData.laplBound`.

## Search log

```text
boundedWeightJointMajorant
boundedWeightJointGradMajorant
def valueCosWeight
gradCosWeight
def builtEs
PhysicalSourceTimeC2
PhysicalResolverJointC2Data
eigenvalue_mul_resolverWeight_le_one
resolverWeight_le_inv_mu
resolverWeight frequency
```
