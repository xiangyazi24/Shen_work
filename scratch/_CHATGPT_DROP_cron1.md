# Q1626 (cron1) -- cron2 tail bound

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1626 (cron1): cron2 /tmp/q_cron2_tail.txt
```

The local file `/tmp/q_cron2_tail.txt` is not accessible through the GitHub connector. I therefore inferred the intended task from the repository itself. The strongest match is the cron2 truncated-Picard tail theorem in:

```text
ShenWork/Paper2/IntervalBFormCron2TruncatedPicard.lean
```

This file begins:

```lean
/-
  Truncated B-form Picard fixed point for the cron2 negative-part route.
...
-/
import ShenWork.Paper2.IntervalBFormNegativePartCron2
```

and contains the theorem:

```lean
truncatedConjugatePicardIter_pointwise_tail_bound
```

I used the GitHub connector only. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link.

## Short answer

The cron2 tail bound is already present on the default branch and the proof is the right one. It is a direct copy/adaptation of the existing B-form Picard tail proof in `IntervalConjugatePicard.lean`, with `conjugatePicardIter` replaced by `truncatedConjugatePicardIter` and `conjugatePicardLimit` replaced by `truncatedConjugatePicardLimit`.

The theorem proves:

```lean
|truncatedConjugatePicardIter p u₀ n t x
    - truncatedConjugatePicardLimit p u₀ T t x|
  ≤ K ^ n * C₀ / (1 - K)
```

under the geometric step estimate

```lean
|truncatedConjugatePicardIter p u₀ (m + 1) t x
    - truncatedConjugatePicardIter p u₀ m t x| ≤ K ^ m * C₀
```

for `0 < t`, `t ≤ T`, `0 ≤ K`, and `K < 1`.

There is no off-by-one error: since the first omitted step from iterate `n` is the increment from `n` to `n+1`, the tail starts at `m = n`, so the bound is

```text
Σ_{r≥0} K^(n+r) C₀ = K^n C₀ / (1-K)
```

not `K^(n+1) C₀ / (1-K)`.

## The committed proof pattern

The theorem in `IntervalBFormCron2TruncatedPicard.lean` is:

```lean
theorem truncatedConjugatePicardIter_pointwise_tail_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (_hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint) (n : ℕ) :
    |truncatedConjugatePicardIter p u₀ n t x
        - truncatedConjugatePicardLimit p u₀ T t x|
      ≤ K ^ n * C₀ / (1 - K) := by
  set a := fun m => truncatedConjugatePicardIter p u₀ m t x
  set d := fun m => K ^ m * C₀
  have hdist : ∀ m, dist (a m) (a m.succ) ≤ d m := by
    intro m
    rw [Real.dist_eq, abs_sub_comm]
    exact hbound m t ht htT x
  have hd_sum : Summable d :=
    Summable.mul_right C₀ (summable_geometric_of_lt_one hK_nn hK)
  have hcauchy : CauchySeq a := cauchySeq_of_dist_le_of_summable d hdist hd_sum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim_eq : truncatedConjugatePicardLimit p u₀ T t x = L := by
    unfold truncatedConjugatePicardLimit
    simp only [ht, htT, and_self, ite_true]
    exact hL.limUnder_eq
  rw [hlim_eq, ← Real.dist_eq]
  calc dist (a n) L ≤ ∑' m, d (n + m) :=
        dist_le_tsum_of_dist_le_of_tendsto d hdist hd_sum hL n
    _ = K ^ n * C₀ / (1 - K) := by
        simp_rw [d, pow_add, mul_assoc]
        rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hK_nn hK]
        ring
```

This is the correct proof. The important helper is:

```lean
dist_le_tsum_of_dist_le_of_tendsto
```

which converts a summable step-distance bound into a distance-to-limit tail bound.

## Why the proof works

Fix `t`, `x`, and define:

```lean
a m := truncatedConjugatePicardIter p u₀ m t x
d m := K ^ m * C₀
```

The hypothesis `hbound` gives:

```lean
dist (a m) (a (m+1)) ≤ d m
```

because `Real.dist_eq` rewrites distance to absolute value, and `abs_sub_comm` fixes the order. Since `0 ≤ K` and `K < 1`, the geometric series `∑ K^m` is summable, hence `d` is summable:

```lean
have hd_sum : Summable d :=
  Summable.mul_right C₀ (summable_geometric_of_lt_one hK_nn hK)
```

Then the generic metric-space lemma gives a Cauchy sequence:

```lean
have hcauchy : CauchySeq a := cauchySeq_of_dist_le_of_summable d hdist hd_sum
```

Completeness of `ℝ` gives a limit `L`:

```lean
obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
```

The definition of `truncatedConjugatePicardLimit` on the active time window `(0,T]` is `atTop.limUnder`, so the proof identifies it with the actual limit:

```lean
unfold truncatedConjugatePicardLimit
simp only [ht, htT, and_self, ite_true]
exact hL.limUnder_eq
```

Finally:

```lean
dist (a n) L ≤ ∑' m, d (n + m)
```

and the right-hand side is evaluated by:

```lean
simp_rw [d, pow_add, mul_assoc]
rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hK_nn hK]
ring
```

This proves exactly `K^n*C₀/(1-K)`.

## Uniform convergence downstream

The file then uses the pointwise tail theorem to prove uniform convergence on the time-space window:

```lean
theorem truncatedConjugatePicardIter_uniform_convergence
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (_hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ t, 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ n t x
          - truncatedConjugatePicardLimit p u₀ T t x| < ε := by
```

The proof uses the scalar fact:

```lean
private theorem truncated_geometric_tail_tendsto_zero {K C₀ : ℝ}
    (hK : K < 1) (hK_nn : 0 ≤ K) :
    Tendsto (fun n => K ^ n * C₀ / (1 - K)) atTop (nhds 0)
```

Then it chooses `N` from that convergence. The crucial point is that the tail bound is independent of `t` and `x`, so the same `N` works uniformly for all `t ∈ (0,T]` and all `x`.

## Exact relationship to the older non-truncated proof

`IntervalConjugatePicard.lean` already contains the same lemma in the non-truncated B-form setting:

```lean
theorem conjugatePicardIter_pointwise_tail_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (_hC₀ : 0 ≤ C₀)
    ... :
    |conjugatePicardIter p u₀ n t x - conjugatePicardLimit p u₀ T t x|
      ≤ K ^ n * C₀ / (1 - K)
```

The cron2 theorem is the same proof with these substitutions:

```text
conjugatePicardIter       ↦ truncatedConjugatePicardIter
conjugatePicardLimit      ↦ truncatedConjugatePicardLimit
intervalConjugateDuhamelMap ↦ truncatedConjugateDuhamelMap
```

No new analytic PDE facts are involved in the tail proof itself. The only inputs are:

```lean
hK    : K < 1
hK_nn : 0 ≤ K
hbound : geometric step estimate
```

## Minimal standalone import snippet

If the theorem needs to be referenced from another file, the import is:

```lean
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

-- Available theorem:
#check truncatedConjugatePicardIter_pointwise_tail_bound
#check truncatedConjugatePicardIter_uniform_convergence
#check truncatedConjugatePicardLimit_bounded
#check truncatedConjugatePicardLimit_hasContinuousSlices

end ShenWork.Paper2.BFormPositiveDatumNegPart
```

## Bottom line

For the likely cron2 tail question:

```text
The pointwise Picard tail bound is already proved correctly.
It is a mechanical metric/geometric-series argument, not an analytic PDE gap.
The formula is K^n*C₀/(1-K), with no off-by-one error.
The proof should be reused as-is anywhere the truncated Picard tail estimate is needed.
```
