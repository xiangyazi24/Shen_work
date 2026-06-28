# Q1783 (cron1/cron2) -- truncated Picard bound proof

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1783 (cron1): cron2 /tmp/q_cron2_bound.txt
```

The local file `/tmp/q_cron2_bound.txt` is not accessible through the GitHub connector. I used the connector only and inferred the target from the current `cron2` files in the repository. I did **not** use Python, `/mnt/data`, the sandbox, or any sandbox link. I did not run Lean locally.

The relevant file is:

```text
ShenWork/Paper2/IntervalBFormCron2TruncatedPicard.lean
```

The relevant bound lane is:

```lean
truncatedConjugatePicardLimit_bounded
TruncatedConjugateMildSolutionData.hbound
truncatedConjugateMildSolution_exists_from_data
```

## Short answer

For the bound on the truncated Picard limit, do **not** try to use uniform convergence. The clean proof is pointwise:

1. Fix `t`, `0 < t`, `t ≤ T`, and `x`.
2. Let `a n := truncatedConjugatePicardIter p u₀ n t x`.
3. Use the geometric difference estimate to prove `a` is Cauchy.
4. Extract `L` with `hL : Tendsto a atTop (nhds L)`.
5. Unfold `truncatedConjugatePicardLimit`; it is `L` by `hL.limUnder_eq`.
6. Transfer the uniform iterate ball bound through the limit using:

```lean
le_of_tendsto (hL.abs) (Eventually.of_forall ...)
```

This is exactly the right tool: a pointwise limit of values bounded by `M` is bounded by `M`.

## Concrete proof of the limit bound

If the local file has a sorry for this theorem, use this proof body:

```lean
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

 theorem truncatedConjugatePicardLimit_bounded
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ (n + 1) t x
        - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ n t x| ≤ M) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ T t x| ≤ M := by
  intro t ht htT x
  unfold truncatedConjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => truncatedConjugatePicardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact le_of_tendsto (hL.abs)
    (Eventually.of_forall (fun n => hball n t ht htT x))

end ShenWork.Paper2.BFormPositiveDatumNegPart
```

In the current repository, this theorem is already present in this form. If your local branch has a proof failure, the likely missing imports are the same imports already used by `IntervalBFormCron2TruncatedPicard.lean`, especially the `IntervalMildPicard` import for:

```lean
real_cauchySeq_of_geometric_bound
cauchySeq_tendsto_of_complete
```

## Concrete `hbound` field fill

Inside:

```lean
def truncatedConjugateMildSolutionData_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀) :
    TruncatedConjugateMildSolutionData p u₀ := by
  ...
```

once you have:

```lean
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ D.hK_nn hball
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
```

fill the `hbound` field by:

```lean
    hbound := truncatedConjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀
      (fun n => hgeom n) hball
```

The complete structure tail should look like:

```lean
  exact {
    T := D.T
    hT := D.hT
    M := D.M
    hM := D.hM
    u := truncatedConjugatePicardLimit p u₀ D.T
    hmild := truncatedConjugatePicardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn
      D.hC₀ D.hM (fun n => hgeom n) hball hcont_iterates hcont_limit
      hmeas_iterates hmeas_limit D.hcontr
    hbound := truncatedConjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀
      (fun n => hgeom n) hball
    hcont := hcont_limit
    hmeas := hmeas_limit
  }
```

## Why `hgeom` has the right type

The bound theorem expects:

```lean
hbound : ∀ n t, 0 < t → t ≤ T → ∀ x,
  |truncatedConjugatePicardIter p u₀ (n + 1) t x
    - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀
```

Inside `truncatedConjugateMildSolutionData_of_data`, `hgeom` has exactly this shape after it is defined as:

```lean
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ D.hK_nn hball
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
```

Therefore `(fun n => hgeom n)` is accepted as the first proof argument after `D.hC₀`.

## If Lean complains about `and_self`

The line:

```lean
simp only [ht, htT, and_self, ite_true]
```

is intended to reduce:

```lean
if 0 < t ∧ t ≤ T then ... else 0
```

If it does not fire in a slightly different local goal, replace it by:

```lean
have hwindow : 0 < t ∧ t ≤ T := ⟨ht, htT⟩
simp only [hwindow, if_true]
```

or:

```lean
rw [if_pos ⟨ht, htT⟩]
```

immediately after unfolding `truncatedConjugatePicardLimit`.

## If Lean complains about `le_of_tendsto`

The intended final step is:

```lean
  exact le_of_tendsto (hL.abs)
    (Eventually.of_forall (fun n => hball n t ht htT x))
```

Here:

```lean
hL.abs : Tendsto (fun n => |a n|) atTop (nhds |L|)
```

and:

```lean
Eventually.of_forall (fun n => hball n t ht htT x)
```

is the eventual bound `|a n| ≤ M`. If elaboration fails, spell out the function:

```lean
  have hlim_abs : Tendsto (fun n => |a n|) atTop (nhds |L|) := hL.abs
  have hev_bound : ∀ᶠ n in atTop, |a n| ≤ M :=
    Eventually.of_forall (fun n => hball n t ht htT x)
  exact le_of_tendsto hlim_abs hev_bound
```

## Bottom line

The cron2 bound is a standard closed-ball-under-limit argument. The Picard iterates are already uniformly in the `M` ball, and the geometric estimate gives pointwise convergence. So the limit bound is just:

```text
bounded sequence + convergent sequence ⇒ bounded limit
```

formalized as:

```lean
le_of_tendsto (hL.abs) (Eventually.of_forall ...)
```
