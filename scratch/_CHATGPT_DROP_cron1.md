# Q1814 (cron1) -- fill the mechanical `Rderiv` sorry

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was only:

```text
Q1814 (cron1): cron1 /tmp/q_cron1_fill_sorry.txt
```

The local file `/tmp/q_cron1_fill_sorry.txt` was not present in the runtime I can inspect, and it is not readable through the GitHub connector. I used the current repo state and the previous `Rderiv` context to infer the intended target.

I did **not** use Python, `/mnt/data`, the sandbox, or a sandbox link. I did not run Lean locally.

## Inferred target

The relevant file is:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

The current `hR_deriv_bounded` block inside `cutoffResolverMajorant_bddAbove_direct` has two local sorries:

```lean
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  sorry -- ContinuousOn of srcSlice1 + L∞ bound via eigenvalue damping
...
sorry -- HasDerivAt assembly from heatSemigroup_d0
```

This answer fills the **second** sorry: the mechanical derivative assembly

```lean
deriv R t = w_k * cosineCoeffs (srcSlice1 ... t) k
```

from `heatSemigroup_d0` plus `resolverTimeCoeff_eq_weight_smul`.  The first `hBsrc` sorry is the real analytic source-slice bound and should stay as a separate lemma.

## Drop-in replacement for the second sorry

Replace only the final

```lean
sorry -- HasDerivAt assembly from heatSemigroup_d0
```

inside `hR_deriv_bounded` by this block.

```lean
            have hsrc_deriv : HasDerivAt
                (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)
                (cosineCoeffs
                  (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k)
                t := by
              obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
                heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
                  hu₀_bound hu₀_cont hfloor t ht_pos
              have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
                  (srcSlice p (conjugatePicardIter p u₀ 0) r)
                  MeasureTheory.volume (0 : ℝ) 1 :=
                hcont.mono fun r hr =>
                  (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
              have hH := cosineCoeffs_hasDerivAt_of_smooth_param
                (f := srcSlice p (conjugatePicardIter p u₀ 0))
                (f' := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
                (τ := t) (δ := δ) (n := k) hδ hint hdiff hcd
              have heq :
                  (fun r => cosineCoeffs
                    (srcSlice p (conjugatePicardIter p u₀ 0) r) k) =
                    srcTimeCoeff p (conjugatePicardIter p u₀ 0) k := by
                funext r
                simp [srcTimeCoeff_eq_cosineCoeffs]
              rw [heq] at hH
              simpa using hH
            have hR_hasDerivAt : HasDerivAt R
                (w_k * cosineCoeffs
                  (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k)
                t := by
              have hEq : R = fun s : ℝ =>
                  w_k * srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
                funext s
                dsimp [R, w_k]
                exact resolverTimeCoeff_eq_weight_smul
                  p (conjugatePicardIter p u₀ 0) k s
              rw [hEq]
              simpa using hsrc_deriv.const_mul w_k
            have hR_deriv_eq : deriv R t =
                w_k * cosineCoeffs
                  (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k :=
              hR_hasDerivAt.deriv
            rw [hR_deriv_eq, abs_mul]
            exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
```

## If `dsimp [R, w_k]` is too aggressive

If Lean does not unfold the local `set` abbreviations cleanly, use this slightly more explicit variant of the `hEq` subproof:

```lean
              have hEq : R = fun s : ℝ =>
                  w_k * srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
                funext s
                change resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s =
                  ShenWork.PDE.intervalNeumannResolverWeight p k *
                    srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s
                exact resolverTimeCoeff_eq_weight_smul
                  p (conjugatePicardIter p u₀ 0) k s
```

This version avoids relying on the generated names from the local `set` commands.

## Better permanent refactor

The local proof above duplicates the `hd0` extraction already present in `heatLevel0_srcTimeCoeff_contDiffAt_two`.  The cleaner permanent patch is to add a named lemma after that theorem:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalResolverDataConcrete
  (srcTimeCoeff resolverTimeCoeff_eq_weight_smul)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete
  (srcSlice srcTimeCoeff_eq_cosineCoeffs)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1)
open ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
  (heatDu heatSemigroup_d0)
open ShenWork.IntervalMildPicardRegularity
  (cosineCoeffs_hasDerivAt_of_smooth_param)

namespace ShenWork.Paper2.HeatResolverJointC2Direct

/-- First derivative of the level-0 source cosine coefficient. -/
theorem heatLevel0_srcTimeCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt
      (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k)
      (cosineCoeffs
        (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k)
      t := by
  obtain ⟨δ, hδ, hcont, hdiff, hcd⟩ :=
    heatSemigroup_d0 (p := p) (u₀ := u₀) (M₀ := M₀)
      hu₀_bound hu₀_cont hfloor t ht
  have hint : ∀ᶠ r in 𝓝 t, IntervalIntegrable
      (srcSlice p (conjugatePicardIter p u₀ 0) r)
      MeasureTheory.volume (0 : ℝ) 1 :=
    hcont.mono fun r hr =>
      (Set.uIcc_of_le (zero_le_one (α := ℝ)) ▸ hr).intervalIntegrable
  have hH := cosineCoeffs_hasDerivAt_of_smooth_param
    (f := srcSlice p (conjugatePicardIter p u₀ 0))
    (f' := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
    (τ := t) (δ := δ) (n := k) hδ hint hdiff hcd
  have heq :
      (fun r => cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) r) k) =
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k := by
    funext r
    simp [srcTimeCoeff_eq_cosineCoeffs]
  rw [heq] at hH
  simpa using hH

/-- First derivative of the level-0 resolver coefficient. -/
theorem heatLevel0_resolverTimeCoeff_hasDerivAt
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k)
      (ShenWork.PDE.intervalNeumannResolverWeight p k *
        cosineCoeffs
          (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k)
      t := by
  have hsrc := heatLevel0_srcTimeCoeff_hasDerivAt
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor ht k
  have hEq : resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k =
      fun s => ShenWork.PDE.intervalNeumannResolverWeight p k *
        srcTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
    funext s
    exact resolverTimeCoeff_eq_weight_smul p (conjugatePicardIter p u₀ 0) k s
  rw [hEq]
  simpa using hsrc.const_mul (ShenWork.PDE.intervalNeumannResolverWeight p k)

/-- `deriv` rewrite form of `heatLevel0_resolverTimeCoeff_hasDerivAt`. -/
theorem heatLevel0_resolverTimeCoeff_deriv_eq
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    deriv (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
      ShenWork.PDE.intervalNeumannResolverWeight p k *
        cosineCoeffs
          (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k := by
  exact (heatLevel0_resolverTimeCoeff_hasDerivAt
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hfloor ht k).deriv

end ShenWork.Paper2.HeatResolverJointC2Direct
```

Then the local second sorry reduces to:

```lean
            rw [heatLevel0_resolverTimeCoeff_deriv_eq
              (p := p) (u₀ := u₀) (M₀ := M₀)
              hu₀_bound hu₀_cont hfloor ht_pos k, abs_mul]
            exact mul_le_mul_of_nonneg_left (hBsrc t ht) (abs_nonneg _)
```

provided the local `R`/`w_k` have been unfolded or the goal has been changed to the raw resolver coefficient form.

## What remains after this fill

This fill discharges the **mechanical** derivative-identification sorry.  The remaining non-mechanical obligation is:

```lean
have hBsrc : ∃ Bsrc : ℝ, ∀ t : ℝ, c + 1 < t →
    |cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k| ≤ Bsrc := by
  sorry
```

That one should be factored as a named lemma using:

* `heatSemigroup_d0` for `ContinuousOn` of `srcSlice1` time slices;
* `cosineCoeffs_abs_le_of_continuous_bounded`;
* a tail `L∞` bound for `heatDu u₀ t x`, via `unitIntervalCosineHeatSecondPointWeight_abs_le` and `reciprocalSquareTerm_summable`;
* a uniform bound for `(S(t)u₀)^(γ-1)` using a positive lower bound, because `CM2Params` only gives `0 < γ`, not `1 ≤ γ`.

Bottom line: for Q1814, the direct `HasDerivAt` assembly sorry is fillable exactly as above; the source coefficient bound is the remaining analytic sorry and should not be hidden in the same local block.
