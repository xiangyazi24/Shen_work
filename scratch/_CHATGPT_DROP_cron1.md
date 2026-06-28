# Q1661 (cron1) -- `i = 0` branch in `hA_global_bounds`

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1661 (cron1): cron1 /tmp/q_cron1_i0.txt
```

The local file `/tmp/q_cron1_i0.txt` is not accessible through the GitHub connector. I therefore inferred the target from the current cron1 boundedness thread. The relevant file is:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

The current default-branch file has the earlier `hmid` block filled. The remaining direct-global proof obstruction is in:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

inside the local tail proof:

```lean
have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
    ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
  intro i hi
  interval_cases i
  · -- i = 0
    ...
    sorry -- need to connect L∞ contraction → srcTimeCoeff bound → A bound
  · -- i = 1
    sorry
  · -- i = 2
    sorry
```

This report answers the `i = 0` branch.

I used the GitHub connector only. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

## Short answer

For the `i = 0` branch, do **not** try to build a fresh `L∞` contraction / `srcTimeCoeff` bound from scratch. The repository already has the correct package:

```lean
PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

Its field

```lean
H.coeff_bound 0 k t (by norm_num)
```

gives exactly the global bound for

```lean
‖resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t‖
```

because order `0` iterated derivative is the function itself.

Then `A(t)` is just:

```lean
smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

so the `i = 0` global bound is:

```text
‖A(t)‖ ≤ Φ₀ * Bt 0 k
```

where:

```lean
Φ₀ := resolverSmoothRightCutoffDerivBound (c / 2) c (by linarith) 0 h0
```

and `h0 : ((0 : ℕ) : ℕ∞) ≤ (2 : ℕ∞)`.

## Recommended local setup

Before entering `hA_global_bounds`, extract the physical data once:

```lean
    obtain ⟨Bt, Hphys⟩ :=
      ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hu₀_pos
```

Also make the local definition of `A` rewrite-friendly. Change:

```lean
  set A := fun t : ℝ =>
    smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

to:

```lean
  set A := fun t : ℝ =>
    smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
    with hA_def
```

That gives an explicit rewrite lemma:

```lean
hA_def : A = fun t : ℝ =>
  smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

## Replacement code for the `i = 0` branch

Replace the `i = 0` branch with:

```lean
      · -- i = 0: bound A(t) = φ(t) · resolverTimeCoeff(k,t)
        have h0Top : ((0 : ℕ) : ℕ∞) ≤ (2 : ℕ∞) := by norm_num
        have h0Nat : (0 : ℕ) ≤ 2 := by norm_num
        have hc'c : c / 2 < c := by linarith
        let Φ0 : ℝ :=
          resolverSmoothRightCutoffDerivBound (c / 2) c hc'c 0 h0Top
        refine ⟨Φ0 * Bt 0 k, ?_⟩
        intro t
        have hφ : ‖smoothRightCutoff (c / 2) c t‖ ≤ Φ0 := by
          dsimp [Φ0]
          simpa [norm_iteratedFDeriv_zero] using
            resolverSmoothRightCutoffDerivBound_spec hc'c h0Top t
        have hΦ0_nonneg : 0 ≤ Φ0 := by
          dsimp [Φ0]
          exact resolverSmoothRightCutoffDerivBound_nonneg hc'c h0Top
        have hR :
            ‖resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t‖ ≤ Bt 0 k := by
          simpa [norm_iteratedFDeriv_zero] using
            Hphys.coeff_bound 0 k t h0Nat
        rw [norm_iteratedFDeriv_zero]
        rw [hA_def]
        change ‖smoothRightCutoff (c / 2) c t *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t‖ ≤ Φ0 * Bt 0 k
        rw [norm_mul]
        calc
          ‖smoothRightCutoff (c / 2) c t‖ *
              ‖resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t‖
              ≤ Φ0 * ‖resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t‖ := by
                exact mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
          _ ≤ Φ0 * Bt 0 k := by
                exact mul_le_mul_of_nonneg_left hR hΦ0_nonneg
```

This is the concrete `i = 0` proof.

## Why this works

The order-zero goal is:

```lean
∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ 0 A t‖ ≤ B_i
```

and `norm_iteratedFDeriv_zero` rewrites it to:

```lean
∃ B_i : ℝ, ∀ t : ℝ, ‖A t‖ ≤ B_i
```

By definition:

```lean
A t = smoothRightCutoff (c / 2) c t * resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t
```

The cutoff bound is already packaged by:

```lean
resolverSmoothRightCutoffDerivBound_spec hc'c h0Top t
```

After rewriting order-zero iterated derivative, it gives:

```lean
‖smoothRightCutoff (c / 2) c t‖ ≤ Φ0
```

The resolver coefficient bound is already packaged by:

```lean
Hphys.coeff_bound 0 k t h0Nat
```

After rewriting order-zero iterated derivative, it gives:

```lean
‖resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t‖ ≤ Bt 0 k
```

Multiplying these two estimates gives the result.

## Important: where `Bt` comes from

The theorem used above is:

```lean
ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
```

It returns:

```lean
∃ Bt : ℕ → ℕ → ℝ,
  PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

The structure field is:

```lean
coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
  ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
```

So for `i = 0`:

```lean
Hphys.coeff_bound 0 k t (by norm_num)
```

is exactly the uniform global resolver coefficient bound. You do not need to reopen the source coefficient definition, the elliptic weight, or the heat semigroup `L∞` contraction in this local proof.

## If `rw [hA_def]` elaboration fails

Depending on how the local `set A := ...` was created, `hA_def` may orient as either:

```lean
hA_def : A = fun t => ...
```

or the reverse. If the direct `rw [hA_def]` fails, use one of these variants:

```lean
        rw [show A = (fun t : ℝ =>
          smoothRightCutoff (c / 2) c t *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) from hA_def]
```

or:

```lean
        change ‖(fun t : ℝ =>
          smoothRightCutoff (c / 2) c t *
            resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t) t‖ ≤ Φ0 * Bt 0 k
```

If the original file did not name the `set` equality, add `with hA_def`; that is the most robust fix.

## Relation to the better global patch

This `i = 0` branch can be made to work, but it is still better to close the whole global theorem using the physical `BddAbove` route:

```lean
cutoffResolverMajorant_bddAbove_of_physical
```

as described in Q1651. That avoids maintaining separate direct proofs for `i = 0`, `i = 1`, and `i = 2`.

If the goal is specifically to fill the `i = 0` branch, the snippet above is the right local patch. If the goal is to make the file robust, replace the whole direct `BddAbove` body with the existing physical-data proof.

## Minimal import/check context

In a scratch file, the relevant imports are:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff)
```

But the target theorem and helper lemmas in this patch are private/local to `IntervalHeatResolverJointC2.lean`, so the actual edit belongs in that file.

## Bottom line

For `i = 0`, use:

```text
order-zero iterated derivative = function itself
A = cutoff * resolver coefficient
cutoff is globally bounded by Φ0
resolver coefficient is globally bounded by Hphys.coeff_bound 0 k
```

The proof is a two-line norm product estimate after the local definitions are unfolded.
