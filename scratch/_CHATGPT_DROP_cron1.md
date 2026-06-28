# Q1752 (cron1) -- fill the `i = 1` tail subgoal

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1752 (cron1): cron1 /tmp/q_cron1_i1fill.txt
```

The local file `/tmp/q_cron1_i1fill.txt` is not accessible through the GitHub connector. I inferred the target from `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`, where the `i = 1` branch has:

```lean
have hA1_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
    ‖iteratedFDeriv ℝ 1 A t‖ ≤ B := by
  sorry -- tail: A' = resolverTimeCoeff' for t > c, bounded by eigenvalue damping
```

I used the GitHub connector only. I did not use Python, `/mnt/data`, the sandbox, or any sandbox link. I did not run Lean locally.

## Replacement code

Replace the `hA1_tail` sorry block with this:

```lean
        have hA1_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
            ‖iteratedFDeriv ℝ 1 A t‖ ≤ B := by
          obtain ⟨Bt, Hphys⟩ :=
            ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
              (p := p) (u₀ := u₀) (M₀ := M₀)
              hu₀_bound hu₀_cont hu₀_pos
          refine ⟨Bt 1 k, fun t ht => ?_⟩
          have hc'c : c / 2 < c := by linarith
          have ht_c : c < t := by linarith
          have hev : A =ᶠ[𝓝 t]
              fun s : ℝ => resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s := by
            filter_upwards [Ioi_mem_nhds ht_c] with s hs
            show smoothRightCutoff (c / 2) c s *
                resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s =
              resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s
            rw [smoothRightCutoff_eq_one_of_ge hc'c (le_of_lt hs)]
            ring
          have hderiv_eq :
              iteratedFDeriv ℝ 1 A t =
                iteratedFDeriv ℝ 1
                  (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t := by
            exact (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 1).eq_of_nhds
          rw [hderiv_eq]
          exact Hphys.coeff_bound 1 k t (by norm_num)
```

## Why this is the right fill

On the tail `c + 1 < t`, we have `c < t`. Hence there is a neighborhood of `t` contained in `Ioi c`. On that neighborhood, the right cutoff is identically `1`:

```lean
smoothRightCutoff_eq_one_of_ge (by linarith : c / 2 < c) (le_of_lt hs)
```

Therefore the local time factor

```lean
A s = smoothRightCutoff (c / 2) c s *
  resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k s
```

is eventually equal near `t` to the raw resolver coefficient. Then:

```lean
Filter.EventuallyEq.iteratedFDeriv
```

rewrites `iteratedFDeriv ℝ 1 A t` to the first iterated derivative of the raw resolver coefficient. The needed bound is exactly:

```lean
Hphys.coeff_bound 1 k t (by norm_num)
```

from:

```lean
PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt
```

## Shorter variant if `Bt, Hphys` are extracted before `hA_global_bounds`

If you move this once above `hA_global_bounds`:

```lean
    obtain ⟨Bt, Hphys⟩ :=
      ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
        (p := p) (u₀ := u₀) (M₀ := M₀)
        hu₀_bound hu₀_cont hu₀_pos
```

then the `hA1_tail` proof can start directly with:

```lean
          refine ⟨Bt 1 k, fun t ht => ?_⟩
```

and omit the local `obtain`.

## Same pattern for `i = 2`

The next tail sorry for `i = 2` is filled by the same proof, replacing `1` by `2` and using:

```lean
Hphys.coeff_bound 2 k t (by norm_num)
```

## Bottom line

The `i = 1` tail is not a manual eigenvalue-damping calculation at this location. It is a local-cutoff rewrite plus the packaged physical coefficient bound:

```text
cutoff = 1 near t  ⇒  A locally equals resolverTimeCoeff
PhysicalResolverJointC2Data.coeff_bound 1  ⇒  first derivative bound
```
