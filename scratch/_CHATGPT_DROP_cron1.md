# Q1793 (cron1) -- direct `hA1_tail` route

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1793 (cron1): cron1 /tmp/q_cron1_direct.txt
```

The local file `/tmp/q_cron1_direct.txt` is not accessible through the GitHub connector. I used the connector only and inferred the target from the current direct proof in:

```text
ShenWork/Paper2/IntervalHeatResolverJointC2.lean
```

I did **not** use Python, `/mnt/data`, the sandbox, or any sandbox link. I did not run Lean locally.

## Target in the current file

The direct proof is inside:

```lean
private theorem cutoffResolverMajorant_bddAbove_direct
```

in the local tail proof:

```lean
have hA_global_bounds : ∀ i : ℕ, i ≤ 2 →
    ∃ B_i : ℝ, ∀ t : ℝ, ‖iteratedFDeriv ℝ i A t‖ ≤ B_i := by
  intro i hi
  interval_cases i
```

The `i = 0` branch is mostly direct and uses an `L∞` bound. The current `i = 1` branch stops at:

```lean
have hA1_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
    ‖iteratedFDeriv ℝ 1 A t‖ ≤ B := by
  -- A = φ * resolverTimeCoeff. Use 1D Leibniz: A' = φ'*R + φ*R'.
  -- φ' bounded (resolverSmoothRightCutoffDerivBound_spec), R bounded (i=0 bound).
  -- φ bounded (≤1), R' bounded (THIS is the hard part — needs eigenvalue damping).
  -- For R' = resolverTimeCoeff': for t > c+1 > 0, srcTimeCoeff is C²
  -- (heatLevel0_srcTimeCoeff_contDiffAt_two), so srcTimeCoeff' is continuous.
  -- srcTimeCoeff'(t) = cosineCoeffs(srcSlice1(t), k) from d0 (HasDerivAt).
  -- |cosineCoeffs(srcSlice1(t), k)| ≤ 2·‖srcSlice1(t)‖_∞
  -- ‖srcSlice1(t)‖_∞ ≤ νγ·M_sup^{γ-1}·‖Δu(t)‖_∞
  -- ‖Δu(t)‖_∞ ≤ M₀·(4/((c+1)²π²))·Σ(1/n²) from unitIntervalCosineHeatSecondPointWeight_abs_le
  sorry
```

## Short answer

The direct route is possible for `i = 1`, but the current file is missing one clean helper:

```lean
∀ t, c + 1 < t →
  ‖iteratedFDeriv ℝ 1 (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤ B
```

or equivalently a source-side positive-time-lower-bound estimate for:

```lean
|cosineCoeffs (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k|
```

The local proof should **not** manually expand all spectral estimates inside `hA1_tail`. Add a named helper, then the tail proof is short.

## Direct helper to add

Add a helper with this shape near the direct proof, after `heatLevel0_resolverTimeCoeff_contDiffAt_two` / source coefficient lemmas are available:

```lean
private theorem heatLevel0_resolverTimeCoeff_deriv_bound_on_tail
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ c : ℝ}
    (hc : 0 < c)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_pos : ∀ x : intervalDomainPoint, 0 < u₀ x)
    (hfloor : ∀ t : ℝ, 0 < t → ∀ x ∈ Set.Icc (0:ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x)
    (k : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
      ‖iteratedFDeriv ℝ 1
        (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖ ≤ B := by
  -- Proof outline:
  -- 1. rewrite resolverTimeCoeff = resolverWeight * srcTimeCoeff;
  -- 2. use const-smul derivative transfer;
  -- 3. identify srcTimeCoeff' with cosineCoeffs(srcSlice1(t), k);
  -- 4. bound cosineCoeffs by a uniform sup norm;
  -- 5. bound srcSlice1 = νγ u^(γ-1) heatDu on t ≥ c+1;
  -- 6. bound heatDu by the second-spatial heat-series estimate with lower time c+1.
  sorry
```

This helper is the true direct analytic payload for `i = 1`.

## Replacement for the local `hA1_tail` after adding that helper

Once the helper above exists, the local `hA1_tail` block becomes:

```lean
        have hA1_tail : ∃ B : ℝ, ∀ t : ℝ, c + 1 < t →
            ‖iteratedFDeriv ℝ 1 A t‖ ≤ B := by
          obtain ⟨BR, hBR⟩ :=
            heatLevel0_resolverTimeCoeff_deriv_bound_on_tail
              (p := p) (u₀ := u₀) (M₀ := M₀) (c := c)
              hc hu₀_bound hu₀_cont hu₀_pos hfloor k
          refine ⟨BR, fun t ht => ?_⟩
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
          rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev 1).eq_of_nhds]
          exact hBR t ht
```

This part is mechanical: the cutoff is locally `1` on the tail, so `A'` is the raw resolver coefficient derivative.

## What the helper must prove directly

The hard helper should follow this chain.

First, use the constant elliptic weight:

```lean
resolverTimeCoeff p u k t =
  intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

from:

```lean
resolverTimeCoeff_eq_weight_smul
```

Then identify the source derivative at positive time. The already used `heatSemigroup_d0` gives the local time derivative of `srcSlice`, so the coefficient derivative should be:

```lean
deriv (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t =
  cosineCoeffs
    (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀) t) k
```

for `0 < t`. If this exact theorem is not public, add a local theorem modeled on the private `srcTimeCoeff_hasDerivAt` proof in `IntervalPhysicalSourceTimeC2Concrete.lean`.

Finally, bound the coefficient by sup norm:

```lean
|cosineCoeffs f k| ≤ 2 * C
```

where `|f x| ≤ C` on `[0,1]`. The repo already uses:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
```

in the `i = 0` branch.

For `f = srcSlice1 ... t`, use:

```lean
srcSlice1 p u heatDu t x =
  p.ν * p.γ * (intervalDomainLift (u t) x) ^ (p.γ - 1) * heatDu u₀ t x
```

and, on `t ≥ c + 1`, combine:

```text
|intervalDomainLift (u t) x| ≤ M_sup
|heatDu u₀ t x| ≤ CΔ(c,M₀)
```

The second estimate is where the existing spectral bound enters. The repo has:

```lean
ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondPointWeight_abs_le
```

which bounds the second spatial heat weight by a reciprocal-square summand. Together with `hu₀_bound` and `reciprocalSquareTerm_summable`, this gives a uniform bound for `heatDu` on any tail `t ≥ c + 1`.

## Why the current inline proof is too large

Trying to prove all of this inside `hA1_tail` causes a huge local goal with:

```text
cutoff algebra
resolver/source coefficient rewriting
coefficient derivative identification
source-slice sup bound
heat Laplacian spectral summability
```

all mixed together. That is brittle. The direct route should isolate the real analytic statement as the helper above, then keep `hA1_tail` as a short cutoff-localization proof.

## Alternative if directness is not required

If the goal is simply to close the file robustly, the already packaged physical route is much shorter:

```lean
obtain ⟨Bt, Hphys⟩ :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatSemigroup_level0_resolverJointC2Data
    (p := p) (u₀ := u₀) (M₀ := M₀)
    hu₀_bound hu₀_cont hu₀_pos
```

then use:

```lean
Hphys.coeff_bound 1 k t (by norm_num)
```

on the tail after rewriting `A` locally to the raw resolver coefficient. But that is no longer the fully direct proof advertised by `cutoffResolverMajorant_bddAbove_direct`.

## Bottom line

For the direct proof, the next correct step is **not** another local tactic patch. Add the named helper:

```lean
heatLevel0_resolverTimeCoeff_deriv_bound_on_tail
```

prove it from source derivative identification plus the heat-Laplacian spectral sup bound, and then the `hA1_tail` block is a short `EventuallyEq.iteratedFDeriv` rewrite followed by that helper.
