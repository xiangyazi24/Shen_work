# Q1229 (cron2) — `srcTimeCoeff_iteratedDeriv2`

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Target

In `ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean`, replace the `sorry` in:

```lean
/-- `iteratedDeriv 2 (srcTimeCoeff k) t = cosineCoeffs (s₂ t) k` for `t > 0`. -/
private theorem srcTimeCoeff_iteratedDeriv2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (srcTimeCoeff p u k) t = cosineCoeffs (s₂ t) k := by
  ...
```

## Checked facts

The file already has the two local private facts needed immediately above the target:

```lean
private theorem srcTimeCoeff_iteratedDeriv1
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 1 (srcTimeCoeff p u k) t = cosineCoeffs (s₁ t) k
```

and:

```lean
private theorem cosS1_hasDerivAt
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s₁ s₂ : ℝ → ℝ → ℝ}
    (H : FlooredSourceTimeData p u s₁ s₂) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => cosineCoeffs (s₁ s) k) (cosineCoeffs (s₂ t) k) t
```

The repo uses `iteratedDeriv_succ` by plain `rw [iteratedDeriv_succ]` on numerals, for example in `ShenWork/PDE/SpecialCases.lean`:

```lean
rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
```

`Filter.EventuallyEq.deriv_eq` is also already used throughout the repo in exactly this style.

## Proof body

Paste this over the `sorry`:

```lean
  -- `iteratedDeriv 2 f = deriv (iteratedDeriv 1 f)`.
  rw [iteratedDeriv_succ]
  change deriv (fun s => iteratedDeriv 1 (srcTimeCoeff p u k) s) t =
    cosineCoeffs (s₂ t) k

  -- On a neighborhood of `t`, all nearby times are positive, so the already-proved
  -- first iterated derivative identity identifies `iteratedDeriv 1 f` with
  -- `s ↦ cosineCoeffs (s₁ s) k`.
  have hnear :
      (fun s => iteratedDeriv 1 (srcTimeCoeff p u k) s) =ᶠ[𝓝 t]
        (fun s => cosineCoeffs (s₁ s) k) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact srcTimeCoeff_iteratedDeriv1 H k hs

  -- Transfer `deriv` across that local equality, then use the `d1` coefficient
  -- derivative lemma.
  have hderiv_eq :
      deriv (fun s => iteratedDeriv 1 (srcTimeCoeff p u k) s) t =
        deriv (fun s => cosineCoeffs (s₁ s) k) t :=
    Filter.EventuallyEq.deriv_eq hnear
  rw [hderiv_eq]
  exact (cosS1_hasDerivAt H k ht).deriv
```

## If the `change` line is too strict

A slightly more tolerant variant is:

```lean
  rw [iteratedDeriv_succ]
  have hnear :
      (fun s => iteratedDeriv 1 (srcTimeCoeff p u k) s) =ᶠ[𝓝 t]
        (fun s => cosineCoeffs (s₁ s) k) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact srcTimeCoeff_iteratedDeriv1 H k hs
  rw [Filter.EventuallyEq.deriv_eq hnear]
  exact (cosS1_hasDerivAt H k ht).deriv
```

I expect the first version to be more robust because it pins the post-`iteratedDeriv_succ` expression to the lambda form used by `hnear`.
