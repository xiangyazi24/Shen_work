# Q873 / cron1: `cosineCoeffs_hasDerivAt_of_smooth_param` location

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Ref inspected: `main`

## Answer

Yes.  The theorem exists.

File:

```text
ShenWork/Paper2/IntervalMildPicardRegularity.lean
```

Line:

```text
494
```

Namespace / full name:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
```

Exact signature:

```lean
theorem cosineCoeffs_hasDerivAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {τ δ : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hf_cont : ∀ᶠ s in 𝓝 τ, ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ∀ s ∈ Metric.ball τ δ,
        HasDerivAt (fun r => f r x) (f' s x) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc (τ - δ) (τ + δ) ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' τ) n) τ := by
```

This is exactly the theorem that differentiates a cosine coefficient under the integral sign:

```lean
HasDerivAt (fun s => cosineCoeffs (f s) n)
  (cosineCoeffs (f' τ) n) τ
```

under local continuity, pointwise `HasDerivAt` on the interior, and joint continuity of the derivative slice on the compact slab.

## Related integral identity nearby

The theorem uses the real integral formula:

```lean
theorem cosineCoeffs_eq_factor_mul_integral (f : ℝ → ℝ) (n : ℕ) :
    cosineCoeffs f n =
      (if n = 0 then 1 else 2) *
        ∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x) * f x
```

This appears immediately before the time-Leibniz theorem in the same file.