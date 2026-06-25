# Q617 / cron1: `unitIntervalCosineMode_eq_cosineMode`

Yes — `unitIntervalCosineMode_eq_cosineMode` exists on `chatgpt-scratch`.

Exact declaration location:

- `ShenWork/PDE/HeatKernelLpEstimates.lean:1095`

Exact signature/proof:

```lean
/-- The `unitIntervalCosineMode` used by the heat semigroup is the same
cosine mode as the spectral API in `CosineSpectrum`. -/
theorem unitIntervalCosineMode_eq_cosineMode (n : ℕ) (x : ℝ) :
    unitIntervalCosineMode n x =
      ShenWork.CosineSpectrum.cosineMode n x := by
  rfl
```

Nearby context:

```lean
/-- Derivative of the unit-interval cosine mode, imported from the spectral API. -/
theorem unitIntervalCosineMode_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (unitIntervalCosineMode n)
      (-((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x)) x := by
  simpa [unitIntervalCosineMode_eq_cosineMode] using
    ShenWork.CosineSpectrum.cosineMode_hasDerivAt n x
```

Also observed use in `ShenWork/Wiener/EWA/ResolverEvalBridge.lean`, where it rewrites the interval resolver's `unitIntervalCosineMode` basis to the Wiener `cosineMode` basis in the final `tsum_congr` step.
