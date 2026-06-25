# Q567 / cron1: `intervalFullSemigroupOperator` equals the explicit cosine tsum

## Verdict

Yes: the repo already has the closed-interval heat-kernel-to-spectral theorem you want, and there is already a small theorem converting the committed `unitIntervalCosineHeatValue` into the explicit `tsum` with `cosineMode`.

The useful theorem is:

```lean
ShenWork.EWA.cosineHeatSynthesis_eq_cosineHeatValue
```

from `ShenWork/Wiener/EWA/HeatFloor.lean`.  It states:

```lean
theorem cosineHeatSynthesis_eq_cosineHeatValue (c₀ : ℕ → ℝ) (t x : ℝ) :
    (∑' k : ℕ, (Real.exp (-t * ((k : ℝ) * Real.pi) ^ 2) * c₀ k)
        * ShenWork.CosineSpectrum.cosineMode k x)
      = unitIntervalCosineHeatValue t c₀ x := by
  rw [unitIntervalCosineHeatValue]
  refine tsum_congr (fun k => ?_)
  rw [unitIntervalCosineHeatPointWeight,
    unitIntervalCosineEigenvalue,
    unitIntervalCosineMode_eq_cosineMode]
  ring
```

So `unitIntervalCosineHeatValue` is definitionally a `tsum` after unfolding `unitIntervalCosineHeatValue`; to get the exact `cosineMode` and factor-order shape, use the theorem above.  The proof shows the conversion is only unfolding plus `unitIntervalCosineMode_eq_cosineMode` plus `ring`.

The closed-interval semigroup theorem is:

```lean
ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
```

from `ShenWork/PDE/IntervalFullKernelSpectralClean.lean`:

```lean
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ n, |cosineCoeffs f n| ≤ M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t f x =
      unitIntervalCosineHeatValue t (cosineCoeffs f) x
```

It is proved by taking the already-proved interior identity and extending to `[0,1]` by continuity.

## Exact route for your goal

For `f := intervalDomainLift u₀`, use:

```lean
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.Wiener.EWA.HeatFloor

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)

example
    {s x M : ℝ} {u₀ : intervalDomainPoint → ℝ}
    (hs : 0 < s)
    (hu₀cont : Continuous (intervalDomainLift u₀))
    (hM : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator s (intervalDomainLift u₀) x =
      ∑' k : ℕ,
        (Real.exp (-s * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
  calc
    intervalFullSemigroupOperator s (intervalDomainLift u₀) x
        = unitIntervalCosineHeatValue s
            (cosineCoeffs (intervalDomainLift u₀)) x := by
          exact
            ShenWork.IntervalFullKernelSpectralClean
              .intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
                (t := s) hs (f := intervalDomainLift u₀) hu₀cont hM hx
    _ = ∑' k : ℕ,
        (Real.exp (-s * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k x := by
          simpa [unitIntervalCosineEigenvalue] using
            (ShenWork.EWA.cosineHeatSynthesis_eq_cosineHeatValue
              (cosineCoeffs (intervalDomainLift u₀)) s x).symm
```

If the import environment already opens `IntervalFullKernelSpectralClean` and `EWA`, the namespace qualifiers can be shortened.

## Is `unitIntervalCosineMode = cosineMode` definitional?

There is a theorem/bridge:

```lean
unitIntervalCosineMode_eq_cosineMode
```

The heat-synthesis bridge rewrites with it explicitly:

```lean
rw [unitIntervalCosineHeatPointWeight,
  unitIntervalCosineEigenvalue,
  unitIntervalCosineMode_eq_cosineMode]
```

and its comment says both `λ_k = (kπ)^2` and `cosineMode = unitIntervalCosineMode` are definitional in this development.  In practice, use the theorem name in rewrites; it is already what the repo uses.

## File/line anchors from the search

* `IntervalFullKernelSpectralClean.lean`: theorem `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc` is at lines 110–128 in the connector fetch.
* `HeatFloor.lean`: theorem `cosineHeatSynthesis_eq_cosineHeatValue` is at lines 5–17 in the connector fetch around the theorem.
* `HeatFloor.lean`: `cosineMode_neg` and `cosineMode_add_two` are immediately after it, lines 21–33 in the same fetch, confirming the same `cosineMode` convention.

## Final answer

Use `intervalFullSemigroupOperator_eq_cosineHeatValue_Icc` for the semigroup-to-`unitIntervalCosineHeatValue` step, then use `(cosineHeatSynthesis_eq_cosineHeatValue _ s x).symm` plus `simpa [unitIntervalCosineEigenvalue]` for the explicit `tsum` with `cosineMode`.
