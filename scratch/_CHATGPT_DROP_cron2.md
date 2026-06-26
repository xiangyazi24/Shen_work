# Q701 (cron2): `PhysicalResolverJointC2Data`

Static repo inspection only; I did not run a Lean build.

Yes, the repo defines `PhysicalResolverJointC2Data`.

Grep target:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean:89:structure PhysicalResolverJointC2Data
```

Definition context:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  /-- Each coefficient is `C²` in time. -/
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  /-- Three-time-order coefficient bounds. -/
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  /-- The bounded-weight **value** joint majorant is summable (orders `0,1,2`). -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  /-- The bounded-weight **gradient** joint majorant is summable. -/
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

Fields:

1. `coeff_contDiff`
   ```lean
   ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
   ```

2. `coeff_bound`
   ```lean
   ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
     ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
   ```

3. `value_summable`
   ```lean
   ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
     Summable (boundedWeightJointMajorant Bt m)
   ```

4. `grad_summable`
   ```lean
   ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
     Summable (boundedWeightJointGradMajorant Bt m)
   ```
