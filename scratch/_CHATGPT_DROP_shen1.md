# Q2903 (shen1) — anchored gradient time-integrability from raw integrability

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target files: `ShenWork/PDE/P3MoserEnergyContinuity.lean`, `ShenWork/PDE/P3MoserRegularityProducer.lean`  
Source edit requested: none; answer file only.

## Verdict

Yes. The anchored gradient time-integrability is honestly derivable from the raw one, because the anchored and raw time integrands differ only at `t = 0`, and `{0}` is `volume`-null. This is exactly an **a.e. congruence** problem under the restricted measure

```lean
volume.restrict (Set.uIcc (0 : ℝ) T)
```

Do **not** use `IntegrableOn.congr_fun` as the primary route: it requires pointwise equality on the set, and `0 ∈ Set.uIcc 0 T`. The right route is `Integrable.congr` / `IntegrableOn` unfolded to `Integrable _ (volume.restrict s)` with an `=ᵐ[...]` proof.

No positivity, no `0 < T`, no regularity of `u₀`, and no gradient facts at `t = 0` are needed for this transfer. Integrability ignores one null time value.

## Recommended helper definition

This helper shortens all statements and avoids duplicating the long integrand.

```lean
import ShenWork.PDE.P3MoserEnergyContinuity
import ShenWork.PDE.P3MoserRegularityProducer

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
open ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
open scoped Topology Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- The Moser gradient-energy time integrand used by the regularity producer. -/
def intervalDomainMoserGradientEnergyTimeIntegrand
    (u : ℝ → intervalDomain.Point → ℝ) (p : ℝ) (t : ℝ) : ℝ :=
  intervalDomain.integral (fun x =>
    (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

If you prefer not to add a definition, inline it in the theorem. The proof is the same but much less readable.

## Core AE equality lemma

This is the main local lemma. It says the raw and anchored gradient time integrands are equal a.e. on the unordered interval.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Re-anchoring at `t = 0` does not change the Moser gradient-energy integrand
a.e. on any time interval, because the only changed time is the null singleton
`{0}`. -/
theorem intervalDomain_moserGradientEnergyTimeIntegrand_withInitialSlice_ae_eq_raw
    {T p : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ} :
    (fun t =>
      intervalDomainMoserGradientEnergyTimeIntegrand
        (intervalDomainWithInitialSlice u₀ u) p t)
      =ᵐ[volume.restrict (Set.uIcc (0 : ℝ) T)]
    (fun t => intervalDomainMoserGradientEnergyTimeIntegrand u p t) := by
  rw [ae_restrict_iff' measurableSet_uIcc]
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by
    simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
  filter_upwards [hne] with t ht_ne ht_mem
  have hslice :
      (fun y : intervalDomain.Point =>
          ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) =
        (fun y : intervalDomain.Point => (u t y) ^ (p / 2)) := by
    funext y
    simp [intervalDomainWithInitialSlice, ht_ne]
  simp [intervalDomainMoserGradientEnergyTimeIntegrand, hslice]

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

Notes:

* `ht_mem` is intentionally unused; it is supplied by `ae_restrict_iff'` after restricting to `Set.uIcc 0 T`.
* `measurableSet_uIcc` avoids a case split on `T`. Do not rewrite `Set.uIcc 0 T` to `Set.Icc 0 T` unless you have `0 ≤ T` and really need it.
* If `simp` does not rewrite under the lambda, the explicit `hslice` equality above fixes it.

## Main transfer theorem

This is the theorem I recommend adding near the anchored producer, either in `P3MoserEnergyContinuity.lean` or in `P3MoserRegularityProducer.lean` if the gradient-data structure lives there.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Raw gradient time-integrability transfers to the re-anchored representative:
the two time integrands differ only at `t = 0`, a null time. -/
theorem intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw
    {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hraw :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t => intervalDomainMoserGradientEnergyTimeIntegrand u p t)
          (Set.uIcc (0 : ℝ) T) volume) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomainMoserGradientEnergyTimeIntegrand
            (intervalDomainWithInitialSlice u₀ u) p t)
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hraw' : Integrable
      (fun t => intervalDomainMoserGradientEnergyTimeIntegrand u p t)
      (volume.restrict (Set.uIcc (0 : ℝ) T)) :=
    hraw p hp
  have hae :=
    intervalDomain_moserGradientEnergyTimeIntegrand_withInitialSlice_ae_eq_raw
      (T := T) (p := p) (u₀ := u₀) (u := u)
  -- `hae` is anchored = raw.  `Integrable.congr` orientation may require `.symm`
  -- depending on the local elaboration.  The following orientation is usually right:
  exact hraw'.congr hae.symm

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

If the last line complains about orientation, use:

```lean
  exact hraw'.congr hae
```

and define the AE lemma in the opposite orientation:

```lean
(fun t => intervalDomainMoserGradientEnergyTimeIntegrand u p t)
  =ᵐ[volume.restrict (Set.uIcc (0 : ℝ) T)]
(fun t => intervalDomainMoserGradientEnergyTimeIntegrand
  (intervalDomainWithInitialSlice u₀ u) p t)
```

The robust pattern is:

```lean
  change Integrable
      (fun t => intervalDomainMoserGradientEnergyTimeIntegrand
        (intervalDomainWithInitialSlice u₀ u) p t)
      (volume.restrict (Set.uIcc (0 : ℝ) T))
  exact hraw'.congr hae.symm
```

where `hae : anchored =ᵐ[...] raw`.

## Direct theorem without helper definition

If you do not want to introduce `intervalDomainMoserGradientEnergyTimeIntegrand`, use this direct theorem. It is longer but matches the current producer field exactly.

```lean
theorem intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw_direct
    {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u : ℝ → intervalDomain.Point → ℝ}
    (hraw :
      ∀ p, p0 ≤ p →
        IntegrableOn
          (fun t =>
            intervalDomain.integral (fun x =>
              (intervalDomain.gradNorm
                (fun y => (u t y) ^ (p / 2)) x) ^ 2))
          (Set.uIcc (0 : ℝ) T) volume) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hraw' : Integrable
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      (volume.restrict (Set.uIcc (0 : ℝ) T)) :=
    hraw p hp
  have hae :
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
        =ᵐ[volume.restrict (Set.uIcc (0 : ℝ) T)]
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => (u t y) ^ (p / 2)) x) ^ 2)) := by
    rw [ae_restrict_iff' measurableSet_uIcc]
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by
      simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
    filter_upwards [hne] with t ht_ne ht_mem
    have hslice :
        (fun y : intervalDomain.Point =>
            ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) =
          (fun y : intervalDomain.Point => (u t y) ^ (p / 2)) := by
      funext y
      simp [intervalDomainWithInitialSlice, ht_ne]
    simp [hslice]
  change Integrable
      (fun t =>
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm
            (fun y => ((intervalDomainWithInitialSlice u₀ u) t y) ^ (p / 2)) x) ^ 2))
      (volume.restrict (Set.uIcc (0 : ℝ) T))
  exact hraw'.congr hae.symm
```

Again, if `Integrable.congr` orientation differs locally, replace `hae.symm` by `hae` and orient the AE equality accordingly.

## How to use in the anchored producer

Your anchored producer can ask for raw gradient time-integrability instead:

```lean
(hgradRaw :
  ∀ p, p0 ≤ p →
    IntegrableOn
      (fun t => intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      (Set.uIcc (0 : ℝ) T) volume)
```

and fill the anchored field by:

```lean
gradientTimeIntegrable :=
  intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw hgradRaw
```

or, without the helper integrand definition:

```lean
gradientTimeIntegrable :=
  intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw_direct hgradRaw
```

## Pitfalls

1. `Set.uIcc 0 T` always contains `0`, including when `T < 0` and when `T = 0`. So pointwise `IntegrableOn.congr_fun` over the set is not enough.

2. Do not try to prove the anchored and raw gradient integrands are equal at `t = 0`. They are generally not equal: the anchored slice is `u₀`, while the raw slice is `u 0`.

3. Do not unfold or prove anything about `intervalDomain.gradNorm` at `u₀`. The anchored time integrand at `0` can be ignored by a.e. congruence. This avoids unnecessary spatial regularity assumptions on `u₀`.

4. `ae_restrict_iff' measurableSet_uIcc` is the clean way to work under `volume.restrict (Set.uIcc 0 T)`. The singleton-null fact can be obtained by:

```lean
have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) := by
  simp [MeasureTheory.ae_iff, MeasureTheory.measure_singleton]
```

5. If `measurableSet_uIcc` is not in scope, import the interval integral/basic measure files already imported by `P3MoserEnergyContinuity`, or rewrite via `Set.uIcc_of_le` only if you have a sign hypothesis. The theorem above does not need a sign hypothesis, so prefer `measurableSet_uIcc`.

## Bottom line

The anchored producer should take the raw gradient integrability field and derive the anchored one internally by AE congruence. This is an honest cleanup: endpoint power-energy continuity needs anchoring, but time-integrability of the gradient energy is invariant under changing a single time slice.
