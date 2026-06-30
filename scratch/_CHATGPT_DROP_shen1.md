# Q2616 shen1 — audit of removing/weakening `epsilonGap` inside `P3MoserIntegratedClosure.lean`

Repo: `xiangyazi24/Shen_work`

Branch read: default branch `main`

Files inspected:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/P3MoserActualWiring.lean
ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean
```

Scope respected: the recommendation below edits, at most, `ShenWork/PDE/P3MoserIntegratedClosure.lean`.  I do **not** recommend touching `IntervalDomainMoserLadderAtoms.lean`.

## Executive answer

The best honest in-file reduction is already essentially present: make the `upper-data-aware` path the canonical path and stop exposing `IntegratedMoserWindowUpperGapEpsilonFrontier` / `IntegratedMoserFirstCrossingLowerAverageEpsilonData` as the preferred API.

Concretely, the non-vacuous weakening is:

```text
old analytic gap:
  IntegratedMoserWindowUpperGapEpsilonFrontier

preferred weaker analytic gap:
  IntegratedMoserWindowUpperDataGapFrontier

preferred first-crossing package:
  IntegratedMoserFirstCrossingLowerAverageUpperDataGapData

consumer:
  integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

This is a real weakening, not just a rename:

```lean
-- Old/all-witness shape, too strong:
∃ eps : ℝ, 0 < eps ∧
  ∀ {Gbound Ceps : ℝ},
    IntegratedMoserWindowUpperBoundWitness
      D u rho p hwin.a hwin.b hwin.M eps Gbound Ceps →
    eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) <
      hwin.lowerBound
```

versus

```lean
-- New/upper-data-aware shape:
-- Given the fixed-window upper-bound data producer, choose one actual witness
-- and prove the strict budget gap for that selected witness.
∀ {Cnext t : ℝ},
  (hwin : IntegratedMoserHighExcursionLowerAverageWindow
    D u T rho p0 p Cnext t) →
  (∀ eps : ℝ, 0 < eps →
    IntegratedMoserWindowUpperBoundData
      D u rho p hwin.a hwin.b hwin.M eps) →
    IntegratedMoserWindowUpperGapWitness
      D u rho p hwin.a hwin.b hwin.M hwin.lowerBound
```

The second version is weaker because it does **not** demand the gap for arbitrary inflated `Gbound/Ceps` witnesses.  It may choose one witness delivered by the fixed-window upper-bound calculation.

However, there is no honest way inside `P3MoserIntegratedClosure.lean` to remove the strict budget inequality altogether.  The fixed-window upper-bound witness gives only

```lean
∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
  eps * Gbound + (b - a) * (Ceps * M)
```

and the lower-average window gives only

```lean
lowerBound ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s
```

Together these imply at most

```lean
lowerBound ≤ eps * Gbound + (b - a) * (Ceps * M)
```

not a contradiction.  The contradiction requires the genuinely additional inequality

```lean
eps * Gbound + (b - a) * (Ceps * M) < lowerBound
```

for the same selected witness.  That is the exact remaining mathematical inequality Zinan’s high-excursion/threshold plan must produce, unless a separate controlled-relative-Moser theorem exposes enough quantitative `eps ↦ Ceps` dependence to prove it.

## What is already good in the closure file

The fixed-window upper-bound witness layer is correctly shaped:

```lean
def IntegratedMoserWindowUpperBoundWitness
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps Gbound Ceps : ℝ) : Prop :=
  0 ≤ Ceps ∧
    (∫ s in a..b, integratedMoserGradientEnergy D u p s) ≤ Gbound ∧
    (∫ s in a..b, integratedMoserEnergy D u (p + rho) s) ≤
      eps * Gbound + (b - a) * (Ceps * M)
```

and the fixed-window theorem correctly packages a witness existentially:

```lean
structure IntegratedMoserWindowUpperBoundData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps : ℝ) : Prop where
  bounds :
    ∃ Gbound Ceps : ℝ,
      IntegratedMoserWindowUpperBoundWitness
        D u rho p a b M eps Gbound Ceps
```

The current theorem

```lean
integratedMoser_windowUpperBoundData_of_lowerAverageWindow
```

is exactly the fixed-window calculation that should be reused.  It is wiring/math already proved in the file: from regularity, nonnegativity, integrated dissipation, relative Moser, and the selected lower-average window geometry, it produces `IntegratedMoserWindowUpperBoundData` for every `eps > 0`.

The current preferred package

```lean
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
```

is therefore the right replacement for

```lean
IntegratedMoserFirstCrossingLowerAverageEpsilonData
```

because it replaces the old all-witness epsilon gap by the strictly weaker `upperDataGap` field:

```lean
upperDataGap :
  ∀ p, p0 ≤ p →
    0 ≤ p →
      Nonempty
        (IntegratedMoserWindowUpperDataGapFrontier D u T rho p0 p)
```

and the existing consumer

```lean
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

already collapses that package to `IntegratedMoserFirstCrossingStep`.

## Recommended next in-file reduction

I would not add a new frontier that merely restates `upper_lt_lower` under a new name.  The clean next change, if you want one, is just a surface wrapper that makes the upper-data-aware path the obvious entry point and removes `epsilonGap` from the theorem signature.

Suggested exact theorem name:

```lean
integratedMoserFirstCrossingStep_of_lowerAverage_and_upperDataGapFrontiers
```

Suggested code:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Preferred direct consumer for the high-excursion route: lower-average
thickness plus an upper-data-aware strict-gap chooser.  This wrapper deliberately
has no `IntegratedMoserWindowUpperGapEpsilonFrontier` argument. -/
theorem integratedMoserFirstCrossingStep_of_lowerAverage_and_upperDataGapFrontiers
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hrho_pos : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hlower :
      ∀ p, p0 ≤ p →
        0 ≤ p →
        LpPowerBoundedBefore D p T u →
          Nonempty
            (Σ Cnext : ℝ,
              IntegratedMoserHighExcursionLowerAverageWindowFrontier
                D u T rho p0 p Cnext))
    (hupperDataGap :
      ∀ p, p0 ≤ p →
        0 ≤ p →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier D u T rho p0 p)) :
    IntegratedMoserFirstCrossingStep D u T rho p0 :=
  integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
    { regularity := hreg
      energyNonneg := hnonneg
      dissipation := hinteg
      relative := hrel
      rho_pos := hrho_pos
      p0_nonneg := hp0_nonneg
      lowerAverage := hlower
      upperDataGap := hupperDataGap }

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

Classification: **pure wiring only**.  It adds no new mathematics and should be acceptable inside `P3MoserIntegratedClosure.lean`.  It is useful because it makes the preferred API explicit and avoids new callers depending on `IntegratedMoserFirstCrossingLowerAverageEpsilonData`.

## Why the old `epsilonGap` should remain compatibility-only

The existing conversion

```lean
IntegratedMoserFirstCrossingLowerAverageEpsilonData.toUpperDataGapData
```

is fine as a backward-compatibility adapter.  But new work should target

```lean
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
```

or the wrapper above, not the old epsilon package.

The old epsilon frontier is too strong because it quantifies over every witness satisfying the upper-bound predicate.  Since larger `Gbound` or `Ceps` can often be made to satisfy the upper-bound inequality, a universal strict gap against all such witnesses is generally not stable.

The upper-data-aware frontier is the honest weakening: it asks for a strict gap only for one selected upper-bound witness coming from the already-proved fixed-window calculation.

## What would be vacuous and should not be added

Do **not** add a structure like this and pretend it removed the gap:

```lean
structure IntegratedMoserWindowBudgetFrontier ... where
  produce :
    ∀ hwin,
      ∃ eps Gbound Ceps,
        0 < eps ∧
        IntegratedMoserWindowUpperBoundWitness
          D u rho p hwin.a hwin.b hwin.M eps Gbound Ceps ∧
        eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) <
          hwin.lowerBound
```

That is just `IntegratedMoserWindowUpperGapWitnessFrontier` / `IntegratedMoserWindowUpperDataGapFrontier` in a different coat unless it is paired with a genuinely new analytic theorem explaining why the strict inequality follows from the high-excursion threshold construction.

Also do **not** claim that

```lean
integratedMoser_windowUpperBoundData_of_lowerAverageWindow
```

plus

```lean
hwin.lowerAverage
```

is enough to derive contradiction.  It is not.  Those two statements are consistent whenever

```lean
hwin.lowerBound ≤ ∫Y ≤ budget
```

and that is exactly the non-contradictory ordering.

## Exact remaining mathematical inequality

For each selected high-excursion lower-average window

```lean
hwin : IntegratedMoserHighExcursionLowerAverageWindow
  D u T rho p0 p Cnext t
```

and for the fixed-window upper-bound data produced by

```lean
fun eps heps =>
  integratedMoser_windowUpperBoundData_of_lowerAverageWindow
    hreg hnonneg hinteg hrel hp hp_nonneg hrho_pos hwin heps
```

Zinan’s high-excursion/threshold plan, or a controlled-relative-Moser constant theorem, must produce:

```lean
∃ eps Gbound Ceps : ℝ,
  0 < eps ∧
  IntegratedMoserWindowUpperBoundWitness
    D u rho p hwin.a hwin.b hwin.M eps Gbound Ceps ∧
  eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) <
    hwin.lowerBound
```

Equivalently, using the already-proved upper-bound data producer as an argument, it must produce:

```lean
IntegratedMoserWindowUpperGapWitness
  D u rho p hwin.a hwin.b hwin.M hwin.lowerBound
```

from

```lean
∀ eps : ℝ, 0 < eps →
  IntegratedMoserWindowUpperBoundData
    D u rho p hwin.a hwin.b hwin.M eps
```

This inequality is **new math**, not wiring.  The wiring is everything after it:

```text
IntegratedMoserWindowUpperDataGapFrontier
  → integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
  → IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.toLowerUpperFrontiers
  → integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

## Relationship to the other inspected files

`P3MoserActualWiring.lean` consumes an `IntegratedMoserFirstCrossingStep` as the atom for the actual integrated route.  It does not need to know whether the step came from `epsilonGap`, `upperDataGap`, or a future Zinan producer.

`IntervalDomainMoserLadderAtoms.lean` has residual packages that consume either an `IntegratedMoserFirstCrossingStep`, an `IntegratedMoserFirstCrossingFromWindowFrontier`, or split lower/upper frontiers.  The current consumption path already routes through the closure-file wrappers.  I would not edit it for this reduction.

## Bottom line

Inside `P3MoserIntegratedClosure.lean`, the honest reduction is:

1. Treat `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData` as the preferred API.
2. Keep `IntegratedMoserFirstCrossingLowerAverageEpsilonData` only as compatibility.
3. Optionally add the direct wrapper `integratedMoserFirstCrossingStep_of_lowerAverage_and_upperDataGapFrontiers` shown above.
4. Do not claim the fixed-window upper-bound witnesses eliminate the strict gap.  They only supply the selected upper witness.  The remaining mathematical inequality is exactly the selected-budget strict inequality:

```lean
eps * Gbound + (hwin.b - hwin.a) * (Ceps * hwin.M) < hwin.lowerBound
```

for a witness actually produced by the fixed-window upper-bound data.
