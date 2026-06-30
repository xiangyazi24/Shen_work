# Q2500 shen1 — honest analytic frontier interface for integrated Moser first-crossing

Repo: `xiangyazi24/Shen_work`

Audited baseline: commit `9d9250e6fbc8e0efb30a61130cd0b6e471ed4321`.

Target file/namespace for eventual interfaces:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

## Goal

Design the minimal honest analytic frontier needed to turn the fixed-window integrated Moser estimates into the atom currently consumed downstream:

```lean
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u
```

The frontier must not assert the false route

```lean
∫ s in a..b, Y_{p+rho} s ≤ K  →  LpPowerBoundedBefore D (p + rho) T u
```

A time-integral bound alone permits arbitrarily narrow spikes.  The missing analytic content is a high-excursion/thickness/lower-average or absolute-continuity mechanism that turns a hypothetical large pointwise value into a quantitatively useful lower bound on some time window.

## Recommended minimal decomposition

There are three layers.

1. **Fixed-window upper estimate provider** — pure plumbing from the existing helpers and the Q2497 precrossing/window data.
2. **First-crossing/topological scaffolding** — mostly pure Lean real-analysis plumbing.
3. **High-excursion contradiction frontier** — real analytic assumption.  This is the minimal honest bridge from window averages to pointwise control.

The final theorem should be a wrapper whose proof is only plumbing once (1), (2), and (3) are supplied.

## Common local abbreviations

These are optional but make the frontier statements readable.

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

/-- `Y_p(t) = ∫ u(t)^p`. -/
def integratedMoserEnergy
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (p t : ℝ) : ℝ :=
  D.integral (fun x => (u t x) ^ p)

/-- `G_p(t) = ∫ |∇(u(t)^(p/2))|²`. -/
def integratedMoserGradientEnergy
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (p t : ℝ) : ℝ :=
  D.integral (fun x =>
    (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification: pure notation/plumbing.

## Layer 1: fixed-window upper estimate provider

This layer is not the hard frontier.  It packages the current fixed-window helpers plus the Q2497 precrossing record.  If Q2497’s `IntegratedMoserPrecrossingIntervalData` and `IntegratedMoserWindowUpperBoundData` have been committed, the following is just an interface for a theorem that should be proved from existing helpers.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Pure-plumbing provider: on every honest precrossing window, the existing
integrated-Moser and relative-Moser fixed-window estimates produce an upper
bound for the higher-power time integral.

This should be derivable from:
* `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds`,
* `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound`, and
* `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound`.
-/
structure IntegratedMoserWindowUpperEstimateProvider
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  upper :
    ∀ {p a b M eps : ℝ},
      IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b M →
      0 < eps →
        IntegratedMoserWindowUpperBoundData D u rho p a b M eps

/-- Shape only: this is the expected pure-plumbing constructor from the current
fixed-window helper family.  Do not treat this as a new analytic assumption. -/
-- theorem integratedMoserWindowUpperEstimateProvider_of_integrated_dissipation_and_relative
--     {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
--     {T rho p0 : ℝ}
--     (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
--     (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
--     IntegratedMoserWindowUpperEstimateProvider D u T rho p0

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification: pure plumbing.  The only dependency is that the precrossing/window data layer exists.

## Layer 2: first-crossing/topological scaffolding

This is the natural topology around “suppose the next exponent is not bounded.”  It is not the hard PDE/Moser input, but it can be tedious Lean work.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- `τ` is the first time in `(0,T)` at which `Y` reaches level `B`. -/
def MoserFirstCrossingAt (Y : ℝ → ℝ) (T B τ : ℝ) : Prop :=
  0 < τ ∧ τ < T ∧ Y τ = B ∧
    ∀ s, 0 < s → s < τ → Y s < B

/-- Pure topology frontier/plumbing: from continuity, initial strict sublevel,
and later exceedance, obtain a first crossing. -/
-- theorem exists_moserFirstCrossingAt_of_continuousOn_exceeds
--     {Y : ℝ → ℝ} {T B : ℝ}
--     (hT : 0 < T)
--     (hcont : ContinuousOn Y (Set.Icc (0 : ℝ) T))
--     (hinit : Y 0 < B)
--     (hexceeds : ∃ t, 0 < t ∧ t < T ∧ B ≤ Y t) :
--     ∃ τ, MoserFirstCrossingAt Y T B τ

/-- Pure topology/plumbing: if no first crossing above an initial sublevel can
exist, then the function is bounded by that level on `(0,T)`. -/
-- theorem LpPowerBoundedBefore_of_no_higherPower_firstCrossing
--     {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
--     {T q B : ℝ}
--     (hno : ¬ ∃ τ,
--       MoserFirstCrossingAt
--         (fun t => integratedMoserEnergy D u q t) T B τ)
--     (hT : 0 < T)
--     (hcont : ContinuousOn
--       (fun t => integratedMoserEnergy D u q t) (Set.Icc (0 : ℝ) T))
--     (hinit : integratedMoserEnergy D u q 0 < B) :
--     LpPowerBoundedBefore D q T u

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification: pure Lean real-analysis plumbing.  These statements require no Moser-specific analytic estimate beyond continuity.

## Layer 3A: preferred minimal hard frontier — high-excursion contradiction

This is the cleanest minimal analytic interface.  It does not try to expose a fake formula for the window length or lower average.  Instead, it says: whenever a high first crossing occurs, the analytic high-excursion machinery can choose a window and an `eps` such that **any** fixed-window upper estimate on that window contradicts the high excursion.

This is intentionally the hard frontier.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Real analytic frontier: a high first crossing of `Y_{p+rho}` can be converted
into a precrossing window whose lower-excursion information contradicts the
fixed-window integrated-Moser upper bound.

The field is phrased against `IntegratedMoserWindowUpperBoundData`; hence it
cannot be misused as a direct time-integral-to-pointwise conversion. -/
structure IntegratedMoserHighExcursionContradictionFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  choose_level_and_contradict :
    ∀ {p Cp C0 : ℝ},
      p0 ≤ p →
      0 ≤ p →
      0 < rho →
      -- current exponent already bounded on the full horizon
      (∀ t, 0 < t → t < T → integratedMoserEnergy D u p t ≤ Cp) →
      -- initial higher-energy is below `C0`
      integratedMoserEnergy D u (p + rho) 0 ≤ C0 →
      ∃ B : ℝ, C0 < B ∧
        ∀ {τ : ℝ},
          MoserFirstCrossingAt
            (fun t => integratedMoserEnergy D u (p + rho) t) T B τ →
          ∃ a b M eps : ℝ,
            0 < eps ∧
            M = Cp ∧
            -- the window is honest/interior and has current `p` control
            (∀ hI : IntegratedMoserPrecrossingIntervalData
                D u T rho p0 p a b M,
              -- every fixed-window upper bound on this window contradicts
              -- the high-excursion/lower-average information.
              IntegratedMoserWindowUpperBoundData D u rho p a b M eps → False)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification of fields:

* `p0 ≤ p`, `0 ≤ p`, `0 < rho`: plumbing/parameters.
* current bound `∀t, Y_p(t) ≤ Cp`: plumbing from `LpPowerBoundedBefore`.
* initial higher-energy bound `Y_{p+rho}(0) ≤ C0`: plumbing from `IntegratedMoserFirstCrossingRegularity.initialPowerBound`.
* existence of `B` and the contradiction for all upper-bound data: real analytic assumption.  This is where high-excursion thickness, lower-average estimates, or absolute-continuity/modulus data must enter.

Why this is minimal: the final first-crossing proof only needs a contradiction to every possible crossing.  It does not need to know the exact lower-average formula as long as the frontier is explicitly analytic and tied to a genuine first-crossing window.

## Layer 3B: more explicit decomposed hard frontier — lower-average plus separation

If you want the analytic content to be more inspectable, split Layer 3A into two structures.  This is less minimal but more informative.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Real analytic frontier: high first crossing produces a nontrivial window on
which the higher-power energy has a lower time-average. -/
structure IntegratedMoserHighExcursionLowerAverageFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  lower_average :
    ∀ {p Cp B τ : ℝ},
      p0 ≤ p →
      0 ≤ p →
      0 < rho →
      (∀ t, 0 < t → t < T → integratedMoserEnergy D u p t ≤ Cp) →
      MoserFirstCrossingAt
        (fun t => integratedMoserEnergy D u (p + rho) t) T B τ →
      ∃ a b M eps Lower : ℝ,
        0 < eps ∧ M = Cp ∧ 0 < Lower ∧
        (∀ hI : IntegratedMoserPrecrossingIntervalData
            D u T rho p0 p a b M,
          Lower ≤
            ∫ s in a..b, integratedMoserEnergy D u (p + rho) s)

/-- Quantitative separation frontier: the lower-average information obtained
from a high excursion dominates the fixed-window upper estimate. -/
structure IntegratedMoserUpperLowerSeparationFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  separate :
    ∀ {p Cp C0 B a b M eps Lower : ℝ},
      p0 ≤ p →
      0 ≤ p →
      0 < rho →
      C0 < B →
      M = Cp →
      0 < eps →
      0 < Lower →
      (Lower ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s) →
      IntegratedMoserWindowUpperBoundData D u rho p a b M eps →
      False

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification:

* `IntegratedMoserHighExcursionLowerAverageFrontier`: real analytic.  It is a thickness/lower-average theorem.
* `IntegratedMoserUpperLowerSeparationFrontier`: usually real analytic unless all constants and `eps ↦ Ceps` dependence are made quantitative.  With only existential `Ceps` from `RelativeMoserInterpolationBefore`, this is not mere algebra.

Layer 3A is better for a minimal route-level interface.  Layer 3B is better if the analytic proof is being developed and audited in smaller pieces.

## Optional absolute-continuity producer interface

Absolute continuity is not by itself enough unless it gives a quantitative high-excursion thickness.  The honest AC-style producer should imply Layer 3B, not replace it with a vague continuity assumption.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Optional real analytic producer: absolute-continuity/modulus data strong
enough to yield high-excursion lower-average windows.

This should be used only as a producer for
`IntegratedMoserHighExcursionLowerAverageFrontier`, not directly as a fake
pointwise extraction theorem. -/
structure IntegratedMoserHigherPowerThicknessFromAC
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  thickness :
    ∀ {p Cp B τ : ℝ},
      p0 ≤ p →
      0 ≤ p →
      0 < rho →
      (∀ t, 0 < t → t < T → integratedMoserEnergy D u p t ≤ Cp) →
      MoserFirstCrossingAt
        (fun t => integratedMoserEnergy D u (p + rho) t) T B τ →
      ∃ a b theta : ℝ,
        0 < theta ∧
        a < b ∧ 0 < a ∧ b < T ∧
        (b - a) * theta * B ≤
          ∫ s in a..b, integratedMoserEnergy D u (p + rho) s

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification: real analytic.  Proving this probably requires absolute continuity plus quantitative derivative/modulus bounds for `Y_{p+rho}` near high excursions.  Plain `ContinuousOn` or `AbsolutelyContinuousOn` without quantitative control is not enough.

## Final theorem shape using the minimal frontier

Once Q2497 plumbing exists, the final wrapper can be shaped as follows.  This code is a theorem **shape only**; it should not be committed with a fake proof.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Shape only.  The proof should be plumbing once the high-excursion
contradiction frontier is supplied. -/
-- theorem integratedMoserFirstCrossingStep_of_windowUpper_and_highExcursion
--     {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
--     {T rho p0 : ℝ}
--     (hT : 0 < T)
--     (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
--     (hupper : IntegratedMoserWindowUpperEstimateProvider D u T rho p0)
--     (hcrossTopo :
--       ∀ {p B : ℝ}, p0 ≤ p →
--         ContinuousOn
--           (fun t => integratedMoserEnergy D u (p + rho) t)
--           (Set.Icc (0 : ℝ) T) →
--         integratedMoserEnergy D u (p + rho) 0 < B →
--         (∃ t, 0 < t ∧ t < T ∧
--           B ≤ integratedMoserEnergy D u (p + rho) t) →
--         ∃ τ,
--           MoserFirstCrossingAt
--             (fun t => integratedMoserEnergy D u (p + rho) t) T B τ)
--     (hexcur : IntegratedMoserHighExcursionContradictionFrontier
--       D u T rho p0) :
--     IntegratedMoserFirstCrossingStep D u T rho p0

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Remarks:

* `hcrossTopo` can later be replaced by the concrete theorem `exists_moserFirstCrossingAt_of_continuousOn_exceeds` once proved.
* `hupper` is derivable from the fixed-window Moser estimates and should not be a final analytic assumption.
* `hexcur` is the real analytic floor.

## Dependency DAG

### Pure plumbing

```text
integratedMoserEnergy / integratedMoserGradientEnergy
  ↓
Q2497 precrossing/window data constructors
  ↓
IntegratedMoserWindowUpperBoundData
  ↓
IntegratedMoserWindowUpperEstimateProvider_of_integrated_dissipation_and_relative
```

```text
MoserFirstCrossingAt
  ↓
exists_moserFirstCrossingAt_of_continuousOn_exceeds
  ↓
LpPowerBoundedBefore_of_no_higherPower_firstCrossing
```

```text
IntegratedMoserFirstCrossingRegularity.initialPowerBound
  ↓
choose C0 for Y_{p+rho}(0)
```

### Real analytic assumptions

```text
High-excursion/thickness OR AC/modulus data
  ↓
IntegratedMoserHighExcursionLowerAverageFrontier
  + IntegratedMoserUpperLowerSeparationFrontier
  ↓
IntegratedMoserHighExcursionContradictionFrontier
```

or directly:

```text
IntegratedMoserHighExcursionContradictionFrontier
```

### Final wrapper

```text
LpPowerBoundedBefore D p T u
  ↓ current Cp extraction (plumbing)
Assume unbounded Y_{p+rho}
  ↓ first-crossing topology (plumbing)
first crossing τ at level B
  ↓ high-excursion contradiction frontier (analytic)
window upper estimate provider (plumbing from fixed-window Moser)
  ↓ contradiction
no crossing above B
  ↓ LpPowerBoundedBefore D (p + rho) T u
```

## What not to add

Do not add any theorem with one of these shapes:

```lean
-- false without thickness/modulus data
theorem LpPowerBoundedBefore_of_timeIntegral_bound ... :
    LpPowerBoundedBefore D (p + rho) T u := ...

-- too tautological to be useful as an analytic frontier
structure IntegratedMoserFirstCrossingFrontier where
  step : IntegratedMoserFirstCrossingStep D u T rho p0
```

The first is mathematically false in this level of generality.  The second is honest but useless: it hides the entire problem in a field with the exact target conclusion.  The recommended minimal frontier is `IntegratedMoserHighExcursionContradictionFrontier`, because it names the actual missing mechanism while remaining just strong enough to make the final first-crossing wrapper routine.

## Suggested `#print axioms` targets after later implementation

```lean
#print axioms IntegratedMoserWindowUpperEstimateProvider_of_integrated_dissipation_and_relative
#print axioms exists_moserFirstCrossingAt_of_continuousOn_exceeds
#print axioms LpPowerBoundedBefore_of_no_higherPower_firstCrossing
#print axioms integratedMoserFirstCrossingStep_of_windowUpper_and_highExcursion
```

The final theorem should list the high-excursion frontier as a hypothesis.  It should not depend on hidden axioms or an unproved direct time-integral-to-pointwise conversion.
