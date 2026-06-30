# Q2520 shen1 — audit and next producer split for high-excursion frontier

Repo: `xiangyazi24/Shen_work`

Target file/namespace:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Visible-source caveat: the GitHub-visible `main` copy I can inspect still lags the described local patch.  This audit is therefore based on the prompt’s description of the passing local patch and the fixed-window APIs already visible around commit `9d9250e6`.

## 1. Honesty audit

The split still looks mathematically honest **provided the contradiction-window definition ties the strict upper/lower gap to the same `Gbound` and `Ceps` witnesses used in the fixed-window upper estimate**.

The honest part is clear:

* `IntegratedMoserWindowUpperBoundData` proves only a fixed-window time-integral upper bound:

```lean
∃ Gbound Ceps, 0 ≤ Ceps ∧
  ∫ G_p ≤ Gbound ∧
  ∫ Y_{p+rho} ≤ eps * Gbound + (b - a) * (Ceps * M)
```

* `IntegratedMoserHighExcursionContradictionWindowFrontier` does not say “time-integral bound implies pointwise bound.”  It says a **pointwise high excursion** produces a window with a lower average and a strict gap against the fixed-window upper estimate.

That is the right mathematical shape.  The high-excursion/thickness/gap field is exactly the genuine analytic frontier.

### The main API hazard: existential upper data

Because `IntegratedMoserWindowUpperBoundData` is a `Prop` existential, it has no projections.  A downstream strict gap must not be stated as a universal claim over all possible upper witnesses, because arbitrary huge `Ceps` values can trivially satisfy the upper inequality and destroy the gap.

Bad shape:

```lean
-- Too strong / usually false: huge Ceps can satisfy the upper-bound inequality.
∀ Gbound Ceps,
  0 ≤ Ceps →
  ∫ G_p ≤ Gbound →
  ∫ Y_{p+rho} ≤ eps * Gbound + (b - a) * (Ceps * M) →
  eps * Gbound + (b - a) * (Ceps * M) < lower
```

Good shape:

```lean
-- Good: the contradiction window existentially carries the same witnesses used
-- by the upper estimate and the strict gap.
∃ Gbound Ceps, 0 ≤ Ceps ∧
  ∫ G_p ≤ Gbound ∧
  ∫ Y_{p+rho} ≤ eps * Gbound + (b - a) * (Ceps * M) ∧
  lower ≤ ∫ Y_{p+rho} ∧
  eps * Gbound + (b - a) * (Ceps * M) < lower
```

If the local `IntegratedMoserHighExcursionContradictionWindow` is already shaped this way, it is good.  If it instead stores only

```lean
upperData : IntegratedMoserWindowUpperBoundData ...
lowerAverage : lower ≤ ∫ Y_{p+rho}
upper_lt_lower : ?
```

then check that `upper_lt_lower` has the actual existential witnesses in scope.  If not, refactor to a witness-level predicate as below.

## 2. Recommended witness-level helper layer

Even if you keep `IntegratedMoserWindowUpperBoundData` as a `Prop` existential, introduce a witness predicate for clarity.  This gives the later gap theorem a precise target.

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

/-- Witness-level form of the fixed-window upper estimate.  This is pure
packaging; it makes the existential witnesses in
`IntegratedMoserWindowUpperBoundData` explicit. -/
def IntegratedMoserWindowUpperBoundWitness
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps Gbound Ceps : ℝ) : Prop :=
  0 ≤ Ceps ∧
    (∫ s in a..b, integratedMoserGradientEnergy D u p s) ≤ Gbound ∧
    (∫ s in a..b, integratedMoserEnergy D u (p + rho) s) ≤
      eps * Gbound + (b - a) * (Ceps * M)

/-- Suggested equivalent definition if `IntegratedMoserWindowUpperBoundData` is
still easy to adjust.  If downstream already uses the existing name, keep the
existing name and add this as a lemma instead. -/
def IntegratedMoserWindowUpperBoundData' 
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M eps : ℝ) : Prop :=
  ∃ Gbound Ceps,
    IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps Gbound Ceps

/-- Pure contradiction eliminator once the same witnesses satisfy both the upper
bound and the strict upper/lower gap. -/
theorem false_of_windowUpperBoundWitness_lowerAverage_gap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {rho p a b M eps Gbound Ceps lower : ℝ}
    (hupper :
      IntegratedMoserWindowUpperBoundWitness
        D u rho p a b M eps Gbound Ceps)
    (hlower :
      lower ≤
        ∫ s in a..b, integratedMoserEnergy D u (p + rho) s)
    (hgap : eps * Gbound + (b - a) * (Ceps * M) < lower) :
    False := by
  rcases hupper with ⟨_hCeps, _hG, hYupper⟩
  linarith

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification: pure plumbing.  This layer adds no analytic claim.  It only prevents confusion caused by existential `Prop` data.

## 3. Next producer theorem split

The current frontier says a high excursion above `Cnext` produces a contradiction window.  To actually prove that frontier, split it into two genuine producer frontiers plus one pure assembler.

### 3.1 High-excursion lower-average window producer

This is the real “thickness” or “absolute-continuity/modulus” analytic step.  It should not mention `Ceps`.  It only turns pointwise high excursion into a window with a lower time-average and the geometry needed for the fixed-window plumbing.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Window selected from a high excursion, before applying the fixed-window upper
estimate. -/
structure IntegratedMoserHighExcursionLowerAverageWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cp Cnext t : ℝ) : Prop where
  a b lower : ℝ
  hab : a < b
  ha_pos : 0 < a
  hb_lt : b < T
  haT : a ∈ Set.Icc (0 : ℝ) T
  hbT : b ∈ Set.Icc a T
  currentEnergy_le_Icc :
    ∀ s ∈ Set.Icc a b,
      integratedMoserEnergy D u p s ≤ Cp
  lowerAverage :
    lower ≤
      ∫ s in a..b, integratedMoserEnergy D u (p + rho) s

/-- Real analytic frontier: every sufficiently high pointwise excursion of
`Y_{p+rho}` produces a lower-average window.

This is where continuity alone is insufficient; the proof needs a quantitative
high-excursion thickness, absolute-continuity/modulus, or equivalent PDE input. -/
structure IntegratedMoserHighExcursionLowerAverageWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  produce :
    ∀ {p Cp Cnext t : ℝ},
      p0 ≤ p →
      0 ≤ p →
      0 < rho →
      (∀ s, 0 < s → s < T → integratedMoserEnergy D u p s ≤ Cp) →
      Cnext < integratedMoserEnergy D u (p + rho) t →
      0 < t → t < T →
        IntegratedMoserHighExcursionLowerAverageWindow
          D u T rho p0 p Cp Cnext t

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification:

* Geometry fields (`a < b`, `0 < a`, `b < T`, endpoint membership) are plumbing once the analytic window is selected.
* `currentEnergy_le_Icc` is plumbing from the current `LpPowerBoundedBefore` bound.
* `lowerAverage` is the real analytic content: it is a thickness/lower-average claim from a pointwise high excursion.

### 3.2 Fixed-window upper witness plus strict gap producer

This is where the `eps/Ceps` dependence belongs.  It must choose `eps` and the upper-bound witnesses together, not quantify over arbitrary `Ceps` witnesses.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Real analytic / quantitative frontier: for a lower-average high-excursion
window, one can choose `eps` and the fixed-window upper-bound witnesses so that
the upper budget is strictly below the lower average.

This is intentionally stronger than merely having
`IntegratedMoserWindowUpperBoundData`, because the latter is existential and has
no projections.  The proof of this frontier must control the selected `Ceps`
from relative Moser, or use a quantitative replacement for
`RelativeMoserInterpolationBefore`. -/
structure IntegratedMoserUpperWitnessGapFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  produce :
    ∀ {p Cp Cnext t : ℝ},
      IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cp Cnext t →
      ∃ eps Gbound Ceps,
        0 < eps ∧
        IntegratedMoserWindowUpperBoundWitness
          D u rho p
            (IntegratedMoserHighExcursionLowerAverageWindow.a)
            (IntegratedMoserHighExcursionLowerAverageWindow.b)
            Cp eps Gbound Ceps ∧
        eps * Gbound +
            ((IntegratedMoserHighExcursionLowerAverageWindow.b) -
              (IntegratedMoserHighExcursionLowerAverageWindow.a)) *
              (Ceps * Cp) <
          IntegratedMoserHighExcursionLowerAverageWindow.lower

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

The notation above uses structure projections schematically.  In actual Lean, bind the window as `hwin` and use `hwin.a`, `hwin.b`, `hwin.lower`:

```lean
produce :
  ∀ {p Cp Cnext t : ℝ},
    (hwin : IntegratedMoserHighExcursionLowerAverageWindow
      D u T rho p0 p Cp Cnext t) →
    ∃ eps Gbound Ceps,
      0 < eps ∧
      IntegratedMoserWindowUpperBoundWitness
        D u rho p hwin.a hwin.b Cp eps Gbound Ceps ∧
      eps * Gbound + (hwin.b - hwin.a) * (Ceps * Cp) < hwin.lower
```

Classification:

* Choosing/applying `integratedMoser_windowUpperBoundData_of_precrossing` is plumbing.
* Proving the selected `Ceps` and `Gbound` budget is below the lower average is real analytic/quantitative.
* This is the correct home for all `eps/Ceps` dependence.  Do not hide this in the lower-average producer.

### 3.3 Pure assembler to existing contradiction-window frontier

Once the two producer frontiers above exist, the current `IntegratedMoserHighExcursionContradictionWindowFrontier` should be obtained by plumbing.

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Pure assembly: lower-average window producer + upper-witness/gap producer
imply the current high-excursion contradiction-window frontier. -/
theorem integratedMoserHighExcursionContradictionWindowFrontier_of_lowerAverage_and_upperGap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hlower : IntegratedMoserHighExcursionLowerAverageWindowFrontier
      D u T rho p0)
    (hgap : IntegratedMoserUpperWitnessGapFrontier
      D u T rho p0) :
    IntegratedMoserHighExcursionContradictionWindowFrontier
      D u T rho p0 := by
  -- Plumbing only:
  -- 1. receive a high excursion from the existing frontier target;
  -- 2. call `hlower.produce` to obtain the window and lowerAverage;
  -- 3. call `hgap.produce` to obtain eps/Gbound/Ceps, upper witness, and gap;
  -- 4. package the current `IntegratedMoserHighExcursionContradictionWindow`;
  -- 5. use `false_of_windowUpperBoundWitness_lowerAverage_gap` in the pure theorem
  --    that eliminates contradiction windows, if needed.
  admit

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

The theorem above is a shape only; do not commit it with `admit`.  Its proof should be straightforward once the exact local fields of `IntegratedMoserHighExcursionContradictionWindowFrontier` are known.

Classification: pure plumbing, assuming the two producer frontiers.

## 4. Concrete route for proving the upper-gap frontier

The hard part in `IntegratedMoserUpperWitnessGapFrontier` is that `RelativeMoserInterpolationBefore` only supplies:

```lean
∀ eps > 0, ∃ Ceps, 0 ≤ Ceps ∧ pointwise_estimate eps Ceps
```

There is no quantitative dependence `Ceps(eps)` exposed.  Therefore a later analytic proof of the gap needs one of the following additional producer interfaces.

### Option A: controlled relative-Moser constants

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Quantitative replacement/refinement for `RelativeMoserInterpolationBefore`.
It exposes a controlled choice of `Ceps`. -/
structure ControlledRelativeMoserInterpolationBefore
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  Ceps : ℝ → ℝ → ℝ
  Ceps_nonneg :
    ∀ p eps, p0 ≤ p → 0 < eps → 0 ≤ Ceps p eps
  estimate :
    ∀ p eps, p0 ≤ p → 0 < eps → ∀ t, 0 < t → t < T →
      integratedMoserEnergy D u (p + rho) t ≤
        eps * integratedMoserGradientEnergy D u p t +
        Ceps p eps * integratedMoserEnergy D u p t
  Ceps_control :
    -- Real analytic quantitative bound, e.g. polynomial/power dependence.
    -- Shape deliberately left as a frontier depending on the actual GN/Young proof.
    ∀ p eps, p0 ≤ p → 0 < eps → True

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Classification: real analytic.  The `estimate` resembles existing relative Moser; the `Ceps_control` field is the new information needed for a strict upper/lower gap.

### Option B: direct upper-gap oracle for the chosen fixed-window theorem

This is less transparent but minimal if you only need the next wrapper:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Direct quantitative oracle saying the fixed-window upper estimate can be
chosen below the high-excursion lower average. -/
structure IntegratedMoserFixedWindowUpperGapOracle
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  choose_upper_below_lower :
    ∀ {p Cp Cnext t : ℝ},
      (hwin : IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cp Cnext t) →
      ∃ eps Gbound Ceps,
        0 < eps ∧
        IntegratedMoserWindowUpperBoundWitness
          D u rho p hwin.a hwin.b Cp eps Gbound Ceps ∧
        eps * Gbound + (hwin.b - hwin.a) * (Ceps * Cp) < hwin.lower

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

This is essentially `IntegratedMoserUpperWitnessGapFrontier`.  It is honest, but it hides the quantitative GN/Young dependence in a single field.  For long-term maintainability, Option A is better.

## 5. Dependency DAG

Recommended next DAG:

```text
Current local fixed-window plumbing
  integratedMoserPrecrossingIntervalData_of_regular_window
  integratedMoser_windowUpperBoundData_of_precrossing
        │
        ▼
Witness-level upper predicate
  IntegratedMoserWindowUpperBoundWitness
  false_of_windowUpperBoundWitness_lowerAverage_gap
        │
        ├─────────────── pure plumbing
        ▼
High-excursion lower-average producer
  IntegratedMoserHighExcursionLowerAverageWindowFrontier
        │
        └── real analytic: thickness / AC / modulus / non-spike theorem
        │
        ▼
Upper-witness gap producer
  IntegratedMoserUpperWitnessGapFrontier
        │
        └── real analytic: eps/Ceps dependence or controlled relative-Moser constants
        │
        ▼
Pure assembler
  integratedMoserHighExcursionContradictionWindowFrontier_of_lowerAverage_and_upperGap
        │
        ▼
Existing pure wrapper
  LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
  integratedMoserFirstCrossingStep_of_windowFrontier
```

## 6. Field classification

### Pure plumbing / already available from current layer

* current `Y_p` bound on a window from `LpPowerBoundedBefore`;
* interval-integrability of `Y_p`, `Y_{p+rho}`, and `G_p` from `IntegratedMoserFirstCrossingRegularity`;
* construction of `IntegratedMoserPrecrossingIntervalData`;
* production of fixed-window upper data from `IntegratedMoserDissipationDropBefore` and `RelativeMoserInterpolationBefore`;
* contradiction from `upper ≤ budget < lower ≤ ∫Y`;
* assembly of lower-window and upper-gap producers into the current frontier.

### Genuine analytic assumptions

* high-excursion lower average/thickness: pointwise high `Y_{p+rho}(t)` gives a time window with a quantitative lower integral;
* control of the `eps/Ceps` dependence in relative Moser, or a direct proof that the fixed-window upper witnesses can be chosen below the lower average;
* any absolute-continuity/modulus theorem strong enough to prevent arbitrarily narrow spikes.

## 7. Recommended audit of current local definitions

Please check the local `IntegratedMoserHighExcursionContradictionWindow` definition for this exact issue:

* If it existentially stores `Gbound` and `Ceps` along with the upper inequalities and the strict gap, it is good.
* If it stores only `IntegratedMoserWindowUpperBoundData` plus a gap that is not tied to the same witnesses, refactor to the witness-level shape above.
* If it states a gap for all possible `Gbound/Ceps` witnesses, it is too strong and likely false, because arbitrarily large `Ceps` can satisfy the upper inequality.

The most robust local shape is:

```lean
def IntegratedMoserHighExcursionContradictionWindow ... : Prop :=
  ∃ a b M eps lower Gbound Ceps,
    -- geometry/current-window fields
    ... ∧
    IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps Gbound Ceps ∧
    lower ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ∧
    eps * Gbound + (b - a) * (Ceps * M) < lower
```

This shape is both honest and usable by the existing pure wrapper.
