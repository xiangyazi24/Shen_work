# Q2522 shen1 — witness-tied Type data for the high-excursion contradiction window

Repo: `xiangyazi24/Shen_work`

Target namespace:

```text
ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Visible-source caveat: the GitHub-visible `main` copy I can inspect still does not contain your local Q2522 refactor.  The audit below is therefore grounded in the current checked-in integrated-Moser APIs in `ShenWork/PDE/P3MoserIntegratedClosure.lean` and in your stated local definitions.

## Verdict

Your refactor is the right repair.

The key correction is that `IntegratedMoserHighExcursionContradictionWindow` now carries the same concrete `Gbound` and `Ceps` used by

```lean
upperWitness :
  IntegratedMoserWindowUpperBoundWitness
    D u rho p a b M eps Gbound Ceps
```

and the strict gap is stated for exactly those witnesses:

```lean
upper_lt_lower : eps * Gbound + (b - a) * (Ceps * M) < lowerBound
```

That avoids the Q2520 bug: a universal gap over all possible `Gbound/Ceps` witnesses is false/too strong because the upper-bound existential can usually be satisfied by larger budgets.  The contradiction eliminator only needs the one selected witness actually stored in the window.

## Hidden API issues to watch

### 1. Type-valued window means the frontier should also be Type-valued, or use `Nonempty`

If you declare

```lean
structure IntegratedMoserHighExcursionContradictionWindow ... where
  a b M eps lowerBound Gbound Ceps : ℝ
  ...
```

without `: Prop`, then it is `Type`-valued data.  A structure declared `: Prop` cannot have a field whose type is arbitrary Type-valued data.  Therefore either make the frontier Type-valued too:

```lean
structure IntegratedMoserHighExcursionContradictionWindowFrontier ... where
  produce : ∀ ..., IntegratedMoserHighExcursionContradictionWindow ...
```

or, if you insist that the frontier itself is a proposition, wrap the produced data in `Nonempty`:

```lean
structure IntegratedMoserHighExcursionContradictionWindowFrontier ... : Prop where
  produce : ∀ ..., Nonempty (IntegratedMoserHighExcursionContradictionWindow ...)
```

For the current route, the Type-valued frontier is simpler and matches your stated refactor.

### 2. Do not store only `IntegratedMoserWindowUpperBoundData` inside the contradiction window

This is good:

```lean
Gbound Ceps : ℝ
upperWitness : IntegratedMoserWindowUpperBoundWitness D u rho p a b M eps Gbound Ceps
upper_lt_lower : eps * Gbound + (b - a) * (Ceps * M) < lowerBound
```

This is still risky:

```lean
upperData : IntegratedMoserWindowUpperBoundData D u rho p a b M eps
upper_lt_lower : ?
```

unless `upper_lt_lower` is stated after unpacking `upperData.bounds` and tied to the unpacked witnesses.  There should be no `.Gbound` or `.Ceps` projections from `IntegratedMoserWindowUpperBoundData`; the only safe consumer shape is:

```lean
rcases hdata.bounds with ⟨Gbound, Ceps, hupperWitness⟩
```

### 3. The pure contradiction lemma needs no geometry, but the upper-witness producer still does

The eliminator

```lean
false_of_windowUpperBoundWitness_lowerAverage_gap
```

only uses

```lean
lowerBound ≤ ∫ Y_{p+rho}
∫ Y_{p+rho} ≤ eps * Gbound + (b-a)*(Ceps*M)
eps * Gbound + (b-a)*(Ceps*M) < lowerBound
```

so it does not need `a ≤ b`, `0 < a`, `b < T`, interval integrability, endpoint nonnegativity, or `hp_nonneg`.

But the producer of `upperWitness` still must supply the exact hypotheses demanded by the checked-in APIs:

* `integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds` needs `hp`, `hp_nonneg`, `haT`, `hbT`, `hYa`, `hYb_nonneg`, and `hmaxInt`, and returns `∃ C, 0 ≤ C ∧ 2 * ∫G ≤ M + C*p*H`.
* `relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound` needs `heps`, `hab`, `ha : 0 < a`, `hb : b < T`, interval integrability for `Y_{p+rho}` and `G`, the current `Y_p ≤ M` bound on `Icc a b`, and the selected gradient bound `∫G ≤ Gbound`.

So keep the geometry/integrability/current-bound fields in the lower-window producer or in the upper-bound-data producer.  They do not have to pollute the final contradiction eliminator.

### 4. `M` does not need nonnegativity for the pure contradiction, but later producers may prefer it

The witness-level contradiction works for any real `M` because the stored `upperWitness` already proves the upper inequality.  However, if an analytic producer derives `M` from `LpPowerBoundedBefore`, remember that `LpPowerBoundedBefore` is only `∃ C, ∀ t, ... ≤ C`; it does not by itself say `0 ≤ C`.  If a later estimate wants nonnegative `M`, choose `max C 0` or prove nonnegativity of the energy separately.

### 5. `eps_pos` is correctly stored in the Type-valued window

The pure contradiction lemma does not use `eps_pos`, but the upper-bound construction does: the checked-in relative-Moser integrated theorem takes `heps : 0 < eps`.  Keeping `eps_pos` in the contradiction window is harmless and useful for tracing the selected upper witness.

## Exact pure helper theorem already implied by your refactor

This is the first theorem I would add after the witness definition.  It is pure and should compile as soon as your local `IntegratedMoserWindowUpperBoundWitness` is in scope.

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

/-- Pure contradiction from a witness-level fixed-window upper bound and a lower
average/gap for the same witnesses. -/
theorem false_of_windowUpperBoundWitness_lowerAverage_gap
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {rho p a b M eps Gbound Ceps lowerBound : ℝ}
    (hupper :
      IntegratedMoserWindowUpperBoundWitness
        D u rho p a b M eps Gbound Ceps)
    (hlower :
      lowerBound ≤
        ∫ s in a..b, D.integral (fun x => (u s x) ^ (p + rho)))
    (hgap : eps * Gbound + (b - a) * (Ceps * M) < lowerBound) :
    False := by
  rcases hupper with ⟨_hCeps_nonneg, _hG_le, hYupper⟩
  linarith

/-- Pure eliminator for the Type-valued contradiction-window data. -/
theorem false_of_integratedMoserHighExcursionContradictionWindow
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p : ℝ}
    (hwin :
      IntegratedMoserHighExcursionContradictionWindow
        D u T rho p0 p) :
    False := by
  exact false_of_windowUpperBoundWitness_lowerAverage_gap
    hwin.upperWitness hwin.lowerAverage hwin.upper_lt_lower

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

If your local `IntegratedMoserHighExcursionContradictionWindow` parameter list omits `T` or `p0`, keep the theorem name and proof body, and only adjust the parameter list.  The important part is that the proof uses `hwin.upperWitness`, `hwin.lowerAverage`, and `hwin.upper_lt_lower`; it must not unpack `IntegratedMoserWindowUpperBoundData` here.

## Minimal next Type-valued producer interfaces

The clean split is:

```text
lower-average window frontier
        +
upper-gap witness frontier
        │
        ▼
pure assembler
        │
        ▼
IntegratedMoserHighExcursionContradictionWindowFrontier
```

### 1. Lower-average window data

This is the output of the high-excursion/thickness frontier.  It deliberately does not mention `eps`, `Gbound`, or `Ceps`.

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

/-- A selected high-excursion window with a lower average for the next exponent.
This is Type-valued because it carries the chosen interval and constants. -/
structure IntegratedMoserHighExcursionLowerAverageWindow
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p Cnext t : ℝ) where
  a b M lowerBound : ℝ
  hab : a ≤ b
  ha_pos : 0 < a
  hb_lt : b < T
  haT : a ∈ Set.Icc (0 : ℝ) T
  hbT : b ∈ Set.Icc a T
  currentEnergy_le_Icc :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ M
  lowerAverage :
    lowerBound ≤
      ∫ s in a..b, D.integral (fun x => (u s x) ^ (p + rho))

/-- Analytic frontier: a high pointwise excursion produces a window carrying a
quantitative lower average.  This is the thickness/modulus/non-spike input. -/
structure IntegratedMoserHighExcursionLowerAverageWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) where
  produce :
    ∀ {p Cnext t : ℝ},
      p0 ≤ p →
      0 ≤ p →
      LpPowerBoundedBefore D p T u →
      0 < t → t < T →
      Cnext < D.integral (fun x => (u t x) ^ (p + rho)) →
        IntegratedMoserHighExcursionLowerAverageWindow
          D u T rho p0 p Cnext t

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

Classification: the structure is plumbing; the `produce` field is genuine analytic content.  In particular, `lowerAverage` is not a consequence of a single pointwise high value without a quantitative continuity/absolute-continuity/thickness input.

### 2. Upper-gap witness data

This is the correct home for the `eps/Gbound/Ceps` dependence.  It returns the exact upper witness and the strict gap for that same witness.

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

/-- A fixed-window upper-bound witness together with a strict gap below the
lower average selected by the lower-window data. -/
structure IntegratedMoserWindowUpperGapWitness
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b M lowerBound : ℝ) where
  eps Gbound Ceps : ℝ
  eps_pos : 0 < eps
  upperWitness :
    IntegratedMoserWindowUpperBoundWitness
      D u rho p a b M eps Gbound Ceps
  upper_lt_lower :
    eps * Gbound + (b - a) * (Ceps * M) < lowerBound

/-- Quantitative upper-gap frontier: for the selected lower-average window, choose
`eps` and the fixed-window upper witnesses so that the upper budget is below the
lower average. -/
structure IntegratedMoserWindowUpperGapWitnessFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) where
  produce :
    ∀ {p Cnext t : ℝ},
      (hwin : IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cnext t) →
        IntegratedMoserWindowUpperGapWitness
          D u rho p hwin.a hwin.b hwin.M hwin.lowerBound

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

Classification: this frontier is not pure if you try to prove it from PDE estimates.  It is where the quantitative `eps ↦ Ceps` dependence of relative Moser, or a direct fixed-window upper-gap theorem, must live.  Existing `RelativeMoserInterpolationBefore` only gives `∀ eps > 0, ∃ Ceps, ...`; it does not expose enough dependence to prove a gap uniformly without additional analytic input.

## Pure assemblers into the contradiction-window frontier

These names are the next exact Lean theorem names I recommend.

### 1. Assemble one contradiction window

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

/-- Pure assembly of a lower-average window and a tied upper-gap witness into the
Type-valued contradiction window. -/
theorem integratedMoserHighExcursionContradictionWindow_of_lowerAverageWindow_and_upperGapWitness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p Cnext t : ℝ}
    (hlower :
      IntegratedMoserHighExcursionLowerAverageWindow
        D u T rho p0 p Cnext t)
    (hupper :
      IntegratedMoserWindowUpperGapWitness
        D u rho p hlower.a hlower.b hlower.M hlower.lowerBound) :
    IntegratedMoserHighExcursionContradictionWindow
      D u T rho p0 p := by
  exact
    { a := hlower.a
      b := hlower.b
      M := hlower.M
      eps := hupper.eps
      lowerBound := hlower.lowerBound
      Gbound := hupper.Gbound
      Ceps := hupper.Ceps
      eps_pos := hupper.eps_pos
      upperWitness := hupper.upperWitness
      lowerAverage := hlower.lowerAverage
      upper_lt_lower := hupper.upper_lt_lower }

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

If your local contradiction-window structure also stores geometry fields, add these assignments from `hlower`:

```lean
hab := hlower.hab
ha_pos := hlower.ha_pos
hb_lt := hlower.hb_lt
haT := hlower.haT
hbT := hlower.hbT
currentEnergy_le_Icc := hlower.currentEnergy_le_Icc
```

The important point is that `upperWitness` and `upper_lt_lower` both come from `hupper`, so they are tied to the same `eps/Gbound/Ceps`.

### 2. Assemble the frontier

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

/-- Pure assembly: lower-average windows plus tied upper-gap witnesses produce the
existing high-excursion contradiction-window frontier. -/
theorem integratedMoserHighExcursionContradictionWindowFrontier_of_lowerAverageWindowFrontier_and_upperGapWitnessFrontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hlower :
      IntegratedMoserHighExcursionLowerAverageWindowFrontier
        D u T rho p0)
    (hupper :
      IntegratedMoserWindowUpperGapWitnessFrontier
        D u T rho p0) :
    IntegratedMoserHighExcursionContradictionWindowFrontier
      D u T rho p0 := by
  refine ⟨?_⟩
  intro p Cnext t hp hp_nonneg hLp ht0 htT hhigh
  let hwin : IntegratedMoserHighExcursionLowerAverageWindow
      D u T rho p0 p Cnext t :=
    hlower.produce hp hp_nonneg hLp ht0 htT hhigh
  exact
    integratedMoserHighExcursionContradictionWindow_of_lowerAverageWindow_and_upperGapWitness
      hwin (hupper.produce hwin)

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

If your existing `IntegratedMoserHighExcursionContradictionWindowFrontier.produce` has a different binder order, keep the theorem name and only reorder the final `intro` line and the call to `hlower.produce`.  The proof should remain pure: call lower producer, call upper-gap producer on the selected lower window, package the Type-valued contradiction window.

If the frontier is `Prop` with `Nonempty`, the last line becomes:

```lean
  exact ⟨
    integratedMoserHighExcursionContradictionWindow_of_lowerAverageWindow_and_upperGapWitness
      hwin (hupper.produce hwin)⟩
```

## Optional safe unpacking theorem for `IntegratedMoserWindowUpperBoundData`

This is the only projection-like helper I would add for the existential upper data.  It does not expose fake projections; it just unpacks the `bounds` field.

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

/-- Safe consumer for `IntegratedMoserWindowUpperBoundData`: the data has no
`Gbound` or `Ceps` projections; consumers must unpack `bounds`. -/
theorem IntegratedMoserWindowUpperBoundData.exists_witness
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {rho p a b M eps : ℝ}
    (hdata : IntegratedMoserWindowUpperBoundData D u rho p a b M eps) :
    ∃ Gbound Ceps,
      IntegratedMoserWindowUpperBoundWitness
        D u rho p a b M eps Gbound Ceps := by
  exact hdata.bounds

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

end
```

Do not add a theorem of the shape

```lean
∀ Gbound Ceps,
  IntegratedMoserWindowUpperBoundWitness ... Gbound Ceps →
  eps * Gbound + ... < lowerBound
```

unless that universal statement is genuinely what you have proved.  It reintroduces the Q2520 issue.

## Exact upper-witness construction call shape

When you prove the upper-bound data producer, the checked-in extraction lemma signature should be consumed in this order.

```lean
rcases
  integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
    (p := p) (a := a) (b := b) (M := M) (H := H)
    hinteg hp hp_nonneg haT hbT hYa hYb_nonneg hmaxInt with
  ⟨Cgrad, hCgrad_nonneg, htwoG_le⟩

let Gbound : ℝ := (M + Cgrad * p * H) / 2
have hG_le :
    (∫ s in a..b,
      D.integral (fun x =>
        (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2)) ≤ Gbound := by
  dsimp [Gbound]
  linarith

rcases
  relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
    (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
    (p := p) (a := a) (b := b) (M := M) (eps := eps)
    (Gbound := Gbound)
    hrel hp heps hab ha_pos hb_lt hZ_int hG_int hY_le hG_le with
  ⟨Ceps, hCeps_nonneg, hZ_le⟩

exact ⟨Gbound, Ceps, hCeps_nonneg, hG_le, hZ_le⟩
```

This matches the current integrated APIs: first select the gradient bound witness from the integrated dissipation estimate, then feed that exact `Gbound` into the integrated relative-Moser bound, then package the witness-level upper data.

## Recommended theorem-name DAG

Use these names in this order:

```text
IntegratedMoserWindowUpperBoundWitness
IntegratedMoserWindowUpperBoundData.exists_witness
false_of_windowUpperBoundWitness_lowerAverage_gap
false_of_integratedMoserHighExcursionContradictionWindow

IntegratedMoserHighExcursionLowerAverageWindow
IntegratedMoserHighExcursionLowerAverageWindowFrontier
IntegratedMoserWindowUpperGapWitness
IntegratedMoserWindowUpperGapWitnessFrontier

integratedMoserHighExcursionContradictionWindow_of_lowerAverageWindow_and_upperGapWitness
integratedMoserHighExcursionContradictionWindowFrontier_of_lowerAverageWindowFrontier_and_upperGapWitnessFrontier

LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier
integratedMoserFirstCrossingStep_of_windowFrontier
```

The first four are pure.  The two `...Window` structures are data.  The lower-average and upper-gap frontiers are the remaining genuine analytic inputs.  The two long `...of_lowerAverage...and_upperGap...` theorems are pure assembly and should not call any PDE estimate.

## Final audit summary

The Q2522 design is mathematically honest if:

1. `IntegratedMoserHighExcursionContradictionWindow` is Type-valued and stores `Gbound/Ceps` explicitly.
2. `upperWitness` and `upper_lt_lower` mention exactly those stored `Gbound/Ceps`.
3. `LpPowerBoundedBefore_of_highExcursionContradictionWindowFrontier` eliminates a produced window via `hwin.upperWitness`, `hwin.lowerAverage`, and `hwin.upper_lt_lower` only.
4. `IntegratedMoserWindowUpperBoundData` is consumed only by unpacking `bounds`; no fake witness projections are introduced.
5. The high-excursion lower-average and upper-gap witness frontiers remain explicit assumptions/producers, because they contain the real analytic thickness and quantitative `eps/Ceps` dependence.
