# Q2631 shen1 — audit of `P3MoserRegularityProducer` frontier after `3baba004`

Repo: `xiangyazi24/Shen_work`

Branch/ref inspected: default branch `main`, plus `3baba004` for `ShenWork/PDE/P3MoserRegularityProducer.lean`.

Files inspected:

```text
ShenWork/PDE/P3MoserRegularityProducer.lean
ShenWork/PDE/P3MoserIntegratedClosure.lean
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
ShenWork/Paper2/Statements.lean
ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean
ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean
ShenWork/Paper2/IntervalDomainLpEnergyFrontiers.lean
ShenWork/Paper2/IntervalDomainMass.lean
ShenWork/PDE/IntervalDomain.lean
```

## Executive answer

From `IsPaper2ClassicalSolution intervalDomain params T u v` or `IsPaper2GlobalClassicalSolution intervalDomain params u v` **alone**, none of the three new frontier fields is currently provable as stated:

```lean
energyContinuous
powerTimeIntegrable
gradientTimeIntegrable
```

The refactor in `P3MoserRegularityProducer.lean` is therefore mathematically honest: the old skeleton that claimed these fields from `IsPaper2ClassicalSolution` was too strong.

There is, however, one real frontier reduction available:

* `powerTimeIntegrable` is redundant **if** `energyContinuous` is retained and `0 ≤ T` is available.  For classical solutions, `0 < T` is available from `IsPaper2ClassicalSolution.T_pos`.  This derives time-integrability of the scalar power energy from continuity on the compact interval.  It does **not** prove `powerTimeIntegrable` from classical regularity alone; it proves that the explicit frontier package can be weakened by dropping `powerTimeIntegrable` and deriving it from `energyContinuous`.

So the best non-vacuous reduction is:

```text
keep explicit:  energyContinuous, gradientTimeIntegrable
derive:         initialPowerBound, powerTimeIntegrable
get from hsol:  energy nonnegativity, T_pos
```

Do not reduce `energyContinuous` or `gradientTimeIntegrable` yet.  Existing repo lemmas provide useful interior/fixed-time facts, but not the closed-time or time-integrability statements required by `IntegratedMoserFirstCrossingRegularity`.

## Field-by-field audit

### 1. `energyContinuous`

Target field:

```lean
∀ p, p0 ≤ p → ContinuousOn
  (fun t => intervalDomain.integral (fun x => (u t x)^p))
  (Set.Icc (0 : ℝ) T)
```

Status: **not provable from the current `IsPaper2ClassicalSolution` or `IsPaper2GlobalClassicalSolution` interface.**

What is available:

```lean
intervalDomainPowerEnergy_hasDerivAt
intervalDomain_lp_timeLeibniz
```

from `ShenWork/Paper2/IntervalDomainLpTimeLeibniz.lean`.  These give differentiability, hence continuity, at interior times `t ∈ Set.Ioo 0 T`.

Precise interior-only skeleton:

```lean
import ShenWork.Paper2.IntervalDomainLpTimeLeibniz

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Interior-only consequence of classical regularity.  This is useful, but it is
not the closed-time `energyContinuous` field required by integrated Moser. -/
theorem intervalDomain_powerEnergy_continuousAt_interior_of_classical
    {params : CM2Params} {T q t : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    ContinuousAt
      (fun s => intervalDomain.integral (fun x => (u s x) ^ q)) t := by
  have hderiv :
      HasDerivAt (fun s => intervalDomainPowerEnergy q u s)
        (∫ y in (0 : ℝ)..1, intervalDomainPowerDeriv q u t y) t :=
    intervalDomainPowerEnergy_hasDerivAt (q := q) hsol ⟨ht0, htT⟩
  -- `intervalDomainPowerEnergy` is definitionally the same interval integral.
  change ContinuousAt (fun s => intervalDomainPowerEnergy q u s) t
  exact hderiv.continuousAt

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

Why this does not close the field:

* `ContinuousOn ... (Set.Icc 0 T)` includes continuity at `t = 0` and at `t = T`.
* `IsPaper2ClassicalSolution` only constrains the solution on interior times `0 < t < T`.  Its positivity, PDE identity, and interval-domain `classicalRegularity` are all interior-time statements.
* `IsPaper2GlobalClassicalSolution` helps at a positive endpoint `T` by allowing a larger horizon, but it still gives no continuity at `t = 0` and no initial trace.  The value `u 0` can be arbitrary from the perspective of the current interface.

Minimal extra data needed:

Either keep the current field exactly, or supply stronger closed-time data such as:

```lean
∀ p, p0 ≤ p,
  ContinuousOn
    (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
    (Set.Icc (0 : ℝ) T)
```

A more constructive future route would require a closed-time initial trace plus a parametric integral continuity theorem for real powers, with enough positivity/lower-bound control near `t = 0` to make `rpow` stable for all `p ≥ p0`.  That route is not currently in the repo.

### 2. `powerTimeIntegrable`

Target field:

```lean
∀ p, p0 ≤ p → IntegrableOn
  (fun t => intervalDomain.integral (fun x => (u t x)^p))
  (Set.uIcc (0 : ℝ) T) volume
```

Status from `IsPaper2ClassicalSolution` alone: **not provable**.

Status as a frontier reduction: **provable from `energyContinuous` plus `0 ≤ T`.**

Existing supporting fact: Mathlib’s `ContinuousOn.integrableOn_Icc`, already used elsewhere in the repo through the `.integrableOn_Icc` projection style.

Lean code for the reduction:

```lean
import ShenWork.PDE.P3MoserRegularityProducer

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- A compact-interval continuity field already implies the corresponding
power-energy time-integrability field. -/
theorem intervalDomain_powerTimeIntegrable_of_energyContinuous
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (henergy :
      ∀ p, p0 ≤ p →
        ContinuousOn
          (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
          (Set.Icc (0 : ℝ) T)) :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.uIcc (0 : ℝ) T) volume := by
  intro p hp
  have hIcc :
      IntegrableOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T) volume :=
    (henergy p hp).integrableOn_Icc
  simpa [Set.uIcc_of_le hT] using hIcc

/-- Reduced regularity frontier: `powerTimeIntegrable` is derived from
`energyContinuous` on `[0,T]` when `0 ≤ T`. -/
structure IntervalDomainIntegratedMoserRegularityFrontierDataLite
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  energyContinuous :
    ∀ p, p0 ≤ p →
      ContinuousOn
        (fun t => intervalDomain.integral (fun x => (u t x) ^ p))
        (Set.Icc (0 : ℝ) T)
  gradientTimeIntegrable :
    ∀ p, p0 ≤ p →
      IntegrableOn
        (fun t =>
          intervalDomain.integral (fun x =>
            (intervalDomain.gradNorm
              (fun y => (u t y) ^ (p / 2)) x) ^ 2))
        (Set.uIcc (0 : ℝ) T) volume

/-- Produce the existing explicit frontier data from the reduced version. -/
theorem intervalDomain_regularFrontierData_of_lite
    {T p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 ≤ T)
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0) :
    IntervalDomainIntegratedMoserRegularityFrontierData u T p0 where
  energyContinuous := hreg.energyContinuous
  powerTimeIntegrable :=
    intervalDomain_powerTimeIntegrable_of_energyContinuous
      hT hreg.energyContinuous
  gradientTimeIntegrable := hreg.gradientTimeIntegrable

/-- Direct producer of integrated-Moser regularity from the reduced frontier. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hreg : IntervalDomainIntegratedMoserRegularityFrontierDataLite u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_frontierData
    (intervalDomain_regularFrontierData_of_lite
      (IsPaper2ClassicalSolution.T_pos hsol).le hreg)

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

end
```

Classification: **wiring / standard compact-continuity integration**, not new PDE math.

What is available from classical regularity without `energyContinuous`:

```lean
intervalDomain_u_rpow_intervalIntegrable_of_regularity
```

from `ShenWork/Paper2/IntervalDomainLpBootstrapEnergyInequality.lean`, but this is only fixed-time spatial interval-integrability:

```lean
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open scoped Interval

noncomputable section

example
    {params : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    IntervalIntegrable
      (intervalDomainLift (fun x : intervalDomain.Point => (u t x) ^ q))
      volume 0 1 :=
  intervalDomain_u_rpow_intervalIntegrable_of_regularity
    (q := q) hsol ht0 htT

end
```

That fixed-time spatial lemma does not imply the target `IntegrableOn` in the time variable.  To prove time integrability without using `energyContinuous`, one would at least need scalar-energy measurability plus a time-integrable or essentially bounded envelope on `Set.uIcc 0 T`.  `LpPowerBoundedBefore` gives a uniform bound but not measurability; classical regularity gives interior local continuity but not endpoint control at `0`.

### 3. `gradientTimeIntegrable`

Target field:

```lean
∀ p, p0 ≤ p → IntegrableOn
  (fun t =>
    intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm
        (fun y => (u t y)^(p/2)) x)^2))
  (Set.uIcc 0 T) volume
```

Status: **not provable from current `IsPaper2ClassicalSolution` / `IsPaper2GlobalClassicalSolution` infrastructure.**

Useful existing fixed-time or algebraic lemmas:

```lean
intervalDomain_moser_gradNorm_sq_eq_weighted_of_regularity
intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
intervalDomainLpMoserGradientControl_of_regularity
intervalDomain_gradient_integral_nonneg
```

Representative fixed-time identity:

```lean
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
import ShenWork.PDE.P3MoserThresholdPlanProducer

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
open ShenWork.IntervalDomainExistence.P3MoserThresholdPlanProducer
open scoped Interval

noncomputable section

example
    {params : CM2Params} {T t q : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (ht0 : 0 < t) (htT : t < T) :
    intervalDomain.integral
        (fun x =>
          (intervalDomain.gradNorm
            (fun y : intervalDomain.Point => (u t y) ^ (q / 2)) x) ^ 2) =
      (q / 2) ^ 2 *
        intervalDomainLpWeightedGradientDissipation q u t :=
  intervalDomain_moser_gradient_integral_eq_weighted_of_regularity
    (pExp := q) hsol ht0 htT

example
    {u : ℝ → intervalDomain.Point → ℝ} {q a b : ℝ}
    (hab : a ≤ b) :
    0 ≤ ∫ s in a..b,
      integratedMoserGradientEnergy intervalDomain u q s :=
  intervalDomain_gradient_integral_nonneg hab

end
```

These are not time-integrability theorems.

Minimal extra data needed:

The current field is already a good minimal interface:

```lean
∀ p, p0 ≤ p → IntegrableOn
  (fun t =>
    intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm
        (fun y => (u t y) ^ (p / 2)) x) ^ 2))
  (Set.uIcc (0 : ℝ) T) volume
```

A more constructive future replacement could provide either:

```lean
∀ p, p0 ≤ p,
  IntegrableOn
    (fun t => intervalDomainLpWeightedGradientDissipation p u t)
    (Set.uIcc (0 : ℝ) T) volume
```

together with the Moser-gradient identity/control, or a closed-slab joint regularity theorem proving measurability and an integrable time envelope for the Moser-gradient energy.  No such theorem currently appears in the repo.

## False assumptions to avoid for `gradientTimeIntegrable`

Do not argue:

```text
classical solution ⇒ each spatial slice is C² ⇒ gradient energy is time-integrable
```

That implication is not valid in the current interface.

The exact problems are:

1. `ContDiffOn ℝ 2 (intervalDomainLift (u t)) ...` is per fixed interior time.  It gives spatial regularity of each slice, not measurability or integrability of the scalar function of time.

2. The interval-domain `classicalRegularity` now contains joint continuity of the solution field and of the time-derivative field, but it does **not** contain joint continuity in `(t,x)` of the spatial derivative `deriv (intervalDomainLift (u t)) x`.  The Moser gradient uses spatial derivatives.

3. Even a future joint continuity result on `(0,T) × [0,1]` would only give local integrability away from `t = 0`.  The target field is on `Set.uIcc 0 T`, so it still needs endpoint control, especially near `t = 0`.

4. `intervalDomain_moser_gradient_integral_eq_weighted_of_regularity` is a fixed-time identity.  It does not say the weighted dissipation is `IntegrableOn` in time.

5. `intervalDomain_gradient_integral_nonneg` proves only nonnegativity of a time interval integral.  Nonnegativity is not integrability.

6. `IntegratedMoserDissipationDropBefore` contains interval integrals in inequalities, but the Lean statement does not produce `IntegrableOn` evidence for the gradient-energy time function.  The integrated-Moser closure later needs actual `IntegrableOn`/`IntervalIntegrable` objects, so this cannot be filled by inequality syntax alone.

## Relation to existing Moser consumers

`P3MoserThresholdPlanProducer.lean` confirms that these fields are genuinely consumed:

* `hreg.energyContinuous (p + rho) hp_rho` is passed into `LpPowerBoundedBefore_of_crossingThresholdPlan`.
* `hreg.powerTimeIntegrable` is converted to interval integrability on selected windows.
* `hreg.gradientTimeIntegrable` is likewise converted to interval integrability on selected windows.

`P3MoserHighExcursionProducer.lean` similarly uses closed-time continuity to turn a pointwise high excursion into a nontrivial lower-average window.  The lemma

```lean
exists_Icc_subinterval_gt_mid_of_continuousOn_gt
```

requires `ContinuousOn Y (Icc 0 T)`, not merely interior continuity.

## Recommended frontier shape

The current explicit frontier is honest.  The only reduction I recommend now is dropping `powerTimeIntegrable` from the explicit producer data and deriving it from `energyContinuous` plus `T ≥ 0`, as shown above.

A reduced frontier could be named:

```lean
IntervalDomainIntegratedMoserRegularityFrontierDataLite
intervalDomain_powerTimeIntegrable_of_energyContinuous
intervalDomain_regularFrontierData_of_lite
intervalDomain_integratedMoserFirstCrossingRegularity_of_lite
```

Classification:

```text
energyContinuous          remains real frontier
powerTimeIntegrable       wiring from energyContinuous + 0 ≤ T
initialPowerBound         already algebraic via max integral 0
gradientTimeIntegrable    remains real frontier
energy nonnegativity      already from hsol positivity
```

Do **not** add a theorem named like this unless it takes explicit frontier data:

```lean
-- Too strong / currently false from the interface alone.
theorem intervalDomain_integratedMoserRegularityFrontierData_of_classical
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v) :
    IntervalDomainIntegratedMoserRegularityFrontierData u T p0 := ...
```

The current interface does not determine enough closed-time behavior at `t = 0`, nor enough time integrability of the Moser-gradient energy, to prove that theorem without new analytic input.

## Final answer to the question

1. **Actually provable now from existing full fields:** `powerTimeIntegrable` can be derived from `energyContinuous` and `0 ≤ T`; use `ContinuousOn.integrableOn_Icc` and `Set.uIcc_of_le`.  This is a valid frontier reduction.

2. **Actually provable now from `IsPaper2ClassicalSolution`:** none of the three full fields.  Only supporting facts are provable: interior-time continuity/differentiability of power energies, fixed-time spatial power integrability, fixed-time Moser-gradient algebra, and nonnegativity.

3. **Minimal extra data:** keep `energyContinuous` and `gradientTimeIntegrable` explicit, or replace them with stronger closed-time/joint-regularity packages that genuinely imply those statements.  The current explicit frontier shape is the right interface, modulo the reducible `powerTimeIntegrable` field.

4. **Main false assumption to avoid:** fixed-time spatial `C²` regularity, even with positivity and the Moser-gradient chain rule, does not imply time integrability of the gradient energy.  Time measurability, time envelopes, and endpoint control are separate analytic data.
