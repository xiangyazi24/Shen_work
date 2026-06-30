# Q2501 shen2: next no-sorry plumbing in `P3MoserIntegratedClosure`

Repo target: `xiangyazi24/Shen_work`, source commit audited: `9d9250e6fbc8e0efb30a61130cd0b6e471ed4321` (`Factor integrated-step Moser residual route`).

Target file:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

## Current source shape

At commit `9d9250e6`, `P3MoserIntegratedClosure.lean` already has the right separation:

```lean
structure IntegratedMoserFirstCrossingRegularity

def IntegratedMoserFirstCrossingStep

theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds

theorem intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound

theorem integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound

theorem intervalIntegral_le_const_mul_integral_add_length_mul_const_of_le_on

theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound

theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound

theorem moser_iteration_chain_of_integrated_first_crossing_step

theorem all_exponents_of_integrated_first_crossing_step_lpmono

theorem intervalDomain_boundedBefore_of_integrated_first_crossing_step
```

The file imports only:

```lean
import ShenWork.PDE.P3MoserDissipationShape
```

and opens:

```lean
open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

That import/open block is sufficient for the next plumbing layer. I would not add another import unless one of the Mathlib projection names below is unavailable through the existing transitive imports.

## Recommendation

The next no-sorry commit should be a **pure plumbing commit** in `P3MoserIntegratedClosure.lean`, placed before any high-excursion/first-crossing frontier. It should add:

1. `IntegrableOn (Set.uIcc 0 T)` to `IntervalIntegrable a b` restriction helpers.
2. A `max 1` interval-integrability helper.
3. `IntegratedMoserFirstCrossingRegularity` interval-integrability producers.
4. An `LpPowerBoundedBefore` bound extractor on `Set.Icc a b`.
5. An honest `IntegratedMoserPrecrossingIntervalData` bundle, constructible from regularity plus a current `LpPowerBoundedBefore` bound.
6. An `IntegratedMoserWindowUpperBoundData` bundle around the existing fixed-window lemmas.

This does **not** produce `IntegratedMoserFirstCrossingStep`. It only packages the fixed-window estimates already proved in the file.

## Placement

Add the first group immediately after:

```lean
def IntegratedMoserFirstCrossingStep
```

and before:

```lean
theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
```

Add the data bundles and wrapper constructor after:

```lean
theorem relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

and before:

```lean
theorem moser_iteration_chain_of_integrated_first_crossing_step
```

This keeps the file order logical:

```text
regularity/integrability plumbing
  -> fixed-window algebraic estimates
  -> fixed-window data wrappers
  -> integrated-step consumers / iteration closure
```

## Snippet 1: interval-integrability plumbing

Paste after `IntegratedMoserFirstCrossingStep`.

```lean
/-- If a function is integrable on the global closed time interval, then it is
interval-integrable on any interval whose unordered endpoints stay inside that
time interval. -/
theorem intervalIntegrable_of_integrableOn_uIcc_subset
    {f : ℝ → ℝ} {T a b : ℝ}
    (hf : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume)
    (hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable f volume a b := by
  have hf' : IntegrableOn f (Set.uIcc a b) volume :=
    hf.mono_set hsub
  exact hf'.intervalIntegrable

/-- A non-reversed subinterval `[a,b]` inside `[0,T]` gives the unordered-interval
subset needed by `intervalIntegrable_of_integrableOn_uIcc_subset`. -/
theorem uIcc_subset_uIcc_zero_T_of_Icc_bounds
    {T a b : ℝ}
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T := by
  have h0T : (0 : ℝ) ≤ T := le_trans (le_trans ha0 hab) hbT
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  rw [Set.uIcc_of_le h0T]
  exact ⟨le_trans ha0 hs.1, le_trans hs.2 hbT⟩

/-- Convenient non-reversed form of the restriction lemma. -/
theorem intervalIntegrable_of_integrableOn_uIcc_of_Icc_bounds
    {f : ℝ → ℝ} {T a b : ℝ}
    (hf : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    IntervalIntegrable f volume a b :=
  intervalIntegrable_of_integrableOn_uIcc_subset hf
    (uIcc_subset_uIcc_zero_T_of_Icc_bounds hab ha0 hbT)

/-- Interval integrability is stable under `max 1`. -/
theorem intervalIntegrable_max_one_of_intervalIntegrable
    {Y : ℝ → ℝ} {a b : ℝ}
    (hY : IntervalIntegrable Y volume a b) :
    IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b := by
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b :=
    intervalIntegrable_const
  exact h1.max hY
```

### Mathlib name uncertainty for Snippet 1

I could not run Lean through the GitHub connector, so the only name uncertainty is the standard Mathlib API around converting `IntegrableOn` on `Set.uIcc` to `IntervalIntegrable`, and the interval-integrability `max` combinator.

Test this in a scratch Lean file before committing the source patch:

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open scoped Interval

#check IntegrableOn.mono_set
#check IntegrableOn.intervalIntegrable
#check IntervalIntegrable.max
#check intervalIntegrable_const
#check Set.uIcc_of_le
```

Expected outcomes:

* If `hf'.intervalIntegrable` fails, search for the local theorem name equivalent to `IntegrableOn -> IntervalIntegrable`; likely alternatives are `MeasureTheory.IntegrableOn.intervalIntegrable` or an iff theorem for `Set.uIcc`.
* If `h1.max hY` fails, test `#check IntervalIntegrable.sup`; for real-valued functions, `max` may be exposed as `sup` instead of `max`.

No mathematical assumption changes in either case.

## Snippet 2: regularity interval-integrability producers

Paste after Snippet 1.

```lean
namespace IntegratedMoserFirstCrossingRegularity

/-- Power time-integrability from the regularity package, restricted to a fixed
non-reversed subinterval of `[0,T]`. -/
theorem power_intervalIntegrable
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    IntervalIntegrable
      (fun t => D.integral (fun x => (u t x) ^ p)) volume a b :=
  intervalIntegrable_of_integrableOn_uIcc_of_Icc_bounds
    (hreg.powerTimeIntegrable p hp) hab ha0 hbT

/-- Gradient time-integrability from the regularity package, restricted to a
fixed non-reversed subinterval of `[0,T]`. -/
theorem gradient_intervalIntegrable
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    IntervalIntegrable
      (fun t =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      volume a b :=
  intervalIntegrable_of_integrableOn_uIcc_of_Icc_bounds
    (hreg.gradientTimeIntegrable p hp) hab ha0 hbT

/-- The `max 1 Y_p` term is interval-integrable on a fixed subinterval whenever
`Y_p` comes from `IntegratedMoserFirstCrossingRegularity`. -/
theorem maxOnePower_intervalIntegrable
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    IntervalIntegrable
      (fun t => max (1 : ℝ)
        (D.integral (fun x => (u t x) ^ p))) volume a b :=
  intervalIntegrable_max_one_of_intervalIntegrable
    (hreg.power_intervalIntegrable hp hab ha0 hbT)

/-- Higher-power time-integrability for the exponent `p + rho`, with the needed
lower-exponent side condition kept explicit. -/
theorem higherPower_intervalIntegrable
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp_rho : p0 ≤ p + rho)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    IntervalIntegrable
      (fun t => D.integral (fun x => (u t x) ^ (p + rho)))
      volume a b :=
  hreg.power_intervalIntegrable hp_rho hab ha0 hbT

end IntegratedMoserFirstCrossingRegularity
```

The `hp_rho : p0 ≤ p + rho` hypothesis is intentionally explicit. If the caller has `hp : p0 ≤ p` and `hrho : 0 ≤ rho`, they can produce it by `nlinarith`; the regularity structure itself does not carry `rho`.

## Snippet 3: current `LpPowerBoundedBefore` bound on an `Icc`

Paste after Snippet 2.

```lean
/-- Extract a single current-exponent bound on a closed time window from the
existing before-`T` Lp bound. -/
theorem LpPowerBoundedBefore_exists_Icc_bound
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p a b : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (ha : 0 < a) (hb : b < T) :
    ∃ Cp, ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ Cp := by
  rcases hLp with ⟨Cp, hCp⟩
  refine ⟨Cp, ?_⟩
  intro s hs
  exact hCp s (lt_of_lt_of_le ha hs.1) (lt_of_le_of_lt hs.2 hb)
```

This is fully justified by the current definition:

```lean
LpPowerBoundedBefore D p T u :=
  ∃ C, ∀ t, 0 < t → t < T → D.integral (fun x => (u t x) ^ p) ≤ C
```

No integrability or positivity theorem is being smuggled in here.

## Snippet 4: honest precrossing interval data

Paste after the existing fixed-window lemmas, before `moser_iteration_chain_of_integrated_first_crossing_step`.

This structure is justified by current APIs. It packages only:

* exponent side conditions,
* a non-reversed interior time window,
* the current `LpPowerBoundedBefore` constant on that window,
* interval-integrability of the current power, `max 1` current power, higher power, and gradient power.

It does **not** state a crossing event, a high-excursion property, or a new Moser step.

```lean
/-- Routine fixed-window data available before any high-excursion/first-crossing
argument.  It packages only current-exponent boundedness and the time
integrability needed by the already-proved fixed-window lemmas. -/
structure IntegratedMoserPrecrossingIntervalData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p a b : ℝ) : Prop where
  hp : p0 ≤ p
  hp_rho : p0 ≤ p + rho
  hp_nonneg : 0 ≤ p
  hab : a ≤ b
  ha_pos : 0 < a
  hb_lt : b < T
  Cp : ℝ
  currentLpBound_on_Icc :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ Cp
  power_int :
    IntervalIntegrable
      (fun s => D.integral (fun x => (u s x) ^ p)) volume a b
  maxOne_int :
    IntervalIntegrable
      (fun s => max (1 : ℝ)
        (D.integral (fun x => (u s x) ^ p))) volume a b
  higher_int :
    IntervalIntegrable
      (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      volume a b
  gradient_int :
    IntervalIntegrable
      (fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      volume a b

namespace IntegratedMoserPrecrossingIntervalData

/-- Constructor for the routine precrossing fixed-window data from the existing
regularity package plus a current Lp bound. -/
def of_regularity_and_Lp
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hLp : LpPowerBoundedBefore D p T u)
    (hp : p0 ≤ p)
    (hp_rho : p0 ≤ p + rho)
    (hp_nonneg : 0 ≤ p)
    (hab : a ≤ b) (ha : 0 < a) (hb : b < T) :
    IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b := by
  classical
  rcases LpPowerBoundedBefore_exists_Icc_bound hLp ha hb with ⟨Cp, hCp⟩
  have hY_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ p)) volume a b :=
    hreg.power_intervalIntegrable hp hab (le_of_lt ha) (le_of_lt hb)
  have hmax_int :
      IntervalIntegrable
        (fun s => max (1 : ℝ)
          (D.integral (fun x => (u s x) ^ p))) volume a b :=
    intervalIntegrable_max_one_of_intervalIntegrable hY_int
  have hZ_int :
      IntervalIntegrable
        (fun s => D.integral (fun x => (u s x) ^ (p + rho))) volume a b :=
    hreg.higherPower_intervalIntegrable hp_rho hab (le_of_lt ha) (le_of_lt hb)
  have hG_int :
      IntervalIntegrable
        (fun s =>
          D.integral (fun x =>
            (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
        volume a b :=
    hreg.gradient_intervalIntegrable hp hab (le_of_lt ha) (le_of_lt hb)
  exact
    { hp := hp
      hp_rho := hp_rho
      hp_nonneg := hp_nonneg
      hab := hab
      ha_pos := ha
      hb_lt := hb
      Cp := Cp
      currentLpBound_on_Icc := hCp
      power_int := hY_int
      maxOne_int := hmax_int
      higher_int := hZ_int
      gradient_int := hG_int }

end IntegratedMoserPrecrossingIntervalData
```

### Why this is honest

The constructor needs `hp_rho : p0 ≤ p + rho` and `hp_nonneg : 0 ≤ p` as explicit inputs. The current APIs do not let `IntegratedMoserFirstCrossingRegularity` infer them. In the bootstrap use case, `hp_rho` comes from `hp` plus `rho ≥ 0`; outside that use case it should not be guessed.

The constructor also does not try to prove:

```lean
0 ≤ D.integral (fun x => (u b x) ^ p)
```

for an arbitrary `BoundedDomainData`. That is not available from the abstract domain API.

## Snippet 5: fixed-window upper-bound data wrapper

Paste after Snippet 4 and before `moser_iteration_chain_of_integrated_first_crossing_step`.

```lean
/-- Fixed-window upper bounds obtained by combining the already-proved integrated
Moser dissipation and integrated relative-Moser lemmas on one precrossing window.
This is still only a window estimate, not a first-crossing step. -/
structure IntegratedMoserWindowUpperBoundData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 p a b eps : ℝ) : Prop where
  Cp : ℝ
  H : ℝ
  currentLpBound_on_Icc :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ Cp
  maxOneIntegralBound :
    ∫ s in a..b,
      max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)) ≤ H
  Cgrad : ℝ
  Cgrad_nonneg : 0 ≤ Cgrad
  gradientIntegralBound :
    2 * ∫ s in a..b,
      D.integral (fun x =>
        (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      Cp + Cgrad * p * H
  Ceps : ℝ
  Ceps_nonneg : 0 ≤ Ceps
  higherPowerIntegralBound :
    ∫ s in a..b,
        D.integral (fun x => (u s x) ^ (p + rho)) ≤
      eps * ((Cp + Cgrad * p * H) / 2) +
        (b - a) * (Ceps * Cp)

namespace IntegratedMoserWindowUpperBoundData

/-- Build the fixed-window upper-bound package from the precrossing data and the
existing fixed-window lemmas.

The endpoint nonnegativity hypothesis is explicit because the abstract
`BoundedDomainData.integral` API does not provide positivity of integrals. -/
theorem of_precrossing
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hpre : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b)
    (heps : 0 < eps)
    (hYb_nonneg :
      0 ≤ D.integral (fun x => (u b x) ^ p)) :
    IntegratedMoserWindowUpperBoundData D u T rho p0 p a b eps := by
  let H : ℝ := (b - a) * max (1 : ℝ) hpre.Cp
  have haT : a ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_of_lt hpre.ha_pos, le_trans hpre.hab (le_of_lt hpre.hb_lt)⟩
  have hbT : b ∈ Set.Icc a T :=
    ⟨hpre.hab, le_of_lt hpre.hb_lt⟩
  have hYa : D.integral (fun x => (u a x) ^ p) ≤ hpre.Cp :=
    hpre.currentLpBound_on_Icc a ⟨le_rfl, hpre.hab⟩
  have hmaxInt :
      ∫ s in a..b,
        max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)) ≤ H := by
    simpa [H] using
      integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
        (D := D) (u := u) (a := a) (b := b) (M := hpre.Cp) (p := p)
        hpre.hab hpre.maxOne_int hpre.currentLpBound_on_Icc
  rcases
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := hpre.Cp) (H := H)
      hinteg hpre.hp hpre.hp_nonneg haT hbT hYa hYb_nonneg hmaxInt with
    ⟨Cgrad, hCgrad_nonneg, hgrad⟩
  let Gbound : ℝ := (hpre.Cp + Cgrad * p * H) / 2
  have hG_le :
      ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
      Gbound := by
    dsimp [Gbound]
    nlinarith [hgrad]
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := hpre.Cp) (eps := eps)
      (Gbound := Gbound)
      hrel hpre.hp heps hpre.hab hpre.ha_pos hpre.hb_lt
      hpre.higher_int hpre.gradient_int hpre.currentLpBound_on_Icc hG_le with
    ⟨Ceps, hCeps_nonneg, hHigher⟩
  exact
    { Cp := hpre.Cp
      H := H
      currentLpBound_on_Icc := hpre.currentLpBound_on_Icc
      maxOneIntegralBound := hmaxInt
      Cgrad := Cgrad
      Cgrad_nonneg := hCgrad_nonneg
      gradientIntegralBound := hgrad
      Ceps := Ceps
      Ceps_nonneg := hCeps_nonneg
      higherPowerIntegralBound := by
        simpa [Gbound] using hHigher }

end IntegratedMoserWindowUpperBoundData
```

This wrapper is the clean next step. It shows exactly what the existing fixed-window lemmas already buy:

```text
current Lp bound on [a,b]
+ time-integrability from IntegratedMoserFirstCrossingRegularity
+ integrated dissipation
+ relative interpolation
+ endpoint nonnegativity at b
=> fixed-window gradient bound and fixed-window ∫Y_{p+rho} bound
```

It still does not assert a new `LpPowerBoundedBefore` for `p + rho`, because a fixed-window integral bound is weaker than a uniform-in-time pointwise bound on the whole interval `(0,T)`.

## Optional axiom-print checks

After the new definitions, optionally add:

```lean
#print axioms intervalIntegrable_of_integrableOn_uIcc_subset
#print axioms intervalIntegrable_max_one_of_intervalIntegrable
#print axioms IntegratedMoserPrecrossingIntervalData.of_regularity_and_Lp
#print axioms IntegratedMoserWindowUpperBoundData.of_precrossing
```

These should report no new axioms beyond imported foundational/classical ones. Do not keep them if the file is trying to reduce diagnostic noise; the current repository already uses `#print axioms` heavily in this area, so either choice is consistent.

## What not to prove in this commit

Do **not** prove any of the following in this plumbing commit:

```lean
IntegratedMoserFirstCrossingStep D u T rho p0
```

from the fixed-window lemmas. The existing lemmas give fixed-window integral bounds, not the global before-`T` pointwise `LpPowerBoundedBefore` promotion.

Do **not** prove:

```lean
LpPowerBoundedBefore D (p + rho) T u
```

from `IntegratedMoserWindowUpperBoundData`. That would be the high-excursion / first-crossing analytic frontier and is not justified by the present APIs.

Do **not** derive:

```lean
MoserDissipationDropBeforeNonnegB D u T rho p0
RelativeMoserInterpolationBefore D u T rho p0
```

from `IntegratedMoserFirstCrossingRegularity`, `Corollary_2_1`, `Proposition_2_5`, or the integrated-step route. Those remain separate analytic surfaces.

Do **not** prove endpoint nonnegativity for arbitrary abstract domains:

```lean
0 ≤ D.integral (fun x => (u b x) ^ p)
```

The current `BoundedDomainData` abstraction does not provide measure positivity or integral monotonicity. Keep this as an explicit hypothesis in the generic wrapper, or specialize later to `intervalDomain` using concrete interval-integral nonnegativity plus positivity of `u`.

Do **not** manufacture `IntegratedMoserFirstCrossingRegularity` from `IsPaper2ClassicalSolution` in this file. The regularity package asks for closed-time continuity and time integrability at every ladder exponent. The current classical-solution API has useful interval-domain spatial integrability lemmas, but not a generic all-exponent time-integrability/closed-time continuity producer for arbitrary `BoundedDomainData`.

Do **not** introduce a named high-excursion or first-crossing frontier in this commit. The honest next source change is the fixed-window plumbing above.

## Minimal commit summary

A good source commit title would be:

```text
P3MoserIntegratedClosure: add fixed-window integrated plumbing
```

Expected touched file:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Expected logical diff:

```text
IntegratedMoserFirstCrossingRegularity
  -> intervalIntegrable producers on [a,b]
LpPowerBoundedBefore
  -> current Cp bound on Icc a b
pre-data bundle
  -> fixed-window upper-bound bundle using existing lemmas
```

No new analytic claim is needed, and no old pointwise Moser atom is derived.
