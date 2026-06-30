# Q2489 shen1 — from precrossing time integrals to a genuine first-crossing step

Repo: `xiangyazi24/Shen_work`

Target namespace for the route map:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Current source status: `P3MoserIntegratedClosure.lean` has the fixed-window helpers through

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

and then still treats

```lean
IntegratedMoserFirstCrossingStep D u T rho p0
```

as the hard atom consumed by the iteration/endpoint route.  The gap is exactly the one described in the prompt: fixed-window time-integral control of `Y_{p+rho}` is not a pointwise bound.

## Executive map

The next honest path has three layers.

1. **Lean plumbing from existing regularity to precrossing-window data.**
   This is mostly feasible now.  It supplies interval integrability, current `Y_p` bounds on an `Icc` window from `LpPowerBoundedBefore`, max-one integrability, endpoint membership, and nonnegativity fields.

2. **A topological crossing skeleton.**
   This is feasible but somewhat nontrivial Lean real-analysis plumbing: define first crossing, prove first-crossing existence from continuity and an exceedance, and select a closed interior time window before/around the crossing.

3. **A real analytic lower-average/thickness frontier.**
   This is the hard missing ingredient.  Continuity alone only says a high value has some positive-width high neighborhood; the width may depend badly on the height.  A time-integral bound cannot rule out arbitrarily narrow high spikes.  To get `LpPowerBoundedBefore`, one needs a quantitative high-excursion thickness/modulus-of-continuity/absolute-continuity statement, or an equivalent first-crossing extraction frontier.  This is not routine Lean plumbing.

The final theorem should only be added once layer 3 is supplied honestly.

## Proposed names and dependency order

All names below should live in `ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure`, unless marked Paper3/interval-domain-specific.

### 0. Local notation: cheap, optional

These definitions reduce binder noise in later statements.  They are safe to add.

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

Risk: low.  These are abbreviations only.

### 1. Regularity-to-window integrability producers: feasible Lean plumbing

The fixed-window precrossing skeleton needs `IntervalIntegrable` hypotheses over `a..b`.  The existing regularity package stores `IntegrableOn ... (Set.uIcc 0 T) volume`, so the next plumbing lemmas should restrict integrability to subintervals.

Suggested names:

```lean
/-- Restrict an `IntegrableOn` hypothesis on `uIcc 0 T` to an interval integral
on `a..b`.  This is a generic real-analysis helper. -/
theorem intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    {f : ℝ → ℝ} {T a b : ℝ}
    (hint : IntegrableOn f (Set.uIcc (0 : ℝ) T) volume)
    (hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable f volume a b := by
  -- Lean plumbing: unfold `IntervalIntegrable` if needed and use
  -- `IntegrableOn.mono_set`/the current Mathlib name.
  sorry

/-- Power-profile interval integrability from
`IntegratedMoserFirstCrossingRegularity`. -/
theorem IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => integratedMoserEnergy D u p s) volume a b := by
  exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    (hreg.powerTimeIntegrable p hp) hsub

/-- Gradient-profile interval integrability from
`IntegratedMoserFirstCrossingRegularity`. -/
theorem IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => integratedMoserGradientEnergy D u p s) volume a b := by
  exact intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
    (hreg.gradientTimeIntegrable p hp) hsub
```

Risk: low-to-medium.  The only risk is the exact Mathlib lemma name for restricting `IntegrableOn` to a subset.  This is plumbing, not a mathematical frontier.

### 2. Max-one integrability producer: feasible Lean plumbing, but not automatic from a bound alone

The current helper `integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound` requires `IntervalIntegrable (fun s => max 1 (Y_p s)) volume a b`.  This is not a consequence of a pointwise upper bound alone in the abstract API, but it follows from interval integrability of `Y_p` plus integrability of constants and closure of integrability under `max`.

Suggested name:

```lean
/-- If `Y` is interval-integrable, then `max 1 Y` is interval-integrable. -/
theorem intervalIntegrable_max_one_of_intervalIntegrable
    {Y : ℝ → ℝ} {a b : ℝ}
    (hY : IntervalIntegrable Y volume a b) :
    IntervalIntegrable (fun s => max (1 : ℝ) (Y s)) volume a b := by
  -- Lean plumbing: use `hY.max intervalIntegrable_const` or equivalent.
  sorry

/-- Max-one current-energy interval integrability from first-crossing regularity. -/
theorem IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hp : p0 ≤ p)
    (hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s => max (1 : ℝ) (integratedMoserEnergy D u p s))
      volume a b := by
  exact intervalIntegrable_max_one_of_intervalIntegrable
    (hreg.power_intervalIntegrable_of_Icc hp hsub)
```

Risk: low-to-medium.  The Mathlib name for integrability under `max` may need adjustment.

### 3. Energy nonnegativity producers: real analytic in abstract, feasible for concrete interval-domain classical solutions

Both the extraction lemma and lower-average arguments need nonnegativity of energy values.  In the abstract `BoundedDomainData` API this is **not derivable**.  For `intervalDomain` plus a positive classical solution it should be provable by interval integral positivity of a nonnegative integrand.

Keep the abstract frontier explicit:

```lean
/-- Nonnegativity of all relevant Moser energies on a finite horizon.

This is not derivable from bare `BoundedDomainData`.  For `intervalDomain` and
positive classical solutions, prove it separately from positivity of `u` and
integral monotonicity. -/
def IntegratedMoserEnergyNonnegativity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → 0 ≤ p → ∀ t, t ∈ Set.Icc (0 : ℝ) T →
    0 ≤ integratedMoserEnergy D u p t
```

Suggested concrete producer:

```lean
theorem intervalDomain_integratedMoserEnergyNonnegativity_of_classicalSolution
    {params : CM2Params} {T p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hp0_nonneg : 0 ≤ p0)
    (hpow_int :
      ∀ pExp : ℝ, p0 ≤ pExp → ∀ t, 0 < t → t < T →
        IntervalIntegrable
          (intervalDomainLift
            (fun x : intervalDomain.Point => (u t x) ^ pExp))
          volume 0 1) :
    IntegratedMoserEnergyNonnegativity intervalDomain u T p0 := by
  -- Real/interval-domain plumbing, not true for arbitrary `BoundedDomainData`.
  sorry
```

Risk: medium.  The concrete proof needs the interval-domain integral monotonicity setup.  Mathematically it is standard for positive classical solutions; abstractly it must remain a field.

### 4. Current `Y_p` Icc bound from `LpPowerBoundedBefore`: easy plumbing

This packages the current exponent bound into the shape expected by the precrossing skeleton.

```lean
theorem currentEnergy_le_Icc_of_LpPowerBoundedBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p a b Cp : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (hCp : ∀ t, 0 < t → t < T → integratedMoserEnergy D u p t ≤ Cp)
    (ha : 0 < a) (hb : b < T) :
    ∀ s ∈ Set.Icc a b, integratedMoserEnergy D u p s ≤ Cp := by
  intro s hs
  exact hCp s (lt_of_lt_of_le ha hs.1) (lt_of_le_of_lt hs.2 hb)
```

In practice `hCp` comes from unpacking `hLp`:

```lean
theorem exists_currentEnergy_Icc_bound_of_LpPowerBoundedBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p a b : ℝ}
    (hLp : LpPowerBoundedBefore D p T u)
    (ha : 0 < a) (hb : b < T) :
    ∃ Cp, ∀ s ∈ Set.Icc a b, integratedMoserEnergy D u p s ≤ Cp := by
  rcases hLp with ⟨Cp, hCp⟩
  exact ⟨Cp, currentEnergy_le_Icc_of_LpPowerBoundedBefore
    hLp hCp ha hb⟩
```

Risk: low.  Adjust unfolding if `integratedMoserEnergy` is not used.

### 5. Build precrossing data from producers: feasible plumbing

Once the Q2475 precrossing data structure is in the source, add a constructor that fills it from `hreg`, `hLp`, and `IntegratedMoserEnergyNonnegativity`.

Suggested name:

```lean
theorem integratedMoserPrecrossingIntervalData_of_LpBoundedBefore
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b Cp : ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hp : p0 ≤ p) (hp_nonneg : 0 ≤ p)
    (hrho_nonneg : 0 ≤ rho)
    (hab : a < b) (ha_pos : 0 < a) (hb_lt : b < T)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hsub : Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T)
    (hYp_le : ∀ s ∈ Set.Icc a b,
      integratedMoserEnergy D u p s ≤ Cp) :
    IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b Cp := by
  -- Fill fields from hreg/hsub/hYp_le/hnonneg.
  -- q := p + rho is only needed for higherPower_intervalIntegrable.
  sorry
```

Key details:

* `higherPower_intervalIntegrable` needs `p + rho ≥ p0`, from `hp` and `hrho_nonneg`.
* `right_currentEnergy_nonneg` needs `hnonneg p hp hp_nonneg b ...`.
* `maxOneEnergy_intervalIntegrable` needs the max-one producer above.

Risk: low after the preceding plumbing exists.

### 6. The fixed-window upper estimate, normalized for first crossing: feasible after the skeleton

The current precrossing theorem should be wrapped into a form that exposes a named upper-bound function.  This helps the later crossing contradiction avoid repeatedly destructing `∃ C` and `∃ Ceps`.

Suggested structure:

```lean
/-- Constants produced by the fixed-window integrated Moser estimate. -/
structure IntegratedMoserWindowUpperBoundData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (rho p a b Cp eps : ℝ) where
  Gbound : ℝ
  Ceps : ℝ
  Ceps_nonneg : 0 ≤ Ceps
  gradient_bound :
    ∫ s in a..b, integratedMoserGradientEnergy D u p s ≤ Gbound
  higherPower_timeIntegral_bound :
    ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤
      eps * Gbound + (b - a) * (Ceps * Cp)

/-- Package the existing fixed-window lemmas into the bound data used by the
first-crossing argument. -/
theorem integratedMoser_windowUpperBoundData_of_precrossing
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b Cp eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p0 p a b Cp)
    (heps : 0 < eps) :
    IntegratedMoserWindowUpperBoundData D u rho p a b Cp eps := by
  -- Destructure `integratedMoser_precrossing_higherPower_timeIntegral_le`.
  sorry
```

Risk: low if the Q2475 skeleton is committed.  This is just packaging constants.

## The hard part: high-excursion lower-average/thickness

### 7. Continuity alone is not enough

A tempting but false route is:

1. if `Y_{p+rho}(b)` crosses a large threshold, continuity gives a small interval where `Y_{p+rho}` is still large;
2. integrate over that interval and compare with the fixed-window upper bound.

This is not enough.  The interval may be arbitrarily small.  Current upper bounds have a term like

```lean
eps * Gbound + (b - a) * (Ceps * Cp)
```

and the integrated gradient bound contains an endpoint term inherited from `Y_p`, not purely a length-scaled term.  After dividing by `(b-a)`, the `eps * Gbound / (b-a)` term can blow up on tiny windows.  Choosing a smaller `eps` is not automatically enough, because `Ceps` may blow up and the current API carries no quantitative dependence of `Ceps` on `eps`.

Therefore the honest next analytic theorem must supply either:

* a uniform high-excursion thickness/modulus for `Y_{p+rho}`;
* an absolute-continuity/derivative bound strong enough to imply such thickness;
* or a quantitative relative-Moser constant schedule that can be balanced against arbitrarily small windows.

### 8. Topological first-crossing skeleton: feasible but not sufficient

Still useful plumbing:

```lean
/-- `τ` is a first crossing of level `B` by `Y` before time `T`. -/
def MoserFirstCrossingAt (Y : ℝ → ℝ) (T B τ : ℝ) : Prop :=
  0 < τ ∧ τ < T ∧ Y τ = B ∧
    ∀ s, 0 < s → s < τ → Y s < B

/-- Existence of a first crossing from continuity, an initial strict bound, and
some later exceedance. -/
theorem exists_moserFirstCrossingAt_of_continuousOn_exceeds
    {Y : ℝ → ℝ} {T B : ℝ}
    (hT : 0 < T)
    (hcont : ContinuousOn Y (Set.Icc (0 : ℝ) T))
    (hinit : Y 0 < B)
    (hexceeds : ∃ t, 0 < t ∧ t < T ∧ B ≤ Y t) :
    ∃ τ, MoserFirstCrossingAt Y T B τ := by
  -- Real-analysis plumbing: use IVT/compactness/infimum of crossing set.
  sorry
```

Risk: medium.  This is mathlib/topology plumbing, but mathematically routine.

### 9. Initial no-crossing zone: feasible from continuity and initial bound

This avoids the endpoint problem `a = 0` when selecting a backward window.

```lean
theorem integratedMoser_initial_higherPower_safe_interval
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 q B : ℝ}
    (hT : 0 < T)
    (hcont : ContinuousOn (fun t => integratedMoserEnergy D u q t)
      (Set.Icc (0 : ℝ) T))
    (hY0 : integratedMoserEnergy D u q 0 < B) :
    ∃ δ > 0, δ < T ∧
      ∀ t, 0 ≤ t → t ≤ δ → integratedMoserEnergy D u q t < B := by
  -- Continuity at 0 within `Icc 0 T`.
  sorry
```

Risk: medium-low.  It is standard real-analysis plumbing.

### 10. Honest analytic frontier: lower-average/thickness data

Do not hide this inside a proof.  Make it an explicit frontier package.

```lean
/-- Quantitative high-excursion data for the higher-power energy.

This is the real analytic floor needed to convert a time-integral upper bound
into pointwise control.  It says that a first crossing of a high level `B`
produces an interior window `[a,b]` on which the higher-power energy has a
large lower average, with all endpoint and length information needed by the
fixed-window upper estimate.

The `dominates` field is intentionally not just `lower ≤ ∫Yq`; it is the
quantitative comparison needed to contradict the fixed-window upper bound after
choosing `eps` and the window constants. -/
structure IntegratedMoserHighExcursionWindowFrontier
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  chooseLevel :
    ∀ p Cp,
      p0 ≤ p → 0 ≤ p → 0 ≤ rho →
      LpPowerBoundedBefore D p T u →
      ∃ B > 0, ∀ τ,
        MoserFirstCrossingAt
          (fun t => integratedMoserEnergy D u (p + rho) t) T B τ →
        ∃ a b eps,
          0 < eps ∧
          a < b ∧ 0 < a ∧ b < T ∧
          a ∈ Set.Icc (0 : ℝ) T ∧ b ∈ Set.Icc a T ∧
          Set.uIcc a b ⊆ Set.uIcc (0 : ℝ) T ∧
          -- current exponent stays bounded on the crossing window
          (∀ s ∈ Set.Icc a b,
            integratedMoserEnergy D u p s ≤ Cp) ∧
          -- quantitative lower average for the higher exponent
          (∀ Gbound Ceps,
            0 ≤ Ceps →
            (∫ s in a..b,
              integratedMoserEnergy D u (p + rho) s) ≤
                eps * Gbound + (b - a) * (Ceps * Cp) →
            False)
```

This statement is deliberately strong: its last field is the exact contradiction interface against the upper-bound theorem.  If a more quantitative theorem is available, replace the last field by explicit inequalities such as

```lean
(b - a) * (B / 2) ≤ ∫ s in a..b, integratedMoserEnergy D u (p + rho) s
```

plus a separate threshold-selection lemma proving that this lower bound dominates the upper bound.  But do **not** pretend continuity alone gives enough.

Risk: high.  This is the genuine analytic frontier.

A more decomposed version is preferable if one has quantitative constants:

```lean
structure IntegratedMoserHighExcursionLowerAverage
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  lowerAverage :
    ∀ p B τ,
      p0 ≤ p → 0 ≤ p → 0 ≤ rho → 0 < B →
      MoserFirstCrossingAt
        (fun t => integratedMoserEnergy D u (p + rho) t) T B τ →
      ∃ a b,
        a < b ∧ 0 < a ∧ b < T ∧
        a ∈ Set.Icc (0 : ℝ) T ∧ b ∈ Set.Icc a T ∧
        (b - a) * (B / 2) ≤
          ∫ s in a..b, integratedMoserEnergy D u (p + rho) s

structure IntegratedMoserUpperLowerSeparation
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop where
  chooseLevel :
    ∀ p Cp,
      p0 ≤ p → 0 ≤ p → 0 ≤ rho →
      ∃ B > 0, ∀ a b eps Gbound Ceps,
        0 < eps → 0 ≤ Ceps → a < b →
        -- lower average from high excursion
        (b - a) * (B / 2) ≤
          ∫ s in a..b, integratedMoserEnergy D u (p + rho) s →
        -- upper estimate from fixed-window Moser
        (∫ s in a..b, integratedMoserEnergy D u (p + rho) s) ≤
          eps * Gbound + (b - a) * (Ceps * Cp) →
        False
```

In this decomposed form, `IntegratedMoserUpperLowerSeparation` is where the quantitative dependence of `eps`, `Ceps`, and the crossing-window length must be handled.

## Final extraction theorem shape

Once the preceding producers and the hard high-excursion/separation frontier are available, the final theorem is mostly plumbing.

```lean
/-- First-crossing/pointwise extraction from the fixed-window integrated Moser
route plus a genuine high-excursion thickness frontier.

This is the theorem that should finally produce the atom consumed by
`P3MoserActualWiring`. -/
theorem integratedMoser_firstCrossingStep_of_precrossing_timeIntegral_and_excursion_frontier
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hT : 0 < T)
    (hrho : 0 < rho)
    (hp0_nonneg : 0 ≤ p0)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity D u T p0)
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hexcur : IntegratedMoserHighExcursionWindowFrontier D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0 := by
  intro p hp hLp
  -- 1. unpack current `LpPowerBoundedBefore` to get `Cp`.
  -- 2. set q := p + rho and prove q >= p0, 0 <= q.
  -- 3. choose the high-crossing level `B` from `hexcur`.
  -- 4. use initial bound/continuity to rule out crossing at t = 0.
  -- 5. suppose `∃ t, Y_q t >= B`; get a first crossing `τ`.
  -- 6. use `hexcur` to get `[a,b]`, `eps`, current `Y_p` Icc bound,
  --    and the contradiction interface.
  -- 7. build `IntegratedMoserPrecrossingIntervalData` from hreg, hnonneg,
  --    the current Icc bound, and interval-integrability restriction lemmas.
  -- 8. apply `integratedMoser_windowUpperBoundData_of_precrossing`.
  -- 9. feed its upper bound to the contradiction interface.
  -- 10. conclude `∀ t, 0 < t -> t < T -> Y_q t < B`, hence
  --     `LpPowerBoundedBefore D q T u` with witness `B` or `max B 0`.
  sorry
```

Risk: medium after `hexcur`; high before `hexcur`.  The proof is long but conceptually straightforward once the high-excursion frontier is honest.

## Dependency order checklist

1. Add optional profile definitions `integratedMoserEnergy` and `integratedMoserGradientEnergy`.
2. Add `intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset`.
3. Add `IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc` and `.gradient_intervalIntegrable_of_Icc`.
4. Add `intervalIntegrable_max_one_of_intervalIntegrable` and `.maxOneEnergy_intervalIntegrable_of_Icc`.
5. Add/keep an explicit `IntegratedMoserEnergyNonnegativity` frontier; prove an interval-domain producer separately from classical positivity.
6. Add `integratedMoserPrecrossingIntervalData_of_LpBoundedBefore` to build the Q2475 precrossing structure.
7. Add `IntegratedMoserWindowUpperBoundData` and `integratedMoser_windowUpperBoundData_of_precrossing` as a clean packaging wrapper around the fixed-window theorem.
8. Add `MoserFirstCrossingAt`, `exists_moserFirstCrossingAt_of_continuousOn_exceeds`, and `integratedMoser_initial_higherPower_safe_interval`.
9. Add the hard analytic frontier: either `IntegratedMoserHighExcursionWindowFrontier`, or the decomposed pair `IntegratedMoserHighExcursionLowerAverage` plus `IntegratedMoserUpperLowerSeparation`.
10. Only then add `integratedMoser_firstCrossingStep_of_precrossing_timeIntegral_and_excursion_frontier`.

## What is feasible Lean plumbing versus real analytic floor

### Feasible Lean plumbing

* Restricting `IntegrableOn` on `uIcc 0 T` to `IntervalIntegrable` on `a..b`.
* Closure of interval integrability under `max 1`.
* Extracting an Icc `Y_p ≤ Cp` bound from `LpPowerBoundedBefore`.
* Proving `p + rho ≥ p0` and `0 ≤ p + rho` from `hp`, `hrho`, `hp0_nonneg`.
* Packaging the fixed-window upper bound into a structure.
* First-crossing existence from continuity and an exceedance.
* Initial no-crossing interval from continuity at `0` and an initial bound.

### Real analytic floors

* Nonnegativity of abstract energies unless specialized to `intervalDomain` plus positive classical solutions.
* Producing the full `IntegratedMoserFirstCrossingRegularity` package from the PDE solution for every ladder exponent.
* Any quantitative high-excursion thickness/lower-average theorem strong enough to rule out narrow spikes.
* Any quantitative control on the dependence `eps ↦ Ceps` in relative Moser if the contradiction chooses `eps` based on crossing-window length.
* The final pointwise extraction theorem itself, unless it is explicitly parameterized by the high-excursion frontier.

## No-go route

Do not add a theorem of the form

```lean
theorem LpPowerBoundedBefore_of_higherPower_timeIntegral_bound
    ...
    (h : ∫ s in a..b, integratedMoserEnergy D u (p + rho) s ≤ K) :
    LpPowerBoundedBefore D (p + rho) T u := by
  ...
```

Such a statement is false without additional regularity/thickness data.  A function can have uniformly bounded integrals on small windows and still have arbitrarily high narrow spikes unless one controls its time modulus or derivative in a quantitative way.  The correct target is the frontier-parameterized first-crossing theorem above.

## Suggested `#print axioms` targets after implementation

```lean
#print axioms intervalIntegrable_of_integrableOn_uIcc_of_Icc_subset
#print axioms intervalIntegrable_max_one_of_intervalIntegrable
#print axioms IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
#print axioms IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
#print axioms exists_moserFirstCrossingAt_of_continuousOn_exceeds
#print axioms integratedMoser_initial_higherPower_safe_interval
#print axioms integratedMoser_windowUpperBoundData_of_precrossing
#print axioms integratedMoser_firstCrossingStep_of_precrossing_timeIntegral_and_excursion_frontier
```

The last print should depend on the high-excursion frontier as a hypothesis, not on hidden axioms or fake conversions.
