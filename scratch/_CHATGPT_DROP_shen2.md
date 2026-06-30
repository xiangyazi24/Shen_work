# Q2447 shen2: honest first-crossing skeleton after integrated relative-Moser time bound

Repo target: `xiangyazi24/Shen_work`.

## Verdict

After the three integrated relative-Moser time-bound lemmas compile, the next smallest honest skeleton is a **pre-crossing subinterval package** plus wrappers that produce only a **time-integral / averaged bound for the next exponent**:

```lean
∫ s in a..b, Y_{p+rho}(s) ≤ ...
```

or, when `a < b`,

```lean
(b - a)⁻¹ * ∫ s in a..b, Y_{p+rho}(s) ≤ ...
```

Do **not** produce `LpPowerBoundedBefore D (p + rho) T u` yet.  That would require a real continuity/first-crossing argument converting a time-average bound into a pointwise bound and is exactly the remaining hard step.

The key point: the next lemma should combine already-proved fixed-interval estimates, not assert the first-crossing theorem.  It should assume the pre-crossing uniform current-exponent bound on a specific interval and the necessary interval-integrability data explicitly.

## Placement / imports / namespace

Add these to:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

after the current helper lemmas:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

The file’s existing import/open block should remain sufficient:

```lean
import ShenWork.PDE.P3MoserDissipationShape

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

No new import should be needed unless the local proof chooses to use extra convenience lemmas for division/averaging.

## Step 1: pre-crossing subinterval data

This is the minimal local data package.  It is intentionally about a **fixed interval** `[a,b]`, not the whole horizon.  The field `currentLp_le` is the “pre-crossing” assumption for the current exponent; `currentLp_nonneg` is needed by the integrated-gradient extraction endpoint bookkeeping.

```lean
/-- Local pre-crossing data on a fixed time interval `[a,b]`.

This packages only the hypotheses needed to combine the integrated dissipation
estimate, the `max 1 Y_p` time-integral bound, and the integrated relative-Moser
interpolation estimate.  It does not contain any first-crossing conclusion. -/
structure IntegratedMoserPrecrossingIntervalData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p a b M : ℝ) : Prop where
  hab : a ≤ b
  ha_pos : 0 < a
  hb_lt : b < T
  currentLp_le :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ M
  currentLp_nonneg :
    ∀ s ∈ Set.Icc a b,
      0 ≤ D.integral (fun x => (u s x) ^ p)
  maxOne_integrable :
    IntervalIntegrable
      (fun s => max (1 : ℝ)
        (D.integral (fun x => (u s x) ^ p)))
      MeasureTheory.volume a b
  higherPower_integrable :
    IntervalIntegrable
      (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      MeasureTheory.volume a b
  gradient_integrable :
    IntervalIntegrable
      (fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      MeasureTheory.volume a b
```

### Tiny helper methods that should compile

These are optional but make later proof scripts much less brittle.

```lean
namespace IntegratedMoserPrecrossingIntervalData

variable {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
variable {T rho p a b M : ℝ}

/-- Left endpoint belongs to the pre-crossing interval. -/
theorem left_mem_Icc
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    a ∈ Set.Icc a b :=
  ⟨le_rfl, hI.hab⟩

/-- Right endpoint belongs to the pre-crossing interval. -/
theorem right_mem_Icc
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    b ∈ Set.Icc a b :=
  ⟨hI.hab, le_rfl⟩

/-- The left endpoint is a valid time for the integrated dissipation inequality. -/
theorem left_mem_Icc_zero_T
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    a ∈ Set.Icc (0 : ℝ) T :=
  ⟨hI.ha_pos.le, le_trans hI.hab hI.hb_lt.le⟩

/-- The right endpoint is a valid successor time for the integrated dissipation inequality. -/
theorem right_mem_Icc_left_T
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    b ∈ Set.Icc a T :=
  ⟨hI.hab, hI.hb_lt.le⟩

/-- Current exponent bound at the left endpoint. -/
theorem currentLp_left_le
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    D.integral (fun x => (u a x) ^ p) ≤ M :=
  hI.currentLp_le a hI.left_mem_Icc

/-- Current exponent nonnegativity at the right endpoint. -/
theorem currentLp_right_nonneg
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    0 ≤ D.integral (fun x => (u b x) ^ p) :=
  hI.currentLp_nonneg b hI.right_mem_Icc

/-- The already-proved max-one helper specialized to the pre-crossing data. -/
theorem maxOne_timeIntegral_le
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∫ s in a..b,
      max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)) ≤
        (b - a) * max (1 : ℝ) M :=
  intervalIntegral_max_one_le_length_mul_max_one_of_Icc_bound
    (Y := fun s => D.integral (fun x => (u s x) ^ p))
    hI.hab hI.maxOne_integrable hI.currentLp_le

end IntegratedMoserPrecrossingIntervalData
```

These helpers do not smuggle any analysis: they are endpoint membership and direct use of the previous max-one lemma.

## Step 2: gradient bound from integrated dissipation on a pre-crossing interval

This wrapper is the first place where the integrated dissipation estimate and the max-one bound meet.  It should output only a bound on the **time-integrated gradient**, not a next-exponent pointwise bound.

Assuming the extraction lemma from the previous patch has the intended shape, the statement should be:

```lean
/-- Integrated dissipation plus pre-crossing bounds gives a bound on the
time-integrated Moser gradient over `[a,b]`.

This only controls `∫G_p`; it does not produce any next-exponent pointwise bound. -/
theorem integratedMoser_gradient_timeIntegral_le_of_precrossing_interval
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        C * p * ((b - a) * max (1 : ℝ) M) + M := by
  rcases hdiss p hp with ⟨C, hC_nonneg, hdiss_p⟩
  refine ⟨C, hC_nonneg, ?_⟩
  exact
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (t1 := a) (t2 := b) (C := C)
      hp hC_nonneg
      hI.left_mem_Icc_zero_T hI.right_mem_Icc_left_T
      hdiss_p
      hI.currentLp_left_le
      hI.currentLp_right_nonneg
      hI.maxOne_timeIntegral_le
```

If the already-added extraction lemma names endpoint hypotheses differently, adapt only the final call.  The wrapper’s **statement** is the important stable interface.

## Step 3: higher-power time-integral bound from pre-crossing data

This is the central “next-exponent time-integral” skeleton.  It combines:

1. current-exponent pre-crossing bound `Y_p ≤ M`;
2. integrated dissipation gradient extraction;
3. max-one time-integral bound;
4. relative-Moser higher-power time-integral bound.

It still outputs only a time-integral bound.

```lean
/-- On a pre-crossing interval, integrated dissipation plus relative Moser
interpolation gives a time-integral bound for the next exponent.

This is still not a first-crossing theorem: the conclusion is an integral bound
for `Y_{p+rho}`, not `LpPowerBoundedBefore D (p + rho) T u`. -/
theorem integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∃ C Ceps, 0 ≤ C ∧ 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * ((C * p * ((b - a) * max (1 : ℝ) M) + M) / 2) +
          (b - a) * (Ceps * M) := by
  rcases
    integratedMoser_gradient_timeIntegral_le_of_precrossing_interval
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      hdiss hp hI with
    ⟨C, hC_nonneg, htwoG_le⟩
  have hG_le :
      ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        (C * p * ((b - a) * max (1 : ℝ) M) + M) / 2 := by
    nlinarith
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M) (eps := eps)
      (Gbound := (C * p * ((b - a) * max (1 : ℝ) M) + M) / 2)
      hrel hp heps hI.hab hI.ha_pos hI.hb_lt
      hI.higherPower_integrable hI.gradient_integrable
      hI.currentLp_le hG_le with
    ⟨Ceps, hCeps_nonneg, hZ_le⟩
  exact ⟨C, Ceps, hC_nonneg, hCeps_nonneg, hZ_le⟩
```

This wrapper is honest because it assumes every interval-integrability and pre-crossing hypothesis explicitly and concludes only a time-integral inequality.

## Step 4: averaged bound, still not pointwise

For first-crossing arguments, one usually wants to say that if the interval is long enough, then some time slice is controlled.  The next non-hard wrapper should only divide by interval length.  It still does **not** assert existence of a good time or pointwise boundedness.

```lean
/-- Averaged version of
`integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval`.

This only divides the time-integral bound by the interval length.  It does not
extract a pointwise time slice. -/
theorem integratedMoser_higherPower_timeAverage_le_of_precrossing_interval
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (heps : 0 < eps)
    (hab_strict : a < b)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∃ C Ceps, 0 ≤ C ∧ 0 ≤ Ceps ∧
      (1 / (b - a)) *
        ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        (1 / (b - a)) *
          (eps * ((C * p * ((b - a) * max (1 : ℝ) M) + M) / 2) +
            (b - a) * (Ceps * M)) := by
  rcases
    integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M) (eps := eps)
      hdiss hrel hp heps hI with
    ⟨C, Ceps, hC_nonneg, hCeps_nonneg, hZ_le⟩
  refine ⟨C, Ceps, hC_nonneg, hCeps_nonneg, ?_⟩
  have hlen_nonneg : 0 ≤ 1 / (b - a) := by
    positivity
  exact mul_le_mul_of_nonneg_left hZ_le hlen_nonneg
```

This statement intentionally leaves the right-hand side unsimplified.  A later purely algebraic lemma can simplify it if useful, but avoiding simplification is more robust for Lean.

## Where the hard gap remains

Even after the averaged bound, the missing theorem is still the real first-crossing/continuity step:

```lean
-- NOT for this patch:
theorem integratedMoserFirstCrossingStep_of_integrated_dissipation_relative
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 : ℝ}
    (hT : 0 < T)
    (hrho : 0 < rho)
    (hreg : IntegratedMoserFirstCrossingRegularity D u T p0)
    (hdiss : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0) :
    IntegratedMoserFirstCrossingStep D u T rho p0
```

The unproved analytic content is:

1. choosing a crossing interval from a hypothetical first time where `Y_{p+rho}` exceeds a threshold;
2. using continuity of `Y_{p+rho}` on that interval to get a lower bound on its time average;
3. contradicting the averaged upper bound above by choosing the threshold/interval length/constants correctly;
4. globalizing the resulting local-in-time contradiction to all `t ∈ (0,T)`.

The proposed pre-crossing wrappers do none of these.  They only provide the fixed-interval quantitative upper estimate that a later first-crossing contradiction will consume.

## Suggested `#print axioms`

```lean
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserPrecrossingIntervalData
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserPrecrossingIntervalData.maxOne_timeIntegral_le
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.integratedMoser_gradient_timeIntegral_le_of_precrossing_interval
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.integratedMoser_higherPower_timeAverage_le_of_precrossing_interval
```

Expected profile: no `sorryAx`, no custom axioms.  These are wrappers around already-proved fixed-interval inequalities and explicit pre-crossing assumptions.
