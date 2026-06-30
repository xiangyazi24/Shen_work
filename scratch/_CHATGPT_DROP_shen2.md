# Q2485 shen2: precrossing interval skeleton audit

Repo target: `xiangyazi24/Shen_work`.

## Verdict

The corrected precrossing interval skeleton is mathematically honest and is the right next local production layer, but keep the first commit minimal:

1. add the local `IntegratedMoserPrecrossingIntervalData` structure;
2. add endpoint/membership helpers and the max-one time-integral helper;
3. add a gradient-integral bound wrapper;
4. add the higher-power **time-integral** bound wrapper;
5. **do not add the average theorem yet**.

The average theorem is allowed by the hard constraint, but it adds no useful API right now: it is just multiplication by `(b - a)⁻¹`, introduces a strict-length hypothesis and possible `positivity`/division proof noise, and no later theorem currently consumes that averaged form.  The time-integral bound is the stable API; a future first-crossing lower-average lemma can divide by the interval length at the exact point where it needs the form.

Most important hard constraint: this patch must not conclude

```lean
LpPowerBoundedBefore D (p + rho) T u
```

or any pointwise-in-time bound.  The output should remain a fixed-window integral estimate for `Y_{p+rho}`.

## Current helper signatures that matter

The current extraction lemma in `P3MoserIntegratedClosure.lean` has this exact API:

```lean
theorem integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M H : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (haT : a ∈ Set.Icc (0 : ℝ) T)
    (hbT : b ∈ Set.Icc a T)
    (hYa : D.integral (fun x => (u a x) ^ p) ≤ M)
    (hYb_nonneg : 0 ≤ D.integral (fun x => (u b x) ^ p))
    (hmaxInt :
      ∫ s in a..b, max 1 (D.integral (fun x => (u s x) ^ p)) ≤ H) :
    ∃ C, 0 ≤ C ∧
      2 * ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        M + C * p * H
```

So a wrapper should pass `hinteg` directly.  Do **not** pre-extract `hdiss_p`, do **not** pass a named `C`, and do **not** use old names like `t1`/`t2` unless they match the actual implicit argument names.  The implicit time names are `a` and `b`.

The current relative-Moser gradient-bound consumer has the useful exact shape:

```lean
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
    ...
    (hY_le :
      ∀ s ∈ Set.Icc a b,
        D.integral (fun x => (u s x) ^ p) ≤ M)
    (hG_le :
      ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        Gbound) :
    ∃ Ceps, 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * Gbound + (b - a) * (Ceps * M)
```

This means the precrossing higher-power theorem should call it directly.  Do not route through the weaker theorem and manually rescale again.

The file already has:

```lean
open scoped Interval
```

so interval integral notation `∫ s in a..b, ...` is already available.  No new scoped open is needed.

## Recommended names

The Q2475-style names are acceptable, but I recommend using the existing `_le_of_...` style already present in the file:

```lean
IntegratedMoserPrecrossingIntervalData
IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le
integratedMoser_gradientIntegral_le_of_precrossing_interval
integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
```

If local code already used `integratedMoser_precrossing_gradientIntegral_bound`, that name is also fine.  The `_le_of_precrossing_interval` names better match existing names such as:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
```

## Minimal corrected code skeleton

Place this before the final step-consumer closure lemmas, after the fixed-interval helper lemmas.

```lean
/-- Local pre-crossing data on a fixed interval `[a,b]` for the integrated
Moser production route.

This is deliberately only fixed-window data.  It does not assert a crossing
principle and does not produce any pointwise bound at exponent `p + rho`. -/
structure IntegratedMoserPrecrossingIntervalData
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p a b M : ℝ) : Prop where
  time_le : a ≤ b
  left_pos : 0 < a
  right_lt_T : b < T
  currentLp_le :
    ∀ s ∈ Set.Icc a b,
      D.integral (fun x => (u s x) ^ p) ≤ M
  currentLp_nonneg :
    ∀ s ∈ Set.Icc a b,
      0 ≤ D.integral (fun x => (u s x) ^ p)
  maxOneEnergy_intervalIntegrable :
    IntervalIntegrable
      (fun s => max (1 : ℝ)
        (D.integral (fun x => (u s x) ^ p)))
      volume a b
  higherPower_intervalIntegrable :
    IntervalIntegrable
      (fun s => D.integral (fun x => (u s x) ^ (p + rho)))
      volume a b
  gradient_intervalIntegrable :
    IntervalIntegrable
      (fun s =>
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2))
      volume a b

namespace IntegratedMoserPrecrossingIntervalData

variable {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
variable {T rho p a b M : ℝ}

/-- The left endpoint lies in the pre-crossing interval. -/
theorem left_mem_Icc
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    a ∈ Set.Icc a b :=
  ⟨le_rfl, hI.time_le⟩

/-- The right endpoint lies in the pre-crossing interval. -/
theorem right_mem_Icc
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    b ∈ Set.Icc a b :=
  ⟨hI.time_le, le_rfl⟩

/-- The left endpoint is admissible for the integrated dissipation inequality. -/
theorem left_mem_Icc_zero_T
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    a ∈ Set.Icc (0 : ℝ) T :=
  ⟨hI.left_pos.le, le_trans hI.time_le hI.right_lt_T.le⟩

/-- The right endpoint is admissible as a successor time. -/
theorem right_mem_Icc_left_T
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    b ∈ Set.Icc a T :=
  ⟨hI.time_le, hI.right_lt_T.le⟩

/-- Current-exponent bound at the left endpoint. -/
theorem currentLp_left_le
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    D.integral (fun x => (u a x) ^ p) ≤ M :=
  hI.currentLp_le a hI.left_mem_Icc

/-- Current-exponent nonnegativity at the right endpoint. -/
theorem currentLp_right_nonneg
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    0 ≤ D.integral (fun x => (u b x) ^ p) :=
  hI.currentLp_nonneg b hI.right_mem_Icc

/-- The fixed-interval `max 1 Y_p` bound from pre-crossing data. -/
theorem maxOneEnergy_timeIntegral_le
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∫ s in a..b,
      max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)) ≤
        (b - a) * max (1 : ℝ) M :=
  integratedMoser_maxOneEnergy_timeIntegral_le_of_Icc_bound
    (D := D) (u := u) (a := a) (b := b) (M := M) (p := p)
    hI.time_le hI.maxOneEnergy_intervalIntegrable hI.currentLp_le

end IntegratedMoserPrecrossingIntervalData
```

## Corrected gradient wrapper

The gradient wrapper should return the **unhalved** integral with the `/ 2` already applied, because that is exactly what the relative-Moser gradient-bound consumer needs.

```lean
/-- Pre-crossing version of the integrated Moser gradient bound.

This is only a fixed-window estimate for the time-integrated Moser gradient; it
does not produce the next Moser exponent pointwise. -/
theorem integratedMoser_gradientIntegral_le_of_precrossing_interval
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∃ C, 0 ≤ C ∧
      ∫ s in a..b,
        D.integral (fun x =>
          (D.gradNorm (fun y => (u s y) ^ (p / 2)) x) ^ 2) ≤
        (M + C * p * ((b - a) * max (1 : ℝ) M)) / 2 := by
  rcases
    integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      (H := (b - a) * max (1 : ℝ) M)
      hinteg hp hp_nonneg
      hI.left_mem_Icc_zero_T hI.right_mem_Icc_left_T
      hI.currentLp_left_le hI.currentLp_right_nonneg
      hI.maxOneEnergy_timeIntegral_le with
    ⟨C, hC_nonneg, htwoG_le⟩
  refine ⟨C, hC_nonneg, ?_⟩
  linarith [htwoG_le]
```

### Division-by-2 hazard

`linarith [htwoG_le]` should usually solve the last goal over `ℝ`.  If it does not, switch to:

```lean
  nlinarith [htwoG_le]
```

Do not introduce a separate lemma unless both fail.  The goal is linear in the integral expression; the `/ 2` is just rational normalization.

### Named-argument hazard

The important correction is this call shape:

```lean
integratedMoser_gradientIntegral_le_of_endpoint_and_timeIntegral_bounds
  (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
  (p := p) (a := a) (b := b) (M := M)
  (H := (b - a) * max (1 : ℝ) M)
  hinteg hp hp_nonneg
  ...
```

Avoid named arguments such as `(t1 := a)`, `(t2 := b)`, or `(C := C)`, because they do not match the actual theorem signature.

## Corrected higher-power time-integral wrapper

This is the main useful API output.  It concludes only a time-integral bound.

```lean
/-- On a pre-crossing interval, integrated dissipation plus relative Moser
interpolation gives a time-integral bound for the next exponent.

This is still not a first-crossing theorem: the conclusion is an integral bound
for `Y_{p+rho}`, not `LpPowerBoundedBefore D (p + rho) T u`. -/
theorem integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T rho p0 p a b M eps : ℝ}
    (hinteg : IntegratedMoserDissipationDropBefore D u T rho p0)
    (hrel : RelativeMoserInterpolationBefore D u T rho p0)
    (hp : p0 ≤ p)
    (hp_nonneg : 0 ≤ p)
    (heps : 0 < eps)
    (hI : IntegratedMoserPrecrossingIntervalData D u T rho p a b M) :
    ∃ C Ceps, 0 ≤ C ∧ 0 ≤ Ceps ∧
      ∫ s in a..b,
          D.integral (fun x => (u s x) ^ (p + rho)) ≤
        eps * ((M + C * p * ((b - a) * max (1 : ℝ) M)) / 2) +
          (b - a) * (Ceps * M) := by
  rcases
    integratedMoser_gradientIntegral_le_of_precrossing_interval
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M)
      hinteg hp hp_nonneg hI with
    ⟨C, hC_nonneg, hG_le⟩
  rcases
    relativeMoser_higherPower_timeIntegral_le_of_Icc_currentLp_and_gradient_bound
      (D := D) (u := u) (T := T) (rho := rho) (p0 := p0)
      (p := p) (a := a) (b := b) (M := M) (eps := eps)
      (Gbound := (M + C * p * ((b - a) * max (1 : ℝ) M)) / 2)
      hrel hp heps hI.time_le hI.left_pos hI.right_lt_T
      hI.higherPower_intervalIntegrable hI.gradient_intervalIntegrable
      hI.currentLp_le hG_le with
    ⟨Ceps, hCeps_nonneg, hZ_le⟩
  exact ⟨C, Ceps, hC_nonneg, hCeps_nonneg, hZ_le⟩
```

This direct call is better than first proving an intermediate time-integral lemma and then substituting a gradient bound manually, because the current helper already does exactly that substitution.

## Average theorem: omit now

Do not include the average theorem in the minimal patch.

Reason:

* it adds no new mathematical content beyond multiplying the time-integral theorem by a nonnegative scalar;
* it needs an extra strict interval length hypothesis `a < b`;
* it may create proof noise around `1 / (b - a)` and `positivity`/`inv_nonneg`;
* no current consumer needs the averaged form.

If a later first-crossing lower-average lemma needs it, add it then with a statement like:

```lean
-- Later, not now:
theorem integratedMoser_higherPower_timeAverage_le_of_precrossing_interval
    ...
    (hab_strict : a < b)
    ... :
    ∃ C Ceps, 0 ≤ C ∧ 0 ≤ Ceps ∧
      (1 / (b - a)) *
        ∫ s in a..b, D.integral (fun x => (u s x) ^ (p + rho)) ≤
      (1 / (b - a)) *
        (eps * ((M + C * p * ((b - a) * max (1 : ℝ) M)) / 2) +
          (b - a) * (Ceps * M))
```

If/when adding it, avoid `positivity` fragility by using:

```lean
have hlen_pos : 0 < b - a := sub_pos.mpr hab_strict
have hcoef_nonneg : 0 ≤ 1 / (b - a) := by
  exact inv_nonneg.mpr hlen_pos.le
exact mul_le_mul_of_nonneg_left hZ_le hcoef_nonneg
```

## Other compile hazards and corrections

### `hp_nonneg` is necessary

Do not try to infer `0 ≤ p` from `hp : p0 ≤ p`; the current API does not guarantee `0 ≤ p0`.  Keep `hp_nonneg : 0 ≤ p` as an explicit theorem hypothesis.

### The extra `maxOneEnergy_intervalIntegrable` field is necessary

The max-one bound theorem requires:

```lean
IntervalIntegrable
  (fun s => max (1 : ℝ) (D.integral (fun x => (u s x) ^ p)))
  volume a b
```

Do not try to synthesize this from `powerTimeIntegrable` inside this small patch.  That would require a separate max-preserves-integrability lemma and would increase the blast radius.  The field is the right minimal design.

### Endpoint helpers should use strict `right_lt_T` only by `.le`

For `hbT : b ∈ Set.Icc a T`, use:

```lean
⟨hI.time_le, hI.right_lt_T.le⟩
```

For `haT : a ∈ Set.Icc 0 T`, use:

```lean
⟨hI.left_pos.le, le_trans hI.time_le hI.right_lt_T.le⟩
```

### Avoid old nonintegrated atoms

The skeleton should mention:

```lean
IntegratedMoserDissipationDropBefore
RelativeMoserInterpolationBefore
```

but should not mention or try to produce:

```lean
MoserDissipationDropBeforeNonnegB
LpPowerBoundedBefore D (p + rho) T u
```

## Minimal `#print axioms` targets

```lean
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.IntegratedMoserPrecrossingIntervalData.maxOneEnergy_timeIntegral_le
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.integratedMoser_gradientIntegral_le_of_precrossing_interval
#print axioms ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure.integratedMoser_higherPower_timeIntegral_le_of_precrossing_interval
```

Expected profile: no `sorryAx`, no custom axioms.  These are fixed-window wrappers around already-compiled integral estimates and explicit precrossing hypotheses.

## Build command

```bash
lake env lean ShenWork/PDE/P3MoserIntegratedClosure.lean
lake build ShenWork.PDE.P3MoserIntegratedClosure
```

Then run the broader build only after the local file passes:

```bash
lake build ShenWork
```
