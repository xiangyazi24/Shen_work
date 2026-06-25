# Q362 / cron1: `hregularize` grep report

## Executive verdict

The exact `χ₀ < 0` residual still has no unconditional theorem of the requested shape:

```lean
∀ u v : ℝ → intervalDomainPoint → ℝ,
  intervalTrajectoryBoundedOn T M u →
  (∀ t x, 0 ≤ t → t ≤ T →
    u t x = intervalCoupledDuhamelOperator p R u0 u t x) →
  (∀ t, v t = R (u t)) →
    RegularityBootstrap p T u0 u
```

That is still carried as `hregularize` in `ShenWork/Paper2/IntervalDomainThm11ChiNegResidual.lean` and again inside `CoupledFluxResolverAnalyticData`.  So the genuinely missing object is not a single small field such as Neumann BC or initial trace; it is the upstream bridge from a **bare bounded coupled Duhamel fixed point** to the spectral/frontier data consumed by the existing regularity assemblers.

Most of the seven analytic ingredients do already exist in the repo, and several exist for **general χ / general p**, not only for `χ₀ = 0`.  The caveat is that they usually require one of these stronger packages:

- `GradientMildSolutionData p u₀`, sometimes plus `HasRestartCosineRepresentations`, `GradientMildHalfStepRestartData`, `HasTimeNeighborhoodSpectralAgreement`, `HasResolverDirectSpectralData`, or `GradientMildClassicalRegularityFrontierData`;
- B-form Picard/frontier data such as `ConjugateMildExistenceData`, `BFormBankedInputs`, or `BFormDirectFrontier`;
- per-time spectral/PDE agreement packages such as `HasBFormSpectralPdeAgreement`.

Thus the current state is:

```text
Existing theoremlets: yes, many, including general-χ B-form versions.
Exact coupled hregularize from bounded fixed point alone: still missing.
```

---

## Requested grep buckets: main hits

I treated the requested grep patterns as code-search buckets and then opened the relevant files to check theorem strength.

```text
positivity:
  mildSolution_strictlyPositive
    ShenWork/Paper2/IntervalMildToClassical.lean
  parabolicMaxPrinciple / maximum principle framework
    ShenWork/PDE/ParabolicMaxPrinciple.lean
  B-form strict positivity / PID floor
    ShenWork/Paper2/IntervalBFormStrictPosClosed.lean
    ShenWork/Paper2/IntervalBFormDirectClassical.lean

C² spatial:
  Schauder
    mostly Paper1/docs; not the Paper2 hregularize bridge
  spatialC2
    ShenWork/PDE/IntervalResolverSpatialC2.lean
    ShenWork/Paper2/IntervalRegularityFrontierWiring.lean
    ShenWork/Paper2/IntervalChiNegConcreteConnectors.lean
    ShenWork/Paper2/IntervalParabolicDuhamelGainNonCircular.lean
  sliceC2 / ContDiffOn ℝ 2 slices
    ShenWork/Paper2/IntervalMildRegularityBootstrap.lean
    ShenWork/Paper2/IntervalBFormDirectClassical.lean
    ShenWork/PDE/IntervalCoupledRegularityBootstrap.lean

C¹ temporal:
  timeDeriv
    ShenWork/PDE/IntervalMildTimeDerivContinuity.lean
    ShenWork/Paper2/IntervalMildTimeRegularity.lean
    ShenWork/Paper2/IntervalMildRegularityFrontierAssembly.lean
    ShenWork/PDE/IntervalMildFrontierFromSpectral.lean
    ShenWork/Paper2/IntervalResolverDirectTimeRegularity.lean
  timeC1
    ShenWork/PDE/IntervalCoupledSourceTimeC1.lean
    ShenWork/Paper2/IntervalResolverSourceTimeC1.lean
    ShenWork/Paper2/IntervalMildRegularityBootstrap.lean
  HasDerivAt.*time.*mild
    mildSolution_hasDerivAt_time
    intervalDomainLift_hasDerivAt_time
    mildSolution_differentiableAt_time

PDE identity:
  parabolicPDE
    ShenWork/Paper2/IntervalMildToClassical.lean
  mildSolution.*PDE
    ShenWork/Paper2/IntervalDomainPdeUProducer.lean        -- χ₀ = 0
    ShenWork/Paper2/IntervalBFormPdeUProducer.lean         -- general χ
    ShenWork/Paper2/IntervalBFormDirectClassical.lean      -- banked B-form direct

Neumann BC:
  neumannBC
    ShenWork/Paper2/IntervalMildToClassical.lean
    ShenWork/Paper2/IntervalMildRegularityBootstrap.lean
    ShenWork/Paper2/IntervalBFormDirectClassical.lean
    ShenWork/PDE/IntervalCoupledRegularityBootstrap.lean
  normalDeriv.*zero
    ShenWork/Paper2/IntervalBFormNeumannDischarge.lean
    ShenWork/Paper2/IntervalMildToClassical.lean

Initial trace:
  initialTrace / InitialTrace.*mild
    ShenWork/Paper2/IntervalMildToClassical.lean
    ShenWork/Paper2/IntervalBFormInitialTrace.lean
    ShenWork/Paper2/IntervalBFormDirectClassical.lean
```

---

## Step-by-step status

### 1. `L∞` bound

**Exists / not the hard part.**

For gradient mild data, the bound is a field of `GradientMildSolutionData`:

```lean
hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
```

For the exact χ-negative residual, the analogous boundedness is already an input to `hregularize`:

```lean
intervalTrajectoryBoundedOn T M u
```

So the `L∞` step is not what is missing.  It is either in the Picard data or explicitly supplied to the residual theorem.

---

### 2. Positivity

**Exists in the packaged Picard routes; not proved from the bare coupled fixed-point signature.**

Relevant existing names:

```lean
theorem mildSolution_strictlyPositive
```

in `IntervalMildToClassical.lean` gives positivity for `D : GradientMildSolutionData p u₀` by returning `D.hpos`.  The underlying gradient Picard construction in `IntervalMildPicard.lean` builds `hpos` using the Picard/mild map positivity machinery.

For the B-form/PID route, there are stronger positivity facts, for example:

```lean
theorem conjugatePicardLimit_ge_half_floor_of_PID
```

and the local helper in `IntervalBFormDirectClassical.lean`:

```lean
private theorem bform_u_pos
```

which supplies strict positivity of the conjugate Picard limit on the B-form horizon.

The classical maximum-principle infrastructure also exists in `ShenWork/PDE/ParabolicMaxPrinciple.lean`, including theorems such as:

```lean
theorem weak_maximum_principle_linear
theorem parabolic_maximum_principle
```

But that file is a classical maximum principle for already sufficiently regular subsolutions.  I did not find a theorem that takes the exact bare coupled Duhamel fixed-point assumptions of `hregularize` and derives strict positivity directly by this maximum principle.

**Classification:** exists for gradient/B-form Picard data; missing for the exact arbitrary bounded coupled fixed point.

---

### 3. Spatial `C²`

**Exists conditionally, including general-χ/B-form routes.  The missing part is deriving the required spectral/restart hypotheses from the bare fixed point.**

Important existing gradient/restart names:

```lean
theorem restartDuhamelFormula_closedC2_of_timeC1_source
theorem restartDuhamelSlice_conjunct7
theorem gradientMild_contDiffOn_of_restartCosineRepresentations
theorem gradientMild_closedC2_neumann_of_restartCosineRepresentations
```

These live mainly in `IntervalMildRegularityBootstrap.lean`.  They turn restart cosine representations and source-time-`C¹` information into closed `ContDiffOn ℝ 2` spatial regularity and endpoint derivative/Neumann data.

The general-χ B-form direct route also has the spatial `C²` endpoint package, e.g. in `IntervalBFormDirectClassical.lean`:

```lean
private theorem bform_u_closedC2_endpointDerivs
```

which proves closed spatial `C²` plus endpoint derivative zero for the B-form Picard limit from banked B-form spectral inputs.

The resolver side is also present in `IntervalCoupledRegularityBootstrap.lean` and `IntervalRegularityFrontierWiring.lean`; closed `C²` plus Neumann for `u` yields source coefficient decay, which yields resolver spatial regularity.

**Classification:** theoremlets exist.  What is missing for `hregularize` is an unconditional derivation of `HasRestartCosineRepresentations` / B-form global restart series / equivalent spectral data from the exact assumptions

```lean
hu_ball : intervalTrajectoryBoundedOn T M u
hfp     : ∀ t x, 0 ≤ t → t ≤ T → u t x = intervalCoupledDuhamelOperator p R u0 u t x
hvR     : ∀ t, v t = R (u t)
```

---

### 4. Temporal `C¹`

**Exists as a spectral-agreement bridge; not from the mild equation alone.**

Key files:

```text
ShenWork/Paper2/IntervalMildTimeRegularity.lean
ShenWork/PDE/IntervalMildTimeDerivContinuity.lean
ShenWork/PDE/IntervalMildFrontierFromSpectral.lean
ShenWork/Paper2/IntervalMildRegularityFrontierAssembly.lean
```

Key names:

```lean
structure HasTimeNeighborhoodSpectralAgreement

theorem mildSolution_differentiableAt_time
theorem mildSolution_hasDerivAt_time
theorem intervalDomainLift_hasDerivAt_time
theorem mildSolution_timeDeriv_continuousOn_fixed_x
theorem mildSolution_timeDeriv_jointContinuousOn
theorem mildSolution_timeDeriv_jointContinuousOn_closed

theorem timeSlices_u_of_spectralAgreement
theorem jointTimeDerivInterior_u_of_spectralAgreement
theorem jointTimeDerivClosed_u_of_spectralAgreement
```

These prove fixed-`x` differentiability, continuity of the time derivative, and joint continuity of the time derivative for the mild solution **assuming** `HasTimeNeighborhoodSpectralAgreement T u`.

The v/resolver side is handled through `HasResolverDirectSpectralData` and assembled in `IntervalMildRegularityFrontierAssembly.lean`.

**Classification:** temporal `C¹` exists conditionally.  The missing upstream fact is:

```text
bounded coupled Duhamel fixed point
  → HasTimeNeighborhoodSpectralAgreement T u
  → HasResolverDirectSpectralData T (mildChemicalConcentration p u) p
```

or an equivalent semigroup-generator theorem deriving `u_t = Au + f` and continuity directly from the mild equation.

---

### 5. PDE identity

**Exists in several forms, including a general-χ B-form spectral producer; the exact coupled fixed-point-to-PDE bridge is still missing.**

There is a wrapper in `IntervalMildToClassical.lean`:

```lean
theorem mildSolution_parabolicPDE
```

but this consumes

```lean
hclassical : IsPaper2ClassicalSolution ...
```

and returns `hclassical.pde_u`.  So it is not a derivation by differentiating the mild form.

For `χ₀ = 0`, `IntervalDomainPdeUProducer.lean` contains:

```lean
structure HasSpectralPdeAgreement

theorem mildSolution_pde_u_of_spectral
    (p : CM2Params) (hχ0 : p.χ₀ = 0) ...
```

For **general χ**, the B-form route contains the important non-χ₀=0 producer in `IntervalBFormPdeUProducer.lean`:

```lean
structure HasBFormSpectralPdeAgreement

theorem intervalConjugateMildSolution_pde_u_of_spectral
```

This theorem proves the full PDE identity with the chemotaxis divergence term:

```lean
intervalDomain.timeDeriv u t x =
  intervalDomain.laplacian (u t) x
    - p.χ₀ * intervalDomain.chemotaxisDiv p (u t)
        (mildChemicalConcentration p u t) x
    + u t x * (p.a - p.b * (u t x) ^ p.α)
```

`IntervalBFormDirectClassical.lean` also packages a banked version:

```lean
theorem BFormBankedInputs.hpde_u
```

**Classification:** PDE identity exists for general χ in the B-form spectral/banked route.  It is not yet connected to the exact `hregularize` inputs for an arbitrary bounded coupled Duhamel fixed point.

---

### 6. Neumann BC

**Exists conditionally; missing only as an unconditional consequence of the bare coupled fixed-point assumptions.**

For the gradient route, `IntervalMildToClassical.lean` has:

```lean
theorem mildSolution_neumannBC_of_closedC2_neumann
theorem mildSolution_neumannBC
```

The first consumes closed `C²` and one-sided endpoint derivative limits.  The second uses `HasRestartCosineRepresentations` to produce those hypotheses.

For the restart/C² route, `IntervalMildRegularityBootstrap.lean` has:

```lean
theorem gradientMild_neumann_left_of_restartCosineRepresentations
theorem gradientMild_neumann_right_of_restartCosineRepresentations
theorem gradientMild_closedC2_neumann_of_restartCosineRepresentations
```

For the B-form route, `IntervalBFormDirectClassical.lean` has:

```lean
private theorem bform_u_neumann_left
private theorem bform_u_neumann_right
```

and uses these to assemble `intervalConjugatePicardLimit_classicalRegularity_direct` and `intervalConjugatePicardLimit_isClassicalSolution_direct`.

The coupled chemical/resolver Neumann bridge exists in `IntervalCoupledRegularityBootstrap.lean`, e.g. via:

```lean
coupledChemical_neumannBC_of_closedC2_neumann
```

**Classification:** Neumann BC theoremlets exist.  What is missing is the direct path

```text
bare bounded coupled Duhamel fixed point → closed spatial C²/restart data → Neumann BC.
```

---

### 7. Initial trace

**Exists in the B-form Picard route and conditionally in the gradient route; not found for the exact arbitrary coupled fixed-point signature.**

Gradient route:

```lean
theorem mildSolution_initialTrace
```

in `IntervalMildToClassical.lean` proves `InitialTrace intervalDomain u₀ D.u`, but it consumes an explicit uniform initial-approach hypothesis for the gradient Duhamel map:

```lean
hInitialApproach : ∀ ε, 0 < ε →
  ∃ δ > 0, ∀ t, 0 < t → t < δ →
    ∀ x, |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε
```

B-form route:

```lean
theorem intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
theorem conjugatePicardLimit_initialTrace_of_conjugate_data
```

in `IntervalBFormInitialTrace.lean` prove the B-form Picard fixed point approaches the initial datum.  `IntervalBFormDirectClassical.lean` then exposes:

```lean
theorem intervalConjugatePicardLimit_initialTrace_direct
```

**Classification:** initial trace is proved for the B-form Picard data and conditionally for gradient mild data.  I did not find a theorem of the exact form required by `hregularize`, i.e. one taking only the arbitrary coupled fixed point equation and `intervalTrajectoryBoundedOn` and returning the trace.

---

## What already fully assembles downstream

The strongest already-assembled general-χ downstream route I found is in `IntervalBFormDirectClassical.lean`:

```lean
structure BFormDirectFrontier

theorem intervalConjugatePicardLimit_classicalRegularity_direct
theorem intervalConjugatePicardLimit_initialTrace_direct
theorem intervalConjugatePicardLimit_isClassicalSolution_direct
theorem localClassicalSolution_of_BFormDirectFrontier
```

This is significant: once `BFormDirectFrontier p DB` is available, the file assembles the B-form Picard limit into a classical Paper 2 solution with initial trace, for general p / general χ.

But `BFormDirectFrontier` still carries exactly the kind of data that a bare `hregularize` would need to produce:

```lean
bank : BFormBankedInputs p DB
hTimeNhd : HasTimeNeighborhoodSpectralAgreement DB.T
  (conjugatePicardLimit p u₀ DB.T)
hResolverData : HasResolverDirectSpectralData DB.T
  (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
hVpos : ∀ t, 0 < t → t < DB.T → ∀ x,
  0 < mildChemicalConcentration p
    (conjugatePicardLimit p u₀ DB.T) t x
```

So this is an assembler after the spectral/frontier witnesses are available, not the missing bare fixed-point regularizer.

---

## Genuinely missing piece

For the exact `χ₀ < 0` residual, the missing theorem is still:

```text
from:
  hu_ball : intervalTrajectoryBoundedOn T M u
  hfp     : ∀ t x, 0 ≤ t → t ≤ T →
              u t x = intervalCoupledDuhamelOperator p R u0 u t x
  hvR     : ∀ t, v t = R (u t)

to:
  RegularityBootstrap p T u0 u
```

The repo already has most of the downstream bricks.  The missing upstream work is to derive, from that fixed-point data, either:

```text
HasRestartCosineRepresentations / B-form global restart series
HasTimeNeighborhoodSpectralAgreement
HasResolverDirectSpectralData or clamped per-t₀ resolver source C¹ data
HasBFormSpectralPdeAgreement or equivalent PDE-source split
resolver strict positivity for v, if the chosen assembler needs it
initial approach for the exact coupled Duhamel operator
```

or to bypass those predicates and prove the seven RegularityBootstrap fields directly from the mild equation.

In short:

```text
Already exists:
  L∞ bound infrastructure, positivity for packed Picard data, C²/Neumann from restart/spectral data,
  C¹-time from spectral neighborhood agreement, general-χ B-form PDE identity, B-form initial trace,
  and downstream classical/RegularityBootstrap-style assemblers.

Genuinely missing:
  the unconditional hregularize bridge from an arbitrary bounded coupled Duhamel fixed point
  to those spectral/frontier hypotheses or directly to RegularityBootstrap.
```
