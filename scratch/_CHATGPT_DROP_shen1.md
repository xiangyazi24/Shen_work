# Q2923 (shen1) — Paper1–3/Paper2 headline cleanup audit

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Scope: source-audit/design only; no Lean source edits.

## Status caveat

The connected GitHub branch does not yet show the newest local additions named in the prompt, e.g.

```lean
higherPowerWindowCoeffFrontier_of_regularEnergy
higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap
intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
EqOnPositiveTimesBefore
IntegratedMoserFirstCrossingStep_congr_pos
intervalDomainWithInitialSlice_eq_raw_of_pos
```

I therefore treat the local additions listed in the prompt as accepted/proved local state, and audit the architecture relative to the visible source stack.

## Executive verdict

Dad cannot honestly have fully unconditional Paper2/Paper1–3 headline theorems today from the current Moser stack unless the remaining analytic frontiers are kept explicit. The new anchored and locality infrastructure is important and correct, but it only removes **false zero-slice / raw-Picard compatibility residuals** and routine higher-power/window coefficient plumbing. It does not prove the remaining near-zero gradient integrability, last-exit high-excursion lower-average, upper-gap, or any global/local-existence frontiers that are still explicitly carried elsewhere.

The clean classification is:

* **PROVED / WIRE NOW:** anchored zero-slice regularity, raw-to-anchored gradient integrability transfer, anchored-to-raw `LpPowerBoundedBefore` / `IntegratedMoserFirstCrossingStep` locality, routine window coefficient/dissipation coefficient assembly from regularity + energy + FTC + nonnegativity, and statement-layer collapse from a raw integrated step to Corollary 2.1 / Proposition 2.5.
* **HONEST FRONTIER:** `IntervalDomainRawMoserGradientTimeIntegrability`, FTC side integrability packages, high-excursion lower-average windows, upper-data/epsilon gap selection, relative/endpoint atoms unless their separate producers are already in hand, and global/local existence or finite-horizon alternative inputs outside the Moser route.
* **UNSAFE ROUTE:** using anchored closed-time regularity/dissipation/FTC as if it were raw closed-time regularity/dissipation/FTC; or filling old universal local step fields from the anchored theorem without supplying global trace/datum data.

## 1. PROVED / WIRE NOW packages

### Anchored endpoint / regularity package

Local proved objects:

```lean
intervalDomainWithInitialSlice u₀ u
initialPowerEnergyCompatibleAtZero_withInitialSlice
initialTrace_withInitialSlice
classical_withInitialSlice
globalClassical_withInitialSlice
initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
```

These are **WIRE NOW** for any producer whose `u` is the anchored representative. They should be used to produce:

```lean
IntegratedMoserFirstCrossingRegularity intervalDomain
  (intervalDomainWithInitialSlice u₀ u) T p0
```

from:

```lean
IsPaper2GlobalClassicalSolution intervalDomain params u v
InitialTrace intervalDomain u₀ u
PaperPositiveInitialDatum intervalDomain u₀
0 < T
IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

Correct file target:

```text
ShenWork/PDE/P3MoserRegularityProducer.lean
```

Use / keep:

```lean
intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
```

or the local name now in that file.

### Raw-to-anchored and anchored-to-raw positive-time locality

Local additions:

```lean
EqOnPositiveTimesBefore
LpPowerBoundedBefore_congr_pos
LpPowerBoundedBefore_iff_of_pos_eq
AbstractLpBootstrapHypothesis_congr_pos
IntegratedMoserFirstCrossingStep_congr_pos
IntegratedMoserFirstCrossingStep_iff_of_pos_eq
intervalDomainWithInitialSlice_eq_raw_of_pos
intervalDomainWithInitialSlice_eq_raw_of_pos_apply
intervalDomain_abstractLpBootstrapHypothesis_anchored_of_raw
intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
```

These are **WIRE NOW** and logically sound.

Reason: the relevant definitions are positive-time only:

```lean
def LpPowerBoundedBefore
    (D : BoundedDomainData) (pExp Tmax : ℝ)
    (u : ℝ → D.Point → ℝ) : Prop :=
  ∃ C, ∀ t, 0 < t → t < Tmax →
    D.integral (fun x => (u t x) ^ pExp) ≤ C
```

and

```lean
def IntegratedMoserFirstCrossingStep
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T rho p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    LpPowerBoundedBefore D p T u →
      LpPowerBoundedBefore D (p + rho) T u
```

`AbstractLpBootstrapHypothesis` is also safe because its only `u`-dependent field is the initial `LpPowerBoundedBefore` bound.

Correct use pattern:

```lean
let uA := intervalDomainWithInitialSlice u₀ u

-- build this using anchored regularity/FTC/window machinery
have hstepA :
  IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0 := ...

-- then export only the positive-time step back to raw u
have hstepRaw :
  IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 :=
  intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored hstepA
```

This is the right way to feed raw-`u` downstream APIs.

### Routine higher-power/window coefficient data

Recent local additions:

```lean
higherPowerWindowCoeffFrontier_of_regularEnergy
higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap
intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
```

Classification: **PROVED / WIRE NOW**, with the exact caveat that they reduce **routine coefficient/window data** from:

```lean
IntegratedMoserFirstCrossingRegularity
LpBootstrapEnergyInequality
IntegratedMoserEnergyWindowFTC
IntegratedMoserEnergyNonnegativity / intervalDomain nonnegativity
coefficient surplus/gap hypotheses
```

They do not prove lower-average/high-excursion. They also do not remove the need for FTC side integrability packages.

Likely file:

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Use them to collapse older explicit fields around:

```lean
IntegratedHigherPowerEnergyWindowCoeffFrontier
IntegratedMoserDissipationDropBeforeCoeff
IntegratedMoserDissipationDropBefore
```

whenever the coefficient gap/surplus assumption is already present.

### Interval integrability and nonnegativity inside windows

From existing pushed `P3MoserIntegratedClosure.lean`, these are **WIRE NOW** from `IntegratedMoserFirstCrossingRegularity`:

```lean
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
intervalIntegrable_max_one_of_intervalIntegrable
```

For intervalDomain nonnegativity:

```lean
intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
```

Thus the following should not remain headline assumptions once `IntegratedMoserFirstCrossingRegularity` and classical positivity are available:

* interval integrability of `Y_p` on windows;
* interval integrability of `Y_{p+rho}` on windows;
* interval integrability of `G_p` on windows;
* interval integrability of `max 1 Y_p` on windows;
* nonnegativity of `Y` and gradient-window integrals for intervalDomain.

### Fixed-window upper-bound data

Existing pushed routine builders:

```lean
integratedMoser_windowUpperBoundData_of_lowerAverageWindow
integratedMoserWindowUpperDataGapFrontier_of_epsilonGap
integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap
IntegratedMoserFirstCrossingLowerAverageEpsilonData.toUpperDataGapData
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.toLowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData
```

Classification: **WIRE NOW** for the upper-bound calculation and structure adapters. But the actual strict gap chooser remains separate; see below.

### Statement-layer collapse from raw integrated step

Existing pushed `IntervalDomainStatementAssembly.lean` has WIRE NOW collapse routes:

```lean
IntervalDomainPaper2Prop25IntegratedMoserFrontierData.toIntegratedStepFrontierData
IntervalDomainPaper2Prop25LowerUpperFrontierData.toIntegratedStepFrontierData
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedStepFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinIntegratedMoserFrontierData
```

These wrappers are sound once they are fed a **raw** `IntegratedMoserFirstCrossingStep intervalDomain u T rho p0`. The local anchored-to-raw step transfer is the right way to produce that raw step from anchored proof internals.

## 2. HONEST FRONTIERS that must remain explicit today

### Raw all-exponent Moser-gradient near-zero integrability

Still honest:

```lean
IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

Anchoring fixes zero-time compatibility; it does not prove:

```lean
∀ p, p0 ≤ p →
  IntegrableOn
    (fun t => intervalDomain.integral (fun x =>
      (intervalDomain.gradNorm (fun y => (u t y) ^ (p / 2)) x) ^ 2))
    (Set.uIcc (0 : ℝ) T) volume
```

for the raw positive-time representative. This should remain an explicit analytic assumption until a heat/spectral/Picard smoothing theorem proves it.

### FTC side integrability packages

The endpoint/zero-slice part is solved by anchoring, but the existing FTC producer still needs initial-window derivative/time-term/PDE-term integrability inputs.

Classification: **HONEST FRONTIER**, unless a separate current local theorem proves exactly those packages.

These belong around:

```text
ShenWork/PDE/P3MoserEnergyContinuity.lean
```

and feed:

```lean
IntegratedMoserEnergyWindowFTC intervalDomain uA T p0
```

### High-excursion lower-average window frontier

Still honest and owned by Zinan:

```lean
IntegratedMoserHighExcursionLowerAverageWindowFrontier
```

and the fields:

```lean
IntegratedMoserFirstCrossingLowerAverageEpsilonData.lowerAverage
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.lowerAverage
```

Do not collapse this into wiring. It is the last-exit/window-thickness analytic step.

### Upper-gap / epsilon-gap chooser

Still honest unless the new `_coeffGap` theorem proves exactly the desired frontier structure:

```lean
IntegratedMoserWindowUpperDataGapFrontier
IntegratedMoserWindowUpperGapEpsilonFrontier
```

The fixed-window upper-bound data is WIRE NOW. The strict gap

```lean
eps * Gbound + (b - a) * (Ceps * M) < lowerBound
```

is not automatic from regularity alone. Algebraic coefficient absorption is WIRE; choosing a quantitatively useful `eps`/witness is analytic/quantitative unless already proved as a theorem with exactly this target.

### Relative interpolation / endpoint atoms

The conversion from mass-gradient data to relative interpolation is WIRE:

```lean
intervalDomain_relativeMoserInterpolationBefore_of_massGradient
```

But the mass-gradient interpolation estimates themselves are analytic unless already proved locally.

The terminal/quantitative endpoint route has many wrappers in `IntervalDomainStatementAssembly.lean`, but if no producer currently proves the terminal pointwise power-control / quantitative endpoint field, it remains **HONEST FRONTIER**:

```lean
IntervalDomainMoserQuantitativeEndpoint
IntervalDomainMoserPointwisePowerControlBefore
```

### Global/local existence and finite-horizon alternatives outside Moser

The Moser cleanup does not discharge statement-stack existence frontiers such as:

```lean
IntervalDomainPaper2Proposition11FrontierData.localExistence
IntervalDomainPaper2Proposition11FrontierData.finiteHorizonAlternative
IntervalDomainPaper3NegativeSensitivityFrontierData.globalSolution
IntervalDomainPaper3NegativeSensitivityFrontierData.eventualSupBound
```

Some chi-zero or already-proved branch wrappers may be closed, but the general headline theorem remains conditional wherever these frontiers are still fields.

## 3. Anchored-to-raw first-crossing route: soundness audit

### Sound

The route is logically sound for:

```lean
LpPowerBoundedBefore
AbstractLpBootstrapHypothesis
IntegratedMoserFirstCrossingStep
```

because all `u`-dependent content in these predicates is positive-time only.

No hidden `t = 0` dependency appears in these three objects.

### Sound downstream if the raw step is exported first

After converting

```lean
IntegratedMoserFirstCrossingStep intervalDomain uA T rho p0
```

to

```lean
IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

it is safe to use existing raw-`u` downstream wrappers such as:

```lean
all_exponents_of_integrated_first_crossing_step_lpmono
intervalDomain_boundedBefore_of_integrated_first_crossing_step
intervalDomain_endpointBoundFromLp_of_actual_integrated_step_atoms
intervalDomain_allLpBoundFromBootstrap_of_actual_integrated_step_atoms
```

The quantitative endpoint field in Proposition 2.5 is also raw-positive-time in the relevant places: it consumes raw `LpPowerBoundedBefore` and raw `InitialTrace`. It should be used after the raw step is recovered.

### Unsafe

Do **not** transfer these from anchored to raw merely by positive-time equality:

```lean
IntegratedMoserFirstCrossingRegularity
IntervalDomainIntegratedMoserClassicalRegularityData
IntervalDomainIntegratedMoserGlobalClassicalRegularityData
IntegratedMoserDissipationDropBefore
IntegratedMoserEnergyWindowFTC
IntervalDomainInitialPowerEnergyContinuityAtZero
IntervalDomainPowerEnergyEndpointContinuity
```

Reason: these involve `t = 0`, endpoint continuity, or windows with `t1 = 0`. Raw Picard may store the wrong zero slice. For example:

```lean
IntegratedMoserDissipationDropBefore
```

quantifies over windows:

```lean
t1 ∈ Set.Icc (0 : ℝ) T
```

so `t1 = 0` is allowed and the zero-time energy term is visible. That predicate must be built for anchored `uA`, not raw `u`, unless extra raw zero compatibility is available.

### Statement-layer mismatch to avoid

The old field in `IntervalDomainPaper2Prop25IntegratedStepFrontierData` is universal/local:

```lean
∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
  IsPaper2ClassicalSolution intervalDomain p T u v →
  CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
  AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0
```

The anchored theorem needs additional data:

```lean
u₀
InitialTrace intervalDomain u₀ u
PaperPositiveInitialDatum intervalDomain u₀
IsPaper2GlobalClassicalSolution intervalDomain p u v
IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

So it is **UNSAFE** to claim the anchored theorem fills that old local field unless you add these hypotheses to the field or prove every local branch comes from a compatible global traced branch. That latter theorem is not present.

Correct options:

1. Preserve the old local `IntegratedStepFrontierData` field as an explicit assumption for old statement wrappers.
2. Add a new **global-trace anchored** statement-layer route whose theorem statement includes the data needed for anchoring.
3. At the solution-specific level, build anchored step then transfer to raw step with `intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored`.

## 4. Zinan lower-average frontier: feasibility and first sublemmas

The last-exit / high-excursion lower-average route is feasible, but it is still an analytic proof, not statement wiring.

Target frontier:

```lean
IntegratedMoserHighExcursionLowerAverageWindowFrontier
```

The structure asks: if

```lean
Cnext < integratedMoserEnergy D u (p + rho) t
```

at a strict positive time, produce a window `[a,b] ⊂ (0,T)` with:

* `a < b`, `0 < a`, `b < T`;
* current-energy bound for exponent `p` on `[a,b]`;
* lower-average inequality for exponent `p + rho`.

### Assumptions it should consume

At minimum:

```lean
IntegratedMoserFirstCrossingRegularity D u T p0
IntegratedMoserEnergyNonnegativity D u T p0
0 < rho
0 ≤ p0
p0 ≤ p
0 ≤ p
LpPowerBoundedBefore D p T u
```

For intervalDomain/classical applications, nonnegativity can come from:

```lean
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
```

The lower-average proof should use regularity, not the upper-data gap. The upper-data gap is consumed later to turn the lower-average window into a contradiction window.

### Sublemmas to attack first

1. **Interior window around a strict positive time**

```lean
lemma exists_Icc_subset_Ioo_around
    {T t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ∃ a b, a < b ∧ 0 < a ∧ b < T ∧ t ∈ Set.Icc a b
```

A concrete choice using `δ = min (t/2) ((T-t)/2)` should work.

2. **Energy lower persistence from continuity**

For

```lean
Yq s := integratedMoserEnergy D u (p + rho) s
```

prove:

```lean
lemma exists_window_energy_lower_of_continuous_high
    (hcont : ContinuousOn Yq (Set.Icc (0 : ℝ) T))
    (ht0 : 0 < t) (htT : t < T)
    (hhigh : Cnext < Yq t) :
    ∃ a b lower,
      a < b ∧ 0 < a ∧ b < T ∧
      (∀ s ∈ Set.Icc a b, lower ≤ Yq s) ∧
      lower > Cnext
```

Using a local continuity ball around `t`, choose `lower = (Yq t + Cnext) / 2`.

3. **Current-energy window bound from `LpPowerBoundedBefore`**

This may already be present as:

```lean
currentEnergy_Icc_bound_of_LpPowerBoundedBefore
```

If not, add:

```lean
lemma currentEnergy_Icc_bound_of_LpPowerBoundedBefore
    (hLp : LpPowerBoundedBefore D p T u)
    (ha_pos : 0 < a) (hb_lt : b < T) :
    ∃ M, ∀ s ∈ Set.Icc a b,
      integratedMoserEnergy D u p s ≤ M
```

Proof: choose the bound from `hLp`; for `s ∈ Icc a b`, get `0 < s` and `s < T`.

4. **Integral lower bound from pointwise lower bound**

```lean
lemma intervalIntegral_lower_bound_of_pointwise
    (hab : a ≤ b)
    (hY_int : IntervalIntegrable Y volume a b)
    (hlower : ∀ s ∈ Set.Icc a b, lower ≤ Y s) :
    (b - a) * lower ≤ ∫ s in a..b, Y s
```

Use `intervalIntegral.integral_mono_on` against the constant function.

5. **Package into `IntegratedMoserHighExcursionLowerAverageWindow`**

Use:

```lean
hreg.energyContinuous (p + rho) hp_rho
hreg.power_intervalIntegrable_of_Icc (p + rho) hp_rho ...
hLp
```

to fill all fields.

### Feasibility caveat

A simple continuity window gives a lower-average window, but it may not by itself give a lower bound strong enough for the strict upper-gap inequality. That quantitative comparison belongs to:

```lean
IntegratedMoserWindowUpperDataGapFrontier
```

or the local `_coeffGap` theorem if it really proves that frontier. Therefore Zinan’s lower-average work is feasible and meaningful, but it does not alone close the full high-excursion contradiction.

## 5. Codex next action plan

### A. Add only positive-time locality wrappers to shared files

Already done locally; keep them. They are **WIRE NOW** and central:

```lean
EqOnPositiveTimesBefore
LpPowerBoundedBefore_congr_pos
AbstractLpBootstrapHypothesis_congr_pos
IntegratedMoserFirstCrossingStep_congr_pos
intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored
```

### B. Add a solution-specific anchored-to-raw first-crossing producer

Recommended theorem shape:

```lean
theorem intervalDomain_integratedMoserFirstCrossingStep_raw_of_globalTraceAnchoredData
    {params : CM2Params} {T rho p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgradRaw : IntervalDomainRawMoserGradientTimeIntegrability u T p0)
    -- exact honest lower/upper/window/FTC inputs here
    : IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  -- build hstepA for uA := intervalDomainWithInitialSlice u₀ u
  -- then:
  exact intervalDomain_integratedMoserFirstCrossingStep_raw_of_anchored hstepA
```

Do not force this through the old universal local `IntervalDomainPaper2Prop25IntegratedStepFrontierData` unless its field is redesigned to include global trace/datum inputs.

### C. Preserve honest assumptions in headline wrappers

Keep explicit assumptions for:

```lean
IntervalDomainRawMoserGradientTimeIntegrability
IntegratedMoserEnergyWindowFTC side integrability packages
IntegratedMoserHighExcursionLowerAverageWindowFrontier
IntegratedMoserWindowUpperDataGapFrontier / EpsilonGapFrontier
RelativeMoserInterpolation or mass-gradient producers, if not already proved
QuantitativeEndpoint / terminal endpoint, if not already proved
Proposition 1.1 local existence / finite horizon alternatives, if not already proved
Paper3 negative sensitivity eventual bound, if not already proved
```

### D. Collapse only routine packages

Remove or lower old residuals that are now pure wiring:

* endpoint zero compatibility for Moser regularity;
* interval integrability of `Y`, `Z`, `G`, `max` when `IntegratedMoserFirstCrossingRegularity` is present;
* intervalDomain nonnegativity of energy/gradient integrals;
* routine higher-power/window coefficient frontiers handled by:

```lean
higherPowerWindowCoeffFrontier_of_regularEnergy
higherPowerWindowCoeffFrontier_of_regularEnergy_coeffGap
intervalDomain_dissipationCoeff_of_regularEnergy_coeffGap
```

### E. Do not claim unconditional headline theorems yet

Current honest conclusion:

```text
No fully unconditional Dad-level Paper2/Paper1–3 headline theorem today,
unless the remaining analytic frontiers are retained as hypotheses.
```

What you can honestly deliver now is a thinner headline theorem whose assumptions are sharply reduced to the real frontiers listed above, with zero-slice/anchoring and routine window-coefficient plumbing removed from the assumption surface.
