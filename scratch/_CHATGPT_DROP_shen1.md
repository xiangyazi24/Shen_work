# Q2910 (shen1) — Paper2/P3 Moser frontier-stack route audit

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Target files: `ShenWork/PDE/P3MoserIntegratedClosure.lean`, `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`, `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`  
Source edit requested: none; answer file only.

## Scope note

The connected GitHub branch is slightly behind the local working session: searches did not find the newest names such as

```lean
IntervalDomainRawMoserGradientTimeIntegrability
intervalDomainWithInitialSlice
IntegratedMoserEnergyWindowFTC
IntegratedHigherPowerEnergyWindowCoeffFrontier
integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
```

I therefore audited the pushed stack plus the local additions you described. The source-side conclusions below are phrased against the local names you gave, and against the pushed identifiers already visible in `P3MoserIntegratedClosure.lean`, `P3MoserRegularityProducer.lean`, `IntervalDomainMoserLadderAtoms.lean`, and `IntervalDomainStatementAssembly.lean`.

## Executive classification

### WIRE NOW

These are now routine wiring from the anchored/FTC infrastructure or from already-proved interval-domain package lemmas:

1. **Anchored zero-time regularity package**, assuming the honest raw gradient frontier:

```lean
IntervalDomainRawMoserGradientTimeIntegrability u T p0
```

is supplied. Endpoint compatibility and initial power-energy continuity are now wiring via anchoring; raw gradient time-integrability transfers to anchored by a.e. equality.

2. **`IntegratedMoserEnergyWindowFTC`**, once the existing `P3MoserEnergyContinuity` producer is fed with:
   - global/classical data for the anchored representative;
   - endpoint power-energy continuity, now produced by anchoring + trace + paper-positive datum;
   - its remaining initial-window derivative/time-term/PDE-term integrability packages.

The endpoint part is no longer a residual. The initial-window derivative/time-term/PDE-term integrability packages remain analytic inputs unless separately discharged.

3. **Interval integrability of `Y`, `Z`, `G`, and `max 1 Y` on closed windows** once `IntegratedMoserFirstCrossingRegularity` is available:
   - `Y_p`: `IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc`
   - `Z = Y_{p+rho}`: same lemma with `p + rho`
   - `G_p`: `IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc`
   - `max 1 Y_p`: `IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc`

4. **Pointwise and window nonnegativity of interval-domain energies** from classical/global positivity:
   - `intervalDomain_integratedMoserEnergyNonnegativity_of_classical`
   - `intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical`
   - `intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg`
   - `intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg`

5. **Fixed-window upper-bound data once a lower-average window is selected**:

```lean
integratedMoser_windowUpperBoundData_of_lowerAverageWindow
```

This already wires from regularity + nonnegativity + integrated dissipation + relative interpolation.

6. **Adapters among upper-window/frontier structures**:
   - `integratedMoserWindowUpperDataGapFrontier_of_epsilonGap`
   - `integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap`
   - `integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap`
   - `IntegratedMoserFirstCrossingLowerAverageEpsilonData.toUpperDataGapData`
   - `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.toLowerUpperFrontiers`
   - `integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData`
   - `integratedMoserFirstCrossingStep_of_lowerAverageEpsilonData`

7. **Statement-layer collapse wrappers** in `IntervalDomainStatementAssembly.lean`:
   - `IntervalDomainPaper2Prop25IntegratedMoserFrontierData.toIntegratedStepFrontierData`
   - `IntervalDomainPaper2Prop25LowerUpperFrontierData.toIntegratedStepFrontierData`
   - `intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData`
   - `intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData`
   - paired wrappers producing both Corollary 2.1 and Proposition 2.5.

### HONEST FRONTIER

These still should not be claimed as unconditional from the current source:

1. **`IntervalDomainRawMoserGradientTimeIntegrability u T p0`**.

Q2906’s conclusion still stands: current classical/global/trace/Picard APIs do not include all-exponent near-zero Moser-gradient time-integrability.

2. **Initial-window derivative/time-term/PDE-term integrability packages** consumed by the existing `IntegratedMoserEnergyWindowFTC` producer.

Anchoring removes the zero-slice compatibility problem but does not prove every initial-window time-derivative/PDE-term integrability fact required by the FTC producer.

3. **Zinan’s lower-average / last-exit high-excursion frontier**:

```lean
IntegratedMoserHighExcursionLowerAverageWindowFrontier
```

and the corresponding field in:

```lean
IntegratedMoserFirstCrossingLowerAverageEpsilonData.lowerAverage
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.lowerAverage
```

This is the window-thickness / last-exit high-excursion analytic input. Do not route it through source edits in `P3MoserHighExcursionProducer.lean` if Zinan owns that file.

4. **Upper-data gap / epsilon-gap chooser**, unless the new local `_coeffGap` theorems already discharge it for the selected upper-bound witness:

```lean
IntegratedMoserWindowUpperDataGapFrontier
IntegratedMoserWindowUpperGapEpsilonFrontier
```

The fixed-window upper-bound calculation is wiring, but proving a strict gap of the form

```lean
eps * Gbound + (b - a) * (Ceps * M) < lowerBound
```

is a quantitative choice problem. It is not automatic from `IntegratedMoserFirstCrossingRegularity` plus `LpBootstrapEnergyInequality` alone unless the local coefficient/gap theorem is already exactly an upper-gap producer.

5. **Integrated dissipation from PDE energy** unless using the new window-FTC/higher-power route with all required inputs.

The existing statement field

```lean
IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
```

is still analytic unless routed from `LpBootstrapEnergyInequality` + `IntegratedMoserEnergyWindowFTC` + interval integrability/nonnegativity + coefficient-surplus/gap via your new local theorem.

## File-level audit

### `P3MoserRegularityProducer.lean`

The pushed file has the important bridge:

```lean
theorem intervalDomain_gradientTimeIntegrable_of_gradientEnergyContinuous
```

and the global-classical data structure:

```lean
structure IntervalDomainIntegratedMoserGlobalClassicalRegularityData
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop where
  atZero : IntervalDomainInitialPowerEnergyContinuityAtZero u T p0
  gradientTimeIntegrable : ∀ p, p0 ≤ p → IntegrableOn ... (Set.uIcc 0 T) volume
```

After anchoring, the `atZero` field is WIRE NOW. The `gradientTimeIntegrable` field should be fed by the named frontier:

```lean
def IntervalDomainRawMoserGradientTimeIntegrability
    (u : ℝ → intervalDomain.Point → ℝ) (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p →
    IntegrableOn
      (fun t => intervalDomain.integral (fun x =>
        (intervalDomain.gradNorm
          (fun y => (u t y) ^ (p / 2)) x) ^ 2))
      (Set.uIcc (0 : ℝ) T) volume
```

Recommended wrapper if not already present:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserRegularityProducer

/-- Anchored regularity for first-crossing from global classical trace plus the
honest raw all-exponent Moser-gradient integrability frontier. -/
theorem intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored_rawGradient
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    (hgradRaw : IntervalDomainRawMoserGradientTimeIntegrability u T p0) :
    IntegratedMoserFirstCrossingRegularity intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  exact intervalDomain_integratedMoserFirstCrossingRegularity_of_globalClassicalTraceAnchored
    hT htrace hdatum hglobal
    (intervalDomain_gradientTimeIntegrable_withInitialSlice_of_raw hgradRaw)

end ShenWork.IntervalDomainExistence.P3MoserRegularityProducer
```

Status: **WIRE NOW**, assuming the local anchored theorem names from the prompt.

### `P3MoserEnergyContinuity.lean`

Local additions now make this route possible:

```lean
initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
```

This should feed the existing `IntegratedMoserEnergyWindowFTC` producer. The right wrapper should not ask again for endpoint compatibility; it should ask only for the actual FTC side conditions.

Recommended theorem shape:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity

/-- Window FTC for the anchored representative.  The endpoint part is now
produced internally from trace + paper-positive datum + global classical;
the derivative/time/PDE initial-window integrability packages remain honest
inputs to the existing FTC producer. -/
theorem integratedMoserEnergyWindowFTC_of_globalTraceAnchored
    {params : CM2Params} {T p0 : ℝ}
    {u₀ : intervalDomain.Point → ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hT : 0 < T)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hdatum : PaperPositiveInitialDatum intervalDomain u₀)
    (hglobal : IsPaper2GlobalClassicalSolution intervalDomain params u v)
    -- keep the exact existing FTC side-condition packages here:
    (hderivInt : /* existing initial-window derivative integrability package */)
    (htimeInt  : /* existing time-term integrability package */)
    (hpdeInt   : /* existing PDE-term integrability package */) :
    IntegratedMoserEnergyWindowFTC intervalDomain
      (intervalDomainWithInitialSlice u₀ u) T p0 := by
  -- call the existing FTC producer, using:
  -- initialPowerEnergyContinuityAtZero_of_trace_paperPositive_global_withInitialSlice
  -- for the endpoint/atZero input.
  exact /* existing FTC producer */

end ShenWork.IntervalDomainExistence.P3MoserEnergyContinuity
```

Status: endpoint part **WIRE NOW**; derivative/time/PDE initial-window integrability inputs **HONEST FRONTIER** unless already produced elsewhere.

### `P3MoserIntegratedClosure.lean`

The pushed file already contains the key window-frontier adapters. From the local additions, the next useful wrapper is to package all routine inputs for your new higher-power coefficient frontier.

Recommended local wrapper against your new theorem names:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Routine interval-domain inputs for the higher-power window coefficient
frontier.  This packages all interval-integrability and nonnegativity obligations
from first-crossing regularity and interval-domain positivity/nonnegativity.
The remaining coefficient gap/surplus hypothesis is kept explicit. -/
theorem integratedHigherPowerEnergyWindowCoeffFrontier_of_regular_energy_ftc
    {T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ}
    (hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0)
    (hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0)
    (henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0)
    (hftc : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    -- exact local coefficient surplus/gap hypothesis consumed by your `_coeffGap` theorem:
    (hcoeffGap : /* coefficient surplus/gap package */) :
    IntegratedHigherPowerEnergyWindowCoeffFrontier intervalDomain u T rho p0 := by
  -- For each p/window, discharge:
  --   G integrability via hreg.gradient_intervalIntegrable_of_Icc
  --   Y integrability via hreg.power_intervalIntegrable_of_Icc
  --   Z = Y_(p+rho) integrability via hreg.power_intervalIntegrable_of_Icc
  --   max integrability via hreg.maxOneEnergy_intervalIntegrable_of_Icc
  --   nonnegativity via hnonneg / intervalDomain nonnegativity lemmas
  -- then call:
  --   integratedHigherPowerEnergyWindowCoeffFrontier_of_LpBootstrapEnergyInequality
  -- or `_coeffGap` as appropriate.
  exact /* local call */

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

Status: **WIRE NOW** for integrability/nonnegativity packaging; coefficient gap/surplus depends on the exact local theorem. If it is a numeric/algebraic hypothesis, keep it explicit. If it is the same as `IntegratedMoserWindowUpperDataGapFrontier`, mark it **HONEST FRONTIER**.

Existing pushed names that should be used in this wrapper:

```lean
IntegratedMoserFirstCrossingRegularity.power_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.gradient_intervalIntegrable_of_Icc
IntegratedMoserFirstCrossingRegularity.maxOneEnergy_intervalIntegrable_of_Icc
intervalIntegrable_max_one_of_intervalIntegrable
intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
intervalDomain_integratedMoserGradientEnergy_intervalIntegral_nonneg
```

For the lower/upper window split, no new theorem is needed for the routine part; use the existing adapters:

```lean
integratedMoser_windowUpperBoundData_of_lowerAverageWindow
integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData.toLowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

Status: upper-bound calculation **WIRE NOW**; lower-average and strict-gap producer **HONEST FRONTIER**.

### `IntervalDomainMoserLadderAtoms.lean`

The current residual record still has these fields:

```lean
l2SeedRegularity
moserDissipation
relativeMoserInterpolation
quantitativeEndpoint
```

For the integrated-window route, the analogous thinner record should no longer carry a monolithic `moserDissipation` if the new window-FTC/higher-power route can produce it. But it must still carry the honest frontiers.

Recommended new record shape in a non-Zinan file:

```lean
structure IntervalDomainIntegratedWindowMoserResiduals
    (p : CM2Params) where
  rawGradient :
    ∀ {T p0 : ℝ} {u₀ : intervalDomain.Point → ℝ}
      {u v : ℝ → intervalDomain.Point → ℝ},
      0 < T →
      InitialTrace intervalDomain u₀ u →
      PaperPositiveInitialDatum intervalDomain u₀ →
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
        IntervalDomainRawMoserGradientTimeIntegrability u T p0

  -- FTC side conditions, exact type to match P3MoserEnergyContinuity producer.
  windowFTCInputs :
    ∀ {T p0 : ℝ} {u₀ : intervalDomain.Point → ℝ}
      {u v : ℝ → intervalDomain.Point → ℝ},
      0 < T →
      InitialTrace intervalDomain u₀ u →
      PaperPositiveInitialDatum intervalDomain u₀ →
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
        /* derivative/time/PDE initial-window integrability packages */

  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0

  lowerAverage :
    ∀ {T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
      IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 →
      IntegratedMoserEnergyNonnegativity intervalDomain u T p0 →
      IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 →
      RelativeMoserInterpolationBefore intervalDomain u T rho p0 →
      0 < rho → 0 ≤ p0 →
        ∀ q, p0 ≤ q → 0 ≤ q →
          LpPowerBoundedBefore intervalDomain q T u →
            Nonempty
              (Σ Cnext : ℝ,
                IntegratedMoserHighExcursionLowerAverageWindowFrontier
                  intervalDomain u T rho p0 q Cnext)

  upperDataGap :
    ∀ {T rho p0 : ℝ} {u : ℝ → intervalDomain.Point → ℝ},
      IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 →
      IntegratedMoserEnergyNonnegativity intervalDomain u T p0 →
      IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 →
      RelativeMoserInterpolationBefore intervalDomain u T rho p0 →
      0 < rho → 0 ≤ p0 →
        ∀ q, p0 ≤ q → 0 ≤ q →
          Nonempty
            (IntegratedMoserWindowUpperDataGapFrontier
              intervalDomain u T rho p0 q)

  quantitativeEndpoint :
    -- keep existing field shape from IntervalDomainMassLpSmoothingMoserLadderResiduals
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ)
          (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

This keeps genuine analytic tasks visible and moves pure adapters out of the headline residual.

Status: record definition **WIRE NOW**; the fields listed above are mixed: `rawGradient`, `windowFTCInputs`, `lowerAverage`, `upperDataGap`, and possibly `quantitativeEndpoint` are **HONEST FRONTIER** unless already supplied by separate producers; the conversions around them are WIRE NOW.

### `IntervalDomainStatementAssembly.lean`

The pushed file already has the collapse routes:

```lean
IntervalDomainPaper2Prop25IntegratedMoserFrontierData.toIntegratedStepFrontierData
IntervalDomainPaper2Prop25LowerUpperFrontierData.toIntegratedStepFrontierData
intervalDomainPaper2_Proposition_2_5_of_integratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_of_integratedStepFrontierData
intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_integratedStepFrontierData
```

Add a wrapper from the preferred lower-average/upper-data-gap data package rather than carrying `IntegratedMoserFirstCrossingLowerUpperFrontiers` directly:

```lean
namespace ShenWork.Paper2

/-- Statement-layer route from lower-average plus upper-data-gap first-crossing
data to the existing integrated-step frontier. -/
def IntervalDomainPaper2Prop25LowerAverageUpperDataGapFrontierData.toIntegratedStepFrontierData
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25LowerAverageUpperDataGapFrontierData p) :
    IntervalDomainPaper2Prop25IntegratedStepFrontierData p where
  integratedStep := by
    intro T rho p0 u v hsol hcross hboot
    exact integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
      (h.lowerAverageUpperDataGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

end ShenWork.Paper2
```

The corresponding record shape should mirror the pushed `IntervalDomainPaper2Prop25LowerUpperFrontierData` but carry the more decomposed data:

```lean
structure IntervalDomainPaper2Prop25LowerAverageUpperDataGapFrontierData
    (p : CM2Params) : Prop where
  lowerAverageUpperDataGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u (p.N : ℝ) T rho p0 →
        IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
          intervalDomain u T rho p0
  quantitativeEndpoint :
    -- same as existing IntervalDomainPaper2Prop25IntegratedStepFrontierData
    ∀ {u₀ : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u₀ →
    ∀ {T : ℝ}, 0 < T →
    ∀ {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
    ∀ pExp,
      max (p.N : ℝ) (max (p.m * (p.N : ℝ)) (p.γ * (p.N : ℝ))) < pExp →
      LpPowerBoundedBefore intervalDomain pExp T u →
        ∃ pSeq rootBound : ℕ → ℝ,
          (∀ r > 1, LpPowerBoundedBefore intervalDomain r T u) →
            IntervalDomainMoserQuantitativeEndpoint u T pSeq rootBound
```

Status: **WIRE NOW**. This is the clean statement-layer route. It does not pretend to prove lower-average or upper-data-gap.

## Fine-grained item classification requested in task 4

### `IntegratedMoserEnergyWindowFTC`

**WIRE NOW** for endpoint continuity via anchoring.  
**HONEST FRONTIER** for its derivative/time-term/PDE-term initial-window integrability packages unless already produced by a separate theorem.

### Interval integrability of `G`, `Y`, `Z`, `max`

**WIRE NOW** from `IntegratedMoserFirstCrossingRegularity`:

```lean
hreg.gradient_intervalIntegrable_of_Icc       -- G
hreg.power_intervalIntegrable_of_Icc          -- Y and Z = p+rho
hreg.maxOneEnergy_intervalIntegrable_of_Icc   -- max 1 Y
```

### Nonnegativity of `∫Y`

**WIRE NOW** for intervalDomain positive classical solutions:

```lean
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
intervalDomain_integratedMoserEnergyNonnegativity_of_global_classical
intervalDomain_integratedMoserEnergy_nonneg_of_pointwise_nonneg
```

For window integrals of nonnegative functions, use the existing interval-domain nonnegativity package plus interval-integrability.

### Coefficient gap / surplus

**WIRE NOW** only when the local theorem’s coefficient-surplus/gap hypothesis is explicitly supplied.  
**HONEST FRONTIER** if it is supposed to choose an epsilon/witness that closes the actual lower-vs-upper high-excursion gap.

Practical rule: algebraic coefficient absorption is wiring; quantitative epsilon choice tied to `Ceps`, `Gbound`, `M`, `(b-a)`, and `lowerBound` is a frontier.

### Lower-average frontier

**HONEST FRONTIER**:

```lean
IntegratedMoserHighExcursionLowerAverageWindowFrontier
```

This is Zinan’s last-exit/window-thickness work. Do not edit `P3MoserHighExcursionProducer.lean`.

### Upper-bound witness / upper-gap frontier

Split it:

* **WIRE NOW**: fixed-window upper-bound data/witness once lower window and gap choice are supplied.

```lean
integratedMoser_windowUpperBoundData_of_lowerAverageWindow
integratedMoserWindowUpperGapWitnessFrontier_of_upperDataGap
integratedMoserWindowUpperGapWitnessFrontier_of_epsilonGap
```

* **HONEST FRONTIER**: producing the actual strict gap chooser.

```lean
IntegratedMoserWindowUpperDataGapFrontier
IntegratedMoserWindowUpperGapEpsilonFrontier
```

unless your new local `_coeffGap` theorem already proves exactly one of those frontier structures from the window FTC + energy inequality data.

## Recommended next cleanup order

1. **Add a statement-layer `LowerAverageUpperDataGapFrontierData` wrapper** in `IntervalDomainStatementAssembly.lean`. This is pure wiring and will expose the preferred decomposed route directly to Proposition 2.5 and Corollary 2.1.

2. **Add a non-Zinan residual record** in `IntervalDomainMoserLadderAtoms.lean` that carries only:
   - raw all-exponent gradient integrability;
   - FTC side-condition packages;
   - relative interpolation;
   - lower-average frontier;
   - upper-data-gap frontier;
   - quantitative endpoint.

3. **Add a producer from that residual record to `IntegratedMoserFirstCrossingLowerAverageUpperDataGapData`**. The body should be pure wiring:
   - anchored regularity from rawGradient;
   - energy nonnegativity from classical/global;
   - integrated/window dissipation from `LpBootstrapEnergyInequality + IntegratedMoserEnergyWindowFTC + higherPower coeff frontier` if your local theorem supports it;
   - relative interpolation from the residual field;
   - lowerAverage and upperDataGap from residual fields.

4. Keep the following marked as frontiers in the headline docs/structures:
   - `IntervalDomainRawMoserGradientTimeIntegrability`;
   - FTC side integrability packages;
   - `IntegratedMoserHighExcursionLowerAverageWindowFrontier`;
   - `IntegratedMoserWindowUpperDataGapFrontier`;
   - quantitative endpoint, unless a separate endpoint producer is ready.

This removes stale residuals without claiming a false unconditional proof.
