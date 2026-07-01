# Q2988 (shen1) — downstream wiring after fixed integrated-dissipation wrapper

Repo: `xiangyazi24/Shen_work`  
Audited HEAD: `3fe8bffd2778a186815e05b2d416cda41b2c4912` (`Remove legacy Moser frontier shortcut wrappers`)  
Scope: source-grounded Lean audit/design only; no source edits.  
Constraint: do not touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.

## Executive answer

After Codex adds

```lean
intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
```

in `ShenWork/PDE/P3MoserIntegratedClosure.lean`, the next lowest-risk downstream wiring step is **additive**, not a field replacement:

1. Add a first-crossing wrapper in `ShenWork/PDE/P3MoserRegularityProducer.lean` that takes classical Moser regularity data, window FTC, relative interpolation, and the coefficient gap, derives `IntegratedMoserDissipationDropBefore` via the new fixed wrapper, and then calls the direct threshold-plan producer.
2. Then add additive statement/residual surfaces that use this wrapper, beginning with `Paper2.IntervalDomainStatementAssembly.IntervalDomainPaper2Prop25...` and then the reusable PDE ladder surface in `IntervalDomainMoserLadderAtoms`.

Do **not** replace existing `integratedDissipation` fields in-place as the next step. That is API-breaking and not necessary for a buildable residual reduction.

## 1. Current black-box `integratedDissipation` carriers

### Paper2 statement layer

File: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.

Current carrier:

```lean
structure IntervalDomainPaper2Prop25IntegratedMoserFrontierData
    (p : CM2Params) : Prop where
  classicalRegularity : ...
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMoserInterpolation : ...
  quantitativeEndpoint : ...
```

Its conversion

```lean
IntervalDomainPaper2Prop25IntegratedMoserFrontierData.toIntegratedStepFrontierData
```

passes that field to

```lean
intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
```

so `integratedDissipation` is a true black-box input here.

### Reusable PDE ladder layer

File: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.

Current carrier:

```lean
structure IntervalDomainMassLpSmoothingIntegratedMoserResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity : ...
  classicalRegularity : ...
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMoserInterpolation : ...
  quantitativeEndpoint : ...
```

Its conversion

```lean
IntervalDomainMassLpSmoothingIntegratedMoserResiduals.to_integratedStepResiduals
```

calls

```lean
intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
```

with `h.integratedDissipation`.

### Paper3 actual-linear compatibility-named layer

File: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

Current carrier:

```lean
structure
    IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
    (p : CM2Params) : Prop where
  boundednessHyp : IntervalDomainBoundednessHyp p
  closedEnergyTrace : ...
  classicalContinuityRegularity : ...
  integratedDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserDissipationDropBefore intervalDomain u T rho p0
  relativeMoserInterpolation : ...
  quantitativeEndpoint : ...
```

Despite the compatibility name, the old lowerAverage/upperDataGap fields are gone. The conversion

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals.to_integratedStepResiduals
```

uses the direct threshold-plan route, but still takes `integratedDissipation` as a black-box field.

### Theorem arguments in `P3MoserRegularityProducer`

File: `ShenWork/PDE/P3MoserRegularityProducer.lean`.

These are not structures, but they are central downstream wiring points with black-box `hdiss` arguments:

```lean
intervalDomain_firstCrossingStep_of_classical_integratedData
intervalDomain_firstCrossingStep_of_lite_classical_integratedData
intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
```

Legacy data constructors still take `hdiss` too:

```lean
intervalDomain_lowerAverageEpsilonData_of_classical
intervalDomain_lowerAverageEpsilonData_of_lite_classical
intervalDomain_lowerAverageUpperDataGapData_of_classical
intervalDomain_lowerAverageUpperDataGapData_of_lite_classical
```

but those construct legacy lower-average packages and should not be the first refactor target.

## 2. Lowest-risk additive wrapper

After the fixed wrapper exists in `P3MoserIntegratedClosure.lean`, add this theorem in `ShenWork/PDE/P3MoserRegularityProducer.lean`, near the existing direct threshold-plan theorem block:

```lean
/-- Direct first-crossing step from classical regularity data, the strict-time
Lp-bootstrap energy inequality, window FTC, relative interpolation, and the
coefficient gap needed to produce the fixed integrated Moser dissipation drop.

This is pure wiring: the hard analytic inputs are still regularity, window FTC,
relative interpolation, and the coefficient gap. -/
theorem intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
    {params : CM2Params} {T rho p0 : ℝ}
    {u v : ℝ → intervalDomain.Point → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain params T u v)
    (hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v)
    (hboot :
      AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0)
    (hdata : IntervalDomainIntegratedMoserClassicalRegularityData u T p0)
    (hFTC : IntegratedMoserEnergyWindowFTC intervalDomain u T p0)
    (hrel : RelativeMoserInterpolationBefore intervalDomain u T rho p0)
    (hgap :
      ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  have hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
      hdata hsol
  have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical
      (p0 := p0) hsol
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
  have hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
    intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
      (params := params) (T := T) (rho := rho) (p0 := p0) (u := u)
      hboot henergy hFTC hreg hnonneg hrel hgap
  exact intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
    hreg hnonneg hdiss hrel
    (AbstractLpBootstrapHypothesis.rho_pos hboot)
    (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
```

Add an axiom-audit line:

```lean
#print axioms intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

Expected build target:

```bash
lake build ShenWork.PDE.P3MoserRegularityProducer
```

Risk: very low. It is additive, uses existing imports in `P3MoserRegularityProducer`, and does not touch Zinan's file.

## 3. Next additive residual/data surfaces

### Patch A: Paper2 additive frontier surface

File: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.

Add a new structure rather than replacing `IntervalDomainPaper2Prop25IntegratedMoserFrontierData`:

```lean
structure IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData
    (p : CM2Params) : Prop where
  classicalRegularity :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntervalDomainIntegratedMoserClassicalRegularityData u T p0
  energyWindowFTC :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        IntegratedMoserEnergyWindowFTC intervalDomain u T p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  coefficientGap :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
      ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
  quantitativeEndpoint :
    -- same field as IntegratedMoserFrontierData
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

Then add:

```lean
namespace IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData

def toIntegratedStepFrontierData
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData p) :
    IntervalDomainPaper2Prop25IntegratedStepFrontierData p where
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
      hsol hcross hboot
      (h.classicalRegularity hsol hcross hboot)
      (h.energyWindowFTC hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (h.coefficientGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData
```

Then add theorem/fact wrappers mirroring the existing integrated-Moser wrappers:

```lean
intervalDomainPaper2_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
intervalDomainPaper2_Corollary_2_1_of_regularEnergyCoeffGapFrontierData
intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_regularEnergyCoeffGapFrontierData
```

Expected build target:

```bash
lake build ShenWork.Paper2.IntervalDomainStatementAssembly
```

Risk: low. It is additive and does not break callers of `IntervalDomainPaper2Prop25IntegratedMoserFrontierData`.

### Patch B: reusable PDE ladder additive surface

File: `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`.

Add a new structure parallel to `IntervalDomainMassLpSmoothingIntegratedMoserResiduals`, not a replacement:

```lean
structure IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
    (p : CM2Params) where
  a_pos : 0 < p.a
  chi_nonneg : 0 ≤ p.χ₀
  boundednessHyp : IntervalDomainBoundednessHyp p
  l2SeedRegularity : ...
  classicalRegularity : ...
  energyWindowFTC : ...
  relativeMoserInterpolation : ...
  coefficientGap : ...
  quantitativeEndpoint : ...
```

Then convert it to `IntervalDomainMassLpSmoothingIntegratedStepResiduals` using the same new regularity-producer wrapper:

```lean
namespace IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals

def to_integratedStepResiduals
    {p : CM2Params}
    (h : IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals p) :
    IntervalDomainMassLpSmoothingIntegratedStepResiduals p where
  a_pos := h.a_pos
  chi_nonneg := h.chi_nonneg
  boundednessHyp := h.boundednessHyp
  l2SeedRegularity := h.l2SeedRegularity
  integratedStep := fun hsol hcross hboot =>
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
      hsol hcross hboot
      (h.classicalRegularity hsol hcross hboot)
      (h.energyWindowFTC hsol hcross hboot)
      (h.relativeMoserInterpolation hsol hcross hboot)
      (h.coefficientGap hsol hcross hboot)
  quantitativeEndpoint := h.quantitativeEndpoint

end IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals
```

Add `to_routeResiduals` and `aprioriBound` wrappers if useful, paralleling the current integrated-Moser residual namespace.

Expected build target:

```bash
lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
```

Risk: low. Additive only.

### Patch C: Paper3 additive actual-linear wrapper, later

File: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`.

Current structure carrying the black-box field:

```lean
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
```

This compatibility-named structure now has no lowerAverage/upperDataGap fields, but still has:

```lean
classicalContinuityRegularity
integratedDissipation
relativeMoserInterpolation
```

Do **not** replace the `integratedDissipation` field in-place yet. A safer later additive surface would replace only this one field by:

```lean
energyWindowFTC : ... IntegratedMoserEnergyWindowFTC intervalDomain u T p0
coefficientGap : ... ∀ q, p0 ≤ q → ∀ A K, 0 < A → 0 < K → (2 : ℝ) < q * A
```

and reuse `classicalContinuityRegularity` by first converting it to `IntervalDomainIntegratedMoserClassicalRegularityData` via:

```lean
intervalDomain_classicalRegularityData_of_continuityRegularityData
```

This is more specialized and more churny than the Paper2/PDE additive surfaces, so it should come after those build.

## 4. API-breaking replacements to avoid for now

Avoid replacing `integratedDissipation` fields in these existing declarations as the next patch:

```lean
IntervalDomainPaper2Prop25IntegratedMoserFrontierData
IntervalDomainMassLpSmoothingIntegratedMoserResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerAverageUpperDataGapResiduals
```

Reasons:

* It will break any caller constructing these records.
* The additive replacement is enough to expose the lower-level route.
* The old surface remains meaningful: it is the abstract threshold-plan data route, where an upstream producer may already have an `IntegratedMoserDissipationDropBefore` package.

Also avoid changing:

```lean
IntervalDomainPaper2Prop25IntegratedStepFrontierData
IntervalDomainMassLpSmoothingIntegratedStepResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallIntegratedStepResiduals
```

Those intentionally abstract over the whole first-crossing step. Replacing `integratedStep` by energy/FTC data would collapse a useful abstraction layer.

## 5. Real analytic inputs that remain after the fixed wrapper

The fixed wrapper does **not** prove high-excursion, regularity, or endpoint closure. After it exists, the remaining genuine inputs are still:

* `IntegratedMoserEnergyWindowFTC intervalDomain u T p0`: the window FTC / absolute-continuity-type input.
* `IntervalDomainIntegratedMoserClassicalRegularityData` or `IntegratedMoserFirstCrossingRegularity`: closed-time energy continuity and gradient time integrability.
* `RelativeMoserInterpolationBefore intervalDomain u T rho p0`.
* The coefficient gap:
  ```lean
  ∀ q, p0 ≤ q → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < q * A
  ```
* `IntervalDomainMoserQuantitativeEndpoint` / terminal pointwise endpoint inputs for Proposition 2.5-style closure.
* The L² seed / closed-energy trace and Paper3 non-Moser residuals such as compactness, resolvent, stability24, continuation, and Paper2-main inputs.

`LpBootstrapEnergyInequality` itself is not necessarily a residual at these interval-domain classical-solution call sites, because existing wiring can produce it from:

```lean
intervalDomain_LpBootstrapEnergyInequality_of_regularity hsol hcross hboot
```

But the proof still depends on that theorem and on the hypotheses needed by `hsol`, `hcross`, and `hboot`.

## 6. High-excursion packages are not affected

The fixed wrapper is about producing `IntegratedMoserDissipationDropBefore` from energy/FTC/coefficient-gap data. It does not replace the Type-valued high-excursion lower/upper packages.

Keep the legacy lower/upper split packages in `P3MoserIntegratedClosure.lean` for now:

```lean
IntegratedMoserFirstCrossingFromWindowFrontier
IntegratedMoserFirstCrossingLowerUpperFrontiers
IntegratedMoserFirstCrossingLowerAverageEpsilonData
IntegratedMoserFirstCrossingLowerAverageUpperDataGapData
integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

They remain distinct, Type-valued high-excursion producer surfaces and are still referenced by lower/upper split routes such as:

```lean
IntervalDomainPaper2Prop25LowerUpperFrontierData
IntervalDomainMassLpSmoothingLowerUpperFrontierResiduals
IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals
```

Deleting or rerouting those surfaces is an API policy decision, not a consequence of the fixed integrated-dissipation wrapper.

## Recommended patch order

1. **P3MoserRegularityProducer additive theorem**  
   Add `intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap`.  
   Build:
   ```bash
   lake build ShenWork.PDE.P3MoserRegularityProducer
   ```

2. **Paper2 additive frontier**  
   Add `IntervalDomainPaper2Prop25RegularEnergyCoeffGapFrontierData` and theorem/fact wrappers.  
   Build:
   ```bash
   lake build ShenWork.Paper2.IntervalDomainStatementAssembly
   ```

3. **Reusable PDE ladder additive residual**  
   Add `IntervalDomainMassLpSmoothingRegularEnergyCoeffGapResiduals` and conversions.  
   Build:
   ```bash
   lake build ShenWork.PDE.IntervalDomainMoserLadderAtoms
   ```

4. **Optional Paper3 additive actual-linear surface**  
   Add a Paper3-specific regular-energy/coefficient-gap residual only after the generic surfaces build.  
   Build:
   ```bash
   lake build ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly
   ```

All four are additive. No axioms, no sorries, no replacement of hard analytic proofs by declarations.
