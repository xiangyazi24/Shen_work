# Q2990 (shen1) — fixed coefficient-gap first-crossing wrapper

Repo: `xiangyazi24/Shen_work`  
Audited HEAD: `e559581bb93e0036af36f7e6f12f5e719e6c065e` (`Expose fixed Moser dissipation coefficient-gap route`)  
Scope: source-grounded Lean code/audit for `ShenWork/PDE/P3MoserRegularityProducer.lean` only.  
Constraint respected: do **not** touch `ShenWork/PDE/P3MoserHighExcursionProducer.lean`.

## Executive answer

The requested theorem is additive and should sit in `P3MoserRegularityProducer.lean` in the existing section

```lean
/-! ### Direct threshold-plan first-crossing producer -/
```

immediately after

```lean
intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
```

and before

```lean
/-! ### Lower-average/epsilon-gap data assembly -/
```

It should not use the lower-average / upper-gap frontier route.  It should use the newly exposed fixed wrapper

```lean
intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
```

to derive `IntegratedMoserDissipationDropBefore`, then call the existing direct threshold-plan consumer

```lean
intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
```

## Exact Lean code

I would add the direct import below.  It is technically already reachable through `P3MoserEnergyContinuity`, but making the dependency explicit is cleaner because the new theorem calls `intervalDomain_LpBootstrapEnergyInequality_of_regularity` directly.

```lean
import ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality
```

Then add this theorem near the direct threshold-plan block:

```lean
/-- Classical-regularity-data first-crossing route with the fixed integrated
Moser dissipation produced from the regular-energy coefficient-gap wrapper.

The classical solution and cross bootstrap estimate first produce the strict-time
`LpBootstrapEnergyInequality`.  The classical regularity data produces the
closed-time/integrability package, and classical positivity supplies Moser-energy
nonnegativity.  The new coefficient-gap wrapper then supplies the fixed
`IntegratedMoserDissipationDropBefore` consumed by the direct threshold-plan
first-crossing producer. -/
theorem
    intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
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
      ∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < p * A) :
    IntegratedMoserFirstCrossingStep intervalDomain u T rho p0 := by
  have henergy : LpBootstrapEnergyInequality intervalDomain u T rho p0 :=
    ShenWork.Paper2.IntervalDomainLpBootstrapEnergyInequality.
      intervalDomain_LpBootstrapEnergyInequality_of_regularity
        hsol hcross hboot
  have hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
    intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
      hdata hsol
  have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
    intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
  have hdiss : IntegratedMoserDissipationDropBefore intervalDomain u T rho p0 :=
    intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
      (params := params) (T := T) (rho := rho) (p0 := p0)
      (u := u) hboot henergy hFTC hreg hnonneg hrel hgap
  exact
    intervalDomain_integratedMoserFirstCrossingStep_of_abstract_data
      hreg hnonneg hdiss hrel
      (AbstractLpBootstrapHypothesis.rho_pos hboot)
      (p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
```

## Axiom-audit line

Add this to the existing `section AxiomAudit`:

```lean
#print axioms intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

A natural placement is immediately after the existing direct threshold-plan audit lines:

```lean
#print axioms intervalDomain_firstCrossingStep_of_classical_integratedData
#print axioms intervalDomain_firstCrossingStep_of_lite_classical_integratedData
#print axioms intervalDomain_firstCrossingStep_of_classicalRegularityData_integratedData
#print axioms intervalDomain_firstCrossingStep_of_classicalRegularityData_regularEnergyCoeffGap
```

## Build target

Use:

```bash
lake build ShenWork.PDE.P3MoserRegularityProducer
```

A narrower parser/elaborator check would be:

```bash
lake env lean ShenWork/PDE/P3MoserRegularityProducer.lean
```

## Type-mismatch notes / corrections

There should be no mismatch with `intervalDomain_LpBootstrapEnergyInequality_of_regularity` if the theorem is called with the raw `u` and the same `hsol`, `hcross`, and `hboot`:

```lean
hsol   : IsPaper2ClassicalSolution intervalDomain params T u v
hcross : CrossDiffusionBootstrapEstimate intervalDomain params T rho u v
hboot  : AbstractLpBootstrapHypothesis intervalDomain u (params.N : ℝ) T rho p0
```

This produces exactly:

```lean
LpBootstrapEnergyInequality intervalDomain u T rho p0
```

which is the `henergy` input expected by

```lean
intervalDomain_integratedMoserDissipationDropBefore_of_regularEnergy_coeffGap
```

The main possible mismatch is nonnegativity.  The fixed dissipation wrapper does **not** take the pointwise lemma

```lean
intervalDomain_power_integral_nonneg_of_classical
```

and it does **not** take endpoint-energy data.  It takes the package:

```lean
IntegratedMoserEnergyNonnegativity intervalDomain u T p0
```

so the correct argument is:

```lean
have hnonneg : IntegratedMoserEnergyNonnegativity intervalDomain u T p0 :=
  intervalDomain_integratedMoserEnergyNonnegativity_of_classical hsol
```

Similarly, the fixed wrapper wants the full first-crossing regularity package, not the classical residual package directly.  The right conversion is the existing theorem:

```lean
have hreg : IntegratedMoserFirstCrossingRegularity intervalDomain u T p0 :=
  intervalDomain_integratedMoserFirstCrossingRegularity_of_classicalRegularityData
    hdata hsol
```

The final `rho_pos` and `p0_nonneg` inputs for the threshold-plan consumer do not need to be separate assumptions.  They follow from `hboot`:

```lean
(AbstractLpBootstrapHypothesis.rho_pos hboot)
(p0_nonneg_of_abstractLpBootstrapHypothesis hboot)
```

The coefficient-gap shape should stay exactly as in the fixed wrapper specialization to `theta = 2`:

```lean
∀ p, p0 ≤ p → ∀ A K : ℝ, 0 < A → 0 < K → (2 : ℝ) < p * A
```

Even though the conclusion does not use `K` in the inequality itself, keeping `K` and `0 < K` in the quantifier matches the surplus interface consumed by the integrated-closure wrapper.
