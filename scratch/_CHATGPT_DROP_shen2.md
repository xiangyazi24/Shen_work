# Q2373 shen2: Paper2 full-statement reduction after common-free actual-atom main wrappers

Repo target: `xiangyazi24/Shen_work`, `main` at commit `cbeb0de2`.

## Executive answer

Yes, a faithful, buildable next reduction exists, but it is **not** a fully common-free full-statement route.

The current common-free actual-atom wrappers are enough for the **headline main theorems**:

```lean
Theorem_1_1 intervalDomain p ∧ Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C
```

via:

```lean
IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
```

But the **full statement target** is larger:

```lean
def IntervalDomainPaper2StatementTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2Corollary21BootstrapTargets p ∧
    IntervalDomainPaper2AprioriTargets p ∧
      IntervalDomainPaper2LocalAndMainTheoremTargets p C
```

So full statement accounting additionally needs:

```lean
IntervalDomainPaper2Corollary21BootstrapTargets p
IntervalDomainPaper2AprioriTargets p
Proposition_1_1 intervalDomain p
```

The actual-atom Cor21/Prop25 route can handle the first item.  The proved `χ₀ = 0` local existence plus finite-horizon frontier can handle `Proposition_1_1`.  The honest remaining side input is the a-priori package, specifically Lemma 4.1.

The next buildable wrapper should therefore combine:

1. common-free actual-atom main-theorem data;
2. thin section-2 data;
3. chi-zero Proposition 1.1 finite-horizon data;
4. an explicit a-priori/Lemma 4.1 producer, preferably the existing positive solution-slice interpolation frontier:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation p
```

through:

```lean
intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
```

This avoids both no-go routes:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
OldUnitIntervalPowerGNYoungForMoser
```

## Source-grounded facts

### Full target shape

In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`:

```lean
def IntervalDomainPaper2StatementTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2Corollary21BootstrapTargets p ∧
    IntervalDomainPaper2AprioriTargets p ∧
      IntervalDomainPaper2LocalAndMainTheoremTargets p C
```

This is why headline-only Theorem 1.1--1.3 wrappers are not full statement wrappers.

### Common-free headline wrappers already present

In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`:

```lean
abbrev IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
    p C

theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C
```

and:

```lean
abbrev
    IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2MainTheoremChiZeroActualAtomMassGradientCor21LocalFreeFrontierData
    p C

theorem
    intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C
```

These are headline-only.  They intentionally do not include section-2 target accounting, Lemma 3.1/4.1 accounting, or Proposition 1.1.

### Actual-atom Corollary 2.1 and Proposition 2.5 producers

In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`:

```lean
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation
    hData.relativeMoserInterpolation
    hData.quantitativeEndpoint

theorem intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
    hData.moserDissipation hData.relativeMoserInterpolation

theorem
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p
```

For mass-gradient lowering of relative Moser:

```lean
def IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms
    {p : CM2Params}
    (h : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    IntervalDomainPaper2Prop25ActualAtomFrontierData p
```

and:

```lean
theorem
    intervalDomainPaper2_Proposition_2_5_of_actualAtomMassGradientFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    Proposition_2_5 intervalDomain p

theorem
    intervalDomainPaper2_Corollary_2_1_of_actualAtomMassGradientFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    Corollary_2_1 intervalDomain p
```

### Existing a-priori producer that avoids false global interpolation

In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`:

```lean
def IntervalDomainPaper2AprioriTargets (p : CM2Params) : Prop :=
  Lemma_3_1 intervalDomain p ∧ Lemma_4_1 intervalDomain p

theorem intervalDomainPaper2_Lemma_3_1
    (p : CM2Params) :
    Lemma_3_1 intervalDomain p :=
  Lemma31Closure.Lemma_3_1_intervalDomain p

theorem intervalDomainPaper2_Lemma_4_1_of_solutionInterpolationFrontier
    (p : CM2Params)
    (hSlice :
      IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
        p) :
    Lemma_4_1 intervalDomain p

theorem intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
    (p : CM2Params)
    (hSlice :
      IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
        p) :
    IntervalDomainPaper2AprioriTargets p
```

This is the current honest Lemma 4.1 route.  It is not common-free, but it is not the refuted global interpolation route.

### No-go a-priori route

Do not use:

```lean
intervalDomainPaper2_Lemma_4_1_of_GN_frontier
intervalDomainPaper2_aprioriTargets_of_GN_frontier
```

because they require:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
```

and the source comments mark it as refuted by:

```lean
IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation
```

Also do not use `OldUnitIntervalPowerGNYoungForMoser`; `ShenWork/Paper2/IntervalDomainGNYObstruction.lean` proves:

```lean
theorem not_oldUnitIntervalPowerGNYoungForMoser :
    ¬ OldUnitIntervalPowerGNYoungForMoser
```

## Answer to the direct questions

### 1. Can full `IntervalDomainPaper2StatementTargets` be assembled from common-free actual-atom Cor21 plus an existing a-priori/Lemma 4.1 producer?

**Yes**, with one honest a-priori input.  The full wrapper can be built now by combining:

```lean
intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData
intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
```

or the mass-gradient variant using:

```lean
IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData.toActualAtoms
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
```

This is faithful because the a-priori/Lemma 4.1 side is a separate explicit input.  It does not pretend actual-atom Cor21 proves Lemma 4.1.

### 2. Missing frontier if trying to make the full route completely common-free

There is no source-grounded theorem currently proving:

```lean
Lemma_4_1 intervalDomain p
```

from the common-free actual-atom Cor21 route alone.  The smallest honest missing input is either:

```lean
Lemma_4_1 intervalDomain p
```

or, preferably in terms of an existing producer:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation p
```

because that feeds:

```lean
intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
```

Inference: if the project wants a truly common-free full statement route, the next analytic theorem to prove is a Lemma 4.1 producer that does not rely on either global `IntervalDomainInterpolation` or the positive solution-slice interpolation frontier.  No such theorem is visible in the current source.

### 3. Minimal Lean patch outline

Add section-2 helpers first.

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-- Section-2 Corollary 2.1 plus bootstrap targets from thin section-2 data and
actual-atom Prop25/Cor21 data. -/
theorem intervalDomainPaper2_corollary21BootstrapTargets_of_thinActualAtomFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hAtoms : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData p hAtoms,
    intervalDomainPaper2_bootstrapEstimateTargets_of_thinActualAtomFrontierData
      p hThin hAtoms⟩

/-- Mass-gradient variant of the section-2 Corollary 2.1 plus bootstrap wrapper. -/
theorem
    intervalDomainPaper2_corollary21BootstrapTargets_of_thinActualAtomMassGradientFrontierData
    (p : CM2Params)
    (hThin : IntervalDomainPaper2BootstrapEstimateThinFrontierData p)
    (hAtoms : IntervalDomainPaper2Prop25ActualAtomMassGradientFrontierData p) :
    IntervalDomainPaper2Corollary21BootstrapTargets p :=
  intervalDomainPaper2_corollary21BootstrapTargets_of_thinActualAtomFrontierData
    p hThin hAtoms.toActualAtoms

end

end ShenWork.Paper2
```

Then add the full-statement package using the existing a-priori producer.

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-- Full-statement data for the `χ₀ = 0` common-free actual-atom main route,
with Lemma 4.1 supplied by the existing positive solution-slice a-priori
producer. -/
structure IntervalDomainPaper2StatementChiZeroActualAtomCor21Section2ThinAprioriFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  aprioriInterpolation :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      p
  main : IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
    p C

/-- Full-statement wrapper from common-free actual-atom main data plus the
separate a-priori interpolation frontier. -/
theorem intervalDomainPaper2_statementTargets_of_chiZeroActualAtomCor21Section2ThinAprioriFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroActualAtomCor21Section2ThinAprioriFrontierData
        p C) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_thinActualAtomFrontierData
      p hData.section2 hData.main.prop25Actual,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.aprioriInterpolation,
    ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
        p hχ0 ha hb hα hγ hData.proposition11,
      intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
        p C hχ0 ha hb hα hγ hData.main⟩⟩

end

end ShenWork.Paper2
```

Mass-gradient variant:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainMoserClosure

namespace ShenWork.Paper2

noncomputable section

/-- Full-statement data for the `χ₀ = 0` common-free mass-gradient actual-atom
main route, with Lemma 4.1 supplied separately by the positive solution-slice
a-priori producer. -/
structure
    IntervalDomainPaper2StatementChiZeroActualAtomMassGradientCor21Section2ThinAprioriFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  aprioriInterpolation :
    IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
      p
  main :
    IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomMassGradientCor21FrontierData
      p C

/-- Full-statement wrapper from common-free mass-gradient actual-atom main data
plus the separate a-priori interpolation frontier. -/
theorem
    intervalDomainPaper2_statementTargets_of_chiZeroActualAtomMassGradientCor21Section2ThinAprioriFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroActualAtomMassGradientCor21Section2ThinAprioriFrontierData
        p C) :
    IntervalDomainPaper2StatementTargets p C :=
  ⟨intervalDomainPaper2_corollary21BootstrapTargets_of_thinActualAtomMassGradientFrontierData
      p hData.section2 hData.main.prop25MassGradient,
    intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
      p hData.aprioriInterpolation,
    ⟨intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
        p hχ0 ha hb hα hγ hData.proposition11,
      intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
        p C hχ0 ha hb hα hγ hData.main⟩⟩

end

end ShenWork.Paper2
```

These wrappers should be buildable in `IntervalDomainStatementAssembly.lean` itself because that file already imports:

```lean
ShenWork.Paper2.IntervalDomainTheorem11Umbrella
ShenWork.Paper2.IntervalDomainTheorem11ChiZeroUnconditional
ShenWork.Paper2.IntervalDomainStructuredMoserData
ShenWork.Paper2.IntervalDomainTheorem12
ShenWork.Paper2.IntervalDomainTheorem13
ShenWork.PDE.P3MoserActualWiring
ShenWork.PDE.P3MoserLemmas
```

If placed in a new file, import only:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly
```

## Headline-only versus full statement accounting

### Headline-only route already improved

The following are headline-only wrappers:

```lean
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomMassGradientCor21FrontierData
```

They prove:

```lean
IntervalDomainPaper2MainTheoremTargets p C
```

They do **not** prove:

```lean
IntervalDomainPaper2StatementTargets p C
```

because they do not include `IntervalDomainPaper2Corollary21BootstrapTargets`, `IntervalDomainPaper2AprioriTargets`, or Proposition 1.1 accounting.

### Full statement route after the proposed patch

The proposed wrappers prove:

```lean
IntervalDomainPaper2StatementTargets p C
```

but still explicitly carry:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation p
```

for Lemma 4.1.  This is honest full statement accounting; it should not be described as a fully common-free a-priori route.

## No-go routes to keep out

### Refuted global interpolation

Do not use:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
intervalDomainPaper2_Lemma_4_1_of_GN_frontier
intervalDomainPaper2_aprioriTargets_of_GN_frontier
IntervalDomainPaper2InterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13InterpolationFrontierData
```

The source comments identify the premise as refuted by:

```lean
IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation
```

### False old Moser GN/Young predicate

Do not use:

```lean
OldUnitIntervalPowerGNYoungForMoser
Proposition_2_5_intervalDomain_of_MCL_frontiers
relativeMoserInterpolationBefore_of_unitIntervalPowerGNYoung
```

because:

```lean
theorem not_oldUnitIntervalPowerGNYoungForMoser :
    ¬ OldUnitIntervalPowerGNYoungForMoser
```

is proved in `ShenWork/Paper2/IntervalDomainGNYObstruction.lean`.

## Recommended next priority

1. Add the two section-2 helper wrappers for actual-atom Cor21 + thin bootstrap.
2. Add the two full-statement structures/wrappers above, using the existing positive solution-slice a-priori producer only for `IntervalDomainPaper2AprioriTargets`.
3. Later, if the goal is a truly common-free full route, prove a new Lemma 4.1 producer that avoids both `IntervalDomainInterpolation` and `IntervalDomainClassicalSolutionPositiveInterpolation`.  Until then, the positive solution-slice a-priori frontier is the smallest honest named input for full statement accounting.
