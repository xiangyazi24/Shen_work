# Q2646 shen1 — next safe statement-level reductions after LowerUpper thin route

Repo: `xiangyazi24/Shen_work`

Target file: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

Context inspected: current `main` has the generic-K LowerUpper Stability24 route and the sup-norm+Stability24 thin LowerUpper headline route from commit `0a648f98`.

Excluded by ownership: no recommendations here require touching

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

## Executive recommendation

Do **not** add Stability24-only wrappers for every historical Moser route.  The useful reduction has already been made for the preferred LowerUpper headline route:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperThinFrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperThinP2MainData
```

The next safe, non-conflicting wrapper worth adding is only the **IntegratedStep P2Main Stability24 route**, because it is the useful alternate headline when another worker can provide an `IntegratedMoserFirstCrossingStep` atom directly but not the lower/upper split.  It avoids high-excursion producer ownership and remains a thinner public surface than the old full-stability IntegratedStep route.

For the older ladder routes:

```text
CETerminal
CERawGrad
CEGrad
ClosedEnergy
base Moser actual-linear
```

Stability24-only wrappers are mechanically valid but mostly redundant.  They add API volume without changing the preferred route.  If someone is actively consuming the terminal endpoint route, CETerminal can be added as an optional compatibility wrapper; otherwise stop at IntegratedStep + LowerUpper.

## Existing generic helper already solves the real reduction

The core reduction is already route-independent:

```lean
IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25
```

It converts:

```lean
IntervalDomainPaper3Stability24ActualLinearFrontierData p C
```

to:

```lean
IntervalDomainPaper3Stability23To25FrontierData p C
```

using:

```lean
ha : 0 < p.a
hχ0 : 0 < p.χ₀
```

That helper is the only mathematical/logical content.  Any further route-specific `...Stability24...FrontierData` is just API convenience around this helper.

## Route-by-route classification

| Route | Current status | Add Stability24 wrapper? | Why |
|---|---:|---:|---|
| LowerUpper | Done | No more | This is the preferred headline route and already has generic-K Stability24 plus sup-norm thin wrappers. |
| IntegratedStep | Good next target | Yes, useful | It is the clean fallback headline if a direct `IntegratedMoserFirstCrossingStep` atom is available. It avoids high-excursion producer files and removes full stability from a live route. |
| CETerminal | Optional | Usually no | It is a plausible legacy/pre-LowerUpper route, but after LowerUpper + IntegratedStep it is mostly a compatibility endpoint. Add only if current callers still use terminal-pointwise data directly. |
| CERawGrad | Redundant | No | It is an intermediate lowering of dissipation/interpolation atoms. Users can route to CETerminal or IntegratedStep instead. |
| CEGrad | Redundant | No | Pure ladder intermediate. Adding a Stability24 surface here duplicates wrappers without new benefit. |
| ClosedEnergy | Redundant | No | Pure L²-seed reduction surface; useful internally, not as a headline statement API. |
| Base Moser actual-linear | Redundant | No | Oldest/widest Moser route. It carries the least reduced Moser fields; avoid adding another public headline variant. |
| AprioriActualLinearSmall | Not asked, redundant | No | It is upstream of Moser routes and not the current headline. Same stability converter can be used inline if needed. |

## Useful next wrapper: IntegratedStep + Stability24 + P2Main

Minimal fields for the recommended IntegratedStep wrapper:

```lean
core :
  IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
compactness :
  IntervalDomainPaper3ConcreteCompactnessRegularizationData
    p M0 uBar vLower K
stability24 :
  IntervalDomainPaper3Stability24ActualLinearFrontierData p
    (intervalDomainPaper3Constants p M0 uBar vLower)
```

Statement-level P2Main wrapper:

```lean
propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
mainline :
  IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K
```

### Lean skeleton

Insert before the closing `end` of the main namespace, not in the reopened `#print axioms` block.

```lean
/-- Integrated-step Moser mainline data with the actual-linear-small stability
package reduced to its non-vacuous Theorem 2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallIntegratedStepFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert IntegratedStep + Stability24 data to the existing full IntegratedStep
frontier surface. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
        p M0 uBar vLower K)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepFrontierData
      p M0 uBar vLower K where
  core := h.core
  compactness := h.compactness
  stability := h.stability24.toStability23To25 ha hχ0

/-- Mainline target from the IntegratedStep Moser route with Stability24-only
actual-linear stability. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    (hData.toCurrent ha hχ0)

/-- Instance-facing mainline target from the IntegratedStep Moser route with
Stability24-only actual-linear stability. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement data for the IntegratedStep Moser route,
Paper2 main theorem targets, and Stability24-only actual-linear stability. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from the
IntegratedStep Moser route, Paper2 main theorem targets, and Stability24-only
actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from the
IntegratedStep Moser route, Paper2 main theorem targets, and Stability24-only
actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out
```

Add `#print axioms` entries after the existing IntegratedStep prints:

```lean
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
```

## Optional wrapper: CETerminal + Stability24 + P2Main

Only add this if there are current consumers of the terminal-pointwise endpoint route.  It is valid, but less important than IntegratedStep because it is no longer the preferred headline surface.

Minimal fields:

```lean
core : IntervalDomainSectorialMainlineMoserActualLinearSmallCETerminalFacts p
compactness :
  IntervalDomainPaper3ConcreteCompactnessRegularizationData p M0 uBar vLower K
stability24 :
  IntervalDomainPaper3Stability24ActualLinearFrontierData p
    (intervalDomainPaper3Constants p M0 uBar vLower)
```

Exact names if added:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalStability24FrontierData
IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalStability24FrontierData.toCurrent
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallCETerminalStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalStability24P2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalStability24P2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallCETerminalStability24P2MainDataFact
```

The `toCurrent` target should be:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallCETerminalFrontierData
  p M0 uBar vLower K
```

with:

```lean
core := h.core
compactness := h.compactness
stability := h.stability24.toStability23To25 ha hχ0
```

## Do not add wrappers for these unless a caller specifically asks

### Base Moser actual-linear route

Existing route:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallFrontierData
```

A Stability24 variant would have fields:

```lean
core : IntervalDomainSectorialMainlineMoserActualLinearSmallFacts p
compactness : ConcreteCompactnessRegularizationData ... K
stability24 : Stability24ActualLinear ...
```

This is valid but low value.  The base Moser route carries the broadest, least reduced Moser residuals.  Prefer IntegratedStep or LowerUpper.

### ClosedEnergy route

Existing route:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallClosedEnergyFrontierData
```

Valid but redundant.  It exists to reduce the L² seed, not as a final headline surface.

### CEGrad route

Existing route:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallCEGradFrontierData
```

Valid but redundant.  It only lowers the relative interpolation interface to mass-gradient data.

### CERawGrad route

Existing route:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallCERawGradFrontierData
```

Valid but redundant.  It is another intermediate analytic-atom surface between terminal and CEGrad.

## Type and constants pitfalls

1. **Use `intervalDomainPaper3Constants` for Stability24**, not sectorial constants:

```lean
IntervalDomainPaper3Stability24ActualLinearFrontierData p
  (intervalDomainPaper3Constants p M0 uBar vLower)
```

2. **Only raw Theorem 2.2 routes use sectorial constants.**  In the raw-linear route, the `theorem22Nonminimal` / `theorem22Minimal` fields use:

```lean
intervalDomainSectorialStabilityNorms.c1Distance
(intervalDomainSectorialPaper3Constants p M0 uBar vLower).chiCritical
```

Moser IntegratedStep / LowerUpper / CETerminal routes do not carry raw Theorem 2.2 fields, so they should not mention `intervalDomainSectorialPaper3Constants` in the Stability24 wrappers.

3. **Keep `K` generic for Stability24-only wrappers.**  Use:

```lean
(K : CompactnessData intervalDomain)
compactness : IntervalDomainPaper3ConcreteCompactnessRegularizationData
  p M0 uBar vLower K
```

Only use `intervalDomainSupNormCompactnessData` in a separate `Thin...` route that also drops `upperEq` and `minimalUpper` using `IntervalDomainPaper3SupNormCompactnessAPosData`.

4. **Statement P2Main propositions field must be:**

```lean
IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
```

not `IntervalDomainPaper3Proposition1WithTheorem13FrontierData p C`.

5. **All actual-linear hypotheses still need to appear on the theorem**, even if only `ha` and `hχ0` are used by `toStability23To25`:

```lean
(ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
(hm : p.m = 1) (hβ : 1 ≤ p.β)
(hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
```

The old target route still uses `hb hm hβ hχ` to produce actual-linear persistence.

6. **Do not derive `0 ≤ p.β` here.**  The Stability24 fields retain the exact `global24` / `exp24` signatures; the converter forwards them unchanged.

7. **Declaration order matters.**  Add the IntegratedStep Stability24 wrapper after the existing IntegratedStep route definitions and before the LowerUpper section, or after the LowerUpper section before the final `end`.  Add prints only in the reopened bottom namespace.

## Best next commit scope

A clean next commit would add only:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData
IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepStability24FrontierData.toCurrent
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierData
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepStability24FrontierDataFact
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallIntegratedStepStability24P2MainDataFact
```

This gives one useful alternate headline beside the existing LowerUpper thin headline and avoids filling the file with route-ladder variants.
