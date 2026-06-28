# Q1586 (cron1) -- which 39-sorry files are on the headline/FAC critical path?

Repository: `xiangyazi24/Shen_work`  
Branch committed: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Method / caveat

Connector-only inspection.  I did not run Lean locally and did not use Python/sandbox.

I used GitHub code search and `fetch_file` on the default/indexed repo.  The scratch file is committed to `chatgpt-scratch`, as requested.  The connector does not expose a full transitive import graph command, so the dependency verdict below is based on:

* the direct imports of the candidate headline files;
* GitHub search hits for each of the 7 suspicious file/module names;
* inspection of the import lists of intermediate files where relevant.

## What is the headline theorem?

There is no obvious `main_theorem` name in the searched code.  The paper-level headline Prop is:

```lean
Theorem_1_1 intervalDomain p
```

The named closers are branch-specific.

### χ₀ = 0 unconditional closer

File:

```text
ShenWork/Paper2/IntervalDomainTheorem11ChiZeroUnconditional.lean
```

Headline theorem:

```lean
theorem intervalDomain_theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
```

This is explicitly documented as “Paper 2 Theorem 1.1 on the interval domain, unconditionally for χ₀ = 0.”

Direct imports:

```lean
import ShenWork.Paper2.IntervalDomainChiZeroUnconditionalLocalExistence
import ShenWork.Paper2.IntervalDomainThm11Assembly
```

### χ₀ < 0 conditional / frontier closer

File:

```text
ShenWork/Wiener/EWA/SourceChiNegTheorem11.lean
```

Headline theorem:

```lean
theorem chiNeg_theorem_1_1 (p : CM2Params) (hchi : p.χ₀ < 0)
    (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hU : ChiNegDatumUniformConstruction p) :
    Theorem_1_1 intervalDomain p :=
```

This file states that it reduces the χ₀<0 headline to one named analytic obligation:

```lean
ChiNegDatumUniformConstruction p
```

Direct imports:

```lean
import ShenWork.Wiener.EWA.SourceReducedCore
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual
```

### Older / residual χ₀ < 0 closer

File:

```text
ShenWork/Paper2/IntervalDomainThm11ChiNegResidual.lean
```

Theorem:

```lean
theorem theorem_1_1_intervalDomain_chiNeg_of_coupledFluxClassicalLocalExistenceResidual
    (p : CM2Params) (hchi_neg : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (_halpha : 1 ≤ p.α) (hgamma : 1 ≤ p.γ)
    (hExist : CoupledFluxClassicalLocalExistenceResidual p) :
    Theorem_1_1 intervalDomain p :=
```

This is also a conditional closer; the open input is the classical local-existence residual.

Direct imports:

```lean
import ShenWork.Paper2.IntervalDomainRestartLocalWiring
import ShenWork.Paper2.IntervalLemma31Closure
import ShenWork.PDE.IntervalLogisticLipschitz
import ShenWork.PDE.IntervalNeumannEllipticResolverR
```

## Which of the 7 files are on the Paper 2 headline theorem import path?

For the two named paper-level headline files above:

```text
ShenWork/Paper2/IntervalDomainTheorem11ChiZeroUnconditional.lean
ShenWork/Wiener/EWA/SourceChiNegTheorem11.lean
```

I found **no evidence that any of the 7 listed files are imported directly by the headline file**.

More importantly, code search shows several of the 7 are not imported by any headline-chain file at all; they are root-build/working-front modules.

### Summary table

| file with sorries | imported by Paper 2 headline closer? | evidence / notes |
|---|---:|---|
| `IntervalLevel0HeatMixedRepr.lean` | No | Search for the module name only found `ShenWork.lean`, i.e. root build closure, not headline. |
| `IntervalConjugateLevel0BFormSourceOn.lean` | No direct paper-headline import | Imported by `IntervalConjugateBFormSourceTower.lean`; the tower itself is not imported by the headline closers. |
| `IntervalHeatSemigroupHighRegularity.lean` | No direct paper-headline import | Imported by old/direct working-front files (`IntervalLevel0HeatMixedRepr`, `IntervalHeatResolverDirectJointC2`, `IntervalHeatResolverJointC2`, `IntervalConjugateLevel0BFormSourceOn`), not by the named headline files. |
| `IntervalConjugateBFormSourceTower.lean` | No | Search hit only itself + docs; no headline-chain importer found. |
| `IntervalResolverLevel0SpectralC2Coeff.lean` | No | Search hit only `ShenWork.lean` for module import; it is a root-closure / working-front module. |
| `IntervalHeatResolverDirectJointC2.lean` | No | Search hit only itself for the module name; not imported by the paper headline closers. |
| `IntervalPhysicalSourceTimeC2Concrete.lean` | Not by paper headline closer; yes by FAC subheadline/working-front files | Imported by `IntervalFlooredSourceTimeDataIterate`, `IntervalHeatResolverJointC2`, `IntervalResolverLevel0SpectralC2Coeff`, `IntervalHeatSemigroupHighRegularity`, `IntervalHeatSemigroupFlooredSourceTimeData`, `IntervalChemDivWinDischarge`, and root `ShenWork.lean`. |

## Why the 39 sorry files are probably not on the current paper-headline critical path

The current χ₀<0 headline file `SourceChiNegTheorem11.lean` does **not** attempt to discharge the FAC source-regularity chain directly.  Instead, it packages the whole analytic frontier as:

```lean
def ChiNegDatumUniformConstruction (p : CM2Params) : Prop := ...
```

and proves:

```lean
theorem chiNeg_theorem_1_1 ...
    (hU : ChiNegDatumUniformConstruction p) :
    Theorem_1_1 intervalDomain p := ...
```

So the paper-level theorem is conditional on a single packaged construction.  The FAC/source-regularity files are not imported as the proof of that construction; the construction is an assumed Prop.

Similarly, `IntervalDomainThm11ChiNegResidual.lean` proves a conditional theorem from:

```lean
CoupledFluxClassicalLocalExistenceResidual p
```

It does not import the 7 FAC/direct-route files either.

## What is the FAC subheadline?

If by “headline FAC theorem” you mean the chem-div/FAC source regularity subpipeline, the relevant file is not the paper-level theorem file.  It is closer to:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

Important objects there:

```lean
structure ChemDivSolutionRegularityResidual
```

```lean
theorem fluxJointC2Hyp_of_residual
```

```lean
noncomputable def coupledChemDivSource_duhamelSourceTimeC1_of_residual
```

```lean
noncomputable def coupledChemDivSource_timeC1On_window_of_gradientSolution
```

This file is a FAC/source-time-C¹ discharge from an explicit residual bundle.  It imports:

```lean
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.PDE.IntervalChemDivTimeDerivative
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On
import ShenWork.Paper2.IntervalMildPicard
```

Through `IntervalFlooredSourceTimeDataIterate`, it reaches:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

So for this **FAC subheadline**, among the 7 listed files, the clearly imported/critical file is:

```text
IntervalPhysicalSourceTimeC2Concrete.lean
```

The other 6 listed files are not imported by `IntervalChemDivWinDischarge.lean` according to the searched module references.

## Critical-path verdict by target

### Target A: actual Paper 2 headline theorem (`Theorem_1_1 intervalDomain p`)

The named theorem files are:

```text
IntervalDomainTheorem11ChiZeroUnconditional.lean
SourceChiNegTheorem11.lean
IntervalDomainThm11ChiNegResidual.lean
```

For these theorem files, the 7 listed 39-sorry files are **not on the active import path**.  They are working-front/root-closure files, not required by the current conditional headline closers.

### Target B: FAC/source-time-C¹ discharge subheadline

The relevant file is:

```text
IntervalChemDivWinDischarge.lean
```

Among the 7 listed files, the only one clearly on this FAC subheadline path is:

```text
IntervalPhysicalSourceTimeC2Concrete.lean
```

This is because `ChemDivSolutionRegularityResidual.hval/hgrad` explicitly uses:

```lean
IntervalPhysicalSourceTimeC2Concrete.builtEs
```

and `fluxJointC2Hyp_of_residual` calls:

```lean
IntervalFlooredSourceTimeDataIterate.coupledChemDivFluxFactorJointC2Inputs_of_iterate
```

which goes through the physical source/resolver route.

### Target C: old/direct heat-Level0 resolver route

If the target is specifically the old/direct Level0 resolver C² route, then these files are relevant:

```text
IntervalHeatSemigroupHighRegularity.lean
IntervalHeatResolverDirectJointC2.lean
IntervalHeatResolverJointC2.lean
IntervalResolverLevel0SpectralC2Coeff.lean
IntervalLevel0HeatMixedRepr.lean
```

But that is **not** the current paper headline theorem.  It is a working-front / alternate resolver-C² route.

## Recommended action

Do not measure criticality from `ShenWork.lean`.  `ShenWork.lean` imports many “working-front modules added to the build closure,” so it makes orphan files look headline-critical when they are not.

For paper-headline triage, use the theorem file import roots:

```text
ShenWork/Paper2/IntervalDomainTheorem11ChiZeroUnconditional.lean
ShenWork/Wiener/EWA/SourceChiNegTheorem11.lean
ShenWork/Paper2/IntervalDomainThm11ChiNegResidual.lean
```

Under that criterion, the 39 sorries in the 7 listed files are **not on the current paper-headline critical path**.

For FAC-subheadline triage, use:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

Under that criterion, the critical file among the 7 is:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

The remaining six are on old/direct/Level0 working fronts unless a separate theorem file imports them explicitly.

## Final answer

The top-level theorem the paper claims is not named `main_theorem`; in this repo the Paper 2 headline is the Prop-valued conclusion:

```lean
Theorem_1_1 intervalDomain p
```

with named closers:

```lean
intervalDomain_theorem_1_1_chiZero_unconditional
chiNeg_theorem_1_1
```

The 39 sorries across the 7 listed files are **not** on the active import path of those paper-level headline closers.  They are mainly FAC/direct-route working-front files.  If the target is the FAC/source-time-C¹ subheadline rather than the paper theorem, then `IntervalPhysicalSourceTimeC2Concrete.lean` is the one clearly on that subheadline path; the other six are not imported by that FAC discharge file.
