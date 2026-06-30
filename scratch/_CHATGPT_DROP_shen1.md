# Q2640 shen1 — audit of LowerUpper Moser headline Stability24 thinning

Repo: `xiangyazi24/Shen_work`

Target file: `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`

## Verdict

The planned thinning is sound.  The cleanest implementation is a **generic-`K` stability-only variant** for the LowerUpper Moser route:

```text
core        unchanged
compactness unchanged, generic K
stability   replaced by stability24, expanded with .toStability23To25 ha hχ0
```

Do **not** force the sup-norm compactness package in this pass.  The route you are targeting already carries:

```lean
compactness :
  IntervalDomainPaper3ConcreteCompactnessRegularizationData
    p M0 uBar vLower K
```

so the new structure should also keep:

```lean
(K : CompactnessData intervalDomain)
```

generic.  A sup-norm-`K` variant would be a separate compactness thinning and would unnecessarily combine two independent reductions.

## Main pitfalls

### 1. Name length

The names are long but consistent with the existing file.  `set_option linter.style.longLine false` is already present near the top, so long declaration names are acceptable.

Recommended names:

```lean
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData.toCurrent
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainDataFact
```

They are verbose, but mirror the existing route names and avoid ambiguity.

### 2. Field types

For the mainline thin structure, use exactly:

```lean
core :
  IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p
compactness :
  IntervalDomainPaper3ConcreteCompactnessRegularizationData
    p M0 uBar vLower K
stability24 :
  IntervalDomainPaper3Stability24ActualLinearFrontierData p
    (intervalDomainPaper3Constants p M0 uBar vLower)
```

Do not use `IntervalDomainMassLpSmoothingMoserActualLinearSmallLowerUpperResiduals p` for `core`; the existing mainline route uses the sectorial mainline fact package.

### 3. Generic `K` vs sup-norm `K`

Use generic `K`.  The target theorem is:

```lean
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) ...
```

and it consumes generic concrete compactness data.  There is no need to mention:

```lean
intervalDomainSupNormCompactnessData
```

unless you also want to drop `upperEq`/`minimalUpper`/duplicate initial-continuity as in the earlier actual-linear raw-22 thin route.

### 4. Placement

Place the new declarations after the existing LowerUpper P2Main route:

```lean
intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperP2MainDataFact
```

and before the first:

```lean
end

end ShenWork.Paper3
```

Then add `#print axioms` entries in the reopened `namespace ShenWork.Paper3` block, after the existing LowerUpper prints.  Do not put declarations after the first `end`; that block is for printing only.

### 5. Hypotheses

The new mainline and statement theorems should keep all actual-linear-small hypotheses:

```lean
(ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
(hm : p.m = 1) (hβ : 1 ≤ p.β)
(hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
```

Only `ha` and `hχ0` are used directly by the stability24 expansion, but the existing LowerUpper route still needs `hb hm hβ hχ` downstream to produce actual-linear persistence.

### 6. No `0 ≤ p.β` threading needed

`IntervalDomainPaper3Stability24ActualLinearFrontierData.global24` and `.exp24` already expose the `0 ≤ p.β` argument exactly as the full stability frontier does.  The converter:

```lean
h.stability24.toStability23To25 ha hχ0
```

only fills the impossible branches and forwards `global24` / `exp24`; it should not derive or consume `0 ≤ p.β`.

## Concise Lean skeleton

This is intended to be inserted in `IntervalDomainActualLinearStatementAssembly.lean` before the closing `end`, not as a separate file.  The import line below is only for standalone checking in a scratch file; omit it when inserting into the existing file.

```lean
import ShenWork.Paper3.IntervalDomainActualLinearStatementAssembly

set_option linter.style.longLine false

open ShenWork.IntervalDomain
open ShenWork.IntervalDomainExistence
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring
open ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
open ShenWork.Paper2.IntervalDomainEnergyStep
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Lower-average / upper-gap Moser mainline data with the actual-linear-small
stability package reduced to its non-vacuous Theorem 2.4 branches. -/
structure
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain) : Prop where
  core :
    IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p
  compactness :
    IntervalDomainPaper3ConcreteCompactnessRegularizationData
      p M0 uBar vLower K
  stability24 :
    IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)

/-- Convert the Stability24-thinned LowerUpper Moser mainline data to the current
full LowerUpper frontier surface. -/
def
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData.toCurrent
    {p : CM2Params} {M0 uBar vLower : ℝ}
    {K : CompactnessData intervalDomain}
    (h :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
        p M0 uBar vLower K)
    (ha : 0 < p.a) (hχ0 : 0 < p.χ₀) :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperFrontierData
      p M0 uBar vLower K where
  core := h.core
  compactness := h.compactness
  stability := h.stability24.toStability23To25 ha hχ0

/-- Mainline target from LowerUpper Moser frontiers and the Stability24-only
actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
        p M0 uBar vLower K) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperFrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ
    (hData.toCurrent ha hχ0)

/-- Instance-facing mainline target from LowerUpper Moser frontiers and the
Stability24-only actual-linear stability package. -/
theorem
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierDataFact
    (p : CM2Params) (M0 uBar vLower : ℝ)
    (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
        p M0 uBar vLower K)] :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K :=
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
    p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

/-- Full interval-domain Paper3 statement frontiers using LowerUpper Moser
frontiers, Paper2 main theorem targets for Proposition 1.3/1.4, and the
Stability24-only actual-linear stability package. -/
structure
    IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain) : Prop where
  propositions : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C
  mainline :
    IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData
      p M0 uBar vLower K

/-- Assemble the full interval-domain Paper3 statement target from LowerUpper
Moser frontiers, Paper2 main theorem target inputs, and Stability24-only
actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
        p C M0 uBar vLower K) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
      p C hData.propositions,
    intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
      p M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing full interval-domain Paper3 statement target from LowerUpper
Moser frontiers, Paper2 main theorem target inputs, and Stability24-only
actual-linear stability. -/
theorem
    intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ) (K : CompactnessData intervalDomain)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperStability24P2MainData
        p C M0 uBar vLower K)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower K :=
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
    p C M0 uBar vLower K ha hb hχ0 hm hβ hχ hData.out

end

end ShenWork.Paper3
```

## `#print axioms` additions

Add these in the reopened print-only namespace block near the bottom, after the existing LowerUpper prints:

```lean
#print axioms
  IntervalDomainPaper3MainlineMoserActualLinearSmallLowerUpperStability24FrontierData.toCurrent
#print axioms
  intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpperStability24FrontierData
#print axioms
  intervalDomain_paper3_statementTargets_of_moserActualLinearSmallLowerUpperStability24P2MainData
```

You can also print the Fact wrapper if desired, but printing the non-Fact theorem is usually enough.

## Is there a more generic helper?

Yes and no.

The useful generic helper already exists:

```lean
IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25
```

That is the core reduction and should be reused across every actual-linear route.  It avoids duplicating the six vacuous branch proofs.

Beyond that, Lean record types are route-specific.  You could avoid adding a new structure by making only a theorem that takes `core`, `compactness`, and `stability24` as separate arguments:

```lean
theorem intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallLowerUpper_core_compactness_stability24
    ...
    (core : IntervalDomainSectorialMainlineMoserActualLinearSmallLowerUpperFacts p)
    (compactness : IntervalDomainPaper3ConcreteCompactnessRegularizationData p M0 uBar vLower K)
    (stability24 : IntervalDomainPaper3Stability24ActualLinearFrontierData p
      (intervalDomainPaper3Constants p M0 uBar vLower)) :
    IntervalDomainPaper3MainlineTargets p M0 uBar vLower K := ...
```

But since the file already exposes many `...FrontierData` and `...Fact` surfaces, the proposed structure is consistent and useful for instance-facing routes.  The route-specific wrapper is not mathematically new; it is a convenience surface for the preferred headline route.

## Final checklist

* Keep `K` generic.
* Reuse `IntervalDomainPaper3Stability24ActualLinearFrontierData.toStability23To25` exactly.
* New `mainline` field type is the sectorial LowerUpper facts package, not the residual package.
* New `statement` propositions field remains `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C`.
* Keep all actual-linear-small theorem hypotheses; only `ha` and `hχ0` are used by stability thinning, but the old route needs the rest.
* Insert declarations before the first closing `end` of `namespace ShenWork.Paper3`.
* Add `#print axioms` entries in the reopened print block after existing LowerUpper prints.
* No high-excursion producer files are touched or required.
