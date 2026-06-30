# Q2347 shen1 — Paper2 actual-atoms Prop25 wiring audit

Repo audited: `xiangyazi24/Shen_work` on `main` around commit `6eccd68f`.

Question: how to wire the actual-atoms/nonnegative-`B` Prop. 2.5 route into the preferred interval-domain `χ₀ = 0` statement route, avoiding import cycles and avoiding the false old GN route.

## Bottom line

Use a **new small Paper2-facing file**, then import it into `IntervalDomainStatementAssembly.lean`.

Recommended new file:

```lean
ShenWork/Paper2/IntervalDomainProp25ActualAtoms.lean
```

It should import only the lower actual-atoms bridge:

```lean
import ShenWork.PDE.P3MoserActualWiring
```

and expose a Paper2 statement-layer structure:

```lean
IntervalDomainPaper2Prop25ActualAtomFrontierData
```

plus a theorem:

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
```

Then `IntervalDomainStatementAssembly.lean` imports this new file and adds conversion wrappers from “actual atom Prop25 data” into the already-existing preferred `χ₀ = 0` local-free positive-solution-slice route.

This is better than putting the actual-atom structure directly in `StatementAssembly`: it isolates the PDE/Moser actual-atom dependency and gives a clean cycle boundary.  It also avoids bloating `StatementAssembly` with low-level atom signatures.

## Why this placement avoids cycles

The existing actual theorem lives in:

```lean
ShenWork/PDE/P3MoserActualWiring.lean
```

with namespace:

```lean
namespace ShenWork.IntervalDomainExistence.P3MoserActualWiring
```

and exact theorem:

```lean
theorem intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    {params : CM2Params}
    (hdiss : ... MoserDissipationDropBeforeNonnegB ...)
    (hrel : ... RelativeMoserInterpolationBefore ...)
    (hEndpoint : ... IntervalDomainMoserQuantitativeEndpoint ...)
    : Proposition_2_5 intervalDomain params
```

`P3MoserActualWiring.lean` imports lower Paper2/PDE modules, not `IntervalDomainStatementAssembly.lean`.  So this direction is safe:

```lean
PDE/P3MoserActualWiring
  -> Paper2/IntervalDomainProp25ActualAtoms
  -> Paper2/IntervalDomainStatementAssembly
```

Do **not** import `IntervalDomainStatementAssembly` from the new file.  That would create the cycle risk.

## New file skeleton

Create:

```lean
import ShenWork.PDE.P3MoserActualWiring

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open ShenWork.IntervalDomainExistence.P3MoserActualWiring

namespace ShenWork.Paper2

noncomputable section

/-- Paper2-facing actual-atom frontier for Proposition 2.5 on `intervalDomain`.

This is the preferred replacement for structured-Moser or theorem-shaped Prop25
frontiers.  It carries the actual atoms consumed by
`intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`: physical/nonnegative-`B`
Moser dissipation, relative Moser interpolation, and the quantitative endpoint
root-tower producer.

It does not assume `Proposition_2_5 intervalDomain p` directly. -/
structure IntervalDomainPaper2Prop25ActualAtomFrontierData
    (p : CM2Params) : Prop where
  moserDissipation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        MoserDissipationDropBeforeNonnegB intervalDomain u T rho p0
  relativeMoserInterpolation :
    ∀ {T rho p0 : ℝ} {u v : ℝ → intervalDomain.Point → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u v →
      CrossDiffusionBootstrapEstimate intervalDomain p T rho u v →
      AbstractLpBootstrapHypothesis intervalDomain u
        (p.N : ℝ) T rho p0 →
        RelativeMoserInterpolationBefore intervalDomain u T rho p0
  quantitativeEndpoint :
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

/-- Actual-atom frontier produces Proposition 2.5. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Proposition_2_5 intervalDomain p :=
  intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
    hData.moserDissipation hData.relativeMoserInterpolation
    hData.quantitativeEndpoint

/-- Instance-facing wrapper. -/
theorem intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierDataFact
    (p : CM2Params)
    [hData : Fact (IntervalDomainPaper2Prop25ActualAtomFrontierData p)] :
    Proposition_2_5 intervalDomain p :=
  intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData p hData.out

#print axioms intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData

end
end ShenWork.Paper2
```

Notes:

* The `open ShenWork.IntervalDomainExistence.P3MoserDissipationShape` line exposes `MoserDissipationDropBeforeNonnegB`.
* The `open ShenWork.IntervalDomainExistence.P3MoserActualWiring` line exposes `intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB`.
* Qualifying the theorem instead of opening is also fine:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

## StatementAssembly import

In `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, add:

```lean
import ShenWork.Paper2.IntervalDomainProp25ActualAtoms
```

Place it with the other Paper2 imports near the top.  This should be cycle-free because the new file imports only lower PDE/Paper2 actual-atom dependencies and does not import `StatementAssembly`.

## Minimal preferred χ₀=0 conversion layer

The existing preferred local-free positive-solution-slice Theorem 1.2/1.3 data has a direct field:

```lean
prop25 : Proposition_2_5 intervalDomain p
```

The actual-atom variant should replace only that field.

Add in `IntervalDomainStatementAssembly.lean`:

```lean
/-- Actual-atom variant of the preferred `χ₀ = 0` local-free Theorem 1.2/1.3
frontier.  This replaces the direct `Proposition_2_5` field by the lower
actual-atom producer. -/
structure
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  common :
    IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
  prop25Actual : IntervalDomainPaper2Prop25ActualAtomFrontierData p
  globalExtension : IntervalDomainPaper2GlobalExtensionFrontier p
  slowBootstrap :
    1 ≤ p.β → p.m < 1 →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalBootstrap :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  criticalEventualSupBound :
    1 ≤ p.β → p.m = 1 → p.χ₀ < chiBeta p →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
  strongBootstrap :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ T > 0, ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2ClassicalSolution intervalDomain p T u v →
      InitialTrace intervalDomain u₀ u →
        IntervalDomainPaper2BootstrapOutput p T u v
  strongEventualSupBound :
    0 < p.a → 0 < p.b → StrongLogisticCondition p C →
    1 ≤ p.m →
    ∀ u₀ : intervalDomain.Point → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ u v : ℝ → intervalDomain.Point → ℝ,
      IsPaper2GlobalClassicalSolution intervalDomain p u v →
      InitialTrace intervalDomain u₀ u →
      (∀ T > 0, IntervalDomainPaper2BootstrapOutput p T u v) →
        ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Convert actual-atom local-free data to the existing preferred local-free data. -/
def
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData.toLocalFree
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad where
  common := h.common
  prop25 := intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
    p h.prop25Actual
  globalExtension := h.globalExtension
  slowBootstrap := h.slowBootstrap
  criticalBootstrap := h.criticalBootstrap
  criticalEventualSupBound := h.criticalEventualSupBound
  strongBootstrap := h.strongBootstrap
  strongEventualSupBound := h.strongEventualSupBound
```

Then add the nested main/local/full-statement wrappers only as thin conversions, not copied proofs.

```lean
structure
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
      p C cGrad

def
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData.toLocalFree
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad where
  theorem12And13 := h.theorem12And13.toLocalFree

structure
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  proposition11 : IntervalDomainPaper2Proposition11ChiZeroFrontierData p
  main :
    IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
      p C cGrad

def
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData.toLocalFree
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
      p C cGrad where
  proposition11 := h.proposition11
  main := h.main.toLocalFree

structure
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeActualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p
  localAndMain :
    IntervalDomainPaper2LocalAndMainChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData
      p C cGrad

def
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeActualAtomFrontierData.toLocalFree
    {p : CM2Params} {C : Paper2Constants p}
    {cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ}
    (h :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeActualAtomFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
      p C cGrad where
  section2 := h.section2
  localAndMain := h.localAndMain.toLocalFree
```

Then expose the actual preferred statement wrapper:

```lean
abbrev IntervalDomainPaper2PreferredChiZeroActualAtomStatementFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeActualAtomFrontierData
    p C cGrad

theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData : IntervalDomainPaper2PreferredChiZeroActualAtomStatementFrontierData
      p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.toLocalFree
```

Add an instance-facing wrapper if this repo pattern wants it:

```lean
theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2PreferredChiZeroActualAtomStatementFrontierData
        p C cGrad)] :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData
    p C cGrad hχ0 ha hb hα hγ hData.out
```

## Minimality and no-smuggling check

This is a real reduction if `prop25Actual` is the only replacement for `prop25`.  The new package should **not** contain any of these as fields:

```lean
Proposition_2_5 intervalDomain p
IntervalDomainPaper2Corollary21FrontierData p
IntervalDomainLemma41.IntervalDomainInterpolation
Paper2BootstrapEstimateBranchData intervalDomain p
Prop25MoserFrontiers ...
```

It should contain exactly the three actual atom families consumed by:

```lean
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

namely:

```lean
MoserDissipationDropBeforeNonnegB
RelativeMoserInterpolationBefore
IntervalDomainMoserQuantitativeEndpoint
```

This means the old direct `Proposition_2_5` field is removed from the preferred statement route and reconstructed by an existing theorem.

## Why not the structured-Moser Prop25 frontier?

The current structured-Moser file has:

```lean
structure Prop25MoserFrontiers ...
theorem Proposition_2_5_intervalDomain_of_prop25_moser_frontiers
```

That route is useful but not the strongest repair.  It still packages a per-solution `Prop25MoserFrontiers` object and uses the older `MoserDissipationDropBefore` / structured bootstrap shape.  The actual-atoms route goes lower and aligns with the repaired physical-`B` predicate:

```lean
MoserDissipationDropBeforeNonnegB
```

and the exact theorem:

```lean
intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

So the preferred chi-zero statement route should use the actual atom data, not the structured-Moser data, if the goal is net frontier reduction.

## Warning: nonnegative-B is still an honest atom

Do not claim `MoserDissipationDropBeforeNonnegB` is automatic.  The repo explicitly contains:

```lean
theorem unitLinearDrop_not_MoserDissipationDropBeforeNonnegB
```

in `ShenWork/PDE/P3MoserDissipationShape.lean`.  That is a false-premise detector for deriving the drop from arbitrary abstract data.  The actual-atom route is valid because it **carries** the physical nonnegative-`B` dissipation atom; it does not prove it for free.

## Warning: avoid the old false GN route

Do not add an import or field that reintroduces:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
```

The global interpolation premise is known false as literally stated via:

```lean
IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation
```

Avoid old wrappers such as:

```lean
intervalDomainPaper2_Lemma_4_1_of_GN_frontier
intervalDomainPaper2_aprioriTargets_of_GN_frontier
IntervalDomainPaper2InterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13InterpolationFrontierData
```

The preferred route should continue using:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
```

## Axiom checks to add

In the new file:

```lean
#print axioms intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
```

In `IntervalDomainStatementAssembly.lean`, after the new wrappers:

```lean
#print axioms intervalDomainPaper2_preferredChiZeroStatementTargets_of_actualAtomFrontierData
```

Also audit the base theorem already present in lower files:

```lean
#print axioms intervalDomain_endpointBoundFromLp_of_actual_atoms_nonnegB
```

Expected output should be the usual classical/propext/quotient axioms only, matching the rest of the repo’s statement-layer wrappers.  If the wrapper’s axiom print includes an unexpected imported axiom or an untrusted constant, stop and inspect the dependency.

## Final recommendation

Add `ShenWork/Paper2/IntervalDomainProp25ActualAtoms.lean`, import it in `IntervalDomainStatementAssembly.lean`, and add a local-free preferred chi-zero **actual-atom statement frontier** as shown above.  This is the cleanest minimal wiring: no cycles, no direct Prop25 smuggling, no false global GN interpolation premise, and a strictly lower Prop25 residual than the structured-Moser interface.
