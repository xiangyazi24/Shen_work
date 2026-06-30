# Q2357 shen1 — Paper2 next headline-frontier reduction audit

Repo: `xiangyazi24/Shen_work`

Audited target: `main` at commit `69e2c9cca92966652a1e89938191160a15d17611` (`Add Paper2 actual-atom Prop25 frontiers`).

Scope: route-selection audit for the next best Paper2 headline-frontier reduction after the new actual-atom Proposition 2.5 wrappers in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`.

## Verdict

The next highest-leverage reduction that is already mostly wireable is **not** `globalExtension`, the slow/critical/strong bootstrap fields, or the eventual sup-bound fields. It is to remove

```lean
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
```

from the **χ₀ = 0 main-theorem route for Theorems 1.1--1.3**, by using the same actual Moser atoms to produce both:

```lean
Corollary_2_1 intervalDomain p
Proposition_2_5 intervalDomain p
```

The key existing theorem is already available:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
```

It consumes exactly the first two fields of the current actual-atom frontier:

```lean
hData.moserDissipation
hData.relativeMoserInterpolation
```

and produces `Corollary_2_1 intervalDomain p`. The already-added wrapper

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
```

then produces `Proposition_2_5 intervalDomain p` from the same `IntervalDomainPaper2Prop25ActualAtomFrontierData p`.

So the next headline step should be a **common-free actual-atom main theorem wrapper**: no `cGrad`, no `common`, no `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData`. It should directly call the existing Theorem 1.2/1.3 structural assemblers:

```lean
IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_parameter_fields_and_eventual_sup_bound
IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
```

This is a main-theorem-only reduction. It should not be advertised as a full `IntervalDomainPaper2StatementTargets` reduction, because the full statement target still includes `IntervalDomainPaper2AprioriTargets`, hence still needs the sound Lemma 4.1 route. Actual Moser atoms produce `Corollary_2_1`/`Proposition_2_5`; they do **not** produce the positive solution-slice interpolation statement used for Lemma 4.1.

## Exact proposed names

I would add the following names, in this order:

```lean
intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomFrontierData

IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData

IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData

IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
```

The `Cor21` marker is intentional: it distinguishes this route from the current actual-atom wrapper, which only replaces the nested `Proposition_2_5` field but still carries the positive solution interpolation/energy `common` package.

## Minimal Lean skeleton

If this is added directly inside `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, no new import is required: that file already imports `ShenWork.PDE.P3MoserActualWiring`, `IntervalDomainTheorem12`, and `IntervalDomainTheorem13`.

For an isolated check file, the minimal import is:

```lean
import ShenWork.Paper2.IntervalDomainStatementAssembly

open ShenWork.IntervalDomain

namespace ShenWork.Paper2

noncomputable section

/-- Corollary 2.1 from the actual Moser atoms carried by the Proposition 2.5
actual-atom frontier.  This is the bridge that makes the main-theorem route
independent of `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData`. -/
theorem intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Corollary_2_1 intervalDomain p :=
  ShenWork.IntervalDomainExistence.P3MoserActualWiring.intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
    (params := p)
    hData.moserDissipation
    hData.relativeMoserInterpolation

/-- The two Tier-1 inputs needed by the direct Theorem 1.2/1.3 structural route,
assembled from one actual-atom frontier. -/
theorem intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomFrontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper2Prop25ActualAtomFrontierData p) :
    Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
  ⟨intervalDomainPaper2_Corollary_2_1_of_actualAtomFrontierData p hData,
    intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData p hData⟩

/-- Common-free actual-atom frontier for interval-domain Theorems 1.2 and 1.3 in
the proved `χ₀ = 0` local-free route.

Compared with
`IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeActualAtomFrontierData`,
this removes the `common : IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad`
field and removes the `cGrad` parameter entirely.  `Corollary_2_1` and
`Proposition_2_5` are both produced from `prop25Actual`. -/
structure IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
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

/-- Assemble Theorems 1.2 and 1.3 from the common-free actual-atom route. -/
theorem intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
        p C) :
    Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C := by
  have hTier :
      Corollary_2_1 intervalDomain p ∧ Proposition_2_5 intervalDomain p :=
    intervalDomainPaper2_Corollary_2_1_and_Proposition_2_5_of_actualAtomFrontierData
      p hData.prop25Actual
  let hlocal : IntervalDomainPaper2LocalExistenceFrontier p :=
    fun u₀ hu₀ =>
      intervalDomain_localExistence_chiZero_unconditional
        p hχ0 ha hb hα hγ hu₀
  exact
    ⟨IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_parameter_fields_and_eventual_sup_bound
        p hTier.1 hTier.2 hlocal hData.globalExtension
        hData.slowBootstrap hData.criticalBootstrap
        hData.criticalEventualSupBound,
      IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_parameter_m_pos_and_eventual_sup_bound
        p C hTier.1 hTier.2 hlocal hData.globalExtension
        hData.strongBootstrap hData.strongEventualSupBound⟩

/-- Common-free actual-atom frontier for interval-domain Paper2 Theorems 1.1--1.3
in the proved `χ₀ = 0` route. -/
structure IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  theorem12And13 :
    IntervalDomainPaper2Theorem12And13ChiZeroActualAtomCor21LocalFreeFrontierData
      p C

/-- Assemble interval-domain Paper2 Theorems 1.1--1.3 from the common-free
actual-atom Theorem 1.2/1.3 route. -/
theorem intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  ⟨intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
      p hχ0 ha hb hα hγ,
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroActualAtomCor21LocalFreeFrontierData
      p C hχ0 ha hb hα hγ hData.theorem12And13⟩

/-- Preferred grep-visible alias for the common-free actual-atom χ₀ = 0
main-theorem frontier. -/
abbrev IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  IntervalDomainPaper2MainTheoremChiZeroActualAtomCor21LocalFreeFrontierData
    p C

/-- Preferred wrapper for the common-free actual-atom χ₀ = 0 main-theorem route. -/
theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
        p C) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroActualAtomCor21LocalFreeFrontierData
    p C hχ0 ha hb hα hγ hData

/-- Instance-facing preferred wrapper for the common-free actual-atom χ₀ = 0
main-theorem route. -/
theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData :
      Fact
        (IntervalDomainPaper2PreferredChiZeroMainTheoremActualAtomCor21FrontierData
          p C)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_actualAtomCor21FrontierData
    p C hχ0 ha hb hα hγ hData.out

end

end ShenWork.Paper2
```

## Why this is the best next reduction

### 1. It is mostly pure wiring

The existing current actual-atom main route still carries:

```lean
common : IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData p cGrad
prop25Actual : IntervalDomainPaper2Prop25ActualAtomFrontierData p
```

The `common` package is only used in the existing main-theorem path to manufacture `Corollary_2_1`. But the actual atoms already manufacture `Corollary_2_1` through:

```lean
intervalDomain_allLpBoundFromBootstrap_of_actual_atoms_nonnegB
```

and they manufacture `Proposition_2_5` through:

```lean
intervalDomainPaper2_Proposition_2_5_of_actualAtomFrontierData
```

Therefore the `common` package and the `cGrad` parameter can be bypassed for Theorems 1.1--1.3.

### 2. It does not smuggle in the false global interpolation route

This route does not mention:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
```

and does not mention:

```lean
OldUnitIntervalPowerGNYoungForMoser
```

It also does not try to prove `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData`; it simply stops using that package for the main theorem bundle.

### 3. It respects the theorem/statement distinction

The proposed wrapper is safe for:

```lean
IntervalDomainPaper2MainTheoremTargets p C
```

It is not, by itself, a replacement for:

```lean
IntervalDomainPaper2StatementTargets p C
```

because the statement target includes:

```lean
IntervalDomainPaper2AprioriTargets p
```

and the sound current route for `Lemma_4_1 intervalDomain p` is still the positive solution-slice interpolation route:

```lean
intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
```

Actual Moser atoms do not prove that Lemma 4.1 frontier.

## Cycle/import audit

Recommended placement: add the bridge and wrappers in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, after `IntervalDomainPaper2Prop25ActualAtomFrontierData` and before or near the current preferred main-theorem aliases.

No new import is needed there. The file already has the necessary imports:

```lean
import ShenWork.Paper2.IntervalDomainTheorem12
import ShenWork.Paper2.IntervalDomainTheorem13
import ShenWork.PDE.P3MoserActualWiring
```

No namespace opening is required if the P3 theorem is fully qualified as in the skeleton. Keeping it fully qualified is preferable because the actual theorem lives in:

```lean
ShenWork.IntervalDomainExistence.P3MoserActualWiring
```

while the nonnegative-`B` predicate in the existing actual-atom structure lives in:

```lean
ShenWork.IntervalDomainExistence.P3MoserDissipationShape
```

Do not move this wrapper down into `ShenWork/PDE/P3MoserActualWiring.lean`: that would create the wrong dependency direction, because `P3MoserActualWiring` should not import the Paper2 statement assembly just to see `IntervalDomainPaper2Prop25ActualAtomFrontierData`.

If you create a new file instead, make it import `ShenWork.Paper2.IntervalDomainStatementAssembly`, but do **not** import that new file back into `IntervalDomainStatementAssembly.lean`. Otherwise the cycle is immediate.

## No-go routes

1. **Do not use `IntervalDomainLemma41.IntervalDomainInterpolation`.** It is a legacy/global interpolation interface and is already documented in the assembly file as refuted by `IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.

2. **Do not use `OldUnitIntervalPowerGNYoungForMoser`.** That route is separately refuted by `IntervalDomainGNYObstruction.not_oldUnitIntervalPowerGNYoungForMoser`.

3. **Do not try to fill `IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData` from actual atoms.** Actual atoms provide a Moser route to `Corollary_2_1` and `Proposition_2_5`; they do not provide the positive solution-slice interpolation field, the chain-rule gradient comparison, the mass-control field, or the energy-from-cross-diffusion field in the shape of that structure. The correct move is to bypass `common` for main theorems.

4. **Do not claim the common-free actual-atom route proves the full statement bundle.** It proves the main theorem bundle only, unless a separate sound Lemma 4.1/positive-solution-slice route is still supplied for the a priori target.

## What is not currently wireable

After the common-free actual-atom reduction, the remaining fields are honest PDE/Cauchy frontiers in the current repo shape:

```lean
IntervalDomainPaper2GlobalExtensionFrontier p
slowBootstrap
criticalBootstrap
criticalEventualSupBound
strongBootstrap
strongEventualSupBound
```

I do not see an existing proved wrapper that closes any of these from the current imported code. In particular:

* `globalExtension` is the Cauchy continuation criterion: bounded finite-horizon classical solutions extend globally. It is consumed by Theorem 1.2/1.3 assemblers; it is not produced by Corollary 2.1 or Proposition 2.5.
* the branch bootstrap fields produce the initial cross-diffusion bootstrap seed plus an initial `LpPowerBoundedBefore`; they are upstream of Corollary 2.1/Proposition 2.5 and cannot be derived from those outputs without circularity.
* the eventual sup-bound fields are long-time/global boundedness inputs. The existing theorem code converts eventual sup bounds into `IsPaper2Bounded`, but it does not prove the eventual bounds.

If forced to name the next honest atom after the common-free actual-atom wrapper, I would name `IntervalDomainPaper2GlobalExtensionFrontier p` as the clean Cauchy-theory atom, and keep the slow/critical/strong bootstrap and eventual sup-bound fields as separate regime-specific PDE-estimate atoms. None of those should be represented as already-wireable from the current proved code.

## Bottom line

Implement the common-free actual-atom main-theorem wrapper next. It removes the largest remaining non-PDE-analysis package from the χ₀ = 0 headline main theorem route, drops `cGrad` from that route entirely, reuses existing proved code, and avoids both refuted interpolation paths.
