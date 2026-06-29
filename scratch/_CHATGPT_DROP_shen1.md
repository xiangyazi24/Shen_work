# PAPER1-POSITIVE-BRANCH-AUDIT-REQUEST

Audited current `main` around `e3aa461e` or newer, focusing only on Paper1 statement assembly and the positive-critical frozen-stationary branch.

## 1. Where the positive branch actually sits

The positive construction branch is needed for **Paper1 Theorem 1.1**, and therefore for the full three-target package

```lean
Paper1MainStatementTargets := Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3
```

It is **not** an input to the current B5 route for **Theorem 1.2 / Theorem 1.3**.  Those are assembled separately by

```lean
paper1_mainlineStatementTargets_of_mainlineExistence
  : Paper1MainlineExistence cStarStarFn → Paper1MainlineStatementTargets
```

with

```lean
Paper1MainlineStatementTargets := Theorem_1_2 ∧ Theorem_1_3
```

So the positive frozen-stationary branch affects the full Paper1 main statement through Theorem 1.1, while Theorem 1.2/1.3 remain conditional on the B5 package `Paper1MainlineExistence`.

## 2. Exact branch now named in the repo

The newly named branch is:

```lean
Paper1PositiveCriticalFrozenStationaryBranch
```

It is definitionally the old `hpos` input to

```lean
paper1_Theorem_1_1_of_constructionNegSMPProvider
```

and to the positive half of

```lean
Theorem_1_1.of_assumed_frozenStationaryProfile_branches
```

Its shape is:

```lean
∀ p : CMParams, p.α = p.m + p.γ - 1 →
  0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
  ∀ c : ℝ, 2 < c →
    ∃ U : ℝ → ℝ,
      FrozenStationaryWaveProfile p c U ∧
        ShenUpperBoundPositive p c U ∧
        ∀ κ₁, kappa c < κ₁ →
          κ₁ < min ((1 + p.α) * kappa c)
            (min (p.m * kappa c + 1 / 2) 1) →
          HasWaveRightTailAsymptotic c κ₁ U
```

Classification: **genuine analytic residual / theorem-branch-shaped frontier**.

It is not an empty declaration and it does not literally contain `Theorem_1_1`; however it is essentially the positive half of Theorem 1.1 at the frozen-stationary-profile level.  It should not be treated as produced unless a theorem constructs it.

## 3. New `Paper1MainStatementSMPMainlineData` route

The new bundle is:

```lean
structure Paper1MainStatementSMPMainlineData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveCritical : Paper1PositiveCriticalFrozenStationaryBranch
  mainline : Paper1MainlineExistence cStarStarFn
```

The wrapper is:

```lean
paper1_mainStatementTargets_of_smpMainlineData
  : Paper1MainStatementSMPMainlineData cStarStarFn →
      Paper1MainStatementTargets
```

Classification: **pure wiring from explicit conditional packages**.

The route is semantically honest: the fields are named residual packages, and the doc comment says it does not construct `ConstructionNegSMPProvider`, the positive branch, or `Paper1MainlineExistence`.  It is a cleaner bundle than the old monolithic `Paper1MainResultsData`, but it is not an unconditional headline theorem.

## 4. Can the positive branch be wired from existing construction theorems?

Only partially.

Existing positive construction wrappers can produce a lower-pinned frozen stationary profile under substantial route data, for example:

```lean
b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData
b1_chiPos_existence_paper_min_noBar_of_cubeApproxData
b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData
```

The endpoint shape of these wrappers is of the form:

```lean
∃ U,
  InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
    FrozenStationaryWaveProfile p c U
```

This is meaningful progress, but it is **not** the exact `Paper1PositiveCriticalFrozenStationaryBranch`, because the exact branch additionally requires:

```lean
ShenUpperBoundPositive p c U
```

and

```lean
∀ κ₁, kappa c < κ₁ →
  κ₁ < min ((1 + p.α) * kappa c)
    (min (p.m * kappa c + 1 / 2) 1) →
  HasWaveRightTailAsymptotic c κ₁ U
```

I found no existing theorem that supplies those two fields for the `U` produced by the positive Rothe/Schauder route.

## 5. Input-by-input classification

### Already produced unconditionally in Lean

- `Theorem_1_1.of_assumed_frozenStationaryProfile_branches`: the bridge from branch data to `Theorem_1_1` is proved.
- `paper1_Theorem_1_1_of_constructionNegSMPProvider`: the bridge using the weakened negative provider plus the positive branch is proved.
- `paper1_mainlineStatementTargets_of_mainlineExistence`: the bridge from `Paper1MainlineExistence` to `Theorem_1_2 ∧ Theorem_1_3` is proved.
- `paper1_mainStatementTargets_of_smpMainlineData`: the new bundle-to-main-target wrapper is proved.
- `whole_line_super_barrier_pos`: used inside `rotheFloorResidual_of_trap_pos` to discharge the positive super-barrier part of the floor residual.
- Structural facts such as `PositivePaperLemma42ExactConditions.upperBarrier_barLip`, `positivePaperLowerRawParabolicFloorRouteACore_of_noBar`, and trap-derived boundedness/right endpoint facts are already wired where used.
- `logisticProfile_shenUpperBoundPositive` is proved, but only for the explicit logistic profile `logisticProfile (kappa c)`; it is not a producer for the Rothe fixed point.

### Pure wiring from existing produced facts

- `Paper1PositiveCriticalFrozenStationaryBranch`: as a `def`, it is only a name for the existing `hpos` proposition.  Naming it is pure interface factoring, not production.
- `Paper1MainStatementSMPMainlineData`: pure bundling of three conditional inputs.
- `paper1_mainStatementTargets_of_smpMainlineData`: combines `paper1_Theorem_1_1_of_constructionNegSMPProvider` with `paper1_mainlineStatementTargets_of_mainlineExistence`.
- `rotheFloorResidual_of_trap_pos`: swaps in the positive super-barrier and carries the deep Green core; it is not itself a full branch producer.
- `positivePaperLowerRawParabolicFloorRouteACore_of_noBar` and `paperLowerRawStepProducerRouteACore_of_paramCore`: field-for-field adapters between thinner packages and older route packages.

### Conditional but plausibly wireable from existing packages

- `b1_chiPos_existence`: reuses the sign-agnostic `b1_chiNeg_existence_unconditional` once the positive route supplies `hcoreAll`, step/tail dependence, Schauder, Green identity, positivity, boundedness, and endpoint limits.
- `b1_chiPos_existence_rootPin`, `b1_chiPos_existence_stationary_floor_rootPin`, and `b1_chiPos_existence_profileClean_stationary_floor_rootPin`: reduce strict positivity/left endpoint profile obligations using floor, stationary flatness, and strong maximum principle inputs.
- `b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData`: fills the upper-barrier Lipschitz scalar from `PositivePaperLemma42ExactConditions` but still needs the producer/step/tail/stationarity/SMP/flatness route inputs.
- `b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData`: produces the lower-pinned frozen profile from `PaperLowerRawParabolicFloorCoreNoBar`, stationary-flat floor data, and SMP.
- `b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData`: replaces the all-`u` producer by the Route-A floor package.
- `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData`: thins Route-A further to source-box parameter packages.  This is the best inspected positive-profile producer route, but it still produces only profile + lower-pinned trap, not the full `positiveCritical` branch.

### Genuine analytic residuals / theorem-branch-shaped frontiers

- `Paper1PositiveCriticalFrozenStationaryBranch`: the exact positive half-branch remains a residual.
- `ShenUpperBoundPositive p c U` for the `U` produced by the positive Rothe route: no existing bridge found from lower-pinned trap + frozen stationarity to this strict upper bound.  The explicit logistic-profile theorem does not apply to the constructed fixed point.
- `HasWaveRightTailAsymptotic c κ₁ U` for the produced `U`: no existing producer found from the positive lower-pinned frozen stationary profile.  This is the sharp right-tail linearization/asymptotic residual.
- `PaperLowerRawParabolicFloorRouteAParamCoreNoBar`: still carries per-step source-box parameter/witness/rest/zsuper/lower-raw auxiliary data.
- `PaperLowerPinnedStationaryFlatFloor`: still carries fixed-point stationarity/flatness-style information for the lower-pinned route.
- `StationaryStrongMaxPrinciple` / `StationaryStrongMaxPrincipleODERealization`: still analytic residuals; `hsmp_of_odeRealization` is wiring, but the realization/SMP input itself is not produced unconditionally.
- `Paper1MainlineExistence`: genuine B5 residual package for Theorems 1.2/1.3.  It is unrelated to closing the positive Theorem 1.1 construction branch.

## 6. Final judgement

The positive construction branch cannot currently be fully wired into `Paper1PositiveCriticalFrozenStationaryBranch` from existing theorems.  The repo has a strong conditional producer for a lower-pinned `FrozenStationaryWaveProfile`, but the strict positive upper bound and sharp right-tail asymptotic remain outside that producer.

The new `Paper1PositiveCriticalFrozenStationaryBranch` / `Paper1MainStatementSMPMainlineData` route is semantically honest as a **named conditional interface**.  It does not hide a proof of the target theorem, because it explicitly carries `positiveCritical` and `mainline` as fields and the wrapper is pure wiring.  The caveat is that `Paper1PositiveCriticalFrozenStationaryBranch` is branch-shaped: it should be read as a remaining frontier, not as a discharged construction theorem.
