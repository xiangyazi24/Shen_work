# PAPER1-POSITIVE-BRANCH-AUDIT-REQUEST

Audit target: Paper1 headline statement assembly on current `main` around `e3aa461e` or newer, with focus on the positive-critical/frozen-stationary branch.

## Executive answer

The exact positive branch needed by Paper1 Theorem 1.1 is **not already produced unconditionally** and is **not yet fully wireable** from currently proved facts. The repo has a substantial conditional Rothe/Schauder Route-A chain that can produce a lower-pinned frozen stationary profile in the positive regime, but the exact headline branch still additionally needs `ShenUpperBoundPositive` and the sharp right-tail asymptotic `HasWaveRightTailAsymptotic`. I did not find an existing theorem that supplies those two for the produced fixed point.

Also, this branch is **not an input to the strongest Paper1 Theorem 1.2/1.3 mainline route**. Theorems 1.2 and 1.3 are assembled from `Paper1MainlineExistence` via `paper1_mainlineStatementTargets_of_mainlineExistence`. The positive frozen-stationary branch is a Theorem 1.1 construction input, hence part of the all-main-statement bundle `Paper1MainStatementTargets`, not a prerequisite for the B5 stability/uniqueness mainline itself.

## Where the positive branch enters

The exact branch shape is the `hpos` argument of:

`Theorem_1_1.of_assumed_frozenStationaryProfile_branches`

and of the statement wrapper:

`paper1_Theorem_1_1_of_constructionNegSMPProvider`

It requires:

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

Classification of that whole `hpos`: **genuine analytic residual / not fully wired**.

## Existing positive-branch production chain

The repo does have a positive B1 Rothe/Schauder chain. The strongest inspected wrappers include:

- `rotheFloorResidual_of_trap_pos`
- `b1_chiPos_existence`
- `b1_chiPos_existence_rootPin`
- `b1_chiPos_existence_profileClean_stationary_floor_rootPin`
- `b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData`
- `b1_chiPos_existence_paper_min_noBar_of_cubeApproxData`
- `b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData`
- `b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData`
- `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData`

The best endpoint among these currently produces only the lower-pinned stationary profile package:

```lean
∃ U,
  InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
  FrozenStationaryWaveProfile p c U
```

This is valuable, but it is not the exact `hpos` branch, because the exact branch also needs:

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

## Input classification for the positive branch route

| Input / theorem / structure | Status | Reason |
|---|---|---|
| `Theorem_1_1.of_assumed_frozenStationaryProfile_branches` | pure wiring | Converts a negative frozen-stationary branch and the positive `hpos` branch into `Theorem_1_1`; it proves no construction itself. |
| `paper1_Theorem_1_1_of_constructionNegSMPProvider` | pure wiring plus negative-branch thinning | Replaces the negative branch by `ConstructionNegSMPProvider`, but still takes the full positive `hpos` as an explicit argument. |
| `Paper1MainlineExistence` | conditional B5 route, not positive construction | It proves `Theorem_1_2 ∧ Theorem_1_3` via `Theorem_1_2_and_1_3.of_mainlineExistence`; it does not consume the positive frozen-stationary branch. |
| `rotheFloorResidual_of_trap_pos` | pure wiring from existing positive super-barrier theorem plus carried core | It swaps in `whole_line_super_barrier_pos` and reuses the sign-agnostic floor residual route; the deep Green core is still an input. |
| `b1_chiPos_existence` | conditional but meaningful wiring | Reuses `b1_chiNeg_existence_unconditional` once `hcoreAll`, `hstep`, `htail`, Schauder principle, Green identity, positivity, and endpoint data are supplied. Produces a frozen profile plus trap membership, not the full `hpos`. |
| `b1_chiPos_existence_rootPin` / `b1_chiPos_existence_profileClean_stationary_floor_rootPin` | conditional but plausibly wireable from existing route packages | These reduce some profile obligations: strict positivity can come from the floor, right endpoint from trap, and left endpoint from stationary flatness. Still depend on core/step/tail/Schauder/stationarity/floor/flat inputs. |
| `b1_chiPos_existence_paper_*_of_cubeApproxData` wrappers | conditional route wrappers | They package the lower-pinned cube/Schauder route and produce `∃ U, InLowerPinnedMonotoneTrap ... U ∧ FrozenStationaryWaveProfile p c U`. They do not produce `ShenUpperBoundPositive` or sharp right-tail asymptotics. |
| `positivePaperLowerRawParabolicFloorRouteACore_of_noBar` and `PositivePaperLemma42ExactConditions.paperLowerRawParabolicFloorCore_of_noBar` | pure structural wiring | Fill the `barLip` field from positive paper Lemma 4.2-style parameter conditions; does not discharge analytic producer/core data. |
| `PaperLowerRawParabolicFloorRouteAParamCoreNoBar` | genuine analytic/frontier package | Contains per-step source-box/Green-core witness/rest/zsuper/lower-raw auxiliary data. It is thinner than a monolithic core but is still a residual provider, not an unconditional theorem. |
| `PaperLowerPinnedStationaryFlatFloor` | genuine analytic/frontier package | Supplies stationarity/flatness-style fixed-point limit properties used by the wrappers. No unconditional producer found in the inspected statement route. |
| `StationaryStrongMaxPrinciple` / `StationaryStrongMaxPrincipleODERealization` | genuine analytic residual | Used to get strict positivity/root pinning. There is `hsmp_of_odeRealization`, but the ODE realization itself remains an input. |
| `ShenUpperBoundPositive p c U` for the produced `U` | genuine analytic residual | The repo proves `logisticProfile_shenUpperBoundPositive` for the explicit logistic profile, but the produced Rothe fixed point is an arbitrary `U`; no bridge from `InLowerPinnedMonotoneTrap ... U ∧ FrozenStationaryWaveProfile p c U` to `ShenUpperBoundPositive p c U` was found. Trap membership gives non-strict upper envelope information; the headline bound is strict. |
| `HasWaveRightTailAsymptotic c κ₁ U` for the produced `U` | genuine analytic residual | The wrappers still do not produce the sharp asymptotic. No theorem was found deriving it from the positive lower-pinned frozen stationary profile. This is the same kind of right-end linearization gap that appears elsewhere in the Paper1 construction audits. |

## What is already produced unconditionally?

For this specific positive branch, no theorem in the inspected files produces the exact full `hpos` shape unconditionally.

The following are produced/wired unconditionally only as local components:

- The positive super-barrier is available through `whole_line_super_barrier_pos`, used by `rotheFloorResidual_of_trap_pos`.
- The all-purpose sign-agnostic Rothe/Schauder machinery is reused by `b1_chiPos_existence` through `b1_chiNeg_existence_unconditional`.
- Trap-derived facts such as boundedness and right-end vanishing are used inside the profile-clean wrappers.
- `logisticProfile_shenUpperBoundPositive` proves the positive upper bound for the explicit logistic profile, but it is not a producer for the Rothe fixed point.

## Can the full positive branch be wired now?

Not from the inspected existing facts alone.

A partial branch can be wired:

```lean
PositivePaperLemma42ExactConditions
+ Route-A / lower-raw parabolic floor data
+ lower-pinned stationary/flat floor data
+ stationary strong maximum principle
⇒ ∃ U, InLowerPinnedMonotoneTrap ... U ∧ FrozenStationaryWaveProfile p c U
```

using, for example:

```lean
b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
```

But the full headline branch additionally needs:

```lean
ShenUpperBoundPositive p c U
```

and

```lean
HasWaveRightTailAsymptotic c κ₁ U
```

for all admissible `κ₁`. Those are not produced by the current chain.

## Empty / same-as-goal assessment

The positive branch packages are not empty declarations in the sense of containing the theorem conclusion itself. The Route-A and lower-raw packages expose detailed finite-step, Green-core, Schauder, stationarity, floor, and SMP obligations. They are genuine conditional infrastructure.

However, the exact `hpos` argument to `paper1_Theorem_1_1_of_constructionNegSMPProvider` is still theorem-branch-shaped: it is essentially the full positive half of `Theorem_1_1` at the frozen-stationary-profile level. It should be treated as a remaining analytic frontier unless a new wrapper is added that combines the existing positive profile producer with separate producers for `ShenUpperBoundPositive` and `HasWaveRightTailAsymptotic`.

## Smallest honest next edit

A useful non-fake cleanup would be a documentation wrapper, not a theorem claiming full closure. Add a comment near `paper1_Theorem_1_1_of_constructionNegSMPProvider` noting:

```lean
/-- The positive branch is still a genuine construction frontier.  Existing
positive Rothe/Schauder wrappers such as
`b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData` produce a
lower-pinned `FrozenStationaryWaveProfile`, but the exact `hpos` input here also
requires `ShenUpperBoundPositive` and the sharp right-tail asymptotic for the
produced profile.  Those are not currently produced by the positive branch
wrappers.  Theorems 1.2/1.3 instead use `Paper1MainlineExistence` and do not
consume this construction branch. -/
```

Do not replace the `hpos` argument with the existing positive profile producer alone; that would hide the strict upper-bound and sharp-tail residuals.
