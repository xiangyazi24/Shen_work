# PAPER1-POSITIVE-BRANCH-AUDIT-REQUEST

Audit target: Paper1 headline statement assembly on current `main` around `e3aa461e` or newer, focused only on the positive-critical/frozen-stationary branch.

## First correction: this branch is for Theorem 1.1, not the B5 Theorem 1.2/1.3 route

The positive-critical/frozen-stationary branch appears in Paper1 Theorem 1.1 construction, not in the current strongest Paper1 Theorem 1.2/1.3 mainline.  The B5 stability/uniqueness route is:

```lean
paper1_mainlineStatementTargets_of_mainlineExistence
  : Paper1MainlineExistence cStarStarFn → Theorem_1_2 ∧ Theorem_1_3
```

So Theorems 1.2/1.3 are conditional on `Paper1MainlineExistence`, whose fields are stability-threshold, traveling-wave regularity, perturbation energy dissipation, weighted-L2-to-uniform upgrade, and Cauchy uniqueness.  They do not require the positive frozen-stationary construction branch.

The positive branch is needed when assembling the full Paper1 main statement target:

```lean
Paper1MainStatementTargets := Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3
```

via either:

```lean
paper1_mainStatementTargets_of_mainResultsData
paper1_Theorem_1_1_of_constructionNegSMPProvider
```

## Exact positive branch required by the headline wrapper

`paper1_Theorem_1_1_of_constructionNegSMPProvider` thins only the negative branch.  It still takes the positive branch as an explicit input:

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

That is exactly the `hpos` argument of:

```lean
Theorem_1_1.of_assumed_frozenStationaryProfile_branches
```

Classification of this full `hpos` input: **genuine analytic residual / theorem-branch-shaped frontier**.  It is not currently produced unconditionally.

## Existing positive-branch infrastructure

The repo has significant positive-branch Rothe/Schauder infrastructure.  The relevant chain includes:

```lean
rotheFloorResidual_of_trap_pos
b1_chiPos_existence
b1_chiPos_existence_rootPin
b1_chiPos_existence_profileClean_stationary_floor_rootPin
b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData
b1_chiPos_existence_paper_min_noBar_of_cubeApproxData
b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData
b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
```

The strongest inspected positive construction wrappers produce a lower-pinned stationary profile:

```lean
∃ U,
  InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
    FrozenStationaryWaveProfile p c U
```

This is not enough for the exact `hpos` branch, because `hpos` additionally requires:

```lean
ShenUpperBoundPositive p c U
```

and the sharp tail:

```lean
∀ κ₁, kappa c < κ₁ →
  κ₁ < min ((1 + p.α) * kappa c)
    (min (p.m * kappa c + 1 / 2) 1) →
  HasWaveRightTailAsymptotic c κ₁ U
```

I found no existing theorem that turns the produced lower-pinned `FrozenStationaryWaveProfile` into those two fields.

## Classification by input / route piece

| Item | Classification | Notes |
|---|---|---|
| `paper1_mainlineStatementTargets_of_mainlineExistence` | pure wiring from a conditional package | Proves `Theorem_1_2 ∧ Theorem_1_3` from `Paper1MainlineExistence`; it does not use the positive construction branch. |
| `Paper1MainlineExistence` | genuine analytic residual package | Carries `cStarStar_spec`, `regularity`, `energyDissipation`, `l2ToUniform`, and `cauchyUnique`.  It is not an empty declaration and does not contain `Theorem_1_2`/`Theorem_1_3` as fields. |
| `paper1_Theorem_1_1_of_constructionNegSMPProvider` | pure wiring plus negative-branch thinning | Consumes `ConstructionNegSMPProvider` and the full positive `hpos`; only the negative upper-bound slot is thinned. |
| `Theorem_1_1.of_assumed_frozenStationaryProfile_branches` | pure wiring | Converts negative and positive frozen-stationary profile branches into `Theorem_1_1`. |
| Exact `hpos` branch | genuine analytic residual / theorem-branch-shaped frontier | Requires profile, `ShenUpperBoundPositive`, and `HasWaveRightTailAsymptotic`; not currently produced as a whole. |
| `rotheFloorResidual_of_trap_pos` | pure wiring from existing produced facts plus carried core | Swaps in `whole_line_super_barrier_pos`; still carries the deep Green/core input. |
| `b1_chiPos_existence` | conditional but meaningful wiring | Reuses the sign-agnostic `b1_chiNeg_existence_unconditional`; still needs `hcoreAll`, `hstep`, `htail`, Schauder principle, Green identity, positivity, boundedness, and endpoint-limit inputs. |
| `b1_chiPos_existence_rootPin`, `b1_chiPos_existence_stationary_floor_rootPin`, `b1_chiPos_existence_profileClean_stationary_floor_rootPin` | conditional but plausibly wireable from existing packages | Reduce profile endpoint/positivity obligations using floor, stationary flatness, and SMP inputs; still conditional. |
| `b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData` | conditional route wrapper | Fills the upper-barrier Lipschitz scalar from `PositivePaperLemma42ExactConditions`, but still needs producer, step, tail, stationarity, SMP realization, and flatness. |
| `b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData` | conditional route wrapper | Produces the lower-pinned frozen profile from a core no-bar parabolic floor plus stationary-flat floor and SMP. |
| `b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData` | conditional route wrapper | Replaces the all-`u` producer by the Route-A core floor, but still needs Route-A floor data, stationary-flat floor, and SMP. |
| `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData` | conditional but plausibly wireable from smaller packages | Further replaces the monolithic Route-A Green core by explicit source-box parameter packages; still a frontier package, not an unconditional producer. |
| `PaperLowerRawParabolicFloorRouteAParamCoreNoBar` | genuine analytic residual package | Carries per-step source-box parameters, witnesses, rest provider, super-solution transfer, and lower-raw auxiliary data. |
| `PaperLowerPinnedStationaryFlatFloor` | genuine analytic residual package | Supplies stationarity/flatness properties for the lower-pinned fixed point route. |
| `StationaryStrongMaxPrinciple` / `StationaryStrongMaxPrincipleODERealization` | genuine analytic residual | `hsmp_of_odeRealization` is wiring, but the realization/SMP itself remains an input. |
| `ShenUpperBoundPositive p c U` for the produced `U` | genuine analytic residual | There is `logisticProfile_shenUpperBoundPositive` for the explicit logistic profile, but no bridge from the Rothe fixed point to `ShenUpperBoundPositive`. |
| `HasWaveRightTailAsymptotic c κ₁ U` for the produced `U` | genuine analytic residual | No producer was found from the current positive lower-pinned stationary profile route. |

## Already produced unconditionally in Lean

For this positive branch, the following are produced only as local components, not as the full `hpos`:

- `whole_line_super_barrier_pos`, consumed by `rotheFloorResidual_of_trap_pos`.
- Sign-agnostic Rothe/Schauder reuse through `b1_chiNeg_existence_unconditional`.
- Trap-derived boundedness/right-end behavior used by the profile-clean wrappers.
- `logisticProfile_shenUpperBoundPositive`, but only for the explicit profile `logisticProfile (kappa c)`, not for the constructed fixed point.

No inspected theorem unconditionally produces:

```lean
∀ p, p.α = p.m + p.γ - 1 → 0 ≤ p.χ →
  p.χ < min (1 / 2 : ℝ) (chiStar p) → ∀ c, 2 < c →
    ∃ U, FrozenStationaryWaveProfile p c U ∧
      ShenUpperBoundPositive p c U ∧
      ∀ κ₁, ... → HasWaveRightTailAsymptotic c κ₁ U
```

## Is the positive branch empty or same-as-goal?

The lower-level positive route packages are not empty declarations: they expose concrete finite-dimensional/Schauder/Rothe/Green/stationarity/SMP obligations and produce a real lower-pinned `FrozenStationaryWaveProfile` once those obligations are supplied.

The exact `hpos` argument at the headline wrapper is still close to the positive half of `Theorem_1_1`; it is not “empty,” but it is theorem-branch-shaped and should be treated as a genuine remaining construction frontier.

## Smallest honest next edit

A safe edit is documentation near `paper1_Theorem_1_1_of_constructionNegSMPProvider`, not a theorem pretending the branch is closed:

```lean
/-- The positive branch remains a genuine construction frontier.  Existing
positive Rothe/Schauder wrappers such as
`b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData` produce a
lower-pinned `FrozenStationaryWaveProfile`, but the exact `hpos` input here also
requires `ShenUpperBoundPositive` and the sharp right-tail asymptotic for the
produced profile.  Those are not currently produced by the positive branch
wrappers.  Theorems 1.2/1.3 use `Paper1MainlineExistence` and do not consume this
construction branch. -/
```

Do not replace the exact `hpos` argument with the existing positive profile producer alone; that would hide the strict upper-bound and sharp-tail residuals.
