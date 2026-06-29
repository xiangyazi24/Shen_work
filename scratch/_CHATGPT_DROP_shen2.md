# Q2237 R3 Paper1 preferred SMP/mainline wrapper audit for `Shen_work` main around `e3aa461e`

## Answer in one sentence

Yes: the proposed wrapper is sound **pure statement-level wiring** if it exposes all three remaining inputs—`ConstructionNegSMPProvider`, the positive frozen-stationary branch for Theorem 1.1, and `Paper1MainlineExistence`; it would hide a residual only if it pretended that `ConstructionNegSMPProvider` alone proves Theorem 1.1 or that `Paper1MainlineExistence` is constructed internally.

## Source evidence

`ShenWork/Paper1/StatementAssembly.lean` already defines the target:

```lean
def Paper1MainStatementTargets : Prop :=
  Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3
```

It also has the old monolithic route:

```lean
theorem paper1_mainStatementTargets_of_mainResultsData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainResultsData cStarStarFn) :
    Paper1MainStatementTargets :=
  paper1_main_results_bundled cStarStarFn hData
```

The separate current Theorem 1.1 route is:

```lean
theorem paper1_Theorem_1_1_of_constructionNegSMPProvider
    (hneg : ConstructionNegSMPProvider)
    (hpos :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            FrozenStationaryWaveProfile p c U ∧
              ShenUpperBoundPositive p c U ∧
              ∀ κ₁, kappa c < κ₁ →
                κ₁ < min ((1 + p.α) * kappa c)
                  (min (p.m * kappa c + 1 / 2) 1) →
                HasWaveRightTailAsymptotic c κ₁ U) :
    Theorem_1_1 :=
  Theorem_1_1.of_constructionNeg_provider_smp hneg hpos
```

The separate current mainline route is:

```lean
theorem paper1_mainlineStatementTargets_of_mainlineExistence
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hexist : Paper1MainlineExistence cStarStarFn) :
    Paper1MainlineStatementTargets :=
  Theorem_1_2_and_1_3.of_mainlineExistence hexist
```

and `Paper1MainlineStatementTargets` is exactly:

```lean
def Paper1MainlineStatementTargets : Prop :=
  Theorem_1_2 ∧ Theorem_1_3
```

`ShenWork/Paper1/StationaryUpperTail.lean` confirms that `ConstructionNegSMPProvider` is itself still a substantial provider package: it supplies lower-pinned Schauder data, stationarity, flatness, the scalar `U 0 < 1`, and the sharp right-tail asymptotic family. The theorem `Theorem_1_1.of_constructionNeg_provider_smp` still also takes the positive branch `hpos`.

`ShenWork/Paper1/Lemma25Helpers.lean` confirms that `Paper1MainlineExistence` is a genuine mainline existence/frontier package with fields such as `cStarStar_spec`, `regularity`, `energyDissipation`, `l2ToUniform`, and `cauchyUnique`, and that `Theorem_1_2_and_1_3.of_mainlineExistence` simply projects Theorems 1.2 and 1.3 from that package.

## Classification

The proposed preferred wrapper is **pure wiring**. It does not add or discharge analysis. It only avoids requiring the old all-in-one `Paper1MainResultsData` bundle when the repo already has separate, clearer routes:

```lean
ConstructionNegSMPProvider + positive branch  ==> Theorem_1_1
Paper1MainlineExistence                      ==> Theorem_1_2 ∧ Theorem_1_3
```

It is therefore safe as a preferred statement-layer entry point, provided the structure name and doc comment say “data/frontier/conditional,” not “closed theorem.”

## Minimal addition

Add this near the existing Paper1 main-statement wrappers in `ShenWork/Paper1/StatementAssembly.lean`, preferably after `paper1_Theorem_1_1_of_constructionNegSMPProviderFact` and before the `Paper1MainlineStatementTargets` block, or immediately after the single-target Theorem 1.2/1.3 wrappers.

No new imports are needed in that file: it already imports `ShenWork.Paper1.Lemma25Helpers` and `ShenWork.Paper1.StationaryUpperTail`.

```lean
import ShenWork.Paper1.Lemma25Helpers
import ShenWork.Paper1.StationaryUpperTail

namespace ShenWork.Paper1

noncomputable section

/-- Positive critical frozen-stationary branch used with
`ConstructionNegSMPProvider` to prove Paper1 Theorem 1.1.

This is the existing `hpos` argument of
`paper1_Theorem_1_1_of_constructionNegSMPProvider`, factored out so the
preferred bundled main wrapper can expose every remaining input explicitly. -/
def Paper1PositiveCriticalFrozenStationaryBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
          ShenUpperBoundPositive p c U ∧
          (∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U)

/-- Preferred Paper1 main-statement input package using the thinner current
routes instead of the old monolithic `Paper1MainResultsData`.

Still conditional: `constructionNeg` is the weakened negative construction
provider, `positiveCritical` is the positive frozen-stationary branch for
Theorem 1.1, and `mainline` is the B5 stability/uniqueness mainline package for
Theorems 1.2 and 1.3.  This package is not an unconditional Paper1 headline
producer. -/
structure Paper1MainStatementSMPMainlineData
    (cStarStarFn : CMParams → ℝ → ℝ) : Prop where
  constructionNeg : ConstructionNegSMPProvider
  positiveCritical : Paper1PositiveCriticalFrozenStationaryBranch
  mainline : Paper1MainlineExistence cStarStarFn

/-- Preferred Paper1 main-statement wrapper from the current thinner input
packages.

This is pure wiring:
* Theorem 1.1 is obtained from
  `paper1_Theorem_1_1_of_constructionNegSMPProvider`.
* Theorems 1.2 and 1.3 are obtained from
  `paper1_mainlineStatementTargets_of_mainlineExistence`.

It does not construct `ConstructionNegSMPProvider`, the positive branch, or
`Paper1MainlineExistence`. -/
theorem paper1_mainStatementTargets_of_smpMainlineData
    {cStarStarFn : CMParams → ℝ → ℝ}
    (hData : Paper1MainStatementSMPMainlineData cStarStarFn) :
    Paper1MainStatementTargets :=
  ⟨paper1_Theorem_1_1_of_constructionNegSMPProvider
      hData.constructionNeg hData.positiveCritical,
    paper1_mainlineStatementTargets_of_mainlineExistence hData.mainline⟩

/-- Instance-facing wrapper for the preferred conditional Paper1 main-statement
route. -/
theorem paper1_mainStatementTargets_of_smpMainlineDataFact
    (cStarStarFn : CMParams → ℝ → ℝ)
    [hData : Fact (Paper1MainStatementSMPMainlineData cStarStarFn)] :
    Paper1MainStatementTargets :=
  paper1_mainStatementTargets_of_smpMainlineData hData.out

end

end ShenWork.Paper1
```

When inserted into `StatementAssembly.lean`, omit the repeated imports/namespace/end lines and keep only the declarations inside the existing namespace/section.

## Exact theorem chain and field mapping

| New field | Consumed by | Produces |
|---|---|---|
| `constructionNeg : ConstructionNegSMPProvider` | first argument of `paper1_Theorem_1_1_of_constructionNegSMPProvider` | part of `Theorem_1_1` proof |
| `positiveCritical : Paper1PositiveCriticalFrozenStationaryBranch` | second argument of `paper1_Theorem_1_1_of_constructionNegSMPProvider` | remaining part of `Theorem_1_1` proof |
| `mainline : Paper1MainlineExistence cStarStarFn` | `paper1_mainlineStatementTargets_of_mainlineExistence` | `Theorem_1_2 ∧ Theorem_1_3` |

The final theorem pairs those outputs into `Paper1MainStatementTargets`, whose shape is `Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3`.

## Important warning

Do **not** add a wrapper with only these fields:

```lean
constructionNeg : ConstructionNegSMPProvider
mainline : Paper1MainlineExistence cStarStarFn
```

That would be incomplete: the current Theorem 1.1 wrapper still requires the positive critical branch `hpos`. Omitting it would either fail to typecheck or force an invented analytic producer. The honest preferred bundle must include the positive branch explicitly.

## Naming note

The name `Paper1MainStatementSMPMainlineData` is intentionally verbose and conditional. A shorter name like `Paper1PreferredMainData` would be easier to misuse as a no-assumption headline theorem. If a shorter alias is desired later, add it only after the doc comment makes the residual status explicit.
