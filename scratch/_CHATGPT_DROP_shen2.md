# Q2223 R2 cleanup patch plan for `Shen_work` main `09140eae`

## Scope and principle

This is a minimal **code/doc cleanup plan only**. It should not change theorem statements, structures, proof terms, imports, or mathematical claims. The goal is to make headline wrappers visibly conditional where they consume `...Data`, `...FrontierData`, or `...BranchData` packages.

The current main already contains several Q2214-style fixes, especially in Paper3: `Paper3Proposition1FromPaper2MainTargetsData`, `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData`, and `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData` now explicitly mention that `negativeBound` remains independent. Do not duplicate those comments; only add the small missing warnings below.

No new imports are needed for the suggested snippets below. They are in-place doc-comment or alias fragments inside files that already import the relevant names.

## Patch 1: `UNDERSTANDING.md`

**Location:** under the existing `Input-package audit:` bullets near the end of the current-state section.

**Why:** the file already states the rule, but a tiny table would make the intended reading impossible to miss.

```md
### R2 headline-wrapper reading rule

| Surface form | Safe reading |
|---|---|
| `theorem ..._of_data`, `..._of_frontierData`, `..._of_branchData`, `...Fact` | Conditional assembly theorem unless a named producer constructs the required package. |
| `structure ...Data` / `...FrontierData` / `...BranchData` | Input interface, not an axiom and not a proof hole. |
| Current closed producers | Paper1 `paper1_lemma25Targets`; Paper2 interval `intervalDomainPaper2_Theorem_1_1_chiZero_unconditional`; Paper3 interval actual-linear-small `intervalDomain_paper3_Theorem_2_1_of_actualLinearSmall` and part/sectorial variants. |
| Deprecated/no-go routes | Routes consuming `IntervalDomainLemma41.IntervalDomainInterpolation` until that statement is repaired; Paper3 derivation of Proposition 1.2 from Paper2 Theorem 1.1, refuted by `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`. |
```

## Patch 2: `ShenWork/Paper1/StatementAssembly.lean`

### 2A. Clarify the main-results wrapper

**Location:** doc comment immediately above `paper1_mainStatementTargets_of_mainResultsData`.

Replace the current two-line comment with:

```lean
/-- Main Paper1 statement-target assembly from the existing main-results
frontier record.

Conditional interface: this theorem does not construct `Paper1MainResultsData`.
It only turns that package into `Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3`.
The closed no-frontier component in this file is `paper1_lemma25Targets`. -/
```

### 2B. Clarify the mainline-existence wrapper

**Location:** doc comment immediately above `paper1_mainlineStatementTargets_of_mainlineExistence`.

```lean
/-- Mainline-existence assembly for Paper1 Theorems 1.2 and 1.3.

Conditional interface: `Paper1MainlineExistence` is the B5 mainline input
package.  This wrapper does not construct that package. -/
```

### 2C. Clarify combined-data status

**Location:** doc comment immediately above `Paper1CombinedStatementData`.

```lean
/-- Bundled data for the Paper1 combined statement-target assembly.

This is a frontier bundle: `main`, `propositions`, `lemma51`, and `lemma52`
are still supplied inputs.  Only the nested Lemma 2.5 targets are closed
inside `paper1_combinedStatementTargets_of_data`. -/
```

### 2D. Optional small warning on the weakened negative construction wrapper

**Location:** extend the existing doc comment above `paper1_Theorem_1_1_of_constructionNegSMPProvider`.

```lean
/-- Single-target Paper1 Theorem 1.1 wrapper using the weakened negative
construction provider.  The negative branch no longer carries
`ShenUpperBoundNegative` directly; it carries the scalar strictness `U 0 < 1`
through `ConstructionNegSMPProvider`.

Still conditional: both `hneg : ConstructionNegSMPProvider` and the positive
branch `hpos` are headline construction inputs. -/
```

No aliases are needed for Paper1 in the minimal patch.

## Patch 3: `ShenWork/Paper2/StatementAssembly.lean`

### 3A. Clarify generic main target shape

**Location:** doc comment immediately above `Paper2MainTheoremTargets`.

```lean
/-- Paper2 main theorem target shape covered by the solution-branch package.

This is only the target conjunction `Theorem_1_1 ∧ Theorem_1_2 ∧ Theorem_1_3`;
`paper2_mainTheoremTargets_of_solutionBranchData` remains conditional on
`Paper2MainSolutionBranchData`. -/
```

### 3B. Clarify generic statement data

**Location:** doc comment immediately above `Paper2StatementData`.

```lean
/-- Bundled generic Paper2 statement-target data.

Frontier bundle: `bootstrap` and `localAndMain` are supplied input packages.
The wrapper `paper2_statementTargets_of_data` is statement assembly, not a
no-assumption headline theorem. -/
```

These are doc-only changes; no alias needed.

## Patch 4: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`

### 4A. Mark the GN/global interpolation route as no-go for headlines

**Location:** doc comment immediately above `intervalDomainPaper2_Lemma_4_1_of_GN_frontier`.

```lean
/-- Single-target interval-domain wrapper for Lemma 4.1 from the concrete GN
frontier.

Deprecated as a headline route: this consumes
`IntervalDomainLemma41.IntervalDomainInterpolation`, which is refuted as
literally stated by
`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.
Use the solution-slice or positive-solution-slice interpolation routes instead
until the global interpolation statement is repaired. -/
```

Also update the comment above `intervalDomainPaper2_aprioriTargets_of_GN_frontier` similarly:

```lean
/-- Assemble the interval-domain Lemma 3.1 and Lemma 4.1 targets from the GN
frontier.

Deprecated as a headline route for the same reason as
`intervalDomainPaper2_Lemma_4_1_of_GN_frontier`: the global
`IntervalDomainInterpolation` premise is currently refuted. -/
```

### 4B. Warn on the interpolation-energy frontier that contains the refuted premise

**Location:** doc comment immediately above `IntervalDomainPaper2InterpolationEnergyFrontierData`.

```lean
/-- Common interpolation/energy inputs shared by the thinner interval-domain
Theorem 1.2 and Theorem 1.3 route.

Legacy/no-go headline interface: the `interpolation` field is the global
`IntervalDomainInterpolation` premise, refuted as literally stated by
`IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation`.
Prefer `IntervalDomainPaper2SolutionInterpolationEnergyFrontierData` or the
positive solution-slice variant for current headline routes. -/
```

### 4C. Warn on H2/logistic statement packages that still carry the global premise

**Location:** doc comment above `IntervalDomainPaper2StatementH2SourceFrontierData`; repeat the same idea for the logistic-source counterpart if present below the fetched block.

```lean
/-- Interval-domain Paper 2 statement-frontier record using the half-step
H2-source local-existence route.

Legacy/no-go headline interface as written: the `interpolation` field is the
refuted global `IntervalDomainInterpolation` premise.  Prefer the
`...PositiveSolutionInterpolation...` H2-source statement routes. -/
```

### 4D. Optional noninvasive alias for the preferred Paper2 full route

This is safe but not required. Add only if the team wants a grep-friendly entrypoint name. It does not change any interface or proof.

**Location:** immediately after `intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData`.

```lean
/-- Explicit-name alias for the current preferred `χ₀ = 0` interval-domain
Paper2 full statement route.

Still conditional on the positive solution-slice common data, finite-horizon
alternative, global-extension/bootstrap/eventual-sup frontiers, and the thin
section-2 fields. -/
theorem
    intervalDomainPaper2_statementTargets_chiZero_posSolutionSlice_section2Thin_localFree_fromFrontiers
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
        p C cGrad) :
    IntervalDomainPaper2StatementTargets p C :=
  intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData
```

If namespace length is a concern, skip this alias; the doc-comment patches are enough.

## Patch 5: `ShenWork/Paper3/Statements.lean`

**Location:** immediately above `NegativeSensitivityGlobalEventualBound`.

**Why:** this is the most important residual to label at the source definition, not only at downstream wrappers.

```lean
/-- Analytic residual used to prove Paper3 Proposition 1.2: global existence
and eventual-in-time boundedness in the negative-sensitivity regime.

This is not supplied by Paper2 Theorem 1.1 under the current abstract API; see
`not_paper2_theorem_1_1_implies_paper3_proposition_1_2`. -/
def NegativeSensitivityGlobalEventualBound
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        ∃ M : ℝ, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M
```

This replaces only the missing doc comment; the definition body is unchanged.

## Patch 6: Paper3 `FromPaper2MainTargets` names

### Current main status

No urgent doc patch is needed in these declarations because current main already has the critical warning:

- `ShenWork/Paper3/StatementAssembly.lean`: `Paper3Proposition1FromPaper2MainTargetsData` says `negativeBound` is independent and not derived from Paper2 Theorem 1.1; `paper3_proposition1Targets_of_paper2MainTargetsData` says only Theorems 1.2/1.3 are consumed from `main`.
- `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`: `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData` says `negativeBound` is still the independent Proposition 1.2 residual.
- `ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean`: `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData` says Paper2 main routes Proposition 1.3/1.4 and does not discharge `negativeBound`.

### Optional aliases, not renames

If Xiang wants grep-friendly names without breaking current users, add aliases, not renames.

**Generic alias in `ShenWork/Paper3/StatementAssembly.lean`, after `paper3_proposition1Targets_of_paper2MainTargetsData`:**

```lean
/-- Explicit-name alias: Paper2 main targets supply only the Proposition 1.3/1.4
branches; `negativeBound` remains the Proposition 1.2 residual. -/
theorem paper3_proposition1Targets_of_negativeBoundAndPaper2MainTargetsData
    {D : BoundedDomainData} {p : CM2Params} {C : Paper2Constants p}
    (hData : Paper3Proposition1FromPaper2MainTargetsData D p C) :
    Paper3Proposition1Targets D p C :=
  paper3_proposition1Targets_of_paper2MainTargetsData hData
```

**Interval alias in `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`, after `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData`:**

```lean
/-- Explicit-name alias: Paper2 main targets supply Proposition 1.3/1.4;
`negativeBound` remains the Proposition 1.2 residual. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_negativeBoundAndPaper2MainTargetsData
    (p : CM2Params) (C : Paper2Constants p)
    (hData : IntervalDomainPaper3Proposition1FromPaper2MainTargetsData p C) :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
    p C hData
```

These aliases are optional. They add names only; they do not replace existing APIs.

## Deferred changes: too invasive for this cleanup

1. **Do not rename existing structures/theorems now.** Renaming `Paper3Proposition1FromPaper2MainTargetsData`, `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData`, or `IntervalDomainPaper3StatementMoserActualLinearSmallCETerminalP2MainData` would churn downstream references. Use comments or aliases first.
2. **Do not add `@[deprecated]` attributes yet.** Formal deprecation on GN/interpolation routes may create noisy warnings across existing files. Prefer doc warnings in this patch.
3. **Do not split frontier structures.** Splitting Paper2/Paper3 large data records into produced-vs-residual subrecords is a larger API migration.
4. **Do not remove old routes.** Keep legacy wrappers for comparison and build stability; mark their status clearly instead.
5. **Do not assert new discharge theorems.** This patch should only label current status and optionally add definitional aliases.

## Minimal patch checklist

Required minimal patch:

1. `UNDERSTANDING.md`: add the R2 reading-rule table.
2. `Paper1/StatementAssembly.lean`: clarify `paper1_mainStatementTargets_of_mainResultsData`, `paper1_mainlineStatementTargets_of_mainlineExistence`, `Paper1CombinedStatementData`, and optionally the weakened negative-construction wrapper.
3. `Paper2/StatementAssembly.lean`: clarify `Paper2MainTheoremTargets` and `Paper2StatementData`.
4. `Paper2/IntervalDomainStatementAssembly.lean`: add no-go doc warnings to GN/global interpolation routes and to statement packages that still consume `IntervalDomainInterpolation`.
5. `Paper3/Statements.lean`: add the missing doc comment on `NegativeSensitivityGlobalEventualBound`.

Optional safe aliases:

- One explicit Paper2 preferred-route alias for the `χ₀ = 0`, positive solution-slice, section-2-thin, local-free full statement route.
- Paper3 `negativeBoundAndPaper2MainTargets` aliases for the generic and interval proposition wrappers.

That is the smallest safe cleanup: it is documentation-first, preserves all theorem interfaces, and avoids overclaiming conditional wrappers as closed headline theorems.
