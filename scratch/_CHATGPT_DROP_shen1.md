# Q2793 (shen1) — next non-producer frontier wrappers

Repo: `xiangyazi24/Shen_work`  
Current status from prompt: no true `sorry`/`admit`, no explicit axioms; Paper3 P2Main NoNeg statement wrappers already landed in `2758736f` and `5be74d1d`; a Codex wrapper in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean` is locally passing on uisai2 but not visible on default branch.

Off-limits producer files:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

I did not inspect, depend on, or propose edits to those files.

## Verdict

The next highest-signal non-producer patch is a **generic Paper3 Proposition 1.x NoNeg wrapper** in:

```text
ShenWork/Paper3/IntervalDomainStatementAssembly.lean
```

Specifically, add a positive-`χ₀` variant of the existing Paper2-Theorems data surface:

```lean
IntervalDomainPaper3Proposition1FromPaper2TheoremsNoNegData
```

with fields only:

```lean
theorem12 : Theorem_1_2 intervalDomain p
theorem13 : Theorem_1_3 intervalDomain p C
```

and a theorem taking:

```lean
(hχ0 : 0 < p.χ₀)
```

to produce:

```lean
IntervalDomainPaper3Proposition1WithTheorem13Targets p C
```

This is pure wiring, not a mathematical frontier. It discharges the already-vacuous negative-sensitivity field by contradiction from `0 < χ₀` and then reuses the existing theorem:

```lean
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
```

This is the cleanest next step because the local Paper2 wrapper you described produces exactly Theorems 1.2/1.3, not necessarily the full `IntervalDomainPaper2MainTheoremTargets` bundle. The generic Paper3 NoNeg wrapper makes that local Paper2 result immediately usable by Paper3 proposition/headline routes without carrying `negativeBound`.

## Why this is not stale

Already done, so do **not** repeat:

- Paper3 P2Main NoNeg wrappers in `IntervalDomainActualLinearStatementAssembly.lean`.
- The local Paper2 positive-solution-interpolation wrapper described in the prompt.

The proposed wrapper is different: it lives one layer lower in generic Paper3 statement assembly and targets the `Theorem_1_2`/`Theorem_1_3` surface rather than the full `Paper2Main` surface. It is the natural consumer of the new Paper2 theorem12/theorem13 wrapper.

Existing declarations to grep:

```text
IntervalDomainPaper3Proposition1FromPaper2TheoremsData
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
IntervalDomainPaper3Proposition1FromPaper2MainTargetsData
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData
NegativeSensitivityGlobalEventualBound
```

## Patch skeleton: safest candidate

Target file:

```text
ShenWork/Paper3/IntervalDomainStatementAssembly.lean
```

Suggested location: immediately after

```lean
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsDataFact
```

and before `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData`.

If pasted directly into that file, do not include an import block.

```lean
/-- In positive-sensitivity regimes, the negative-sensitivity Proposition 1.2
residual is vacuous. -/
theorem intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
    (p : CM2Params) (hχ0 : 0 < p.χ₀) :
    NegativeSensitivityGlobalEventualBound intervalDomain p := by
  intro hχ_nonpos _hm _u₀ _hu₀
  exact False.elim (not_le_of_gt hχ0 hχ_nonpos)

/-- Interval-domain Paper3 Proposition 1.x data with Proposition 1.4 routed
through Paper2 Theorem 1.2 and Proposition 1.3 routed through Paper2 Theorem
1.3, while the negative-sensitivity Proposition 1.2 branch is discharged by
`0 < χ₀`. -/
structure IntervalDomainPaper3Proposition1FromPaper2TheoremsNoNegData
    (p : CM2Params) (C : Paper2Constants p) : Prop where
  theorem12 : Theorem_1_2 intervalDomain p
  theorem13 : Theorem_1_3 intervalDomain p C

/-- Assemble interval-domain Paper3 Propositions 1.2--1.4 using Paper2
Theorems 1.2 and 1.3, without carrying the independent negative-sensitivity
residual in the positive-sensitivity regime. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : 0 < p.χ₀)
    (hData : IntervalDomainPaper3Proposition1FromPaper2TheoremsNoNegData p C) :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
    p C
    { negativeBound :=
        intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
          p hχ0
      theorem12 := hData.theorem12
      theorem13 := hData.theorem13 }

/-- Instance-facing interval-domain Paper3 Proposition 1.x wrapper using Paper2
Theorems 1.2 and 1.3, with the negative-sensitivity branch discharged by
`0 < χ₀`. -/
theorem
    intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (hχ0 : 0 < p.χ₀)
    [hData : Fact
      (IntervalDomainPaper3Proposition1FromPaper2TheoremsNoNegData p C)] :
    IntervalDomainPaper3Proposition1WithTheorem13Targets p C :=
  intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsNoNegData
    p C hχ0 hData.out
```

### Compile notes

This should be very close to compiling because:

- `NegativeSensitivityGlobalEventualBound`, `Theorem_1_2`, `Theorem_1_3`, and `IntervalDomainPaper3Proposition1WithTheorem13Targets` are already in scope in `IntervalDomainStatementAssembly.lean`.
- The existing wrapper `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData` already accepts the record we construct.
- The proof of `negativeBound` is just contradiction from `not_le_of_gt hχ0 hχ_nonpos`.

One caveat: `IntervalDomainActualLinearStatementAssembly.lean` already has a theorem named:

```lean
intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
```

If this name is already imported into the same namespace via `IntervalDomainActualLinearStatementAssembly`, then adding the same name in `IntervalDomainStatementAssembly.lean` would conflict when both are imported. To avoid any risk, either:

1. use a slightly more generic name in `IntervalDomainStatementAssembly.lean`, such as

```lean
intervalDomainPaper3_negativeSensitivityResidual_of_chi_pos
```

or

2. move/rename the existing actual-linear theorem in a separate cleanup.

For the smallest safe patch, prefer option 1 and update the skeleton call accordingly:

```lean
negativeBound := intervalDomainPaper3_negativeSensitivityResidual_of_chi_pos p hχ0
```

## Candidate 2: full-statement wrapper using the new proposition wrapper

After Candidate 1 compiles, a direct Paper3 full-statement wrapper can consume the theorem12/theorem13 NoNeg proposition data plus any existing mainline data.

Target file:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

Candidate name:

```lean
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinTheoremsNoNegData
```

Possible fields:

```lean
propositions : IntervalDomainPaper3Proposition1FromPaper2TheoremsNoNegData p C
mainline : IntervalDomainPaper3MainlineMoserActualLinearSmallIntegratedStepThinFrontierData
  p M0 uBar vLower locallyConverges neumannResolventGradientBound
```

Then the theorem reuses:

```lean
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsNoNegData
intervalDomain_paper3_mainlineTargets_of_moserActualLinearSmallIntegratedStepThinFrontierData
```

This is also pure wiring. I would do it second, not first, because the generic proposition wrapper in `IntervalDomainStatementAssembly.lean` is reusable by more than one actual-linear route.

## Candidate 3: lower-average / upper-data-gap NoNeg variants, only if absent

If a grep shows any of these are still absent:

```text
IntervalDomainPaper3StatementMoserActualLinearSmallLowerAverageUpperDataGapStability24P2MainNoNegData
IntervalDomainPaper3StatementMoserActualLinearSmallLowerUpperP2MainNoNegData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
```

then adding the missing one is safe and purely wiring. But the prompt says the Paper3 P2Main NoNeg statement wrappers are already done, so this is lower priority and likely stale.

## Candidate 4: local-existence compression is not next

Avoid trying to compress local existence / global extension at this stage. The current Paper2/Paper3 routes distinguish:

- local existence;
- bounded initial data;
- global extension;
- Paper2 main theorem target bundle;
- Moser/integrated-step inputs.

Compressing local-existence packages would likely be either a larger statement-surface redesign or a real PDE existence frontier. It is not comparable to the NoNeg wrappers and is not the next low-conflict patch.

## Bottom line

Highest-signal next patch:

```text
ShenWork/Paper3/IntervalDomainStatementAssembly.lean
```

Add a theorem12/theorem13 NoNeg proposition wrapper:

```lean
IntervalDomainPaper3Proposition1FromPaper2TheoremsNoNegData
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsNoNegData
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsNoNegDataFact
```

This is a small pure-wiring patch that lets the newly passing Paper2 theorem12/theorem13 positive-interpolation route feed Paper3 proposition/headline routes without carrying `negativeBound`, and it does not touch or rely on any Zinan-owned producer files.
