# Q2754 (shen1) — next low-conflict non-Zinan wrapper after actual-linear NoNeg

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`

Off-limits producer files, not touched and not needed:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

I inspected the visible statement-assembly surfaces. Current default branch already has later variants of some of the wrappers discussed below, but for the baseline described in the prompt — after adding only

```lean
IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
```

— the best next low-conflict edit is still clear.

## Recommendation

Add a Paper3 actual-linear wrapper that avoids carrying the full Paper2 main theorem bundle when Paper3 only needs Paper2 Theorems 1.2 and 1.3.

Target file:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

The current NoNeg wrapper removes the Paper3 negative-sensitivity residual but still asks for:

```lean
paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

inside:

```lean
IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
```

That is stronger than necessary for Paper3 Proposition 1.3/1.4. The generic interval-domain Paper3 statement assembly already has a theorem12/theorem13 route:

```lean
intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
```

and the Paper2 interval assembly already has the proved-positive Agmon route:

```lean
IntervalDomainPaper2Theorem12And13ProvedPositiveSolutionInterpolationFrontierData
intervalDomainPaper2_Theorems_1_2_and_1_3_of_provedPositiveSolutionInterpolationFrontierData
```

So the next wrapper should combine:

1. `intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos` for Proposition 1.2;
2. Paper2 proved-positive theorem12/theorem13 route for Proposition 1.3/1.4;
3. the existing actual-linear thin mainline route.

This is pure wiring. It does not touch Moser producers, high-excursion, threshold-plan files, or Agmon proofs.

## Why this is higher signal than another Moser wrapper

The NoNeg wrapper already removed `negativeBound`; the next opaque input is `paper2Main`. But Paper3 does not consume Paper2 Theorem 1.1 through the proposition route. It consumes only:

```lean
theorem12 : Theorem_1_2 intervalDomain p
theorem13 : Theorem_1_3 intervalDomain p C
```

for Paper3 Proposition 1.4 and Proposition 1.3. Therefore a theorem12/theorem13 wrapper is a real headline-surface reduction.

This also connects naturally to the proved Agmon baseline: the Paper2 route no longer needs an `agmon` field, because it can call:

```lean
intervalDomain_classicalSolutionPositiveInterpolation p
```

through the proved-positive data conversion.

## Patch sketch

Suggested new names:

```lean
IntervalDomainPaper3StatementActualLinear22ThinTheorem12And13ProvedPositiveNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegDataFact
```

Place near the existing `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` block.

```lean
/-- Full Paper3 statement frontiers in the actual-linear-small regime, with the
negative-sensitivity Proposition 1.2 residual discharged from `0 < χ₀` and
Proposition 1.3/1.4 routed through the proved-positive Paper2 Theorem 1.2/1.3
frontier rather than the full Paper2 main theorem bundle. -/
structure
    IntervalDomainPaper3StatementActualLinear22ThinTheorem12And13ProvedPositiveNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop where
  paper2Theorems :
    IntervalDomainPaper2Theorem12And13ProvedPositiveSolutionInterpolationFrontierData
      p C cGrad
  mainline :
    IntervalDomainPaper3MainlineActualLinear22ThinFrontierData
      p M0 uBar vLower locallyConverges neumannResolventGradientBound

/-- Assemble the full Paper3 statement target from the actual-linear thin
Theorem 2.2 mainline route and the proved-positive Paper2 Theorem 1.2/1.3
frontier, without carrying a separate negative-sensitivity residual and without
requiring the full Paper2 main theorem bundle. -/
theorem
    intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegData
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    (hData :
      IntervalDomainPaper3StatementActualLinear22ThinTheorem12And13ProvedPositiveNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound cGrad) :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) := by
  have h23 : Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
    intervalDomainPaper2_Theorems_1_2_and_1_3_of_provedPositiveSolutionInterpolationFrontierData
      p C cGrad hData.paper2Theorems
  exact
    ⟨intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData
        p C
        { negativeBound :=
            intervalDomainPaper3_negativeSensitivityGlobalEventualBound_of_chi_pos
              p hχ0
          theorem12 := h23.1
          theorem13 := h23.2 },
      intervalDomain_paper3_mainlineTargets_of_actualLinear22ThinFrontierData
        p M0 uBar vLower locallyConverges neumannResolventGradientBound
        ha hb hχ0 hm hβ hχ hData.mainline⟩

/-- Instance-facing version of
`intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegData`. -/
theorem
    intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (M0 uBar vLower : ℝ)
    (locallyConverges :
      (ℕ → ℝ → intervalDomain.Point → ℝ) →
        (ℝ → intervalDomain.Point → ℝ) → Prop)
    (neumannResolventGradientBound :
      (mu nu : ℝ) → (intervalDomain.Point → ℝ) → ℝ → Prop)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (ha : 0 < p.a) (hb : 0 < p.b) (hχ0 : 0 < p.χ₀)
    (hm : p.m = 1) (hβ : 1 ≤ p.β)
    (hχ : p.χ₀ < p.a / (p.μ * Theta_beta (p.β - 1)))
    [hData : Fact
      (IntervalDomainPaper3StatementActualLinear22ThinTheorem12And13ProvedPositiveNoNegData
        p C M0 uBar vLower
        locallyConverges neumannResolventGradientBound cGrad)] :
    IntervalDomainPaper3StatementTargets p C M0 uBar vLower
      (intervalDomainSupNormCompactnessData
        locallyConverges neumannResolventGradientBound) :=
  intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegData
    p C M0 uBar vLower locallyConverges neumannResolventGradientBound cGrad
    ha hb hχ0 hm hβ hχ hData.out
```

## If the local branch uses `...ProvedAgmonFrontierData`

The prompt says the preferred Paper2 raw-drop terminal-endpoint route now has a local `...ProvedAgmonFrontierData` with only `section2` and `localAndMain` fields and no `agmon` field. I do not see that exact name in the current default-branch surface exposed to the connector; the visible default-branch theorem12/13 proved-Agmon route is named `...ProvedPositiveSolutionInterpolation...`.

If the local branch has the newer name, use the same wrapper shape but replace the `paper2Theorems` field and call with the local theorem that produces:

```lean
Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C
```

or, if it produces `IntervalDomainPaper2MainTheoremTargets p C`, avoid using the Theorem 1.1 component and extract only:

```lean
hMain.2.1 : Theorem_1_2 intervalDomain p
hMain.2.2 : Theorem_1_3 intervalDomain p C
```

The point of the wrapper remains the same: Paper3 actual-linear NoNeg should not require the full Paper2 main bundle when theorem12/theorem13 are enough.

## Secondary candidate if not already present

If the branch only has the raw-theorem-2.2 `ThinP2MainNoNegData`, the same NoNeg pattern should also be ported to the Moser/integrated-step statement routes:

```lean
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainNoNegData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
```

On the current default branch visible to me, these integrated-step NoNeg variants already exist. On the baseline branch described in the prompt, if they are absent, they are safe pure-wiring patches: copy the exact construction pattern from `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData`, replacing the mainline target theorem with the corresponding integrated-step theorem.

## Do not do next

Do not work in:

```text
ShenWork/PDE/P3MoserHighExcursionProducer.lean
ShenWork/PDE/P3MoserThresholdPlanProducer.lean
```

Do not try to route the `χ₀ = 0` Paper2 local-free wrappers into the actual-linear-small Paper3 route, because the actual-linear route requires:

```lean
0 < p.χ₀
```

while the chi-zero route requires:

```lean
p.χ₀ = 0
```

Those hypotheses are incompatible.

## Bottom line

Best next edit after the current `ActualLinear22ThinP2MainNoNegData` wrapper:

1. Add an actual-linear thin Paper3 wrapper that consumes only Paper2 Theorem 1.2/1.3 proved-Agmon data, not full `IntervalDomainPaper2MainTheoremTargets`.
2. If absent on the local branch, port the same NoNeg pattern to the integrated-step Moser statement routes.

Both are pure statement-assembly wiring and are low conflict.
