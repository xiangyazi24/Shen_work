# Q2754 (shen1) — next low-conflict non-Zinan wrapper after actual-linear NoNeg

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Source edit requested: none; answer file only.

Off-limits producer files, not inspected or used:

- `ShenWork/PDE/P3MoserHighExcursionProducer.lean`
- `ShenWork/PDE/P3MoserThresholdPlanProducer.lean`

## What I could verify from the connector-visible repo surface

The connector-visible default branch exposes the proved Agmon/positive-solution route through these names in `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`:

```lean
IntervalDomainPaper2ProvedPositiveSolutionInterpolationEnergyFrontierData
IntervalDomainPaper2ProvedPositiveSolutionInterpolationEnergyFrontierData.toPositive
IntervalDomainPaper2Theorem12And13ProvedPositiveSolutionInterpolationFrontierData
intervalDomainPaper2_Theorems_1_2_and_1_3_of_provedPositiveSolutionInterpolationFrontierData
```

The exact local name mentioned in the prompt,

```text
...ProvedAgmonFrontierData
```

is not visible in the connector’s current default-branch code search/fetch surface; I only see that wording in docs/doctrine. So I will not invent that exact identifier. The wrapper below uses the verified default-branch names. If the local branch has the newer `...ProvedAgmonFrontierData` with fields `section2` and `localAndMain`, use the same pattern and replace the Paper2 theorem12/theorem13 call with the local theorem that produces either

```lean
Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C
```

or

```lean
IntervalDomainPaper2MainTheoremTargets p C
```

and then extract only `.2.1` and `.2.2`.

## Recommendation

After the current local NoNeg wrapper

```lean
IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData
```

the next lowest-conflict reduction is to remove the **full Paper2 main theorem bundle** from the actual-linear Paper3 proposition surface.

The current NoNeg wrapper still carries:

```lean
paper2Main : IntervalDomainPaper2MainTheoremTargets p C
```

but the Paper3 Proposition 1.3/1.4 part needs only:

```lean
Theorem_1_2 intervalDomain p
Theorem_1_3 intervalDomain p C
```

Paper2 Theorem 1.1 is not consumed by `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2TheoremsData`. Therefore the next wrapper should consume the proved-positive Paper2 Theorem 1.2/1.3 route directly and keep the Paper3 actual-linear mainline unchanged.

Target file:

```text
ShenWork/Paper3/IntervalDomainActualLinearStatementAssembly.lean
```

Suggested names:

```lean
IntervalDomainPaper3StatementActualLinear22ThinTheorem12And13ProvedPositiveNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegData
intervalDomain_paper3_statementTargets_of_actualLinear22ThinTheorem12And13ProvedPositiveNoNegDataFact
```

This is **pure wiring**, not a mathematical frontier. It composes already-proved/wrapped declarations and removes an unnecessary Paper2 Theorem 1.1 input from this Paper3 route.

## Patch sketch against visible default-branch identifiers

Place after the existing `IntervalDomainPaper3StatementActualLinear22ThinP2MainNoNegData` block.

```lean
/-- Full Paper3 statement frontiers in the actual-linear-small regime, with
negative sensitivity discharged by `0 < χ₀` and Paper3 Proposition 1.3/1.4
routed through the proved-positive Paper2 Theorem 1.2/1.3 frontier, not through
the full Paper2 main theorem bundle. -/
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
requiring full Paper2 main theorem targets. -/
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

/-- Instance-facing version of the proved-positive Theorem 1.2/1.3 NoNeg
actual-linear thin route. -/
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

## Variant if the local branch exposes `...ProvedAgmonFrontierData`

If the local branch has a preferred Paper2 route such as:

```lean
IntervalDomainPaper2MainTheoremRawDropTerminalEndpointProvedAgmonFrontierData
intervalDomainPaper2_mainTheoremTargets_of_rawDropTerminalEndpointProvedAgmonFrontierData
```

or similar, do **not** guess the name in the patch. Use the exact local identifier and define the Paper3 data field as that local data type:

```lean
paper2 : <exact local ...ProvedAgmonFrontierData name> p C
```

Then either:

```lean
have hMain : IntervalDomainPaper2MainTheoremTargets p C :=
  <local theorem> p C hData.paper2
have h23 : Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  ⟨hMain.2.1, hMain.2.2⟩
```

or if the local theorem already returns the pair:

```lean
have h23 : Theorem_1_2 intervalDomain p ∧ Theorem_1_3 intervalDomain p C :=
  <local theorem12/13 theorem> p C hData.paper2
```

The rest of the Paper3 proof is exactly the same.

## Secondary candidate

If the local branch only added the raw-Theorem-2.2 thin NoNeg wrapper, port the same NoNeg pattern to the integrated-step Moser surfaces:

```lean
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepP2MainNoNegData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepStability24P2MainNoNegData
IntervalDomainPaper3StatementMoserActualLinearSmallIntegratedStepThinP2MainNoNegData
```

On the current default branch visible to me, these integrated-step NoNeg variants already exist. On the baseline branch in the prompt, if they are absent, they are safe pure-wiring copies of the current `ActualLinear22ThinP2MainNoNegData` pattern.

## Do not do next

Do not route `χ₀ = 0` Paper2 local-free wrappers into this actual-linear Paper3 route. The actual-linear route assumes:

```lean
0 < p.χ₀
```

while chi-zero wrappers assume:

```lean
p.χ₀ = 0
```

Those regimes are incompatible.

Do not work in high-excursion or threshold-plan producer files for this task.

## Bottom line

Best next edit: add the actual-linear thin Paper3 wrapper consuming Paper2 Theorem 1.2/1.3 proved-Agmon/proved-positive data directly, not full Paper2 main theorem targets. It is pure statement-assembly wiring and reduces the headline input surface without touching Zinan-owned producer files.
