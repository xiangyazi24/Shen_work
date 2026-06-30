# Q2340 shen1 — Paper2 preferred χ₀=0 headline frontier audit

Repo audited: `xiangyazi24/Shen_work` main, requested around commit `6eccd68f`.

Files inspected: `ShenWork/Paper2/IntervalDomainStatementAssembly.lean`, `IntervalDomainTheorem11.lean`, `IntervalDomainTheorem12.lean`, `IntervalDomainTheorem13.lean`, `PDE/IntervalDomainExistence.lean`, and `UNDERSTANDING.md`.

## Bottom line

The preferred interval-domain `χ₀ = 0` **Theorem 1.1** route itself is already closed:

```lean
theorem intervalDomain_theorem_1_1_chiZero_unconditional
    (p : CM2Params) (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p
```

and it is exposed in statement assembly as:

```lean
theorem intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
```

So the next net reduction should not try to “prove Theorem 1.1” again.  The best concrete wiring reduction is to make the **preferred χ₀=0 main-theorem headline route** explicit, separate from the full statement-target route that also carries Proposition 1.1 and section-2 targets.

Current preferred full statement wrapper is:

```lean
abbrev IntervalDomainPaper2PreferredChiZeroStatementFrontierData :=
  IntervalDomainPaper2StatementChiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData

theorem intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
```

This is sound and preferred, but it still carries residuals needed only for the **full statement-target bundle**:

* `finiteHorizonAlternative` through `IntervalDomainPaper2Proposition11ChiZeroFrontierData`,
* section-2 thin fields `lemma26`, `lemma27`, `prop22`, `prop23`,
* and the nested Theorem 1.2/1.3 frontiers.

For the main headline bundle, the already-existing target is:

```lean
def IntervalDomainPaper2MainTheoremTargets
    (p : CM2Params) (C : Paper2Constants p) : Prop :=
  Theorem_1_1 intervalDomain p ∧
    Theorem_1_2 intervalDomain p ∧
      Theorem_1_3 intervalDomain p C
```

and the already-existing local-free positive solution-slice route is:

```lean
theorem intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

I recommend adding a grep-visible preferred alias/wrapper for that route.  This is a real interface reduction for headline accounting: it removes the Proposition 1.1 finite-horizon alternative and section-2 thin frontiers from the main-theorem target.  It does not pretend to prove the full `IntervalDomainPaper2StatementTargets`.

## Concrete patch idea

Add near the preferred full-statement alias in `IntervalDomainStatementAssembly.lean`:

```lean
/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem frontier package.

This is the headline route for Theorems 1.1--1.3 only.  It avoids the refuted
`IntervalDomainInterpolation` premise by using the positive solution-slice route,
and it uses the local-free `χ₀ = 0` interface for Theorem 1.2/1.3.  It does not
carry Proposition 1.1 or section-2 target frontiers. -/
abbrev IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ) :
    Prop :=
  IntervalDomainPaper2MainTheoremChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad

/-- Preferred `χ₀ = 0` interval-domain Paper2 main-theorem wrapper.

Pure wiring alias for
`intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData`.
This intentionally targets `IntervalDomainPaper2MainTheoremTargets`, not the full
statement bundle. -/
theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_frontierData
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    (hData :
      IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData p C cGrad) :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
    p C cGrad hχ0 ha hb hα hγ hData

/-- Instance-facing alias for the preferred `χ₀ = 0` main-theorem route. -/
theorem intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_frontierDataFact
    (p : CM2Params) (C : Paper2Constants p)
    (cGrad : (ℝ → intervalDomain.Point → ℝ) → ℝ → ℝ → ℝ → ℝ → ℝ)
    (hχ0 : p.χ₀ = 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ)
    [hData : Fact
      (IntervalDomainPaper2PreferredChiZeroMainTheoremFrontierData p C cGrad)] :
    IntervalDomainPaper2MainTheoremTargets p C :=
  intervalDomainPaper2_preferredChiZeroMainTheoremTargets_of_frontierData
    p C cGrad hχ0 ha hb hα hγ hData.out
```

This is deliberately small.  It does not smuggle a hard theorem as an assumption; it only gives the already-preferred local-free main theorem route the same short name that the full statement route already has.

## Comparison of remaining fields

### `finiteHorizonAlternative`

Current chi-zero Proposition 1.1 frontier:

```lean
structure IntervalDomainPaper2Proposition11ChiZeroFrontierData
    (p : CM2Params) : Prop where
  finiteHorizonAlternative :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
    ∀ Tmax > 0, ∀ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v →
      InitialTrace intervalDomain u₀ u →
        FiniteHorizonAlternative intervalDomain Tmax u ∧
        (1 ≤ p.m → MGeOneFiniteHorizonAlternative intervalDomain Tmax u)
```

The local existence part is already removed by:

```lean
intervalDomainPaper2_Proposition_1_1_of_chiZeroFrontierData
```

which inserts:

```lean
intervalDomain_localExistence_chiZero_unconditional
```

Do not try to remove `finiteHorizonAlternative` by assuming `IntervalDomainPaper2Proposition11FrontierData`; that would reintroduce the old bigger package and undo the reduction.  Also do not claim it follows from `globalExtension`; their shapes differ.  `globalExtension` turns bounded-before solutions into global solutions under `1 ≤ p.m`; `finiteHorizonAlternative` is a maximal-time alternative statement about a finite `Tmax` solution and includes both the base and `m ≥ 1` alternatives.

For main theorem targets, the clean move is to bypass Proposition 1.1 entirely via the preferred main-target wrapper above.  For full statement targets, `finiteHorizonAlternative` remains an honest Cauchy/frontier input.

### `globalExtension`

Current common abbreviation:

```lean
abbrev IntervalDomainPaper2GlobalExtensionFrontier
    (p : CM2Params) : Prop :=
  ∀ u₀, PositiveInitialDatum intervalDomain u₀ →
  ∀ Tmax > 0, ∀ u v,
    IsPaper2ClassicalSolution intervalDomain p Tmax u v →
    InitialTrace intervalDomain u₀ u →
      IsPaper2BoundedBefore intervalDomain Tmax u →
        1 ≤ p.m →
          IsPaper2GlobalClassicalSolution intervalDomain p u v
```

This is still needed for the global branches in Theorem 1.2 and Theorem 1.3.  The existing Theorem 1.2/1.3 assemblies consume it through:

```lean
IntervalDomainTheorem12.Theorem_1_2_intervalDomain_of_corollary21_and_proposition25
IntervalDomainTheorem13.Theorem_1_3_intervalDomain_of_corollary21_and_proposition25
```

There are subcritical wrappers that make the global branch vacuous under `p.m < 1`, e.g. in Theorem 1.3:

```lean
Theorem_1_3_intervalDomain_m_lt_one_regime_of_corollary21_and_proposition25
```

but for the full mixed-regime Theorem 1.2/1.3 headline, `globalExtension` is a genuine remaining continuation frontier.  Do not hide it inside a new “main data” record unless the record name advertises it.

### Section-2 thin fields: `lemma26`, `lemma27`, `prop22`, `prop23`

Current thin package:

```lean
structure IntervalDomainPaper2BootstrapEstimateThinFrontierData
    (p : CM2Params) : Prop where
  lemma26 : ...
  lemma27 : ...
  prop22 : ...
  prop23 : ...
```

It is used by:

```lean
intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
```

Together with the proved mass result:

```lean
intervalDomain_Proposition_2_4
```

and `Proposition_2_5` from the nested Theorem 1.2/1.3 data, this produces the section-2 target bundle.  These fields are not needed for `IntervalDomainPaper2MainTheoremTargets`; they are only needed for `IntervalDomainPaper2StatementTargets`, which includes section-2 targets.

So the preferred main-target wrapper above legitimately removes them from the headline theorem route.  For full statement accounting, they remain honest estimate frontiers.  Do not replace them by `Paper2BootstrapEstimateBranchData` if the purpose is thinning; that would be a regression.

### Solution-slice interpolation / energy

The global interpolation route is explicitly unsafe.  The deprecated wrapper says the global premise is refuted by:

```lean
IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation
```

Avoid these in current headline routes:

```lean
IntervalDomainPaper2InterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13InterpolationFrontierData
intervalDomainPaper2_aprioriTargets_of_GN_frontier
intervalDomainPaper2_statementTargets_of_chiZeroInterpolationFrontierData
```

Preferred route uses positive solution-slice interpolation:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionPositiveInterpolation
IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
IntervalDomainPaper2Theorem12And13ChiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

and the conversion:

```lean
IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionInterpolation_of_positive
```

This is the right residual shape.  It is still analytic, but not known-false and not vacuous.

### `Proposition_2_5`

This is the Lp-to-sup bridge.  It is consumed structurally by:

```lean
IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
```

and carried in the preferred positive solution-slice Theorem 1.2/1.3 data.  The section-2-thin wrapper reuses that nested `prop25`; it does not require a second independent `Prop25` field.

Do not remove `Prop25` unless you actually prove a replacement Lp-to-sup theorem.  A wrapper that simply assumes `boundedBefore` or `Theorem_1_2` would smuggle the hard step.

## Vacuity / known-false warnings

Do not use the global interpolation route as a headline route:

```lean
IntervalDomainLemma41.IntervalDomainInterpolation
```

It is known false as literally stated by:

```lean
IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation
```

Do not advertise a full-statement reduction if the patch only targets:

```lean
IntervalDomainPaper2MainTheoremTargets
```

That is a valid headline theorem target, but it intentionally excludes Proposition 1.1 and section-2 targets.

Do not “reduce” finite-horizon alternative by carrying:

```lean
IntervalDomainPaper2Proposition11FrontierData
```

because that is a larger package containing local existence plus the same finite-horizon alternative.

Do not “reduce” solution-slice interpolation by replacing it with the global interpolation premise.

## Exact names to audit with `#check` / `#print axioms`

For the preferred main-theorem route:

```lean
#check intervalDomain_theorem_1_1_chiZero_unconditional
#check intervalDomainPaper2_Theorem_1_1_chiZero_unconditional
#check intervalDomainPaper2_Theorems_1_2_and_1_3_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
#check intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
#print axioms intervalDomain_theorem_1_1_chiZero_unconditional
#print axioms intervalDomainPaper2_mainTheoremTargets_of_chiZeroPositiveSolutionInterpolationLocalFreeFrontierData
```

For the full preferred statement route:

```lean
#check IntervalDomainPaper2PreferredChiZeroStatementFrontierData
#check intervalDomainPaper2_preferredChiZeroStatementTargets_of_frontierData
#check intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
#print axioms intervalDomainPaper2_statementTargets_of_chiZeroPositiveSolutionInterpolationSection2ThinLocalFreeFrontierData
```

For the known-false/deprecated route:

```lean
#check IntervalDomainInterpolationCounterexample.not_intervalDomainInterpolation
#check intervalDomainPaper2_Lemma_4_1_of_GN_frontier
#check intervalDomainPaper2_aprioriTargets_of_GN_frontier
```

For section-2 thinning:

```lean
#check IntervalDomainPaper2BootstrapEstimateThinFrontierData
#check intervalDomainPaper2_bootstrapEstimateTargets_of_thinFrontierData
#check intervalDomain_Proposition_2_4
#check IntervalDomainTheorem12.boundedBefore_of_corollary21_and_proposition25
```

For solution-slice interpolation and energy:

```lean
#check IntervalDomainPaper2PositiveSolutionInterpolationEnergyFrontierData
#check IntervalDomainTheorem11Composite.IntervalDomainClassicalSolutionInterpolation_of_positive
#check IntervalDomainTheorem11Composite.Corollary_2_1_intervalDomain_of_solution_interpolation_frontier
#check intervalDomainPaper2_aprioriTargets_of_solutionInterpolationFrontier
```

## Recommended next action

Add the preferred main-theorem alias/wrapper above.  It is small, non-smuggling, and clarifies the current status: Paper2 interval `χ₀ = 0` Theorem 1.1 is closed, and the preferred main headline route carries only the Theorem 1.2/1.3 positive solution-slice local-free frontiers.  Keep the existing preferred full-statement wrapper for users who need Proposition 1.1 and section-2 targets; those fields remain genuine residuals.
