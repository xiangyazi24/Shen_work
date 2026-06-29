# PAPER3-NEGATIVEBOUND-CLOSURE-ROUTE

## Bottom line

`IntervalDomainPaper3NegativeSensitivityResidual p` is currently only an abbreviation for

```lean
NegativeSensitivityGlobalEventualBound intervalDomain p
```

It is not closed by Paper2 Theorem 1.1, Paper2 main targets, or any current Paper3 wrapper. The smallest honest next route is to split it into two domain/PDE-specific residuals:

1. global existence plus initial trace for `PositiveInitialDatum` in the negative-sensitivity, `m ≥ 1` regime;
2. an eventual sup-norm bound for such global solutions.

The conversion from those two fields to `IntervalDomainPaper3NegativeSensitivityResidual p` is pure Lean wiring. Proving either field is real analysis.

## 1. Exact current statement shape and difference from Proposition 1.2

In `ShenWork/Paper3/Statements.lean`, the recalled proposition is:

```lean
def Proposition_1_2 (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    ∀ u₀ : D.Point → ℝ, PaperPositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        IsPaper2Bounded D u
```

The residual is:

```lean
def NegativeSensitivityGlobalEventualBound
    (D : BoundedDomainData) (p : CM2Params) : Prop :=
  p.χ₀ ≤ 0 → 1 ≤ p.m →
    ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
      ∃ u v : ℝ → D.Point → ℝ,
        IsPaper2GlobalClassicalSolution D p u v ∧
        InitialTrace D u₀ u ∧
        ∃ M : ℝ, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M
```

In `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`, the interval alias at commit `b98c3a39` is:

```lean
abbrev IntervalDomainPaper3NegativeSensitivityResidual
    (p : CM2Params) : Prop :=
  NegativeSensitivityGlobalEventualBound intervalDomain p
```

Differences from bare `Proposition_1_2 intervalDomain p`:

- `NegativeSensitivityGlobalEventualBound` quantifies over `PositiveInitialDatum`, while `Proposition_1_2` quantifies over the stronger paper-facing `PaperPositiveInitialDatum`.
- It exposes the eventual-bound witness directly as `∃ M, ∀ᶠ t in atTop, ...`.
- `Proposition_1_2` stores the same eventual-bound shape through `IsPaper2Bounded`; in `Paper2/Statements.lean`, `IsPaper2Bounded D u` is definitionally `∃ M, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M`.
- The bridge `Proposition_1_2_of_negativeSensitivityGlobalEventualBound` is pure packaging: it applies `PaperPositiveInitialDatum.toPositive`, then repackages the exposed eventual-bound witness as `IsPaper2Bounded`.

So `negativeBound` is stronger than the final proposition interface. It is not merely a same-as-goal field.

## 2. Existing theorems that nearly produce it

### Pure existing bridge: exact consumer, not producer

```lean
Proposition_1_2_of_negativeSensitivityGlobalEventualBound
```

This consumes the residual and produces `Proposition_1_2`; it does not produce the residual.

### Paper2 Theorem 1.1: blocked as a producer

Paper2 Theorem 1.1 has the tempting negative-sensitivity shape, but it is formally insufficient. Its definition gives, under `p.χ₀ ≤ 0`, branch-local finite-horizon solutions and finite-time sup bounds on `0 < t < Tmax`, plus global classical existence for `1 ≤ p.m` in the positive-logistic and zero-source branches. It does not provide an eventual-in-time sup bound for the global solution, and it takes `PaperPositiveInitialDatum`, not arbitrary `PositiveInitialDatum`.

The no-go theorem in `Paper3/Statements.lean` is decisive:

```lean
theorem not_paper2_theorem_1_1_implies_paper3_proposition_1_2 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2.Theorem_1_1 D p → Proposition_1_2 D p)
```

Therefore any route that claims

```lean
Paper2.Theorem_1_1 intervalDomain p →
  IntervalDomainPaper3NegativeSensitivityResidual p
```

without additional domain/PDE hypotheses would be dishonest.

### Interval-domain Theorem 1.2 critical branch: close only in a narrower regime

`IntervalDomainTheorem12.Theorem_1_2_intervalDomain_critical_branch_of_corollary21_and_proposition25` has the right style of conclusion for positive data:

```lean
0 ≤ p.a → 0 ≤ p.b → 1 ≤ p.β →
p.m = 1 → p.χ₀ < chiBeta p →
∀ u₀ : intervalDomain.Point → ℝ,
  PositiveInitialDatum intervalDomain u₀ →
    ∃ u v,
      IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
      InitialTrace intervalDomain u₀ u ∧
      IsPaper2Bounded intervalDomain u
```

But it requires real residual inputs: `Corollary_2_1`, `Proposition_2_5`, local existence, global extension, the critical bootstrap seed, and the critical long-time boundedness bridge. It also only covers the `p.m = 1`, `p.χ₀ < chiBeta p`, `1 ≤ p.β` branch, not the full `1 ≤ p.m`, `p.χ₀ ≤ 0` residual.

The statement-layer route also packages this through `intervalDomainPaper2_Theorems_1_2_and_1_3_of_solutionInterpolationFrontierData` and positive-solution variants, but those wrappers still carry the same critical eventual-sup frontier and branch restrictions.

### Interval-domain Theorem 1.3 strong-logistic branch: close only under strong logistic hypotheses

`IntervalDomainTheorem13.Theorem_1_3_intervalDomain_global_branch_of_corollary21_and_proposition25` also has a nearby conclusion:

```lean
0 < p.a → 0 < p.b → 0 < p.m → StrongLogisticCondition p C →
1 ≤ p.m →
∀ u₀ : intervalDomain.Point → ℝ,
  PositiveInitialDatum intervalDomain u₀ →
    ∃ u v,
      IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
      InitialTrace intervalDomain u₀ u ∧
      IsPaper2Bounded intervalDomain u
```

Again, it requires `Corollary_2_1`, `Proposition_2_5`, local/global extension, strong bootstrap, and the strong long-time boundedness bridge. It is also a strong-logistic route, not a negative-sensitivity theorem for all `p.χ₀ ≤ 0`, `1 ≤ p.m`.

### Paper2 statement-assembly eventual-sup fields: useful atoms, not producers

The preferred interval Paper2 Theorem 1.2/1.3 frontier data already has atoms shaped like eventual-bound bridges:

```lean
criticalEventualSupBound : ... → ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
strongEventualSupBound : ... → ∃ T₀ M, ∀ t, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M
```

These are good templates for a Paper3 negative-sensitivity decomposition, but they remain assumptions/frontiers in current code.

## 3. Minimal new residual package/decomposition

Add a more atomic interval-domain package near `IntervalDomainPaper3NegativeSensitivityResidual` in `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`. It should not mention Paper2 Theorem 1.1. It should split monolithic `negativeBound` into global-existence and eventual-bound pieces.

Standalone skeleton with imports:

```lean
import ShenWork.Paper3.IntervalDomainStatementAssembly

open Filter
open ShenWork.IntervalDomain
open ShenWork.Paper2

namespace ShenWork.Paper3

noncomputable section

/-- Atomic interval-domain frontiers for Paper3 Proposition 1.2 in the
negative-sensitivity regime.

This is still a residual package.  It separates existence/trace from the
long-time sup-norm bound, so future PDE work can discharge them independently. -/
structure IntervalDomainPaper3NegativeSensitivityFrontierData
    (p : CM2Params) : Prop where
  globalSolution :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ u v : ℝ → intervalDomain.Point → ℝ,
            IsPaper2GlobalClassicalSolution intervalDomain p u v ∧
            InitialTrace intervalDomain u₀ u
  eventualSupBound :
    p.χ₀ ≤ 0 → 1 ≤ p.m →
      ∀ u₀ : intervalDomain.Point → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
      ∀ u v : ℝ → intervalDomain.Point → ℝ,
        IsPaper2GlobalClassicalSolution intervalDomain p u v →
        InitialTrace intervalDomain u₀ u →
          ∃ T₀ M : ℝ,
            ∀ t : ℝ, T₀ ≤ t → intervalDomain.supNorm (u t) ≤ M

/-- Pure packaging from the two atomic negative-sensitivity frontiers to the
existing Paper3 Proposition 1.2 residual. -/
theorem intervalDomainPaper3_negativeSensitivityResidual_of_frontierData
    (p : CM2Params)
    (hData : IntervalDomainPaper3NegativeSensitivityFrontierData p) :
    IntervalDomainPaper3NegativeSensitivityResidual p := by
  intro hχ hm u₀ hu₀
  rcases hData.globalSolution hχ hm u₀ hu₀ with
    ⟨u, v, hglobal, htrace⟩
  rcases hData.eventualSupBound hχ hm u₀ hu₀ u v hglobal htrace with
    ⟨T₀, M, hM⟩
  exact ⟨u, v, hglobal, htrace, M, eventually_atTop.mpr ⟨T₀, hM⟩⟩

end

end ShenWork.Paper3
```

When inserting into `IntervalDomainStatementAssembly.lean`, omit the self-import and namespace/end wrappers; add `open Filter` near the top only if `eventually_atTop`/`atTop` is not already in scope.

Why this is smaller/honester than the current monolithic field:

- `globalSolution` is where local existence, continuation/globalization, positivity class, and parameter branch coverage belong.
- `eventualSupBound` is where the PDE maximum-principle/logistic/long-time estimate belongs.
- The theorem from this package to `IntervalDomainPaper3NegativeSensitivityResidual` is pure packaging and cannot be mistaken for analysis.

## 4. Pure wiring vs real new analysis

### Pure wiring

- `Proposition_1_2_of_negativeSensitivityGlobalEventualBound`.
- The interval alias `IntervalDomainPaper3NegativeSensitivityResidual`.
- The proposed `intervalDomainPaper3_negativeSensitivityResidual_of_frontierData` theorem.
- Converting `∃ T₀ M, ∀ t ≥ T₀, supNorm ≤ M` into `∃ M, ∀ᶠ t in atTop, supNorm ≤ M` with `eventually_atTop.mpr`.
- Unpacking `IsPaper2Bounded.eventually_bound` if an existing branch theorem produces `IsPaper2Bounded`.

### Real analysis still needed

- A global solution/trace theorem for **all** `PositiveInitialDatum intervalDomain u₀` under `p.χ₀ ≤ 0`, `1 ≤ p.m`, not just `PaperPositiveInitialDatum` and not just the Paper2 Theorem 1.1 finite-horizon package.
- A long-time sup-norm estimate for those global solutions. The current no-go shows that Paper2 Theorem 1.1's finite-`Tmax` bound alone cannot provide this under the abstract API.
- Parameter-branch coverage. Paper2 Theorem 1.2 critical branch covers `m = 1`, `χ₀ < chiBeta p`, `1 ≤ β`; Paper2 Theorem 1.3 covers strong logistic hypotheses; neither covers the full `p.χ₀ ≤ 0`, `1 ≤ p.m` residual.
- If the intended PDE route uses Paper2 Theorem 1.1, extra interval-domain assumptions must explicitly bridge the gaps: initial-data class, global-in-time propagation of the finite-horizon sup bound, and branch coverage for the allowed logistic parameters.

## Recommended smallest follow-up edit

Add only the new `IntervalDomainPaper3NegativeSensitivityFrontierData` structure and the pure packaging theorem above. Then update `IntervalDomainPaper3Proposition1FrontierData` documentation to say its `negativeBound` field can now be supplied either monolithically or via `intervalDomainPaper3_negativeSensitivityResidual_of_frontierData`.

Do **not** replace `negativeBound` fields everywhere yet; that would be churn. Do **not** add any theorem deriving this residual from Paper2 Theorem 1.1 or Paper2 main targets without the extra PDE-specific frontiers, because that would conflict with `not_paper2_theorem_1_1_implies_paper3_proposition_1_2`.
