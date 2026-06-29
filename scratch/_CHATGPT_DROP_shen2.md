# Q2230 R3 Paper3 `negativeBound` residual audit for `Shen_work` main `e3aa461e`

## Classification

`negativeBound : NegativeSensitivityGlobalEventualBound ...` is a **genuine analytic residual**, not pure packaging, not currently wireable by a small existing theorem chain, and not a deprecated/same-as-goal declaration.

There is already a tiny packaging bridge:

```lean
Proposition_1_2_of_negativeSensitivityGlobalEventualBound
```

So once `NegativeSensitivityGlobalEventualBound D p` is supplied, Paper3 Proposition 1.2 is immediate. But the repo currently does not contain a producer of `NegativeSensitivityGlobalEventualBound` itself. It is the residual producer that must still be proved analytically.

## What the residual requires

In `ShenWork/Paper3/Statements.lean`, `Proposition_1_2` asks, under `p.χ₀ ≤ 0` and `1 ≤ p.m`, that every **paper-positive** initial datum has a global classical solution, trace, and `IsPaper2Bounded D u`.

Nearby, `NegativeSensitivityGlobalEventualBound D p` asks, under the same parameter inequalities, that every `PositiveInitialDatum D u₀` has global solution, trace, and an explicit eventual sup-norm bound:

```lean
p.χ₀ ≤ 0 → 1 ≤ p.m →
  ∀ u₀ : D.Point → ℝ, PositiveInitialDatum D u₀ →
    ∃ u v : ℝ → D.Point → ℝ,
      IsPaper2GlobalClassicalSolution D p u v ∧
      InitialTrace D u₀ u ∧
      ∃ M : ℝ, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M
```

This is not merely identical to `Proposition_1_2`: it is a stronger, more analytic interface. It quantifies over `PositiveInitialDatum` rather than only `PaperPositiveInitialDatum`, and it exposes the eventual sup-norm witness directly. The conversion to `Proposition_1_2` uses `PaperPositiveInitialDatum.toPositive` and packages the eventual bound as `IsPaper2Bounded`.

For comparison, `IsPaper2Bounded D u` in `ShenWork/Paper2/Statements.lean` is definitionally:

```lean
∃ M, ∀ᶠ t in atTop, D.supNorm (u t) ≤ M
```

So `NegativeSensitivityGlobalEventualBound` is exactly the analytic global-existence-plus-eventual-bound input needed for Proposition 1.2, in a form slightly stronger than the final recalled Paper3 proposition.

## Existing routing: where `negativeBound` is consumed

### Generic Paper3 routing

In `ShenWork/Paper3/StatementAssembly.lean`:

- `Paper3Proposition1FrontierData` has fields
  - `negativeBound : NegativeSensitivityGlobalEventualBound D p`,
  - `proposition13`,
  - `proposition14`.
- `paper3_proposition1Targets_of_frontierData` maps `negativeBound` through `Proposition_1_2_of_negativeSensitivityGlobalEventualBound` and maps the other two fields through assumed existence branches.
- `Paper3Proposition1FromPaper2TheoremsData` replaces only the Proposition 1.3/1.4 fields with Paper2 `Theorem_1_3` and `Theorem_1_2`; it still has `negativeBound`.
- `Paper3Proposition1FromPaper2MainTargetsData` replaces the Paper2 theorem fields by `Paper2.Paper2MainTheoremTargets`, but still has `negativeBound`.
- `paper3_proposition1Targets_of_paper2MainTargetsData` extracts only `main.2.1` and `main.2.2` for Paper2 Theorems 1.2 and 1.3. It does not use `main.1` to produce Proposition 1.2.

Current main already has good comments here saying that `negativeBound` is independent and not derived from Paper2 Theorem 1.1.

### Interval-domain Paper3 routing

In `ShenWork/Paper3/IntervalDomainStatementAssembly.lean`:

- `IntervalDomainPaper3Proposition1FrontierData` has
  - `negativeBound : NegativeSensitivityGlobalEventualBound intervalDomain p`,
  - `criticalExistence` for Proposition 1.4.
- `IntervalDomainPaper3Proposition1FromPaper2TheoremsData` still has `negativeBound` plus Paper2 Theorem 1.2/1.3 fields.
- `IntervalDomainPaper3Proposition1FromPaper2MainTargetsData` still has `negativeBound` plus `paper2Main`.
- `intervalDomain_paper3_proposition1WithTheorem13Targets_of_paper2MainTargetsData` delegates to the generic Paper3 main-target bridge; Paper2 main is used only for Proposition 1.3/1.4.

Current main already documents this correctly in the interval-domain main-target route.

## Why it is not currently wireable

### 1. Paper2 Theorem 1.1 is formally insufficient

`ShenWork/Paper3/Statements.lean` contains the formal no-go theorem:

```lean
theorem not_paper2_theorem_1_1_implies_paper3_proposition_1_2 :
    ¬ (∀ D : BoundedDomainData, ∀ p : CM2Params,
        Paper2.Theorem_1_1 D p → Proposition_1_2 D p)
```

The proof builds `proposition12CounterDomain`, `proposition12CounterParams`, and `proposition12CounterU`, proves

```lean
proposition12Counter_paper2_theorem_1_1 :
  Paper2.Theorem_1_1 proposition12CounterDomain proposition12CounterParams
```

and then derives a contradiction from any alleged eventual bound. This directly blocks the tempting route

```lean
Paper2.Theorem_1_1 D p → NegativeSensitivityGlobalEventualBound D p
```

because such a route would imply `Paper2.Theorem_1_1 D p → Proposition_1_2 D p` by composition with `Proposition_1_2_of_negativeSensitivityGlobalEventualBound`, contradicting the no-go theorem.

### 2. Paper2 main targets do not fill the gap

`Paper2MainTheoremTargets D p C` is the tuple

```lean
Theorem_1_1 D p ∧ Theorem_1_2 D p ∧ Theorem_1_3 D p C
```

But the Paper3 bridge from Paper2 main targets uses only Theorems 1.2 and 1.3 for Propositions 1.4 and 1.3. It leaves `negativeBound` as a separate field. There is no current wrapper projecting `main.1` or any combination of `main.1`, `main.2.1`, and `main.2.2` into `NegativeSensitivityGlobalEventualBound`.

That is correct: the no-go theorem rules out any API-level derivation from `Theorem_1_1` alone, and Theorems 1.2/1.3 cover different regimes/branches rather than the full `p.χ₀ ≤ 0`, `1 ≤ p.m` negative-sensitivity Proposition 1.2 interface.

### 3. Paper2 Theorem 1.2-style eventual-bound frontiers are regime-specific and conditional

Paper2 interval Theorem 1.2 machinery does contain eventual-sup/global-bound fields, but those are conditional branch inputs such as critical/strong eventual-sup frontiers. For example `IntervalDomainTheorem12.lean` explicitly states that Theorem 1.2 still leaves Cauchy theory, branch bootstrap seeds, `Proposition_2_5`, and critical long-time boundedness/eventual-sup frontiers as named hypotheses. These are not a ready-made global `NegativeSensitivityGlobalEventualBound intervalDomain p` producer.

### 4. Repository search did not reveal a producer

Searches for `NegativeSensitivityGlobalEventualBound`, `negativeBound :`, `GlobalEventualBound`, and related “eventual bound / negative sensitivity” phrases surfaced the definition and routing structures in Paper3, plus documentation/status files. They did not reveal a theorem of shape:

```lean
... : NegativeSensitivityGlobalEventualBound D p
```

or

```lean
... : NegativeSensitivityGlobalEventualBound intervalDomain p
```

outside the existing pass-through/proposition-routing packages.

## Not same-as-goal and not deprecated

It is close to the goal, but not a suspicious same-as-goal field. It is a deliberately stronger analytic interface:

- uses `PositiveInitialDatum`, then the bridge consumes `PaperPositiveInitialDatum.toPositive`;
- exposes the exact eventual sup-norm witness used to build `IsPaper2Bounded`;
- is reusable independently of the recalled Paper3 proposition statement.

It is also not deprecated. The no-go theorem says only that this residual cannot be obtained from Paper2 Theorem 1.1 under the current abstract API. It does not say the residual is false or vacuous; it says it needs extra analytic input or a narrower, more concrete domain/API where the missing eventual bound is actually proved.

## Smallest honest next edit

The smallest useful edit is documentation at the definition site, plus optionally a named interval alias for readability.

### Required doc edit

Add this doc comment immediately above `NegativeSensitivityGlobalEventualBound` in `ShenWork/Paper3/Statements.lean`:

```lean
/-- Analytic residual used to prove Paper3 Proposition 1.2: global existence
and eventual-in-time boundedness in the negative-sensitivity regime.

This is stronger than the final recalled Proposition 1.2 interface because it
quantifies over `PositiveInitialDatum` and exposes the eventual sup-norm witness
that becomes `IsPaper2Bounded`.  It is not supplied by Paper2 Theorem 1.1 under
the current abstract API; see
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

This changes no theorem interface and no proof.

### Optional readability alias

If the interval-domain route is where people keep misreading the field, add an alias in `ShenWork/Paper3/IntervalDomainStatementAssembly.lean` near the proposition-routing section:

```lean
/-- Interval-domain abbreviation for the independent Paper3 Proposition 1.2
negative-sensitivity residual.  This is not produced by Paper2 main targets. -/
abbrev IntervalDomainPaper3NegativeSensitivityResidual
    (p : CM2Params) : Prop :=
  NegativeSensitivityGlobalEventualBound intervalDomain p
```

Then future structures can use the alias in new code, but do not rewrite existing fields yet. Rewriting all existing fields is unnecessary churn.

### Do not do this

Do not add any theorem claiming:

```lean
Paper2.Theorem_1_1 D p → NegativeSensitivityGlobalEventualBound D p
```

or

```lean
IntervalDomainPaper2MainTheoremTargets p C →
  NegativeSensitivityGlobalEventualBound intervalDomain p
```

unless it includes additional hypotheses strong enough to avoid the formal no-go theorem. Any such theorem without extra analytic/domain-specific assumptions would imply the refuted `Paper2.Theorem_1_1 → Proposition_1_2` route.

## Final status

`negativeBound` is an honest, live Paper3 Proposition 1.2 analytic residual. Existing code already routes it correctly once supplied. The only immediate cleanup needed is a stronger doc comment at the definition site and, optionally, a narrow interval-domain alias to make the residual status grep-visible.
