# DOCTRINE — Theorem 1.2 (Paper I) fully UNCONDITIONAL

Run start: 2026-07-12 evening (automode, Xiang asleep).

## Goal (one sentence)
Make `Theorem_1_2_intervalDomain_positive_critical_branch` fully UNCONDITIONAL and NON-VACUOUS: no
`hlocal`/`hglobalExtension` hypotheses, the global bounded solution CONSTRUCTED (not assumed), axiom-clean.

## Why (the defect being fixed)
Q4614 vacuity audit: boundedness CORE is genuine (Lp produced, seed nonempty, guard correct), but the wrapper is
VACUOUS — `hglobalExtension` (`∀ arbitrary u v, sol-on-Tmax ∧ trace ∧ bounded → global`) is PROVABLY FALSE
(IsPaper2ClassicalSolution only pins (0,Tmax); modify u,v after Tmax → counterexample). `#print axioms` clean does NOT
catch this. Fix = construct the CANONICAL global solution, drop the universal-extension assumption.

## Avenues (ranked)
(a) PRIMARY — canonical maximal-continuation construction. Chain:
    local existence (Banach FP on intervalDuhamelOperator + intervalLogisticSource_lipschitz, machinery exists)
    → a-priori L∞ bound on every finite horizon (the affine-restart boundedness, already proven)
    → StandardContinuationAlternative = ReachableArbitrarilyLong ∨ FiniteContinuationAlternativeBranch
    → rule out the finite-blowup branch USING the a-priori L∞ bound
    → ReachableArbitrarilyLong → glue to a canonical global classical solution (∀T reachable)
    → discharge hglobalExtension BY CONSTRUCTION + hlocal.
    Codex#1 owns PositiveCritical.lean + the existence files; already closed `continuation for alpha gamma ge one`.
    API present: ReachableClassicalHorizon/ArbitrarilyLong/StandardContinuationAlternative + extension lemmas
    (IntervalDomainExistence.lean ~2775-2956).
(b) If maximal-continuation gluing too heavy: replace hglobalExtension by the EXISTENTIAL `∃ global u v extending the
    local solution`, proven from local existence + a-priori bound + a bespoke gluing/uniqueness lemma.
(c) FALLBACK — decompose: (i) local-existence lemma (Banach FP), (ii) continuation criterion (a-priori bound ⟹ no
    finite blowup ⟹ ReachableArbitrarilyLong), (iii) gluing/uniqueness to THE canonical solution. Grind each; dispatch
    the hardest sub-lemma to Fable/ChatGPT.

## Known hard points / where to dispatch if stuck
- The continuation criterion "bounded-before on every finite horizon ⟹ no finite-time blowup ⟹ global" — the exact
  form (a-priori L∞ + parabolic regularity ⟹ the maximal existence time is +∞). Dispatch to Fable/ChatGPT if the
  gluing/uniqueness is not already in the repo.
- Local existence for ARBITRARY positive C(Ī) data via the Duhamel contraction (short-time, ball in C([0,T];C(Ī))).
- Uniqueness (to make the constructed solution THE canonical one) — check repo first.

## Terminal conditions
- SUCCESS: Theorem_1_2 positive critical branch with NO hlocal/hglobalExtension; the conclusion's ∃ genuinely
  constructed; re-audited NON-VACUOUS (hypotheses all satisfiable / inhabited) AND axiom-clean
  ([propext,Classical.choice,Quot.sound]).
- BLOCK (rare): a genuinely-missing PDE result not in Mathlib and not constructible from repo infra — documented in
  RUN_LOG with the exact obstruction.

## Discipline
Verify EVERY "close" two ways now: (1) #print axioms clean, (2) hypotheses satisfiable / theorem non-vacuous (the
Q4614 lesson — axiom-clean ≠ non-vacuous). Keep chatgpt-scratch synced (autosync running) so ChatGPT audits see live
code. Do not edit Codex#1's files (one writer/file); coordinate + verify + dispatch.
