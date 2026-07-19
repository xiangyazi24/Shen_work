# DOCTRINE — χ>0 全清通宵跑 (2026-07-19, automode)

## Main goal (one sentence)
Close the remaining 1D headlines of the Shen trilogy: P1 Thm 1.2 full (χ>0 branch,
hhalf : χ<1/2 faithful), then the chained P1 Prop 1.2(2) / Thm 1.3 full / Prop 1.1 χ>0,
plus P2 Lem 2.6 — all 0 sorry, 0 axiom, clean-3, pushed.

## Avenues (ranked)

(a) **Whole-line rectangle squeeze → Prop 1.2(2) critical.**
    Codex phase 2 in flight (brief: codex-brief-chipos-impl2.md + item 0 weighted floor).
    On return: verify against HANDOFF/chipos-squeeze-P0-checklist.md (P0-1 weighted contact,
    P0-2 δ(ε), P0-3 normalization lemma, P0-4 side-of-root invariant), fix, wire the round
    induction with chiPos_squeeze_gap_step_sharp, land
    wholeLineCauchyGlobal_uniformConvergesToConstant_one_of_chi_pos_half.
    Terminal: Proposition12PositiveBranch critical-case theorem builds clean-3 OR written
    proof-of-failure of the squeeze wiring (concrete failing obligation).

(b) **Buffered half-line squeeze + plateau seed → left-eq χ>0 → Thm 1.2 full.**
    Machinery: phase-1 buffered comparisons (refactor to weighted per P0-1), buffer
    closeness (χ-general, done), seed = plateau mirror at trap height MChi+r
    (design doc §seed; positive ledgers exist at heights 1/MChi, χ<1/2).
    Then mirror ChiNegStabilityNatural + headline with hhalf.
    Terminal: paper1_Theorem_1_2 χ>0 branch headline clean-3.

(c) **Supercritical ceiling → Prop 1.1 χ>0.** Blueprint = gpt-Q82 (10 steps, new atom
    rpow_tangent_at_one_of_one_le). Independent of (b) — parallel Codex lane.
    Terminal: Prop 1.1 positive conjunct (critical + supercritical) clean-3; the
    γ=1 division-by-zero formalization bug resolved per Q7 answer (pending).

(d) **Thm 1.3 χ>0 mirror.** After (b). Adaptation points per Q5 answer (pending).
    Terminal: Theorem_1_3_amended full clean-3.

(e) **P2 Lem 2.6 Moser frontier.** 7 hypotheses (IntervalDomainTheorem11.lean:110);
    Q6 answer (pending) classifies easy vs hard; Moser infra 5572 lines exists.
    Independent lane — dispatch Codex when a lane frees.
    Terminal: Lemma_2_6 unconditional OR named-frontier verdict per hypothesis.

## Fallbacks
- Squeeze wiring stalls in Codex → self-grind the round induction (engine committed,
  templates read); Codex re-dispatched on narrower leaf.
- Plateau seed too heavy → 3 concrete attempts, then re-audit against Q4 answer;
  fallback = state left-eq with an explicit seed hypothesis and continue the chain
  (NAMED carried residual, not silent).
- Any keystone unsatisfiable → statement-level fix per assemble-early rule.

## Standing constraints
- 只用 cron 系列 ChatGPT tab（血缘检查已入 ask-gpt.py）。
- 新文件 only；诈尸红线见 CAPSTONE_REGISTRY；trunk green per commit。
- χ∈[1/2,χ*): genuinely open (Q83 verdict) — do NOT attempt tonight; hhalf is the scope.
- Q1-Q7 answers arriving on old-name tabs: harvest + verify + archive as they land.

## AVENUE STATUS (updated during run)

- (a) CLOSED 2026-07-19. `Proposition_1_2_positive_branch_critical`, root build 9912 jobs,
  clean-3, non-vacuity witness landed (WholeLineChiPosRectangleWitness.lean) proving the
  χ<1/2 threshold IS floor-margin positivity at the equilibrium ceiling in the model case.
- (c) IN PROGRESS. Math layer DONE by Fable (atoms + ceiling + supersolution + one-sided
  Lipschitz, all clean-3); mechanical long-time chain dispatched to Codex.
  NEW FINDING (errata, ours): Prop 1.1(2)'s Lean threshold mis-transcribes the paper AND
  is vacuous at γ=1. Faithful encoding + 4 certificates landed
  (Proposition11PositiveErrata.lean). Prop 1.1 positive branch now splits three ways:
    supercritical (all χ>0) — covered once the Codex chain lands;
    critical χ<chiStar — covered by the committed MChi chain;
    critical chiStar ≤ χ < faithful threshold — OPEN, paper uses another argument.
  ⇒ Prop 1.1 will close as a FAITHFUL PARTIAL (two of three windows) unless the third
  window's argument is reconstructed. Do not over-claim.
- (b) NEXT. Q99 (route choice: localize vs transport) in flight on cron4.
- (e) P2 Lem 2.6: phase A landed (4 of 7 hypotheses discharged, clean-3 3584 jobs).
  hdiss verified unsatisfiable at interface level AND circular at chain level; the
  time-integrated Moser replacement is the phase-B design (Q100 in flight on cron5).
