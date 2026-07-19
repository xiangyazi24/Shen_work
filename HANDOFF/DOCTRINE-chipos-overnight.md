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

## Operational lesson (2026-07-19, cost: one wasted full-tree verification)

NEVER edit an existing file in a working tree while a Codex lane is live there:
Codex reverts the tree to a clean state, silently discarding the edit AND
invalidating any build/axiom verification run against it. During a live lane,
restrict yourself to NEW files (Codex leaves them alone), HANDOFF docs, and
analysis. Afterwards: reapply, `git status` to confirm the edit survived, verify,
and commit IMMEDIATELY — uncommitted work is not safe in a concurrent tree.

## AVENUE STATUS v2 (2026-07-19, late)

- (a) CLOSED. Prop 1.2(2) χ>0 critical. Q98 adversarial audit: PASS.
- (c) CLOSED for both windows the ceiling method can reach:
  `Proposition_1_1_positive_critical_branch` (now χ<1 after the regime weakening)
  and `Proposition_1_1_positive_supercritical_branch` (all χ>0), plus the combined
  `Proposition_1_1_positive_branches_of_regime` = the paper's (1.10).
  Residual: critical 1 ≤ χ < faithful threshold — MChi undefined there, needs the
  paper's local-Lp route (Q103 gives the full recipe if we take it up).
- (e) Lem 2.6 practical content CLOSED hdiss-free; abstract predicate documented
  as unsound. No headline depended on it.
- (b) THE LAST PIECE of P1 Thm 1.2 χ>0: buffered half-line successor.
  Abstract layer committed. Implementation spec written by hand:
  HANDOFF/fable-halfline-successor-spec.md (R(δ) choice, moving cut, both
  weighted contact inequalities, buffer boundary supply, seed decomposition).
  One genuinely missing producer: the χ>0 persistent-plateau floor seed — route
  fixed (mirror the χ≤0 chain with the positive ledgers at trap height MChi+r).
- (d) Thm 1.3 χ>0: unblocked once (b) lands; adaptation inventory = gpt-Q74 (A–G).
