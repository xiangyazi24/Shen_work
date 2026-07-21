# DOCTRINE — clear every outstanding condition to a clean proof (2026-07-21, automode)

Supersedes the 2026-07-17 5-frontier doctrine (kept below in git history).

**Goal (one sentence):** discharge every smuggled/hard condition in `OUTSTANDING_MAP.md`
so each paper headline is either genuinely proved (unconditional or only inherent
hypotheses) or a correct replacement of a wrong paper statement — 0 sorry, 0 axiom.

Detail per item: `OUTSTANDING_MAP.md`. Verified per-headline status:
`THEOREM_LIST_BY_PAPER.md`. Method: I ORCHESTRATE (heavy context) — dispatch each deep
piece to a fresh-context sub-agent with a precise brief (exact producers + file:line),
fire ChatGPT (cron1-7) design/audit questions in parallel, verify-don't-transcribe every
return (#print axioms clean-3 + root build), commit per landed lemma. Codex is OUT this
session; sub-agents + ChatGPT are the parallel compute.

**Check-existing gate (from the old doctrine's stale-vs-real conflict):** the 2026-07-17
doctrine claims several CONCRETE-layer items already proved on `intervalDomain`/`intervalDomainM`
that my abstract-focused audit listed as outstanding (e.g. `intervalDomain_Proposition_2_2/2_4/2_5`,
`Lemma_2_6_intervalDomain_of_...`, `Corollary_2_1_intervalDomain_of_...`). BEFORE grinding any
P2/P3 lemma, grep the concrete name and #print axioms — do NOT reinvent what the concrete layer
already has. Reconcile the map on each such find.

## Avenues (ranked; grind in order, each to a terminal verdict)

- **(a) O-P1-1b — Rothe-wave `TravelingWaveRegularity`** → completes P1 Thm 1.2 for χ≤0.
  Crux: bootstrap `ContDiff ℝ 2 U` for the stationary negative wave from `stationary_eq`
  (step-level ContDiff 2 exists: `PaperLocalFixedStepData.contDiff_two`,
  `WaveNegativeSelfStepClosedGraph:110`; stationary producer
  `paperNegativePinned_fixed_stationary_of_selfStep` stops at differentiability). Then feed
  trap + analytic-step + `ContDiff 2 V` (`WavePaperRotheProducer:4142`) into
  `FrozenStationaryWaveProfile.travelingWaveRegularity_of_green_step`; compose into
  `paper1_Theorem_1_2_chi_nonpos_unconditional` mirroring the pos version.
  Terminal: chi_nonpos stability unconditional-in-wave, clean-3; OR a proof the Rothe wave
  genuinely lacks C² (counterexample).
- **(b) O-P3-1 — eventual → all-time** for `intervalDomainM` Thms 2.1–2.5.
- **(c) O-P2-3 / O-P3-3 — the analytic lemma stacks** (Neumann-semigroup / sectorial /
  energy on the interval domain) — AFTER reconciling which are already concrete-proved.
- **(d) O-P2-1 / O-P2-2 / O-P3-2** — cross-diffusion slow branch, strong-logistic, non-vacuity.
- **(e) O-P1-4 — Prop 1.1** general Cauchy existence + a-priori bounds for arbitrary data.
- **(f) research edge — P1 [½, chiStar), then far-left → (1+√α)²** (`INJECTION_PLAN.md`).

## Fallbacks / rules
- Deep piece resists self + sub-agent → pin to ONE exact statement, maximize surrounding
  verifiable scaffolding, keep grinding (never "needs fresh context" to the user).
- Assemble each headline end-to-end EARLY to surface an unsatisfiable keystone.
- Conditional milestone ≠ done until every carried hypothesis is witnessed satisfiable.
- Report only verified-stable state (green build + hash), never exploration churn.
