# General-`m` checklist — Shen trilogy (2026-07-24)

Scope: the `u^m` chemotactic-flux generalization (`intervalDomainM`) of the
bounded-domain Paper 3 headlines (`m = 1` → general `m ≥ 1`). Paper 1 (whole-line
traveling wave) and Paper 2 (linear-flux mild theory) are `m = 1` by design;
general-`m` is a Paper 3 concern. Source of truth: mini handoff 2026-07-23 +
repo scan. Knock off one by one.

## CATEGORY A — proved general-`m` headlines, NOT imported (integration only)
Mechanical: add the import to `ShenWork.lean`, root-build, confirm clean-3.
Targeted remote build already passed 9066 jobs (handoff). No new math.

- [ ] **A1. Thm 2.2-m** — `ShenWork.Paper3.IntervalDomainMMinimalFaithfulTheorem22`
      headline `intervalDomainM_Theorem_2_2_minimalEventual_branch_unconditional`
- [ ] **A2. Thm 2.3-m** — `ShenWork.Paper3.IntervalDomainMTheorem23Eventual`
      headline `intervalDomainM_Theorem_2_3_positiveEventual` (+ χ≤0 global minimal)
- [ ] **A3. Thm 2.4-m** — `ShenWork.Paper3.IntervalDomainMTheorem24Eventual`
      headline `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula`

(Already imported general-m: Thm 2.3 AllTimeC1, Thm 2.3 RestartDuhamel, Thm 2.2
FaithfulTheorem22 — verify which headline each carries during A.)

## CATEGORY B — missing general-`m` (genuinely new, beyond-paper)
- [ ] **B1. Thm 2.5-m** — no `IntervalDomainMTheorem25*` file exists (only the
      `m = 1` `IntervalDomainTheorem25Eventual`). Handoff item 2. Assess
      tractability (ChatGPT) then build or record as deliberate scope stop.
- [ ] **B2. Thm 2.1-m** — no `IntervalDomainMTheorem21*` file. Assess whether
      Thm 2.1 (existence/well-posedness class) is ALREADY covered by the general-m
      existence files (`IntervalDomainMSmallDataGlobalExistence`,
      `IntervalDomainMMinimalSmallDataGlobalExistence`) — may be a naming gap, not
      a math gap. Verify before treating as new work.

## CATEGORY C — in-progress dynamic producer (handoff item 3, Paper 1)
- [~] **C1. Paper 1 far-left χ≤4−δ** dynamic localized entropy producer.
      LANDED (clean-3): weighted entropy engine + real-orbit bridge + dt-wrapper.
      OPEN crux: the anti-escape floor (log-entropy coercivity fails as u→0).
      This is beyond-paper; not an m-generalization. Tracked separately in RUN_LOG.

## Order of attack
A1→A2→A3 (integration, verify clean-3 in root closure) → B2 (likely a non-gap,
cheap to resolve) → B1 (real new math, ChatGPT-assess first) → C1 continues.
