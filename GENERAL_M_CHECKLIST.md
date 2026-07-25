# General-`m` checklist — Shen trilogy (2026-07-24)

Scope: the `u^m` chemotactic-flux generalization (`intervalDomainM`) of the
bounded-domain Paper 3 headlines (`m = 1` → general `m ≥ 1`). Paper 1 (whole-line
traveling wave) and Paper 2 (linear-flux mild theory) are `m = 1` by design;
general-`m` is a Paper 3 concern. Source of truth: mini handoff 2026-07-23 +
repo scan. Knock off one by one.

## CATEGORY A — proved general-`m` headlines, NOT imported (integration only)
Mechanical: add the import to `ShenWork.lean`, root-build, confirm clean-3.
Targeted remote build already passed 9066 jobs (handoff). No new math.

- [x] **A1. Thm 2.2-m** — `ShenWork.Paper3.IntervalDomainMMinimalFaithfulTheorem22`
      headline `intervalDomainM_Theorem_2_2_minimalEventual_branch_unconditional`
- [x] **A2. Thm 2.3-m** — `ShenWork.Paper3.IntervalDomainMTheorem23Eventual`
      headline `intervalDomainM_Theorem_2_3_positiveEventual` (+ χ≤0 global minimal)
- [x] **A3. Thm 2.4-m** — `ShenWork.Paper3.IntervalDomainMTheorem24Eventual`
      headline `intervalDomainM_Theorem_2_4_EventualGlobalStabilityFormula`

(Already imported general-m: Thm 2.3 AllTimeC1, Thm 2.3 RestartDuhamel, Thm 2.2
FaithfulTheorem22 — verify which headline each carries during A.)

## CATEGORY B — missing general-`m` (genuinely new, beyond-paper)
- [ ] **B1. Thm 2.5-m** — no `IntervalDomainMTheorem25*` file exists (only the
      `m = 1` `IntervalDomainTheorem25Eventual`). Handoff item 2. Assess
      tractability (ChatGPT) then build or record as deliberate scope stop.
- [x] **B2. Thm 2.1-m** — RESOLVED: non-gap. — no `IntervalDomainMTheorem21*` file. Assess whether
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

## Status (2026-07-24)
- SYNC: done (merged mini's far-left scope correction + my weighted-entropy work; origin/main=c496e263; root build 10100 jobs).
- A1/A2/A3: DONE — 3 general-m headlines integrated into ShenWork.lean closure, clean-3, pushed.
- B2: RESOLVED non-gap — general-m existence is intervalDomainM_smallDataGlobalExistence_of_linearlyStable (Thm 2.1 covered, just not named 2.1).
- B1 (Thm 2.5-m): GENUINELY NEW — general-m minimal eventual-stability producers (minimal1/minimal2 analogs) do NOT exist; must be built mirroring the done nonminimal Thm 2.4-m. ChatGPT design fired (Q984). BLOCKED ON IMPLEMENTATION VEHICLE: Codex out of credits until 2026-07-28; conserving Claude per directive.
- C1 (far-left χ≤4−δ): engine+bridge+dt-wrapper landed clean-3; floor is open crux; ChatGPT quadratic-entropy floor-free angle fired.

## B1 refined scope (ChatGPT Q984 verdict, 2026-07-24)
Thm 2.5-m is DOABLE (no fundamental obstruction), but genuinely new (not a mirror).
Minimal equilibrium (a=b=0) = mass-parametrized family (u*, (ν/μ)u*^γ); constant mode
NEUTRAL (no logistic damping) ⇒ work on the physical-mass hyperplane, Poincaré after
removing mean. ALREADY proved for general-m (reuse): mass-constrained local bootstrap
intervalDomainM_minimal_eventualC1_of_uniformSup_of_massGap, the χ₀≤0 branch (Thm 2.3-m),
Stage B. SINGLE NEW CRUX: general-m, positive-χ₀, ORBIT-INDEPENDENT EVENTUAL UPPER BOX
for u (the m=1 eventual-box producer casts intervalDomain↔intervalDomainM via the m=1
equality — no general-m version exists). Given u≤uBar, the signal floor vLower is benign
(conserved positive mass + elliptic resolver). Key functional: relative entropy
E=∫[u−u*−u* log(u/u*)] on the mass hyperplane. → Build target when a vehicle is available:
the general-m eventual upper box, then assemble via existing minimal machinery.
BLOCKED: Codex out until 2026-07-28; conserving Claude.

## C1 resolved (ChatGPT Q985, 2026-07-24) — the floor is FUNDAMENTAL, not removable
Quadratic/matrix-Lyapunov floor-free angle: NEGATIVE and instructive. There is no
floor-free unconditional far-left threshold by ANY entropy/Lyapunov method. Reason:
bistability — the system has the competing equilibrium (u,v)=(0,0); since v−1 is
elliptically slaved (v−1=(1−∂zz)⁻¹(u−1)), every translation-invariant positive
quadratic/matrix functional is a positive Fourier multiplier × the same scalar symbol,
so it cannot change the sign threshold and cannot separate the u=1 and u=0 basins.
The quadratic entropy gives a clean LOCAL/BASIN theorem for all χ<4, but the basin
condition itself IS the floor u≥1−ρ>0. This MATCHES the mini scope-correction
(global uniform convergence to 1 is FALSE for the co-moving self-front). So:
CONCLUSION: the anti-escape floor is the CORRECT PHYSICAL SCOPE (stay in the u=1
basin), not a gap to remove. The honest clean deliverable is the χ<4 BASIN-CONDITIONAL
far-left theorem, which the landed weighted-entropy engine + orbit bridge + dt-wrapper
now support. Remaining build (needs a vehicle): the discharge engine ⇒ basin-conditional
far-left χ<4. This CLOSES the "can we get χ<4 floor-free" research question: no.

## B1 BUILD-READY (ChatGPT Q1003, 2026-07-24) → see SPEC_thm25m_FINAL.md
Thm 2.5-M tractable for 1≤m<2 (subcritical). Exact obstruction: exponent coincidence
P+2m−2=P ⟺ m=1. M-native fix: scalar_seed_agmon_absorb (1D GN/Agmon), closes m<2;
m=2 critical, m>2 supercritical. Final Lp→L∞ already general-m
(solutionSlice_le_of_restart_affine_lp_general). ONE new lemma: orbit-independent
eventual L^P bound M-native for 1≤m<2. Rest reuses existing general-m machinery.
Build-ready; awaiting vehicle (Codex 7/28 or Claude go-ahead).

## B1 STATUS CORRECTION (2026-07-25, verified) — two halves, not one crux
CORRECTION: I earlier relayed "step 5 is mostly wiring, Thm 2.5-M is close" — that was a
SIGN ERROR, now caught + verified. Reality: Thm 2.5-M has TWO halves:
1. UPPER BOX (eventual L∞ bound, the ChatGPT-Q1003 "crux"): LANDED for 1≤m<2 on branch
   thm25m-wip — seed + eventual_lp + high_lp + uniform_upper_bound compile clean (8908 jobs).
   The two "errors" were wiring (namespace + import), fixed. REAL progress.
2. χ>0 MINIMAL CONVERGENCE: GENUINELY NEW multi-lemma work, NOT wiring (verified):
   - minimal_completeLyapunov_frontier is χ₀≤0 ONLY (IntervalDomainEnergyDissipation.lean:488);
     Thm 2.5 minimal condition requires 0<χ₀ (Statements.lean:3596) — direct contradiction.
   - strongMEntropyCoefficient = p.b − χ₀²·(pos) needs 0<p.b; minimal forces b=0 ⇒ coeff ≤0.
   - All minimal1/minimal2 entropy machinery is m=1-hardcoded (IntervalDomainMinimalEntropy.lean).
   Needs (per grep-exhaustive subagent, matches commit ba2398f5): ~6 new M-native minimal1
   lemmas (half-Young split keeping partial gradient dissipation + mass-Poincaré at weight 2−2m,
   general-m minimal1 coefficient+threshold, entropy-slope assembly, L2↔θ(α) bridge, late chain)
   PLUS the full minimal2 signal-energy route re-done M-native (~1900 lines). Real formalization,
   best for Codex 7/28. Narrower honest milestone possible: Thm 2.5-M restricted to minimal1 disjunct.
