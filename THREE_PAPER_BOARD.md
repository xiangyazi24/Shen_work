# THREE-PAPER FORMALIZATION BOARD (Chen-Ruau-Shen) — honest cross-paper status
Last verified: full-closure 8862 jobs; 7 real sorry tactics repo-wide (all P2 χ₀<0 analytic).
Audit standard (playbook §3.3): headline UNCONDITIONAL on satisfiable CMParams, no sorry/admit/
native_decide/custom-axiom, no carried-hard/unsatisfiable hypothesis, faithful to paper.

## P1 — Remark 1.3.2 / Theorem 1.1 (traveling-wave existence)
Headline: paper1_Theorem_1_1_of_mainResultsData (Paper1/StatementAssembly.lean:34) — CONDITIONAL on
`Paper1MainResultsData cStarStarFn`. Landed: left-floor, per-step Green solve + existence + max-principle,
order-layer, chemo-monotone, hLU. OPEN: discharge Paper1MainResultsData = the localExistence constructor
(T6/T7 per-datum existence) + order-layer hsign from trap bounds + Rothe limit. STATUS: 🔨 bundle open.

## P2 — Theorem 1.1 (bounded-domain boundedness), two regimes
χ₀=0: ✅ UNCONDITIONAL — from_cone_construction (IntervalPicardTowerSupply.lean:336, "unconditional bridge
  from the strengthened cone"). [confirm #print axioms clean at audit.]
χ₀<0: chiNeg_theorem_1_1 (Wiener/EWA/SourceChiNegTheorem11.lean:127) (p)(hchi:χ₀<0)(ha,hb,hα,hγ) — CONDITIONAL
  on the SINGLE bundle `ChiNegDatumUniformConstruction p` (the per-datum classical local existence). This
  bundle traces to the regularity chain: R1 trajectory envelope → SliceMildStepData → UniformBootstrapStep →
  MemHSigma 1 → H¹ field → H1-hom/src/chem weak identities → boundedness. STATUS: 🔨 see χ₀<0 detail below.

## P3 — persistence (Thm 2.1) + stability (Thm 2.2)
T10/persistence + stability-of-positive-equilibrium: paper3_T10_positiveEquilibriumStable_of_chi_nonpos
  (PaperOne/WholeLineLeftTail.lean:64) (p3)(hχ:χ₀≤0) — appears UNCONDITIONAL (only satisfiable param). [confirm.]
T2.2 (full stability): paper3_unitInterval_T22_with_fractionalPowerEmbedding (PDE/FractionalPowerSpace.lean:555)
  — CONDITIONAL on Paper3Constants + the fractional-power-embedding neighborhood frontier. STATUS: 🟡 T10 likely
  done, T2.2 frontier open (cascades from P2 once χ₀≤0 boundedness lands).

## χ₀<0 DETAIL (the main remaining engine — this run's focus)
✅ H1-grad (t^{-1/2} L² bound, real sine-Parseval). ✅ keystone B step (UniformBootstrapStep mild-only, non-
circular by test). ✅ trajectory propagator + genv/glenv wiring + σ-ladder step (trajLadder_step). ✅ 4 false
fields fixed. ⚠️ 1 overclaim caught+corrected.
OPEN (the residual, converged + precisely named):
 R1a. τ-uniform flux factor-envelope from Uσ — the FIXED-POINT bootstrap (flux Q built from the u being
      enveloped). Elliptic relay (v_x via resolver_memHSigmaPlus2) LANDED. The genuine hard core. → codex.
 R1b. hdecomp τ-lift: ∀τ∈[0,t] version of the landed per-endpoint IntervalBootstrapDecomp identity. Tractable.
 + per-τ ∀k fields at the joint-continuity interface (k=0 mode included).
 + 7 named sorries (P2 χ₀<0 analytic): trajectory joint measurability (IntervalMildPicardThreshold:2005,
   IntervalMildPicard:2644 — same), R-src0F-2/hCwin_ex (IntervalPicardWeightedC2Bootstrap), Lemma_3_1 closure
   (IntervalLemma31Closure), mildSlice_restart_bound restart identity (IntervalPicardLimitSliceTimeContinuity).

## DISTANCE (atom inventory, not time): discharge {P1: Paper1MainResultsData} + {P2 χ₀<0: R1a+R1b+per-τ
fields+7 sorries → ChiNegDatumUniformConstruction} + {P3 T2.2: fractional-power frontier}. χ₀=0 + P3 T10 done.
Genuine multi-session PDE. R1a is the hard fixed-point core (codex Jun 26); R1b + several sorries are tractable.

## ★ CORRECTION (2026-06-22): repo is SORRY-FREE; the work is DISCHARGING CONDITIONAL BUNDLES, not closing sorries
Definitive grep (bare `^\s*sorry\s*$` + inline `:=/by/exact sorry`, comments/strings stripped): **0 real sorry
tactics repo-wide.** My earlier "7 sorries" was wrong — all matches were docstring/comment prose ("named
sorry", "R-src0F-2 residual sorry", "(0 sorry)") referencing ALREADY-CLOSED gaps (e.g. the "trajectory joint
measurability sorry" at IntervalMildPicardThreshold:2005 / IntervalMildPicard:2644 was a STALE COMMENT — the
branch already discharges via gradDuhamel_intervalIntegrable_of_joint_measurable, IntervalDuhamel
Integrability:769, 0 sorry; enclosing theorems axiom-clean). Comment cleanup applied to those 2 lines.
SO THE REAL AUDIT STATE: the codebase is sorry-free + (headlines) axiom-clean, but the three headlines are
CONDITIONAL on carried hypothesis bundles — sorry-free conditional wrappers. "Passing playbook §3.3" =
DISCHARGING those bundles so the headlines become UNCONDITIONAL on satisfiable CMParams:
 · P1: discharge Paper1MainResultsData.
 · P2 χ₀<0: discharge ChiNegDatumUniformConstruction (← the R1a/R1b/per-τ regularity chain this run builds).
 · P3 T2.2: discharge Paper3Constants fractional-power frontier. (χ₀=0 + P3 T10 already unconditional.)
The remaining work is NOT sorry-closing — it is the genuine analytic DISCHARGE of these satisfiable bundles
(R1a fixed-point flux envelope is the hard core → codex Jun 26). MUST audit each bundle is SATISFIABLE (non-
vacuous) before claiming discharge — a sorry-free conditional on an UNSATISFIABLE bundle is the §3.3 vacuity trap.

## ★ NUMBERED ATOM REGISTRY (2026-06-22) — flat #N, no more ad-hoc letter-codes
Stable numbers; cite #N in reports/dispatches/commits. ChatGPT dispatches cite their ask-gpt Q<N> / RUN#N.
CLOSED (✅ verified, full-closure + axiom-clean):
  C1 H1-grad NeumannHeatGradientTMinusHalfBound (was "H1-grad")           — b57f439
  C2 UniformBootstrapStep mild-only step (was "keystone B step")          — c356629
  C3 trajectory propagator + genv/glenv wiring + σ-ladder (was "R1/σ-ladder") — de51937/44f4e3f
  C4 conjugate hmap + per-τ k≠0 helpers (building blocks, was "Task A/B")  — d42a783
  C5 4 false fields fixed; C6 structure validated sound; C7 repo sorry-free
OPEN (the discharge frontier):
  #1 [P2 χ₀<0] τ-uniform flux factor-envelope FIXED-POINT (was "R1a") — the hard core. Feeds TrajLadderData
     → SliceMildStepData. Elliptic relay landed. → codex Jun 26.
  #2 [P2 χ₀<0] hdecomp τ-lift (was "R1b") — ∀τ version of landed per-endpoint decomp. IN FLIGHT (opus).
  #3 [P2 χ₀<0] per-τ ∀k fields at joint-continuity interface incl. k=0 mode.
  #4 [P1] construction_neg — frozen stationary wave profile existence χ≤0 (+monotone+tail asymptotic).
  #5 [P1] construction_pos — same, χ≥0 regime.
  #6 [P1] cStarStar_spec — stability speed threshold family asymptotic.
  #7 [P1] stability — orbital stability of traveling waves under perturbations.
  #8 [P3] Theorem 2.2 fractional-power-embedding frontier (cascades from P2 χ₀≤0 boundedness).
Discharging {#1..#3} → ChiNegDatumUniformConstruction (P2 χ₀<0). {#4..#7} → Paper1MainResultsData (P1).
{#8} → Paper3Constants (P3 T2.2). χ₀=0 + P3 T10 already unconditional.

## ★ P1 DISCHARGE MAP (2026-06-22, [ChatGPT cron2 RUN#373 git-drop 296dc66+241d188], key claims tree-verified)
Paper1MainResultsData (4 core fields + 4 aux wave_cont/cauchy_unique/resolvent/tail_asymp for Thm 1.2/1.3).
No producer for the full bundle; only the StatementAssembly wrappers consume it. All 4 core satisfiable EXCEPT
#6 (flagged). Status:
 #4 construction_neg — 🟡 PARTIAL, satisfiable. Landed: b1_neg_hVmono (elliptic deriv monotone), lower-pinned
    Schauder wrappers (non-vacuous, repairs the false bare-trap Schauder principle), Rothe cleanup (hVcont).
    HARD RESIDUAL: the construction theorem = per-step Rothe/Green producer (RotheFloorResidualCore/Rothe
    StepProducer) + Rothe continuous-dependence/Schauder fixed point + stationarity + strict bounds + right-
    tail asymptotic. Carried: hstat/hlim_bot/hupper/htail (WaveBridgeWrappers), hprodTrap/hdep (WaveRotheClose).
 #5 construction_pos — 🟡 PARTIAL, satisfiable. Rothe sign-agnostic; whole_line_super_barrier_pos swapped in
    (rotheFloorResidual_of_trap_pos). Carries same Green/stationary/positivity core (b1_chiPos_existence).
 #6 cStarStar_spec — ⚠️ POTENTIAL VACUITY (was mis-rated ✅; ChatGPT self-corrected). The strict baseline
    `stabilitySpeedBaseline p < cStarStarFn p p.χ` must hold ∀ stable-regime p. VERIFIED: χ=0 IS in the stable
    regime (StableWaveParameterRegime positive branch 0≤χ, Statements.lean:16779). UNRESOLVED: whether
    StabilitySpeedThresholdFamilyAsymptotic PINS cStarStarFn p 0 to = baseline (→ strict < FALSE → over-strong,
    needs statement refactor strict→≤ or χ=0 exclusion/punctured-asymptotic) OR leaves cStarStarFn free (→ pick
    baseline+1, dischargeable). MUST resolve before claiming #6 — do NOT bank as easy. → verify StabilitySpeed
    ThresholdFamilyAsymptotic (faithfulness: check paper's threshold is strict vs ≤ at χ=0).
 #7 stability — 🔨 OPEN, satisfiable. The full weighted orbital stability theorem for the nonlinear Cauchy
    problem. The genuine hard P1 core (comparable to χ₀<0). → codex Jun 26.
NET: P1 is a FULL frontier comparable to χ₀<0 — #4/#5 hard Rothe/Green core, #7 orbital stability, #6 vacuity-
flagged. NOT closer to done. Combined campaign frontier: {#1 χ₀<0 flux fixed-point, #3 k=0, #7 P1 stability,
#4/#5 Rothe/Green} = codex Jun 26; {#2 done-bulk, #6 resolve flag, #8 P3 cascade} = tractable/blocked.
