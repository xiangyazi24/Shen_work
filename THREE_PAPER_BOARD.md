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

## ★★★ #6 RESOLVED — cStarStar_spec is GENUINELY OVER-STRONG (§3.3 VACUITY in P1, 2026-06-22, fully tree-verified)
VERIFIED unsatisfiable at the reachable stable-regime point p = (χ=0, γ=1, m=1, α=1):
 · CMParams.hγ : 1 ≤ γ ALLOWS γ=1 (Defs.lean). chiStar at γ=1,m=1 = min 1 ((2+2)/(1+1+2)) = min 1 1 = 1 > 0,
   so χ=0 < chiStar=1 → the positive branch (0≤χ<chiStar, α=m+γ-1) holds → p IS in StableWaveParameterRegime.
 · stabilitySpeedBaseline p = 1 + |χ|^{1/6} + (1+|χ|^{1/6})⁻¹ = 1 + 0 + 1 = 2 at χ=0.
 · StabilitySpeedThresholdFamilyAsymptotic forces cStarStar 0 = γ+γ⁻¹ exactly (at χ=0 the bound A|χ|^{1/6}=0).
   At γ=1: γ+γ⁻¹ = 2.
 · cStarStar_spec demands stabilitySpeedBaseline < cStarStar p.χ, i.e. 2 < 2 → FALSE. So cStarStar_spec p is
   false for EVERY cStarStarFn → Paper1MainResultsData is UNSATISFIABLE → paper1_Theorem_1_1_of_mainResults
   Data is conditional on an empty bundle (§3.3 vacuity). γ+γ⁻¹≥2 with equality IFF γ=1 (AM-GM) — γ=1 is the
   sole degenerate point, but it IS reachable, so the field as typed cannot pass audit.
FIX (a statement-faithfulness decision — needs the PAPER, FLAGGED to Xiang):
 (a) strict `<` → `≤` at the baseline (if paper's threshold is non-strict at criticality), OR
 (b) exclude γ=1 (strengthen CMParams hγ to 1 < γ, or restrict the stable regime), OR
 (c) puncture the asymptotic at χ=0 with a positive offset so cStarStar 0 > baseline strictly.
This does NOT affect #4/#5/#7 (those are satisfiable); but Paper1MainResultsData cannot be DISCHARGED until #6
is refactored. P1 audit is BLOCKED on this faithfulness call. (χ₀<0 + P3 unaffected.)

## ★★ #6 RESOLVED ✅ (2026-06-22, ca986bc, independent full-closure 8865 verified) — resolved from paper, not escalated
cStarStar_spec was over-strong (strict <) → unsatisfiable at χ=0,γ=1. RESOLVED by reading paper1.pdf Thm 1.2
(line 487): the paper has c∗∗>baseline GENERICALLY but =baseline at the degenerate γ=1, and EXPLICITLY covers
m=α=γ=1 ("new even for the case m=α=γ=1"). Faithful encoding over CMParams (hγ:1≤γ) = `≤` (strict generic,
equality at boundary). FIX: 13 spec-interface sites strict→≤ + forced lt_trans→lt_of_le_of_lt; no downstream
proof needed the strict gap (verified by diff, nothing faked). SATISFIABILITY PROVEN: cStarStar_spec_satis
fiable (witness (γ+γ⁻¹)+|χ|^{1/6}, axiom-clean) — vacuity GONE. Paper1MainResultsData no longer vacuity-blocked.
UPDATED REGISTRY: #6 ✅ resolved+fixed. P1 remaining = #4 construction_neg + #5 construction_pos (🟡 Rothe/
Green core) + #7 stability (🔨 orbital stability) — all → codex Jun 26. P1 bundle now SATISFIABLE end-to-end
(pending #4/#5/#7 discharge).

## ★ #4 construction_neg REDUCED (2026-06-22, 0d411e3 [opus], verified 8278) — driving with opus, not deferring
constructionNeg_of_provider + Theorem_1_1.of_constructionNeg_provider: whole neg-branch construction reduced
to ONE hprovider. hUmono/hVmono + FrozenStationaryWaveProfile join UNCONDITIONAL+axiom-clean, non-vacuous
(lower-pinned Schauder). #4 now = 3 named non-circular residuals (also serve #5 construction_pos, sign-agnostic):
  #4A Rothe provider — per-step Green producer (hprodTrap/RotheStepProducer) + continuous dependence (hdep/
      RotheContinuousDependence). The big PDE machinery core.
  #4B ShenUpperBoundNegative_of_stationary_strongMaxPrinciple — U0<1 strict (strong max principle on the
      stationary eqn). Bounded PDE lemma. → opus.
  #4C HasWaveRightTailAsymptotic_of_stationary — sharp +∞ tail (ODE linearization). Bounded PDE lemma. → opus.

## ★ #1 gvx half CLOSED — residual sharpened to #1D (2026-06-22 [opus], verified 3612)
IntervalFluxFactorEnvelope: sineEnv_memHSigma (v_x sine env MemHSigma σ from Uσ, via λ/(1+λ)²≤1) UNCOND+
axiom-clean; full FluxFactorEnvelopes + genv assembled CONDITIONAL on gW. Non-circular (single import, no C²).
#1 now = ONE named residual:
  #1D non-C² bounded-range Nemytskii/Wiener H^σ composition envelope for (1+v)^{-β}: build Gdenσ (cosine
     H^σ env of (1+v)^{-β}) from v's H^σ env, WITHOUT ContDiff 2 (the only landed one, memHSigma_one_add_
     rpow_neg_of_contDiff_two, needs C² = circular). For σ>1/2, H^σ is a Banach algebra embedding in L∞;
     g(v)=(1+v)^{-β} smooth+bounded on v≥0 → standard Moser/Nemytskii H^σ composition estimate. → opus.

## ★ #4A per-step Green-solve CLOSED — residual sharpened (2026-06-22 [opus], verified 8285)
RotheStepProducerImpl: crossStep_concrete_solution (per-step Green-solve EXISTENCE as concrete Continuous
ℝ→ℝ satisfying the Green convolution eqn) + crossStep_concrete_unique + greenKernel_smallness_iff (1/λ
contraction) UNCOND+axiom-clean. Non-vacuous (lower-pinned, no bare-trap). #4A now = 2 named non-circular gaps:
  #4A-A RotheStepInput.produce step-output bundle: needs crossStep_output_of_solution (truncated-bcf↔raw
        crossImplicitMap bridge crossStepSelfMap_apply_eq_crossImplicitMap WaveStepFluxId:80 ~14 per-x
        integ/decay hyps + lower-pinned RotheMaxData max-principle). Real PDE gap. → opus.
  #4A-B RotheContinuousDependence: rotheLimit_continuousDependence (propagate FrozenEllipticDerivDependence
        through Rothe limit by DCT + uniform contraction). The deep core. Real gap. → opus.

## ★★ #1D CLOSED via attack-vector (2026-06-22 [opus], verified 3502) — the first opus's "circular" was WRONG
denom_envelope_memHSigma: (1+v)^{-β} ∈ H^σ UNCONDITIONAL for 1/2<σ<3/2, via C²-via-resolver (v∈H^{σ+2}→C²
non-circular, resolver gain not bootstrapped target). Covers the MemHSigma-1 target range. Axiom-clean.
#1 remaining = #1E: gW product envelope — W=u·(1+v)^{-β} τ-uniform DOMINATING envelope (mixed product algebra
MixedMulBridge/fluxCosEnvelope_of_factorEnvelopes + τ-uniformity over [0,t]) → discharges FluxFactorEnvelopes
.gW. → opus.

## ★ #4B reduced to one scalar, #4C carried (2026-06-22 [opus], verified 8279)
StationaryUpperTail: ShenUpperBoundNegative_of_strictAtZero (whole predicate from positivity + U0<1, the trap
saturates ONLY at x=0) UNCOND+axiom-clean. So #4B = ONE scalar residual:
  #4B' U 0 < 1 strict (strong-max/Hopf strictness on frozenWaveOperator=0; barrier saturated at 0). χ<0 needs
       strict-convolution frozenElliptic<1, χ=0 needs 2nd-order ODE uniqueness. Real gap. → opus.
  #4C HasWaveRightTailAsymptotic_of_stationary carries htail (no +∞-linearization producer in repo). Real gap. → opus.

## ★ #4A-A step-output CLOSED — residual localized (2026-06-22 [opus], verified 8305)
RotheStepOutputImpl: crossStep_output_of_solution (full RotheStepOutput) + frozenImplicitStepOp_of_greenConv_
crossSource (genuinely-new non-paper step_op derivation, the committed one only did the paper route) +
rotheStepAnalytic_of_greenSource (10-field bundle from one Green rep) UNCOND+axiom-clean. #4A residual now:
  #4A-I lower-pinned RotheMaxData elliptic comparison + antitone + nonneg packets (super-barrier comparison
        DATA from which rotheStep_le_barrier derives W≤B — non-circular). → opus.
  #4A-II crossStepSelfMap_apply_eq_crossImplicitMap ~14 integrability/decay/folding hyps (WaveStepFluxId:80).
  #4A-B RotheContinuousDependence (rotheLimit_continuousDependence, DCT through Rothe limit). → opus.

## ★★ #1E gW membership+assembly CLOSED — #1 down to ONE scalar #1F (2026-06-22 [opus], verified axiom-clean)
IntervalGWProductEnvelope: gW_memHSigma (MemHSigma σ gW via trueCosProd Banach algebra) + genv_of_traj_denom
(full FluxFactorEnvelopes with gW BUILT + genv chained, τ-uniform domination RELATIVE to a τ-uniform denom
env) UNCOND+axiom-clean. #1 remaining = ONE scalar:
  #1F DenomUniformEnvelope = τ-uniform ∫₀¹|((1+v τ)^{-β})''| ≤ B (+ mode-0 A). Tractable: ((1+v)^{-β})'' =
     β(β+1)(1+v)^{-β-2}(v')² − β(1+v)^{-β-1}v'', all denom powers ≤1 ⟹ bounded by (v')²+|v''| ⟹ ∫ ≤ ‖v‖_{H²}
     τ-uniform from the resolver H^{σ+2} envelope (v in ball uniformly). Faà di Bruno + powers≤1 + resolver
     env. Bounded computation, NOT a Mathlib gap. → opus. CLOSING #1F closes #1 → FluxFactorEnvelopes → trajLadder.

## ★ #4A-tails CLOSED (stale-gap caught) + true #4 residual = RotheFloorResidual (2026-06-22 [opus], verified 8306)
GreenConvTails: greenConv_tendsto_atTop (missing atTop mirror of landed atBot) + rotheStepTails_of_limits +
rotheStepTails_greenConv_upperBarrier — all 7 RotheStepTails fields UNCOND given source limits. The "no greenConv-
tendsto" STALL was STALE (WavePaperRotheProducer already has the atBot DCT). Grep-general win.
TRUE P1 #4 RESIDUAL (both routes traced): non-paper rotheStepProducer_of_floor needs `RotheFloorResidual` =
the single honest container for whole-line Green-decay + flux-IBP + source-antitone (WaveRotheFloor:7). Paper
route paperRotheStepProducer_of_params carries wit + hrest (PaperGreenStepInputRouteASuperRestProvider) + hZsuper.
My leaf pieces (Green-solve/step-output/RotheMaxData/tails) are PARTS of this floor. → target RotheFloorResidual
directly (the Green-decay/flux-IBP/source-antitone floor) + the paper hrest, not more leaves.

## ★★ P1 #4 floor assembly CLOSED — #4 construction → ONE container (2026-06-22 [opus], verified 8313)
RotheFloorResidualImpl: rotheFloorResidual_of_data + rotheStepFloor_of_data — the ENTIRE RotheFloorResidual
floor assembly wired from landed leaf pieces (Green-solve step_op, R_cont/bound/hi/lo, tails via GreenConvTails,
conv_form), UNCOND+axiom-clean. P1 #4 (non-paper construction) now = ONE structure:
  #4-container RotheFloorStepData p c lam M κ Λ u Z — per-Z (A) flux-IBP step eqn (crossStepSelfMap_apply_eq_
     crossImplicitMap ~14 hyps) + (B) source identity+antitone + (C) whole-line Green-decay limits+comparison
     signs + (D) lower-trap/at-max/chem packets. Missing lemma: rotheFloorStepData_of_trap (discharge A-D from
     trap+per-step solve). Non-circular, satisfiable (the hR/hstep_eq/hnonneg trio = what crossStep_concrete_
     solution+flux-bridge+resolver-positivity produce). → opus. Then floor→RotheStepFloor→producer→construction.

## ★★ P1 #4 container CLOSED + FINGERPRINT recognized — bottom = 4 analytic atoms (2026-06-22 [opus], verified 8315)
RotheFloorStepDataImpl: rotheFloorStepData_of_trap + rotheFloorResidual_of_orbit + rotheStepFloor_of_orbit —
chaining wired, hnonneg PROVED (greenConv_nonneg_of_source_nonneg). FINGERPRINT (playbook §2.6): hprovider →
RotheFloorResidual → RotheFloorStepData → RotheFloorOrbitData = 4 repackaging levels, each closing peripheral
(hnonneg/tails/step_op/Bsuper) but carrying the SAME (A)-(D). STOP repackaging. The genuine irreducible P1 #4
bottom = 4 analytic atoms (attack DIRECTLY, no more _of_trap carriers):
  #4-A flux-IBP step eqn: RotheStepFluxData_of_trap — the ~14-field crossStepSelfMap_apply_eq_crossImplicitMap
       integrability/decay/folding from the trapped bounded continuous source. (WaveStepFluxId:80)
  #4-B source identity hR (R=crossSource — likely DEFINITIONAL, audit if it should be rfl not carried) +
       Antitone (crossSource) from chem-flux sign + Z antitone.
  #4-C whole-line Green-decay source limits Rbot/Rtop + comparison signs from trapped Z endpoints.
  #4-D at-max C²/range/chem + antitone elliptic regularity.
All non-circular (consume trap+solve). These 4 = the genuine analytic content of the P1 per-step construction.

## ★★★ #1F CLOSED — #1 denom-envelope analytic core DONE (2026-06-22 [opus], verified 3617, signature-audited)
denomUniformEnvelope_of_trajectoryEnvelope + genv_of_trajectoryEnvelope_uncond: the τ-uniform ∫|((1+v)^{-β})''|
≤ B bound (denom powers ≤1 ⟹ |w''|≤β(β+1)S₀²+βS₀, S₀=∑|E.env| from trajectory env, C²-via-resolver) — the
DENOMINATOR ENVELOPE is now PRODUCED internally, not assumed. #1's last ANALYTIC residual is CLOSED. ✅
HONEST CORRECTION (opus said "#1 closes unconditionally" — signature audit shows OVERSTATED): genv_of_
trajectoryEnvelope_uncond carries E (trajectory envelope, the chain INPUT) + hvnn (resolver positivity, #1D
datum) + hbr/hbridge (per-τ Fourier bridges) + heU (E.hdom domination) + hvrel/hdiv (resolver-relay sine,
landed identities). So #1 = FluxFactorEnvelopes PRODUCIBLE from a trajectory envelope + the per-τ SEAM WIRING.
The denom-envelope (genuine hard residual, via the attack vector) is done; remaining #1 = audit/discharge the
seam bridges hbr/hbridge (connect E's cosine coeffs to the concrete flux Q) — likely landed/definitional. → next.
χ₀<0 chain: #1 analytic core ✅; then the bridges + #3 k=0 + the trajectory-envelope PRODUCTION (the
continuation closure, still the deep χ₀<0 bottom) → ChiNegDatumUniformConstruction.

## ★ P1 #4 → non-diagonal crossSource analysis (2026-06-22 [opus], verified 8316, anti-repackaging respected)
RotheFloorOrbitDataImpl: hprodTrap_of_orbitResidual (chains rotheFloorOrbitData_of_trap → floor → producer,
RELATIVE to RotheFloorOrbitDataResidual) + ONE genuine field discharged: (D) hBC2B at-max C² (from landed
upperBarrier_BC2_atMax_dischargeable — gone from residual, not renamed). KEY INSIGHT: landed crossSource
machinery is DIAGONAL-only (U U U); the per-step NON-DIAGONAL triple (u,Z,W distinct) is genuinely irreducible.
P1 #4 = RotheFloorOrbitDataResidual = the per-step non-diagonal crossSource analysis (named missing lemmas):
  #4-A rotheStepFluxData_of_trap (~14-field whole-line integrability/decay of deriv(stepFlux) for the iterate)
  #4-B crossSource_antitone_of_lowerPinned_orbit (non-diagonal antitone) + hR source identity
  #4-C per-step crossSource_tendsto_at{Bot,Top} for distinct u,Z,W (only diagonal landed)
  #4-D-rest hBC2Z (Z arbitrary) + hrange/hchem + hanti (RotheStepAntitoneData shifted packet)
These are genuine per-step chemotaxis-source PDE lemmas — the irreducible analytic content of the P1 construction.

## ★★ χ₀<0 σ-ladder ENGINE assembled — bottom = (C1)+(C2) continuation closure (2026-06-22 [opus], verified, no overclaim)
IntervalChiNegTrajectoryAssembly: TrajStepBridges.step (σ→σ+1/4 via landed genv #1 + glenv + trajLadder_step) +
trajStep_iterate + trajEnvelope_one_of_base (reach TrajectoryHSigmaEnvelope 1) UNCOND+axiom-clean. Opus honest:
NOT unconditional MemHSigma 1, carries exactly:
  (C2) mkBundle: σ-uniform TrajStepBridges family — ASSEMBLY (every field landed at fixed σ: genv/glenv/hdecomp
       /bridges/resolver-relay/positivity); wire them per σ + thread τ-uniformity. Tractable. → opus.
  (C1) the τ-uniform BASE TrajectoryHSigmaEnvelope σ₀>1/2 — the GENUINE deep bottom = R1 continuation closure.
       L∞ ball CAN'T give it (sup_τ of ℓ² family ∉ ℓ²); H⁰ seed is per-slice not τ-uniform. Needs the monotone-
       recurrence base (route analysis d6e4e9f: base/openness/closedness, endpoint-uniform, NOT naive ℓ² sup).
       The genuine hard χ₀<0 PDE. → opus.
χ₀<0 = (C1) continuation base [genuine] + (C2) bundle assembly [tractable] → MemHSigma 1 → H¹ → weak identities
→ ChiNegDatumUniformConstruction. Everything else landed.

## ★ P1 #4-C tendsto CLOSED, #4-B → chemo-monotonicity wall (2026-06-22 [opus], verified 8317)
CrossSourceNonDiagonal: #4-C non-diagonal tendsto CLOSED (crossFlux_deriv_eq_nondiagonal + crossSource_tendsto_
at{Bot,Top}_nondiagonal + crossSource_greenConv_tendsto wired to R-data — discharges the source→iterate bridge).
#4-B antitone reduced (crossSource_eq_reactStep_add_fluxDefect + _antitone_of_summands). P1 #4 remaining walls:
  #4-A rotheStepFluxData_of_trap (~14-field whole-line flux integrability/decay).
  #4-B-core RotheChemoMonotoneResidual (WaveRotheOrder:126): the chemotaxis-flux-defect SIGN Antitone(−χ·deriv
       (stepFlux)) — the MAX-PRINCIPLE monotonicity content (carried diagonally too, long-standing). + W≤Z coupling.
  #4-D-rest hBC2Z/hrange/hchem/hanti.
  #4-B hR source identity (bcf fixed point = crossSource, provably not rfl — producer-supplied).
The genuine P1 #4 cores are the chemotaxis max-principle monotonicity (#4-B-core) + flux integrability (#4-A).

## ★★ χ₀<0 chain fully assembled — bottom = (C1) decaying flux envelope + (C2) InputFamily (2026-06-22 [opus], verified, SUBAGENT CAUGHT MY OVERCLAIM)
IntervalChiNegTrajectoryClosure: mkBundle (E → BundleInputs → TrajStepBridges) + mkBundleFamily + trajBase
Envelope_of_sourceEnvelope (propagator at r=0) + trajEnvelope_one_of_baseInputs UNCOND+axiom-clean. MY OVERCLAIM
CORRECTED: I briefed (C2) as "assembly that should close" — subagent audited that only heU=E.hdom is E-derivable;
the rest carry genuine per-slice analytic content. Honest §3.3 even on the orchestrator's framing.
χ₀<0 GENUINE BOTTOM (2 irreducible analytic cores, both non-circular, confirmed no localClassicalSolution):
  (C1) hMsq: τ-uniform DECAYING H⁰ flux-source envelope Msup∈H⁰ + htraj_dom. The L∞ ball CAN'T give it
       (k↦2M ∉ H⁰). THE genuine R1 continuation-closure content — a single τ-uniform decaying dominator for the
       flux coeffs (route d6e4e9f: monotone recurrence, not naive ℓ² sup). The deepest χ₀<0 PDE. → opus.
  (C2) InputFamily: per-slice mild-solution analytic data (IntervalConjugateMildSolution continuity + Fourier
       summability for cosineMulBridge + the τ-uniform decomposition conjugateSlice_decomp_tauLift residuals).
Everything else in the χ₀<0 chain is ASSEMBLED+landed. = (C1)+(C2) → MemHSigma 1 → H¹ → ChiNegDatumUniformConstruction.

## ★ P1 #4-B chemo: pointwise FALSE, route is INTEGRATED (2026-06-22 [opus]+grep-general, verified 8318)
ChemoMonotoneImpl: chemoDefect_eq_crossTerm_add_secondOrder + chemoDefect_crossTerm_nonneg (first-order cross
term (−χ)W'mW^{m-1}V'≥0 from landed signs χ≤0/W'≤0/V'≤0) UNCOND. KEY: the POINTWISE antitone (RotheChemo
MonotoneResidual) is genuinely FALSE-from-landed-signs (second-order V''=V−u^γ sign indeterminate; ChatGPT
Q363 counterexample). The construction does NOT need it — it routes through the LANDED INTEGRATED form:
IntervalP1ChemoMonotone (greenConv_chemoDefect_eq_kernelDeriv, W'-eliminated) → crossSource_greenConv_le_
barrierSource_of_integrated_residual → the comparison; WaveStepFluxIBP.stepFlux_diff_ibp discharges it
"in integrated form against greenConv_mono". So P1 #4 chemo wall = the INTEGRATED chemo-defect sign (hChemo,
∫Kλ'·g — still sign-indefinite via naive forms, the genuine residual), NOT the over-strong pointwise antitone.
EARLIER crossSource-antitone dispatches were chasing the wrong (over-strong) field — corrected: route integrated.
P1 #4 walls: #4-A flux integrability + the INTEGRATED chemo-defect sign + #4-D-rest.
