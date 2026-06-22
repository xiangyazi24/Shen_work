# χ₀<0 Bank Producer Checklist — `BFormBankedInputs p DB`

The single remaining floor to make Paper 2 boundedness UNCONDITIONAL for χ₀<0
(repulsive chemotaxis). χ₀=0 is ALREADY unconditional (`from_cone_construction`);
the chemotaxis-divergence source vanishes there. Target: a producer
`bFormBankedInputs_of_conjugate_core_negChi (p)(hχ:χ₀≤0)(DB) : BFormBankedInputs p DB`.
Structure def: `IntervalBFormDirectClassical.lean:62` (13 fields). Mapped 2026-06-22.

## The 13 fields (a=trivial/data · b=one-wire from landed brick · c=genuine gap)

- [a] 1  `huPaper`     — datum hypothesis (upstream per-datum)
- [b] 2  `Hinf`        — abs source bounds; ← `conjugatePicardInfThresholdData_of_picard_bounds` + `IntervalConjugateChemFluxIntegrable.*_of_ball`   [subagent C]
- [a] 3  `hsmall`      — scalar smallness; CLOSES via min-horizon (cron2 verified: floor=closed-interval inf, no T→0 decay)
- [a] 4  `MInit`       — u₀ coeff bound witness
- [b] 5  `haInit`      — mechanical from #4
- [b] 6  `hlogSrc`     — logistic timeC1; ← `logisticSource_duhamelSourceTimeC1_of_representation`   [subagent C]
- [c] 7  `hchemSrc`    — chemDiv source timeC1; ← `coupledChemDivSource_timeC1_of_fields` + produce `CoupledChemDivTimeC1Fields`   [subagent B]
- [c] 8  `hB_global`   — global cosine repr; ← landed `conjugatePicardLimit_cosineSeries` + landed `hfix`, MISSING `hsource_bridge` (downstream of #10,#12)
- [b] 9  `hlogCont`    — logistic slice continuity; ← `intervalLogisticSource_continuous`   [subagent A]
- [c] 10 `hlogFourier` — logistic Fourier summability; ← quadratic-decay repr (`logisticSource_cosineCoeff_quadratic_decay_of_representation`)   [subagent A]
- [c] 11 `hchemCont`   — chemDiv slice continuity; ← `ChemMildHolderBootstrap.holderLeg_chemotaxis`   [subagent A]
- [c] 12 `hchemFourier`— chemDiv Fourier summability — DEEPEST; ← `CrossDiffusionBootstrap` + `resolver_memHSigmaPlus2_of_memHSigma`; needs σ>3/2 for Q (cron2b analytic route)   [HELD for cron2b]

## Scoreboard: 4 (a) ✓ · 3 (b) in flight · 5 (c) gaps — 0/5 gaps landed

## Genuine-gap theorems (dependency-ordered)
1. `coupledLogistic_fourierCoeff_summable_of_limit`  (field 10)   [A]
2. `coupledChemDiv_fourierCoeff_summable_of_limit`   (field 12, HEART)  [cron2b→codex/me]
3. `coupledChemDiv_constExtend_continuous_of_limit`  (field 11)   [A]
4. `coupledChemDivSource_timeC1_of_limit`            (field 7)    [B]
5. `conjugatePicardLimit_sourceBridge`              (field 8, downstream of 1,2) [HELD]
→ final mechanical `BFormBankedInputs.of_limit_analytics` wiring all 13.

## Sign-sensitivity (cron1): smoothing/Fourier sign-blind; only the FRONTIER
`hSupNormDeriv` (sup-norm max principle) uses χ₀≤0 essentially [cron1b].
Bank → BFormSpectralFrontier (6 fields) → hPerDatum → unconditional P2 → P3 cascade.

Last verified: 2026-06-22 (mapper a261b373, canonical d7659d9/c516590).

## ⚠️ FRONTIER IMPOSTOR (cron1b + source-verified 2026-06-22) — GATING
`BFormSpectralFrontier.hSupNormDeriv : IntervalDomainSupNormDerivativeNonposOn (limit) (Ioo 0 T)`
(IntervalBFormEndToEnd.lean:213) is the repo's OWN documented-FALSE field
(IntervalHsupNormProof.lean: flat datum 0<ε<K=(a/b)^{1/α} ⟹ logistic ODE ⟹ supNorm INCREASES,
deriv>0, contradicts deriv_nonpos). It is UNSATISFIABLE for admissible small data ⟹ frontier
uninhabitable ⟹ hPerDatum undischargeable ⟹ paper2_theorem_1_1_general_chi_via_bform vacuously
conditional (IMPOSTOR). BUT it is UNUSED downstream: IntervalDomainEndToEnd.lean:158 destructures
it as `_hSupNormDeriv` (discarded). FIX: drop the field (or replace w/ the conditional above-capacity
+ pure-heat true pieces, mirroring HsupNormConsumers.Lemma31CarrierTarget which the cone route uses).
Strict improvement — removes an unsatisfiable hypothesis without weakening the theorem. [me, next]

## Field 12 hchemFourier — COMPLETE analytic route (cron2b, Q275)
u(t)∈H^{3/2+} ⟹ v∈H^{σ+2}, Q=u^m(1+v)^{-β}v_x∈H^σ ⟹ S=Q_x∈H^{σ-1}, σ-1>1/2 ⟹ ℓ¹.
Iteration: 4 half-steps from H^0 (k=4: u∈H^2 → Q∈H^2 → S∈H^1 → ℓ¹). k=3 FAILS (S∈H^{1/2} endpoint).
Caveats handled: (a) H^{1/2} not an algebra → cross first step via L^∞∩H^s Moser (limit has L^∞);
(b) u^m noninteger m → keystone hmapsTo_pos positive floor on slice. Lemma: hchemFourier_of_u_H2.
PREREQ to verify: is u∈H^2 (4-half-step bootstrap) of the limit reachable from landed HSigma bricks
(IntervalBFormHSigmaSmoothing rate (1-σ)/2)? If not, the bootstrap-to-H^2 is the true sub-residual.

Updated: 2026-06-22 (cron1b Q274 impostor, cron2b Q275 route).

## ⚠️⚠️ UNIFIED ROOT FINDING (cron1c Q278 + subagents B/C/D, 2026-06-22)
The conjugate Picard limit is a WEAK mild solution (bounded/continuous/nonneg/windowed
contraction data) — it carries NO classical/global regularity. Several BFormBankedInputs
fields are typed GLOBAL / closed-at-0, which is OVER-STRONG / unsatisfiable for this weak limit:
- field 2 Hinf: producer demands hQ_bound/hL_bound ∀s (global); keystone data only windowed
  (0<t≤T); for s>T no M-control. Consumer DISCARDS the window hyps. [subagent C: windowed
  half landed (hQ_int/hB_int/hL_int via 6 bricks); global hQ_bound/hL_bound block]
- field 6 hlogSrc: global cosine-repr + timeC1; limit carries no RestartCosineRepresentation
  + time-C¹ coeff data. [subagent C: blocked, needs GradientMildSolutionData regularity]
- field 7 hchemSrc: GLOBAL DuhamelSourceTimeC1 — UNSATISFIABLE. cron1c PROVES ‖S(s)‖~1+s^{−1/2}
  as s→0+ (u_x~s^{−1/2} term); no uniform envelope. [subagent B: reduction landed but targets
  the over-strong global type → HELD, not banked]
- field 12 hchemFourier: positive-time already, but the landed ℓ¹ tool needs C²-Neumann SLICE
  ⟹ C³(u)/C⁴(v), strictly above the limit's landed closedC2 (C², keyed IsPaper2ClassicalSolution).
  [subagent D: conditional interface hchemFourier_of_chemDiv_C2Neumann landed (axiom-clean,
  satisfiable); residual = the C²→C⁴ elliptic-gain wiring on the limit]

cron1c FAITHFUL OBJECT: global package is UNNECESSARY (Duhamel converges: ∫₀ᵗ s^{−1/2} ds=2√t).
Correct = PAIR: (i) positive-time windowed C¹ package on every W⊂⊂(0,T) [= existing
HasTimeNeighborhoodSpectralAgreement architecture] + (ii) integrable-singularity-near-0 package
(‖F(s)‖_{L²}≤C, θ=0 for the B-form flux). Does NOT weaken the theorem.

D's finding: HSigma machinery (HSigmaSmoothing/DuhamelEnergy/Scale) is OPERATOR-LEVEL SCAFFOLDING
ONLY — NOT wired to conjugatePicardLimit; single step gated σ<1. No landed iterated H² bootstrap.

## TRUE REMAINING CORE for χ₀<0 unconditional P2 (re-scoped, honest)
NOT 5 leaf lemmas. Two substantial pieces:
1. REFACTOR bank global fields → positive-time windowed + integrable-singularity (cron1c's
   two-part BFormSourceRegularity; matches existing frontier architecture). [design fork: in-place
   vs fresh structure — surfaced to Xiang]
2. The weak→classical POSITIVE-TIME regularity bootstrap for conjugatePicardLimit (wire HSigma
   scaffolding to the limit; C²→C⁴ via elliptic +2 gain ×2). = Paper 2's boundedness core itself.
3 over-strong "global/closed-at-0" fields caught this session: keystone flux (fixed→(0,T]),
frontier hSupNormDeriv (fixed→dropped 5059227), bank globals (diagnosed). Same pattern.

Updated: 2026-06-22 (frontier fix landed 5059227; bank re-scoped).

## SCOREBOARD (2026-06-22, after c32453d)
LANDED axiom-clean (cold-build 3642 jobs):
  ✅ field 9  hlogCont      — coupledLogistic_constExtend_continuous_of_limit (unconditional from DB)
  ✅ field 10 hlogFourier   — coupledLogistic_fourierCoeff_summable_of_limit (unconditional from DB)
  🟡 field 12 hchemFourier  — hchemFourier_of_chemDiv_C2Neumann (conditional interface; residual = C²→C⁴)
  🟡 field 2  Hinf          — 6 windowed integrability bricks (hQ_int/hB_int/hL_int); global hQ/hL_bound block
ALSO LANDED: ✅ frontier hSupNormDeriv DROPPED (5059227, false+unused).
HELD (target over-strong type, NOT banked): field 7 hchemSrc (B's reduction → global DuhamelSourceTimeC1).
FALSE-AS-TYPED (need refactor): field 7 (global→windowed+integrable-sing), field 11 hchemCont
  (constExtend(chemDiv) discontinuous at endpoints since v''(0)≠0 → interior-representative), field 2
  hQ_bound/hL_bound (global→windowed).
BLOCKED on regularity: field 6 hlogSrc, field 8 hB_global (need RestartCosineRepr for the limit),
  field 12 residual (C²→C⁴ elliptic-gain wiring on conjugatePicardLimit).

## LINCHPIN (verified): GradientMildSolutionData IS produced unconditionally
intervalDomain_gradientMildSolutionData_of_continuous_positiveDatum (IntervalPositiveDatumThreshold:56),
coneGradientMildSolutionData_exists_with_gate_data (χ₀=0 in-tower). So χ₀<0 boundedness is NOT
axiomatized — it bottoms out at the chemotaxis-source HALF-STEP REGULARITY upgrade (the gradient path
HAS the regularity machinery via GradientMildHalfStepRestartData → IsPaper2ClassicalSolution; at χ₀=0
the in-tower production handles logistic-only; χ₀<0 needs the chemotaxis half-step). That + the bank
field-type refactor = the true remaining core. NOT leaves.

## NEXT (architecture fork surfaced to Xiang)
A) Refactor bank field types → positive-time windowed + integrable-singularity + interior representatives
   (cron1c BFormSourceRegularity; A's interior-rep finding). In-place vs fresh structure = Xiang's call.
B) Chemotaxis half-step regularity: wire GradientMildHalfStepRestartData (the gradient path's regularity
   engine, already producing IsPaper2ClassicalSolution at χ₀=0) to carry the chemotaxis source for χ₀<0.

Updated: 2026-06-22 (c32453d: fields 9/10/12-iface/2-windowed landed; linchpin verified favorable).

## ★★★ ROUTE RESOLVED (2026-06-22, B-scoping map ada83a41) — ABANDON BANK, USE GRADIENT PATH
The B-form bank (BFormBankedInputs, 4 over-strong fields) is the WRONG OBJECT. The faithful route
to χ₀<0 Paper-2 boundedness is the GRADIENT PATH (same engine that makes χ₀=0 unconditional):
- Engine `isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData`
  (IntervalMildToLocalExistence.lean:456) is SOURCE-AGNOSTIC; `GradientMildClassicalCoreData.hpde_u`
  (:157) ALREADY carries −χ₀·chemotaxisDiv for all χ₀. The bank-refactor architecture fork is MOOT.
- Entire χ₀<0 classical regularity reduces to ONE genuine analytic brick + 4 mechanical wirings.

### THE 5-BRICK GRADIENT-PATH PLAN (subagent a2f8e776 attacking)
- 🔨 BRICK 2 (THE GAP, load-bearing): `duhamelSourceTimeC1_of_shifted_On` — lift windowed one-sided
  DuhamelSourceTimeC1On → global two-sided DuhamelSourceTimeC1 for the t/2-SHIFTED chemDiv source.
  The t/2 shift dissolves the s→0+ singularity (shifted s=0 = physical t/2>0). Needs HasDerivWithinAt
  →HasDerivAt + envelope Icc→0≤s, via CoupledChemDivLocalChainRule + chemDivMixedTimeDeriv_
  jointContinuousOn_closed + resolver_memHSigmaPlus2_of_memHSigma. Builds on landed
  DuhamelSourceTimeC1On.shift_zero + ChemDivUncond windowed producer (already does the shift-trick).
- ⚙️ BRICK 1: chemDivShiftedSource...On_of_window (CLEAN, = shift_zero instantiation)
- ⚙️ BRICK 3: coupledChemDivTimeC1Fields_shifted_of_solutionRegularity (CLEAN-ish given #2)
- ⚙️ BRICK 4: gradientMildHalfStepRestartData_of_chemDivSourceData (CLEAN given 1-3)
- ⚙️ BRICK 5 = END GATE: wire into the engine → χ₀<0 IsPaper2ClassicalSolution (CLEAN)
If #2 lands + wirings compile → χ₀<0 Paper-2 boundedness UNCONDITIONAL → P3 PositiveGlobalBoundedSolution
discharged → P3 unconditional persistence cascade.

Bank bricks landed (fields 9/10/12-iface/2-windowed, c32453d) still feed Residual A (CoupledChemDivTimeC1Fields).
Updated: 2026-06-22 (route resolved: gradient path; χ₀<0 = brick #2 + 4 wirings).

## END-GATE RESIDUALS (precise, after 089e3de) — gradient-path route
END GATE isPaper2ClassicalSolution_of_chemDivSourceData_chiNeg is CONDITIONAL on:
  D (GradientMildSolutionData) — ✅ produced unconditionally
  S (ChemDivHalfStepSourceData) = { win, hagree } — open
  C (GradientMildClassicalCoreData) — reduces to halfStepRestartData + frontierCore
✅ Brick 2 (duhamelSourceTimeC1_of_shifted_On) LANDED (089e3de) — windowed→global shift bridge, real.

win = DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs) (c',d'). Produced by
coupledChemDivSource_timeC1On_of_EWA (ChemDivSourceAssembly.lean:52) from:
  ✅ envelope/henv_summable — EWA SourceEnvelope (Wiener-algebra ℓ¹, LANDED, the hard part)
  🔨 h_coeff — value-envelope domination (eval/coeff bridge) — OPEN
  🔨 adot/h_deriv/h_adotcont/h_Mdot — chemDiv source TIME-DERIVATIVE leg — OPEN, but producers EXIST:
     CoupledChemDivLocalChainRule (IntervalChemDivTimeDerivative:74), chemDivMixedTimeDeriv_
     jointContinuousOn_closed (IntervalChemDivTimeDerivClosed:54). = WIRING on positive-time window
     (c'>0 avoids s→0+; feed the gradient solution's time-C¹ regularity).
🔨 hagree — restart cosine agreement (EqOn lift to cosine series) — OPEN
🔨 frontierCore (for C) — OPEN

NEXT: discharge win (wire closed-slab timeC1 producers + h_coeff bridge → full windowed package
unconditionally), then hagree + frontierCore → END GATE unconditional → χ₀<0 P2 boundedness → P3 cascade.
The ℓ¹ envelope (historically the deep gap) is DONE; remaining = time-deriv wiring + restart agreement.
Updated: 2026-06-22 (Brick 2 + conditional end-gate landed 089e3de; residuals pinned to win-timeC1/hagree/frontierCore).
