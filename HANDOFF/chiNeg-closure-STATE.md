# χ<0 CLOSURE — durable state (2026-07-11, automode; survives compaction)

Goal: make `paper2_chiNeg` UNCONDITIONAL + axiom-clean. Doctrine: HANDOFF/DOCTRINE-chiNeg-closure.md.
Ground truth: hcontr_grad removed (3cce40b1); uisai2 cold build green 9207 jobs, 0 sorryAx.
Route: V6 (`paper2_chiNeg_v6`, IntervalChiNegV6Assembly.lean:249) is 0-sorry, CONDITIONAL on
`UniformTruncatedV6AssemblyInputs p` + `HSpectral`. Discharge the 2 producer gaps → unconditional.

## GAP 1 — energy (DISPATCHED to Codex tmux window 6, working since ~14:18)
Target: `UniformTruncatedEnergyDataV6 p` (def IntervalChiNegV6Assembly.lean:94) → per (M,u₀,C,A),
build DT-indexed `TruncatedNegativePartEnergyCoreRegularData p DT` (IntervalBFormTruncatedBridgeProducerData.lean:50).
- 6/8 fields already 0-sorry: estimate (V5 A2_data / A2Concrete), energy_integrable + initial_vanishes +
  zero_energy_to_pointwise_nonneg (A3 infra), coeff_weak on OPEN t<DT.T (V5 A1_all :298).
- 2 REAL holes feed the 0-sorry reductions IntervalBFormCron2EnergyRegularityConcrete.{energy_cont:30, energy_has_deriv:64}:
  (1) joint continuity of truncatedConjugatePicardLimit on compact windows [a,b]×[0,1]  (V5 sorry :561);
  (2) interior-window time-differentiability + uniform lifted deriv bound (V5 sorry :714, window stops before DT.T).
- LIKELY already provided by untracked files: IntervalTruncatedPicardLimitJointContinuity.lean (hole 1),
  IntervalTruncatedPicardIterJointContinuity.lean (iterate-level), IntervalMildTimeDerivReconstruction.lean (hole 2).
- Plumbing: V6 coeff_weak wants endpoint t=DT.T but A1 gives t<DT.T (consumer only uses τ<DT.T; satisfy endpoint trivially).
- Codex writes NEW file IntervalTruncatedEnergyProducerV6.lean. Brief: /tmp/shen-collab/codex-energy-brief.md.
  Progress: /tmp/shen-collab/codex-energy-progress.md.

## GAP 2 — HSpectral (NOT yet dispatched; brief below)
Target: `HSpectral : ∀ {u₀} (S : ConjugateMildSolutionData p u₀), BFormMildSpectralBootstrapData p S`
(def IntervalBFormMildClassicalBootstrap.lean:17). 4 fields:
- hResolverPos ✅ DONE unconditional (hResolverPos_of_conjugateMild, IntervalResolverBootstrapFromMild.lean:47).
- hResolverData / hTimeNhd / hPdeAgreement ⚠ — all assembled by (both 0 sorry, in IntervalChiNegFinalAssemblyV3.lean):
    bootstrapData_of_positiveTime_frontier (:205)  [HSpectral ⟺ PositiveTimeSpectralBootstrapFrontier]
    positiveTimeSpectralBootstrapFrontier_of_delivered (:114) from EXACTLY 2 carried hyps:
      hLadder : ∀ t₀, 0<t₀→t₀<S.T → LadderOutput p S t₀            (target sig FinalAssemblyV3:75-110)
      hSourceTimeC1 : ∀ c T', 0<c→T'<S.T → DuhamelSourceTimeC1On (bFormSourceCoeffs p S.u) c T'
- ℓ¹ ladder (IntervalCoeffLadderFull.lean eigenvalue_weighted_summable_of_pass4 :232) 0-sorry, NOT a hole.
- DuhamelSourceTimeC1 packagers all 0-sorry: bFormSource_duhamelSourceTimeC1On (IntervalBFormSpectralHtime.lean:60),
  clampedResolverSource_duhamelSourceTimeC1 (IntervalResolverSourceClampedWitness.lean:64, GLOBAL witness for hResolverData),
  logistic/chemDiv On-packagers (IntervalLogisticSourceTimeC1OnFromMild:18, IntervalConjugateChemDivSourceTimeC1On:33,
  IntervalTruncatedBFormSourceTimeC1On:238).
- KEY: IntervalBFormSpectralProviderDischarge.lean (:39/:130/:194, 0 sorry) ALREADY assembles hLadder+hSourceTimeC1
  BUT only for `conjugatePicardLimit p u₀ D.T` (ConjugateMildExistenceData route), NOT for truncated-limit-backed S.
  ⟹ CONCRETE TASK = port/generalize those discharge theorems to the truncated route S.u.
- Both hyps bottom out in one analytic frontier: time-C¹ regularity + ℓ¹/quadratic-decay coefficient envelopes for
  coupledLogisticSourceCoeffs / coupledChemDivSourceCoeffs and the restart/resolver rep of S.u = truncatedConjugatePicardLimit.
- NOTE: IntervalTruncatedTestedSpectral.lean "sorries" are COMMENT false-positives (0 real sorry); it's the V5
  tested-identities route, NOT the V6 critical path — ignore for V6.

## ChatGPT (analysis cores)
- Q4223 = cq1 (energy nonneg): CONFIRMED clean/non-circular; load-bearing = Sobolev weak chain rules for pos/neg parts
  + Hilbert-triple chain rule; suggests prove for smooth iterates then pass to limit. Full: /tmp/gpt_Q4223.md.
- cq2 (spectral summability + DuhamelSourceTimeC1 core): in flight. /tmp/gpt_Q4223... (next Q#).
- cq3 (HSpectral analytic frontier: time-C¹ + ℓ¹ decay envelopes for truncated source coeffs): fired.

## How to drive
- Codex window 6: `tmux capture-pane -t 6 -p | tail`. To SEND: `tmux send-keys -t 6 -l "text"` then SEPARATE
  `tmux send-keys -t 6 Enter` (combined Enter is absorbed as newline — needs its own Enter; verify "Working" appears).
- Verify: lake env lean <file> single-file (allowed); FULL/cold build ONLY uisai2 via ssh+rsync; NO local lake build.
- Do NOT edit: IntervalChiNegV6Assembly, IntervalTruncatedTestedSpectral*, IntervalTruncatedPositiveTimeBootstrap,
  IntervalChiNegV5SelfContained. New producers → new files.

## NEXT ACTIONS
1. Monitor Codex window 6 → when energy producer commits, verify (lake env lean + uisai2), then feed its output type.
2. Dispatch GAP 2 (HSpectral port to truncated route) — to Codex window 6 after energy, or a fresh codex exec /
   subagent. Brief target: port IntervalBFormSpectralProviderDischarge {conjugate→truncated S.u}; supply truncated
   source envelopes (time-C¹ + ℓ¹ decay) via the clamped-witness + ladder inputs.
3. When BOTH producers land: build the unconditional top theorem (feed energy + HSpectral into paper2_chiNeg_v6),
   cold uisai2 gate, #print axioms = 3 standard only. That closes χ<0.

## cq3 steer (Q4228) — CONFIRMED, and Codex found it independently
- (A) joint continuity of truncated LIMIT: needs UNIFORM convergence on compact [a,b]×[0,1] (sup-norm Picard
  contraction ⇒ TendstoUniformlyOn ⇒ uniform limit of continuous = continuous).
- (B) time-C¹: naive kernel differentiation FAILS (nonintegrable 1/(t-s)). MUST use SPECTRAL route: locally-uniform
  ℓ¹ control of source coefficients ⇒ each cosine mode C¹ in time ⇒ termwise differentiation. Same ℓ¹ envelope HSpectral needs.
- Codex energy diagnosis (matches): iterate joint-continuity only proved for n=0; wire SUCCESSOR preservation from
  Duhamel/source continuity infra ⇒ limit joint continuity. Time-deriv rep available in IntervalTruncatedPositiveTimeBootstrap.

## SCOPE CORRECTION — UniformTruncatedV6AssemblyInputs has 3 fields + HSpectral (not 2 gaps)
GAP 3 — jensenStrictPos (V5 sorry-3, the hard one, IntervalChiNegV5SelfContained.lean:809):
- Producer EXISTS: `truncatedJensenStrictPosDataFor_of_localizedDiscountedLower`
  (IntervalTruncatedJensenLocalProducer.lean:39) builds `TruncatedJensenStrictPosDataFor T u` from
  `ReactionDiscountedMildLowerOn` (def :27). ⟹ GAP 3 = build `ReactionDiscountedMildLowerOn` for the truncated limit.
- Analytic route (cq5 fired): mass Gronwall (m(t)≥m0·e^{-Ct}>0) → local positivity → positive restart seed →
  Neumann heat-kernel strict positivity-improving → reaction-discounted mild lower bound u(s+σ)≥e^{-Dσ}S(σ)u(s).
mapCertificate — `UniformTruncatedConjugateMapCertificateData` (abbrev IntervalChiNegUniformCoreComplete.lean:449),
  consumed by uniformTruncatedConjugateMildExistenceCore_of_uniformCore (:288, 0 sorry). LIKELY dischargeable from the
  existence core — VERIFY (what the abbrev unfolds to; whether a producer exists).
⟹ FULL χ<0 closure = discharge {energy, HSpectral, jensenStrictPos(→ReactionDiscountedMildLowerOn), mapCertificate}
  then feed into paper2_chiNeg_v6. All reduce to concrete pieces on top of 0-sorry infra + truncated-limit regularity.

## Codex energy deep-finding (~14min, still working) — KEY
- Verified 3 untracked regularity inputs compile: IntervalTruncatedPicardIterJointContinuity,
  IntervalTruncatedPicardLimitJointContinuity, IntervalMildTimeDerivReconstruction.
- FOUND: A1 (weak-test) chain AND the time-derivative chain both bottom out on the SAME positive-time SPECTRAL
  placeholders ⟹ energy and HSpectral are coupled; possible A1 transitive-axiom regression at current HEAD.
- Codex running its OWN route audit (via ChatGPT bridge on shen channels): can energy's weak-test + window time-deriv
  be built from landed Lipschitz/restart/FTC infra WITHOUT rebuilding the full high-order spectral bootstrap?
  → If YES energy is cheap; if NO, build ONE shared spectral/regularity foundation feeding both energy + HSpectral.
- cq2 (Q4224) confirms: eigenvalue-weighted ℓ¹ needs QUARTIC k^{-4} decay (S∈W^{4,1}+Neumann tower) = the ladder env4/pass4.
- CHANNEL SHARING: Codex now fires ChatGPT on shen1/2/3 too — I BACK OFF my own cq firing to avoid crowding; channels
  stay saturated via Codex's deeper-context questions. My cq2 done, cq5 (Jensen) in flight; no new cq until Codex settles.

## PIVOTAL FORK (Codex ~16min) — energy/HSpectral route through the 6 Bootstrap sorries
- Energy A1 coefficient producer is POLLUTED: transitively depends on 6 proof-position sorries in
  IntervalTruncatedPositiveTimeBootstrap.lean (source-coeff bounds/summability, weighted coeff summability, level-5
  reconstruction). ⟹ the 6 Bootstrap sorries ARE on the critical path to UNCONDITIONAL χ<0 (uisai2 0-sorryAx was only
  the CONDITIONAL headlines; these 6 live in separate theorems needed to discharge HSpectral/energy unconditionally).
- Codex auditing: direct heat-semigroup WEAK-FORM route (IntervalBFormCron2SemigroupWeakDuhamel) as clean replacement
  for polluted A1; and whether restarted positive-time solution gives energy deriv+continuity directly.
- Codex CANNOT use ChatGPT bridge (it's in 'cron' window; bridge only allows flt*/shen*). I RELAY its audit (cq6).
- cq5 (Q4230) Jensen correction: the hard lemma is POSITIVITY-IMPROVING / strong max principle for 1D Neumann linear
  parabolic w/ bounded coeffs (Harnack-type), NOT Jensen. GAP 3 = ReactionDiscountedMildLowerOn via parabolic comparison.

## DECISION (provisional, autonomous, from code) — ENERGY via DIRECT SEMIGROUP WEAK-FORM, bypass 6 spectral sorries
Evidence (IntervalBFormCron2SemigroupWeakDuhamel.lean, 0 sorry):
- negativePartMildSemigroupWeakAfterFluxTestDuality_of_standardHeatSemigroupDuhamelFacts (:226) gives the weak-form
  energy identity + WEAK time-differentiation from NegativePartStandardHeatSemigroupDuhamelFacts (:168), whose fields are
  all "SATISFIABLE standard" heat-Duhamel facts:
    gradient_tminus_half (NeumannHeatGradientTMinusHalfBound = heat L²→L² gradient τ^{-1/2} bound — my hcontr infra),
    source/chem_endpoint_l2_lebesgue (Lebesgue-point endpoint diff of Duhamel), source/chem_dct_dominator (DCT majorant
    via (t-s)^{-1/2} integrability), + algebraic weak decomposition + already-proved B_N duality.
- KEY: energy time-derivative = d/dt of SCALAR ∫u₋² via WEAK differentiation (source_duhamel_differentiation +
  Lebesgue-point), NOT pointwise ∂ₜu ⟹ sidesteps the 1/(t-s) singularity cq3 flagged ⟹ NO spectral coefficient
  summability needed for energy.
Route for energy 8 fields: weak_regular + energy_has_deriv ← semigroup weak-form (discharge the standard facts bundle);
  energy_cont ← untracked joint-continuity + successor preservation; estimate/integrable/initial/zero_to_nonneg ← A2/A3.
⟹ 6 Bootstrap spectral sorries BYPASSED for energy. Finalize on cq6; relay decision to Codex (it's auditing this exact file).

## REFINED PATH (cq6 Q4231 confirmed; energy DECIDED + dispatched to Codex)
- ENERGY: weak-form route DECIDED (cq6: E'=⟨u_t,-u₋⟩_{H⁻¹,H¹}, only u_t∈H⁻¹ + weak PDE; no spectral). Codex building
  IntervalTruncatedEnergyProducerV6.lean via NegativePartStandardHeatSemigroupDuhamelFacts. Decision:
  /tmp/shen-collab/codex-energy-DECISION.md. ⟹ energy BYPASSES the 6 spectral Bootstrap sorries.
- BUT cq6: spectral bootstrap IS still needed for CLASSICAL reconstruction (pointwise ∂ₜ, coefficient floors). HSpectral
  (BFormMildSpectralBootstrapData) feeds localClassicalSolution_of_conjugateMild_spectral (mild→CLASSICAL). ⟹ the 6
  Bootstrap spectral sorries (eigenvalue-weighted summability / source-coeff bounds / level-5) ARE on the critical path
  via HSpectral. Energy does NOT need them; HSpectral DOES.
- ⟹ REMAINING χ<0 critical path: (1) energy [Codex, weak-form, in progress]; (2) HSpectral = close/port the spectral
  coefficient summability for truncated S.u [the 6 Bootstrap sorries or the SpectralProviderDischarge port]; (3) jensen =
  ReactionDiscountedMildLowerOn via 1D Neumann parabolic positivity-improving/Harnack; (4) mapCertificate [verify easy].
- NEXT INVESTIGATION (mine): are the 6 Bootstrap spectral sorries tractable? Does SpectralProviderDischarge (0-sorry
  conjugate route) already discharge them, so the port is the whole job? Or is there genuine missing quartic-decay analysis?

## ChatGPT SATURATION (Xiang: 派满所有 tabs) — all shen channels firing + backlog
IN FLIGHT: cq7 (quartic k⁻⁴ decay of truncated source coeffs = HSpectral/6-sorries math),
  cq8 (1D Neumann parabolic positivity-improving/heat-kernel lower bound = Jensen/ReactionDiscountedMildLowerOn),
  cq9 (DuhamelSourceTimeC1 time-C¹ of truncated source = HSpectral 2nd hyp).
BACKLOG (fire on any return, keep channels full):
  cq10 = exact Sobolev/H⁻¹ weak chain rule E'(t)=⟨u_t,-u₋⟩ for the negative-part energy (energy weak-form leaf).
  cq11 = proof + Mathlib route for NeumannHeatGradientTMinusHalfBound (heat L²→L² gradient τ^{-1/2} bound).
  cq12 = the Duhamel Lebesgue-point endpoint + DCT dominating-function facts (NegativePartStandardHeatSemigroupDuhamelFacts leaves).
  cq13 = level-5 reconstruction / the exact per-mode restart coefficient representation for the truncated limit.
  cq14 = mapCertificate discharge (UniformTruncatedConjugateMapCertificateData) — likely easy, verify.

## HSpectral VERDICT (Explore aa7c4bf) — TRACTABLE PORT, not new analysis. HUGE.
- eigenvalue-weighted ℓ¹ = quadratic k⁻² source decay + parabolic +2 gain (ladder_pass_gain_envelope), NOT quartic.
  NO W^{4,1}/bilaplacian analysis needed. cq7 (quartic) = MOOT/wrong premise → refill that channel.
- SpectralProviderDischarge REPACKAGES (takes summability as hyp); real proof = generic 0-sorry
  duhamelSpectralCoeff_eigenvalue_summable / restartDuhamelCoeff_eigenvalue_summable from a DuhamelSourceTimeC1.
- 6 Bootstrap sorries (all port to 0-sorry engines; truncated source = ordinary source on u≥0):
  #1 :2863 truncatedBFormSourceCoeff_bound — feed flux-W^{1,1} from truncatedPicardLimit_lipschitzOn_positive_time
     (MY unconditional Lipschitz, already at :2862 as _hlip) into truncatedChemDivSourceCoeff_bound_of_fluxW1 (0-sorry). ~near-oneliner.
  #2 :3185 source_l2 — H² Parseval. #3 :3208 grad_l1 — split-Duhamel+parabolic smoothing (NO eigenvalue dep).
  #4 :3225 source_summable (ℓ¹) — quadratic decay cosineCoeffs_C2_neumann_quadratic_decay_of_bound. LOAD-BEARING.
  #5 :3240 eigenvalue_weighted — structurally = 0-sorry duhamelSpectralCoeff_eigenvalue_summable. LOAD-BEARING. PORT.
  #6 :3468 level5 pointwise series — port of cosineCoeffSeries_contDiff_two.
  These feed exports truncatedPicardLimit_{lap,source}_summable_positive_time (:3992/:4041) = HSpectral ladder inputs.
- ⟹ HSpectral = close the 6 Bootstrap sorries (edit Bootstrap, now in-scope) via the named engines. Dispatch to Codex
  after energy commits (avoid file conflict; window-6 warm). Jensen dispatch after cq8 lands.
- REFILL cq7-channel (quartic moot) with backlog: cq10 (energy H⁻¹ chain rule) or cq11 (heat gradient τ^{-1/2}).

## cq8 (Q4234) — JENSEN is the HARDEST gap (drifted parabolic positivity)
- Pure Neumann heat-kernel strict positivity: ALREADY FORMALIZED in repo (reuse).
- BUT ReactionDiscountedMildLowerOn u(t)≥e^{-Dσ}S(σ)u(s) FAILS for arbitrary bounded DRIFT b·u_x (chemotaxis first-order
  drift can't be absorbed into a scalar reaction discount). Needs the DRIFTED Neumann evolution family P_b positivity-
  improving = strong parabolic maximum principle / strictly-positive drifted fundamental kernel. Mathlib likely lacks this.
- ⟹ Jensen = genuine bottleneck. Options to investigate: (a) exploit the chemotaxis DIVERGENCE structure ∂ₓ(u₊·flux) —
  is the "drift" actually a divergence that integrates nicely / can be moved to zero-order? (b) a comparison/barrier
  avoiding the full max principle; (c) build a minimal strong-parabolic-max-principle for 1D Neumann bounded-drift.
- BACKLOG: cq14 = Jensen-drift resolution (how to get ReactionDiscountedMildLowerOn WITH the chemotaxis drift; does the
  divergence structure or an integrated/weak comparison sidestep the drifted max principle? what's the minimal Lean infra?).
  cq15 = mapCertificate discharge (likely easy). 

## JENSEN BOTTLENECK — attacking NECESSITY (could dissolve it) [~15:05]
- cq14 (Q4244) key steer: DON'T prove full strict u>0 unless truly needed; check if downstream only needs RESOLVER/
  DENOMINATOR positivity (both cheap: hResolverPos_of_conjugateMild done unconditionally; 1+R≥1 free since R≥0).
- Attacking: (a) Explore a0633e999fbc943cb — trace ConjugateMildSolutionData.hpos consumers, is strict 0<u or 0≤u
  load-bearing? (b) cq16 — math necessity: is strict u>0 needed anywhere (division/log/u^neg), or does u≥0 + flux
  vanishing on {u=0} suffice for classical PDE?
- IF strict positivity droppable ⟹ Jensen gap = trivial (mass positivity → resolver positivity, already done) ⟹ χ<0
  reduces to {energy [building], HSpectral [port], mapCertificate [easy]}. IF genuinely needed ⟹ build drifted parabolic
  positivity (Aronson Gaussian lower bound for 1D bounded-coeff parabolic; hardest infra).
- hpos fills ConjugateMildSolutionData at V6Assembly:185 (conjugateMildSolutionData_of_truncatedEnergyJensen_v6).

## Leaf confirmations (cq13 Q4241, mapCertificate) [~15:10]
- HSpectral sorry #6 (level-5) = port of the ALREADY-COMMITTED generic cosine-series engine; spatial clean, time needs
  locally-uniform conv (from eigenvalue-weighted summability). Tractable.
- mapCertificate = UniformTruncatedConjugateMapCertificateData (Prop ∀M,u₀,C → UniformTruncatedConjugateMapCertificate C);
  consumed by uniformTruncatedConjugateMildExistenceCore_of_uniformCore. Likely dischargeable from existing map-contraction
  machinery (flux bounds now unconditional) — VERIFY (low priority).
- STATUS: all 4 pieces tractable EXCEPT Jensen (necessity verdict pending: Explore a0633e + cq16). Analysis surface fully
  mapped; bottleneck now = Codex EXECUTION (energy build) + Jensen verdict. Marginal value of new ChatGPT questions dropping.

## JENSEN VERDICT (Explore a0633e) — STRICT u>0 REQUIRED, cannot weaken to u≥0. → ESCALATED TO FABLE.
- Forced by: (1) target IsPaper2ClassicalSolution (Statements.lean:83) DEFINES strict positivity; (2) source C²
  regularity powerSource_contDiffOn_Icc (IntervalCoupledRegularityBootstrap.lean:44, rpow_const_of_ne needs u≠0 on CLOSED
  [0,1]) → feeds elliptic PDE for v + Neumann BC + spectral resolver regularity.
- Gap = u>0 on closed [0,1] (incl. endpoints) for t>0 = strong-max-principle/drifted-Harnack. ConjugateMildSolutionData.hpos
  (IntervalConjugatePicard.lean:515) is the strict field; V6Assembly:185 consumes via strictPos_of_truncatedJensenStrictPosDataFor.
- Resolver positivity is NOT a bypass (derived from hpos, only used as ≥0 downstream — vestigial).
- FABLE dispatched (ad95f97ea1a708f13) on ReactionDiscountedMildLowerOn via 1D LIOUVILLE/GAUGE drift-removal
  (w=u·exp(−∫b/2ν) → driftless + bounded c̃ → reuse formalized Neumann heat-kernel strict positivity). Fallback: Aronson.
  Brief: /tmp/shen-collab/fable-jensen-brief.md. cq18 fired to nail the gauge transform (b_t obstruction?). 
- Energy: Codex committed dafa7a7b "Complete direct weak coefficient certificate"; still building (mapCertificate wiring).

## Reconciliation cq16(Q4247, math) vs Explore(code): strict positivity IS needed (repo route + target def)
- cq16: strict not INTRINSIC to mild→classical (PDE holds at u≥0); only needed if downstream divides by u/log u/rpow(u).
- Explore: repo route DOES use rpow (powerSource_contDiffOn_Icc, u^γ real γ C² needs u≠0) AND target Statements.lean:83
  DEFINES strict. Target strictness is genuine (Chen–Ruau–Shen positive solution) — NOT droppable.
- ⟹ Fable's strict-positivity work is correct/needed. SIDE NOTE (potential simplification, not blocker): if γ is a fixed
  integer, u^γ is polynomial (C² at 0) — could relax the rpow C² coupling downstream, but target still needs u>0.

## cq15 (Q4245) energy_cont steer — use flux continuity, NOT flux-derivative
- Joint continuity of u_{n+1} needs joint continuity of Q_n=truncatedChemFlux(U_n) (continuous: positivePart+resolver),
  NOT continuity of ∂ₓQ_n. The conjugate/B-form Duhamel kernel applies the spatial derivative INTERNALLY (with (t-s)^{-1/2}
  integrability). The IBP-to-flux rewrite is optional + creates an awkward u₊-zero-set derivative problem — AVOID it.
- A uniform gradient bound = boundedness in a Sobolev ball, NOT continuity in gradient topology → derivative route can't
  close from that alone. ⟹ energy_cont via flux continuity + kernel-internal derivative (cleaner). Cross-check for Codex.

## cq18 (Q4251) gauge verdict + Fable steer [~15:25]
- 1D Liouville gauge does NOT reduce to driftless unless b_t bounded (gauge adds (1/2ν)∫₀ˣ b_t dξ); chemotaxis b_t ~ u_t
  not obviously bounded. FIX (relayed to Fable ad95f97): FROZEN-COEFFICIENT — freeze b at t₀ on short window → autonomous
  gauge → driftless → reuse formalized Neumann heat-kernel strict positivity → propagate across windows (repo has the
  equal-step window chain from hcontr work). Boundary preserved: b=−χ₀∂ₓR/(1+R)^β=0 at x=0,1 (R_x=0 Neumann) ⇒ Neumann kept.
- Fallback: minimal Aronson 1D bounded-drift Gaussian lower bound (cq20 fired). 
- Energy: f6f05470, 0 sorry, Codex still assembling full producer (57min). Fable Jensen just started (no progress file yet).

## FINAL ASSEMBLY verified clean [~15:40]
- paper2_chiNeg_v6 (IntervalChiNegV6Assembly.lean:249) IS the headline: → Theorem_1_1 intervalDomain p, from
  (hχ:χ₀<0, ha, hb, hα:1≤α, hγ:1≤γ) + H:UniformTruncatedV6AssemblyInputs{mapCertificate,energy,jensenStrictPos} + HSpectral.
  No separate unconditional theorem_1_1 consumes it. Endgame = build 4 producers → feed in → paper2_chiNeg (unconditional).
- 1≤γ real ⇒ u^γ C² needs u>0 (confirms strict positivity required). Final step is trivial wiring once producers land.
- cq19 (Q4252): "source ℓ¹" for HSpectral must be a SINGLE summable envelope UNIFORM on tail window [t/2,t] (WindowSourceEnvelope),
  not per-slice — port detail.

## JENSEN — Fable's deeper route (barrier, NOT gauge) + the REAL gap [~15:55]
- Fable CAUGHT that frozen-gauge is UNSOUND (u solves time-VARYING eq; frozen-coeff difference is signless additive error).
- BETTER route (repo already has, sorry-free, unconditional): squared-heat-barrier e^{-Mt}(S_ν(t)f)² is a SUBSOLUTION of any
  bounded-drift eq via completing the square (squareHeatResidualCore_nonpos_of_bounds; M≥A²/2+D, |b|≤A, -c≤D) +
  neumann_interval_comparison_with_drift (IntervalBFormLinearDriftComparisonRegularDischarge.lean:1050, time-dependent drift).
  No gauge, no b_x, no freezing, no window chain, no endpoint lemma. Patch the S_N(0)=0 vacuity via restart barrier
  w(0)=f² from restartSliceSqrtSeed.
- Interface: TruncatedJensenStrictPosDataFor has per-(t,x) existential D ⇒ pointwise strict pos SUFFICES; Fable committing
  reduction truncatedJensenStrictPosDataFor_of_strictPos. Producer takes energy data as explicit hyp (assembler feeds same output).
- REAL REMAINING GAP (both routes): u must be a classical SUPERSOLUTION on positive-time windows (u_t,u_x,u_xx + residual≥0
  + Neumann) BEFORE positivity. CIRCULARITY RISK: classical u_xx via mild→classical bootstrap needs strict pos (u^γ C²);
  strict pos needs supersolution. cq23 fired: can barrier-comparison run at MILD/WEAK level, OR does Hölder-Schauder interior
  regularity give classical u_xx from NONNEGATIVITY alone (u^γ Hölder for u≥0 continuous, γ≥1) — breaking circularity?
  Fable auditing PrePositivity regularity chain. IF genuinely circular → the one true blocker, restructure needed.

## WORKER RE-ALLOCATION (Xiang: hand Jensen to window-6 Codex) [~16:05]
- Window-6 Codex: FINISH energy (81min in, near done) → then JENSEN (queued; brief /tmp/shen-collab/codex-jensen-brief.md).
  Continues Fable's file IntervalTruncatedStrictPositivityProducerV6.lean (Fable reduction thm committed 8420c7ba).
- Fable (ad95f97): winding down Jensen — writing findings to /tmp/shen-collab/fable-jensen-handoff.md, then STOP editing.
  Once it confirms handoff → REDIRECT Fable to HSpectral (the tractable port; independent files; strong worker not idle).
- Jensen crux for Codex: u supersolution WITHOUT strict pos (mild/weak comparison OR Hölder-Schauder from u≥0). cq23 landing.
- Barrier route: squareHeatResidualCore_nonpos_of_bounds + neumann_interval_comparison_with_drift (:1050) + restartSliceSqrtSeed.
- PENDING: Fable handoff confirm → redirect to HSpectral; energy done → Codex starts Jensen; cq23 → relay to Codex.

## WORKERS OPTIMALLY ALLOCATED [~16:20]
- Codex (window 6, GPT 5.6 max): energy (DT core assembled, fe1e9c99+19b33533, near done) → JENSEN. Brief updated with
  the Fable's RECOMMENDED u_xx-free route: weak/Stampacchia (w−u)₊ comparison (mirror of nonneg_of_negativePartEnergyCoreDataFor),
  drift-proof squared-heat barrier (squareHeatResidualCore_nonpos_of_bounds, T0Restart dodges S_N(0)=0 vacuity,
  squareHeatRestartDerivativeData_of_semigroup discharges barrier calculus), neumann_interval_comparison_with_drift.
  Jensen NOT circular (PrePositivity positivity-free). Reduction thm 8420c7ba means only pointwise 0<u needed.
- Fable (ad95f97, resumed): HSpectral in NEW file IntervalTruncatedSpectralProducerV6.lean. Recon on SpectralProviderDischarge
  to decide port-into-new-file (recommended: build truncated DuhamelSourceTimeC1 → feed generic 0-sorry eigenvalue engines;
  truncated source = ordinary on u≥0) vs 6-Bootstrap-sorry route. Relayed cq17/19/13; cq21/25 pending.
- Fable ALSO fixed 2 latent blockers (committed): newline-in-qualified-name parse fail in JensenLocalProducer; ρ₊ ripple in
  IntervalChiNegTruncatedRestartStrictPosProducer (from 935396ab). Chain compiles.
- Tabs: cq21/23/24/25 running. cq23=Jensen circularity (Fable already answered: NOT circular), cq24=full-chain acyclicity.

## HSpectral ROUTE SHARPENED (Fable) [~16:35]
- HSpectral is FULLY GENERIC in S:ConjugateMildSolutionData (BFormMildSpectralBootstrapData refs only S.T, S.u). Build
  generically from S fields (hbound,hcont,hmild,hnonneg,hpos) + positive-time parabolic smoothing from hmild.
- ⟹ the 6 IntervalTruncatedPositiveTimeBootstrap sorries are OFF the HSpectral critical path (they're the truncated
  per-slice route; HSpectral uses S.hmild = UNtruncated conjugate Duhamel). Fable will NOT touch them. Big simplification.
- HSpectral CONSUMES S.hpos (strict pos) as an INPUT — no circularity: assembler builds S from {energy→nonneg, Jensen→hpos}
  then applies HSpectral. Dependency order clean.
- Fable route: generalize conjugate spectral machinery to generic mild u; feed generic 0-sorry engines
  (duhamelSpectralCoeff_eigenvalue_summable) via DuhamelSourceTimeC1 from source envelopes + clampedResolverSource_duhamelSourceTimeC1.
  NEW file IntervalTruncatedSpectralProducerV6.lean. 2 recon agents mapping generic-vs-hardwired.
- cq23 (Q4261): strict-pos NON-circular CONFIRMED; missing bridge = WEAK comparison producer (neumann_interval_comparison_with_drift
  needs CLASSICAL supersolution — Codex must build the weak (w−u)₊ energy comparison instead). cq26 firing on its exact algebra.
- cq21 (Q4256): level-5 time-deriv = hasDerivAt_tsum_of_isPreconnected + uniform differentiated-envelope.
- Tabs: cq24 (acyclicity), cq25 (envelope), cq26 (weak comparison), cq27 (level-5 transfer) running.

## ⚠️ MAJOR CORRECTION (Fable, evidence-backed) — HSpectral is the CRUX, NOT a port [~16:55]
- LadderOutput has NO producer (dead code, FinalAssemblyV3 frontier route never entered). HSpectral/BFormMildSpectralBootstrapData
  NEVER discharged unconditionally for ANY solution family (v3/v5/v6 all ASSUME it). SpectralProviderDischarge/PIDUnconditional
  are 0-sorry REPACKAGERS only (take analytic leaves as hypotheses). NO 0-sorry conjugate analog of ladder-summability leaves.
- ⟹ the spectral/Sobolev ladder (source ℓ²→grad-ℓ¹→ℓ¹→eigenvalue-weighted, level-5 reconstruction, restart cosine rep,
  source time-C1, power-source quadratic decay) is GENUINELY OPEN for all routes — the real crux of the whole theorem.
  My earlier "tractable port" (Explore aa7c4bf) was WRONG/optimistic. 6 Bootstrap sorries target a DIFFERENT coeff family,
  never reach the frontier.
- UNLOCK (Fable): engine duhamelSpectralCoeff_eigenvalue_summable_on / localRestartCoeff_eigenvalue_summable gets
  eigenvalue-weighted ℓ¹ from a DuhamelSourceTimeC1 DIRECTLY — BYPASSES the dead LadderOutput/env4. So HSpectral reduces to
  a named leaf bundle: {DuhamelSourceTimeC1 of bForm source, restart cosine rep, Fourier data, resolver data}.
- DECISION (mine): Fable builds GENERIC assembler (bFormMildSpectralBootstrapData_of_leaves), NOT specialized route
  (specialized "closed conjugate bundle" is ILLUSORY — conjugate also bottoms out in assumed BFormBankedInputs; + touches
  protected V6). Reusable (0-sorry, slice-functional-transferable): the engine, bFormSource_duhamelSourceTimeC1On,
  logistic/chemDiv repackagers, C² cosine-slice engine, Fourier slice-builders, hResolverPos_of_conjugateMild,
  clampedResolverSource. truncatedConjugatePicardLimit_eq_conjugatePicardLimit_of_nonneg gives full fn equality.
- SHARED CRUX with Jensen: the hard leaf (DuhamelSourceTimeC1 of source) needs positive-time SPATIAL regularity of S.u
  (uniform W^{2,1}/W^{3,1}, i.e. Hölder-Schauder interior C^{2,1}/C^{3,1} + resolver elliptic gain) — SAME regularity Jensen's
  supersolution needs. Build ONCE. Fable isolating the hard leaf now → will send exact statement.
- REASSESSMENT: χ<0 harder than earlier "all ports" — HSpectral spectral ladder is genuine open math. Workers grinding;
  precise hard-leaf picture pending Fable's isolation.

## cq24 (Q4265) ACYCLICITY — CONFIRMED achievable, no circular blocker [~17:10]
- NO irreducible circular dependency; χ<0 achievable by acyclic route. 3 corrections:
  (1) continuity+nonneg do NOT imply Hölder — need a positive-time parabolic HÖLDER-GAIN theorem before Schauder
      (De Giorgi-Nash-Moser type; Mathlib lacks) — UNLESS the SPECTRAL route substitutes (cq29/cq30 deciding this).
  (2) needs elliptic reg of R + divergence-form parabolic reg of u; (3) C^{2+θ,1+θ/2} on buffered windows.
- ⟹ MAKE-OR-BREAK: does the spectral cosine-eigenvalue bootstrap avoid De Giorgi-Nash-Moser Hölder-gain? If YES (repo
  engines) → χ<0 closes; if only Schauder/Hölder → major infra gap. cq29/cq30 in flight.
- HSpectral FAST progress (Fable): f9a6bb8d M1 generic-S assembler → leaf bundle {hPdeAgreement, hResolverWitness};
  fe90ef7c M2 hPdeAgreement → atomic leaves; 9e394bfa truncated mild time-slice continuity. Decomposition working.
- Energy (Codex): 19b33533 DT core assembled; finishing → Jensen.

## CRUX ISOLATED + DECISION (Fable) — the whole theorem = (C1)+(C2) mild regularity [~17:25]
- Generic-S HSpectral assembler DONE 0-sorry: bFormMildSpectralBootstrapData_of_leaves : BFormMildSpectralLeaves S → HSpectral.
  hResolverPos free, hTimeNhd from hPdeAgreement midpoint, hPdeAgreement via generic-S port (LadderOutput bypassed). Committed.
- HSpectral bottoms out (0-sorry) at BFormMildSpectralLeaves S {bc/hbsum/hagree, hsrcB, hB_restart, hlogData/hchemData,
  hResolverWitness}. ALL 5 reduce to ONE fact = positive-time parabolic regularity of generic mild S.u:
  (C1) SPATIAL: interior slice S.u σ ∈ C²[0,1] Neumann ⟺ eigenvalue-weighted-ℓ¹ cosine coeffs. ⇒ bc/hbsum/hagree + continuity halves + resolver quad decay.
  (C2) TIME: bForm source coeffs time-C¹ + uniform ℓ¹ envelope (W^{2,1}/W^{3,1}) ⇒ hsrcB; localRestartCoeff rep ⇒ hB_restart;
       source-lift Fourier ⇒ hlogData/hchemData; resolver witness ⇒ hResolverWitness.
- = THE SHARED CRUX with Jensen (supersolution regularity). No 0-sorry producer any family — genuine paper core.
- DECISION: Fable grinds (C1) in NEW SHARED file IntervalMildPositiveTimeRegularityV6.lean (generic S), imported by BOTH
  HSpectral + Codex's Jensen. Structure: ⟸ (ℓ¹⇒C²) = cosineCoeffSeries_contDiff_two (easy); HARD = prove eigenvalue-weighted-ℓ¹
  via FINITE regularity bootstrap (base from bounded-source Duhamel ODE, per-pass gain via ladder_pass_gain; SPECTRAL substitute
  for Schauder/De Giorgi — cq29/30/31 deciding wiring-vs-new-lemma). (C2) next.
- Energy (Codex): finishing → Jensen (will IMPORT the Fable's shared (C1)).

## ★ THEOREM REDUCED TO ONE LEMMA [~17:45]
- DELIVERED 0-sorry, axiom-clean (Fable, commits through c9926634/1824f017): HSpectral generic-S assembler
  (bFormMildSpectralBootstrapData_of_leaves), shared (C1) mildSlice_contDiffOn_two_neumann (C²+Neumann slices, acyclicity
  concretely dodged), Jensen reduction (truncatedJensenStrictPosDataFor_of_strictPos), + 2 latent-bug repairs.
- ⟹ ENTIRE χ<0 theorem reduced to ONE named hard lemma: bFormSource_duhamelSourceTimeC1 (the source-regularity ladder:
  per-mode time-C¹ + uniform ℓ¹ envelope W^{2,1}/W^{3,1} + uniform deriv bound, generic S). = genuine paper core =
  finite terminating spectral bootstrap (cq29: +1 deriv/pass, base bounded-source, restart-window; NO Schauder/De Giorgi).
- ROUTING (decided): Fable builds hsrcB generic-S (RESUMED, working). NOT the 6 truncated sorries (different family, no payoff).
- Jensen: Codex imports (C1) [delivered] → weak (w−u)₊ comparison → strict pos → reduction thm → jensenStrictPos.
  Likely does NOT need hsrcB (weak/energy level). Brief updated with the (C1) import.
- Energy: Codex finishing → Jensen. mapCertificate: producer exists.
- REMAINING: hsrcB (Fable, the one crux) + Jensen weak-comparison (Codex) + energy finish + final assembly. cq30/31/32 support hsrcB.

## ★★ REDUCED TO ONE FRESH ENGINE + Jensen [~18:05]
- Fable resolved circularity concretely: hsrcB ladder is FINITE INDUCTION on pass count, base = WindowSourceEnvelope 0
  DIRECT from S.hbound (unconditional, breaks loop, NO (C1)). Heat pass ladder_pass_gain_envelope (IntervalCoeffLadderFull:186,
  +2 gain, 0-sorry) + combiner bFormSource_duhamelSourceTimeC1 + eigenvalue engine = all REUSE.
- THE ONE FRESH ENGINE = sourceEnvelope_of_solutionEnvelope : (u≥δ>0) → WindowCoefficientEnvelope m (u) → WindowSourceEnvelope
  (m−1) (source). = u^γ Nemytskii ‖u^γ‖_{H^{m-1}}≤C(M,δ)‖u‖_{H^m} + R∈H^{m+2} elliptic gain + flux product algebra + Bessel.
  = cq31's content. δ>0 uniform lower bound from S.hpos+S.hcont+compactness (needed for γ∈[1,2), u^{γ-2}).
- ⟹ ENTIRE χ<0 = {Jensen (Codex, weak (w−u)₊ + (C1)[done] + seed Q4273), one fresh engine sourceEnvelope_of_solutionEnvelope
  (Fable/Codex, =cq31)}. Everything else DONE/reuse. 2 passes (r=0→2) reach source ℓ¹.
- Q4273 (cq28) = Jensen sqrt restart seed → Codex (not hsrcB). cq30 done (Schauder-substitute confirm). cq31 (the engine) landing.
- Fable: building base + scaffold (engine stubbed) first milestone; recon on reuse/fresh split from 6-sorry file's non-sorry parts.
- PLAN: if the engine is large, Codex takes JUST sourceEnvelope_of_solutionEnvelope after Jensen; Fable keeps scaffold+time-C¹(cq32).

## ★★★ CRUX MOVED (Fable recon) — the ONE open leaf is the TIME-DERIVATIVE ∂ₜ(S.u) [~18:30]
- SPATIAL ℓ¹/decay leg = ALREADY SOLVED (sorry-free): logisticSource/powerSource_duhamelSourceTimeC1_of_representation
  (IntervalDomainLogisticWeakH2Adapter:119/154), IntervalResolverPowerDecay (ν·u^γ decay done, hpos absorbs δ), +2 ladder
  gain, eigenvalue engine. ⟹ cq31 (u^γ Nemytskii/flux/Bessel) is REDUNDANT — do NOT spend Codex there.
- THE ONE OPEN LEAF: mildSolution_slice_hasDerivAt_time : S → per interior (t,x) HasDerivAt (r↦S.u r x) (∂ₜu) t [+cont+bound].
  ConjugateMildSolutionData has NO time-deriv field; only reconstruction (IntervalMildTimeDerivReconstruction) is circular
  with hsrcB. Non-circular base = restart ODE ∂ₜc_k=−νλ_k c_k + s_k(t), needs only s_k CONTINUOUS (S.hcont) — breaks
  circularity at CONTINUITY level. = the 6 truncated Bootstrap sorries generalized to generic S.
- ROUTE (cq33 fired): per-mode ∂ₜc_k via FTC/Leibniz on ∫e^{-νλ_k(t-s)}s_k (kernel smooth in t, NO 1/(t-s) singularity —
  contrast pointwise ∂ₜu); termwise sum converges by eigenvalue-ℓ¹[done]+s_k ℓ¹[done]; feeds logisticReaction_comp_hasDerivAt
  + CoupledChemDivLocalChainRule.exists_local_slab (∂ₜu,∂ₜv). REDIRECT: cq33 + Codex(after Jensen) → this leaf. cq31 moot.
- Fable building scaffold reduction isolating this ONE leaf (spatial discharged by existing adapters). Combiner + representation reuse.

## ★★★★ HSpectral = ONE EXISTENTIAL LEAF + wiring [~18:45]
- Fable SHIPPED the named leaf 0-sorry (type): MildSolutionSliceHasDerivAtTime S : ∃ udot, (∀t∈(0,T),∀x HasDerivAt(r↦S.u r x)(udot t x) t)
  ∧ (∀t Continuous(udot t)) ∧ (window-uniform bound). In IntervalMildPositiveTimeRegularityV6.lean.
- HSpectral reduced 0-sorry to: (1) FILL this leaf [the analysis, cq33 route: udot=∑(−νλ_k c_k + s_k)cos, per-mode FTC-with-param
  (s_k continuous suffices), termwise via majorant from solved eigenvalue-ℓ¹]; (2) wiring glue hsrcB⟸{representation+leaf}
  (mechanical: coupledLogistic/chemDiv = cosineCoeffs(...∘lift) via cosineCoeffs_congr_on_Icc + producers + combiner).
- DECISION: Fable builds wiring glue NOW (parallel, safe vs fixed leaf type) + first pass on the leaf (has context+cq33);
  Codex stays on Jensen; if leaf balloons, Codex takes JUST the leaf after Jensen.
- ALL else DELIVERED 0-sorry: HSpectral assembler, shared (C1) mildSlice_contDiffOn_two_neumann, δ uniform_positive_lower_bound,
  restartSliceCoeff*, spatial source adapters (logistic/power _of_representation), Jensen reduction. 
- ⟹ ENTIRE χ<0 = {Jensen (Codex, weak comp+C1+√seed, closes at u≥0) + fill MildSolutionSliceHasDerivAtTime (Fable/Codex, cq33)}
  + mechanical wiring + final assembly. cq33 (leaf analysis) landing.

## OPERATIONAL (Xiang) [~18:55]: warm Fable ONLY — no new agent spawns. Route all recon/oracle via SendMessage-resume of
   the warm Fable (ad95f97). Heavy Lean = Fable(Fable5) + window-6 Codex(GPT5.6); analysis = ChatGPT tabs. Main Opus = coordinate only.

## ★ CORRECTION (Fable, signature-verified) — hsrcB ⟸ {R, L}, TWO leaves not one [~19:05]
- Spatial PRODUCERS (logistic/power_of_representation) CONSUME R as hypothesis; R itself (eigenvalue-ℓ¹ of S.u coeffs) is
  OPEN and is the BULK. My "0-sorry when L lands" was WRONG.
- R = spatial ladder: base WindowSourceEnvelope 0 (S.hbound, direct) → heat +2 (ladder_pass_gain_envelope, reuse) →
  source-from-solution −1 (u^γ Nemytskii+flux = cq31, NOT redundant — R's fresh engine). R⟸WindowSourceEnvelope 2 via
  restartCoeff_eigenvalue_weighted_summable_of_pass2_envelope (IntervalCoeffLadderPassBasic:88, sorry-free). ~2 passes.
- L = MildSolutionSliceHasDerivAtTime (committed, cq33 route: mode-ODE ∂ₜc_k=−λc_k+s_k + termwise majorant + δ-floor).
- ⟹ TWO genuine analysis engines: (cq31) sourceEnvelope_of_solutionEnvelope [R's −1 pass], (cq33) L's FTC+termwise.
  Both = paper-core PDE bootstrap. Fable: {R,L} wiring + pass-induction plumbing (reuse) + first pass on both engines.
  Codex: onto heavier engine after Jensen. cq31 back in flight (relay when done); cq33=Q4277 done.
- ACCURATE: χ<0 = {Jensen (Codex) + R spatial-ladder engine + L time-deriv engine}. NOT one leaf. Both bounded/structured.

## ★★ VERIFIED FINAL STRUCTURE (Fable grep) — R is the core; ONE engine = cq31 [~19:20]
- grep: ZERO repo producers for R (eigenvalue-ℓ¹ of generic mild sol from bounded source), the source-from-solution pass,
  or WindowSourceEnvelope base. Spatial adapters only CONSUME R. cq33 shows L DEPENDS on R (majorant needs ∑λ_k|c_k|<∞=R).
- TRUE dep graph: R → L → hsrcB-time; R → hsrcB-spatial; hsrcB+hB_restart → (C1) → HSpectral. ⟹ HSpectral 0-sorry WHEN R LANDS.
- R ⟸ base(S.hbound) + heat gain(ladder_pass_gain_envelope, reuse) + pass-2 lemma(restartCoeff_eigenvalue_weighted_summable_of_pass2_envelope)
  ⟹ leaves EXACTLY ONE engine: sourceEnvelope_of_solutionEnvelope (u≥δ) : WindowCoefficientEnvelope m → WindowSourceEnvelope(m−1)
  = cq31 (u^γ Nemytskii δ-floored + elliptic R-gain + chemDiv flux algebra + Bessel) + finite induction wiring (reuse).
- cq31 IS the single genuine open engine (message-2 "redundant" was wrong; grep confirms the FEEDING pass is unbuilt).
- ROUTING: Fable builds (a) hsrcB⟸R wiring + (b) R→engine reduction + induction plumbing (mechanical/reuse), stubs the engine.
  Codex fills sourceEnvelope_of_solutionEnvelope after Jensen. cq31 in flight → relay.
- ACCURATE ENDGAME: χ<0 = {Jensen (Codex) + ONE nonlinear engine cq31 (Codex after Jensen)}. Everything else 0-sorry/reuse/wiring.

## Honest refinement (Fable) — base NOT free; shared u^γ lemma is the crux [~19:35]
- TWO engine stubs committed 0-sorry: SourceFromSolutionEnvelopePass S (R-engine, cq31: WindowCoefficientEnvelope m →
  WindowSourceEnvelope m−1), MildSolutionSliceHasDerivAtTime (L-engine, cq33). 7 axiom-clean commits.
- (b) ladder BASE not free: chemDiv divergence ∂ₓ(flux) ⟹ raw coeffs grow like k, |a_k|≤C/k^0 FAILS; real base needs
  u∈C¹ (first heat pass) = truncated file's 6-sorry setup. (a) time-half needs source-coeff ∂ₜ (chain rule + diff-under-integral).
- ⟹ 3 analysis pieces (R-engine + C¹ base + source-coeff time-diff) ALL bottom out in the SAME u^γ Nemytskii bound
  ‖u^γ‖_{H^r}≤C(M,δ)‖u‖_{H^r} + elliptic R-gain + flux algebra. LEVER: stub that as ONE shared lemma; fill once → all 3 close.
- ROUTING: Fable grinds base + time-diff + R-engine WIRING around the single shared u^γ/flux stub (mechanical/reuse elsewhere);
  Codex fills the shared Nemytskii/flux lemma (cq31) after Jensen. ⟹ χ<0 = Jensen + ONE u^γ/flux Sobolev lemma.

## WORKER STATE + CODEX ENERGY BOTTLENECK [~19:50]
- Fable OWNS full HSpectral close (redirected): heat-C¹ base + source-coeff time-diff + the big Nemytskii/flux crux
  SourceFromSolutionEnvelopePass (=the shared u^γ/flux stub, committed). Parallel to Codex. cq31 answer still PENDING on bridge.
- ⚠️ Codex STUCK/slow on ENERGY 2h26m+ (no new energy commit; searching heat-kernel deriv continuity for the DCT dominator).
  Energy 0-sorry but not yet producing UniformTruncatedEnergyDataV6. Jensen QUEUED behind energy → blocked.
- cq34 fired (proactive): the DCT-dominator likely needs only the ALREADY-PROVED gradient bound (neumannHeatGradientTMinusHalfBound)
  + (t−s)^{-1/2} integrability + semigroup strong-continuity — NOT full kernel-deriv continuity. If Codex is over-proving
  continuity, relay this to shortcut it.
- WATCH: if Codex stays stuck, consider (a) relaying cq34 to shortcut the DCT dominator, (b) isolating energy's hard leaf.
- HONEST endgame: χ<0 = {energy (Codex, bottlenecked) + Jensen (Codex, blocked behind energy) + HSpectral (Fable, one Nemytskii
  crux + 2 small) + mapCertificate (done)}. Codex serial queue = the risk.

## FABLE DONE (quota out) — full decomposition committed; χ<0 = Jensen + ONE crux + 2 small, all → Codex [~20:10]
- Fable: 10 commits, 0-sorry, axiom-clean. Delivered: generic-S assembler, shared (C1), δ-floor, ladder base WCE 0,
  BOTH engine stubs, and SourceFromSolutionEnvelopePass carrying COMPLETE drop-in spec (cq31 flux-chain + cq36 IBP route +
  cq38 elliptic-multiplier + δ-floored Nemytskii).
- Fable recon: the crux is NOT pure assembly. Elliptic +2 (resolver_memHSigmaPlus2_of_memHSigma) + product algebra
  (memHSigma_*_of_gt_half, envelopes_trueCosProd) done but only in ℓ²-MemHSigma scale; MISSING general-order:
  (1) MemHSigma/C^k ⟹ pointwise C/k^r Bessel output-bridge, (2) real-power Nemytskii (u^γ,(1+R)^{-β}, δ-floored),
  (3) the −1 flux-deriv cos→sin step. cq36 IBP route SIDESTEPS #1 (pointwise decay from pointwise derivative bounds directly).
- ⟹ CRUX FILLER (Codex, after Jensen) = via committed IBP route: pointwise deriv bounds on u^γ/flux (cq35 Nemytskii δ-floored
  + cq38 elliptic-multiplier for R∈C^{r+2}) → elementary IBP on ∫source·cos(kπx) (Neumann-tower boundary vanish) → C/k^r
  = WindowSourceEnvelope. NO Sobolev/MemHSigma general-order bridge needed.
- Codex STATE: energy DCT-majorant discharge in progress (2h39m, shortcut landed) → then Jensen → then crux + 2 small.
- Tabs: 9/9 saturated. Crux analysis cq35/37/38/39 landing → fold into codex-crux-spec.md.

## ★ ENERGY UNBLOCK (cq49/Q4314) — Codex was stuck on FALSE endpoint goals [~20:55]
- Energy bundle NegativePartStandardHeatSemigroupDuhamelFacts quantified over CLOSED 0<t≤T. For the truncated limit
  (zero-extended s>T, slice at T ≠0), the closed-endpoint facts (source/chem_endpoint_l2_lebesgue, two-sided deriv Duhamel,
  tested_mild_decomposition) are GENERALLY FALSE before nonnegativity — right-sided endpoint averages → 0 not the source pairing.
  ⟹ Codex's 3h+ grind = chasing FALSE endpoint goals, not slow grinding.
- CORRECT ORDER (relayed to Codex window 6): (1) prove OPEN-time (0<t<T) variational nonnegativity u≥0 via negative-part
  Gronwall FIRST — on the OPEN interval NO nonlinear crux, all fields = textbook Neumann semigroup weak-Duhamel differentiation
  identity + the proved B_N duality; (2) THEN closed-endpoint bundle fills TRIVIALLY (neg-part test ≡0 once u≥0).
  The committed energy file already notes this open-first order.
- Codex received the reframe at 3h06m. Watch for pivot → UniformTruncatedEnergyDataV6.
- cq48 (endpoint/semigroup strong-continuity shortcut) still running → relay when done (complements).
- Crux/Jensen/assembly analysis EXHAUSTIVE (cq1-52): crux mostly in-repo+δ-bounds (logistic/elliptic/IBP-p2 in-repo, Nemytskii-δ
  provable, pass-2 target); Jensen weak-level confirmed; assembly trivial. All spec'd for Codex. codex-crux-spec.md written.
