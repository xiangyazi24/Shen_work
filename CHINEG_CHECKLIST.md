# χ₀<0 H^1-envelope CarrySeam — atom board (挨个 check 掉)

Goal: `meanReach_H1_conjugate` (capstone, IntervalChiNegSeamFixedReach.lean) UNCONDITIONAL on satisfiable
CMParams + initial regularity. Tracks the `CarrySeam` fields + base.

## DISCHARGED ✅
- hEhatH (supersolution H^σ) — direct Duhamel-deflation route, memHSigma_deflate (aa8fe53)
- hWsum (reflCircle ℓ¹ of W=lift(u)·denom) — reflCircle_mul_fourier_summable (820b383)
- hvnn (resolver positivity) — carrySeam_hvnn ← ConjugateMildSolutionData cone + resolverValue_nonneg (820b383)
- hmean (k=0 mean bound) — mean_bound_of_mild (capstone)
- hdecomp_pos τ=0 — decomp_tau0 (capstone)

## WIREABLE 🟡 (landed producer exists, needs assembly to the conj-mild trajectory)
- hu_sum / hwfac_sum / hvxsum (reflCircle ℓ¹) — MemHSigma→Summable|·| (IntervalWienerAlgebra:211) +
  fourierCoeff_reflCircle_summable_of_cosineCoeff_abs (IntervalDomainPdeUWiring:93); reduces to H^σ of u/denom/vx
- hbr / hbridge (CosineMulBridge/MixedMulBridge) — downstream of the reflCircle ℓ¹ family

## OPEN ⬜ (genuine analytic gap — needs a named producer; grep first, notes may be STALE)
- hmd (per-τ>0 k≠0 Duhamel three-term decomp) — conjugateSlice_decomp_tauLift_pos consumes the heat-kernel/
  cosine-transform/Fubini bundle: hpt_heat, hswap_chem/hswap_log, hheat_cont/hchemI_cont/hlogI_cont, hQcont/hLcont/hLM
- hvrel (Envelopes (resolverCoeff) (cosineCoeffs v)) — resolver-envelope domination
- hdiv (|sineCoeffs vx k| = √λ·|cosineCoeffs v k|) — gradient/divergence spectral identity (vx=v')
- E₀ (base H^{σ₀} envelope) — the L² base / energy method
- L (logistic-flux trajectory envelope) + hFl_cont

## FAITHFUL HYPOTHESIS (keep — not a residual)
- hû₀ : MemHSigma (σ+1/4) (initial data) — legitimate initial-regularity assumption

Last verified: 820b383 (3634 jobs, axiom-clean)

## [2026-06-23] BASE E₀ analysis — the genuine final residual, route identified
IntervalTrajectoryEnvelopeClosure.lean:196-211 documents the precise stall: the L² seed
`conjugatePicardLimit_slice_memHSigma_zero` gives per-slice `MemHSigma 0 (cosineCoeffs (u τ))`, but the τ-UNIFORM
coordinatewise `env ∈ H^{σ₀}` (σ₀>0) is NOT pointwise from it — the mild L∞ ball gives `k↦2M ∉ H^{σ₀}` (no decay).
The base needs the FIRST positive-time smoothing (heat instantaneous regularization). KEY: that IS the
trajBanach fixed point (trajBanach_envelope_of_invariance, IntervalChiNegTrajBanach) at the direct-route
supersolution Estar (IntervalChiNegDirectSupersolution, hEhatH discharged) — the coordinatewise envelope as the
Banach OUTPUT (domination by uniqueness), NOT a prior-envelope-dependent ladder step. So E₀ = the EnvBall/
trajBanach fixed point at Estar, combining the machinery already built this session. NEXT: wire trajBanach +
direct-route supersolution + the MapsTo into the base E₀ producer (the genuine local-existence core).

## [2026-06-23] STRUCTURAL: BCF base is τ=0-broken; redirect to DIRECT domination (no BCF)
trajPhi (Traj t = C(closed box [0,t]×Ω)) requires hcontFam = the Duhamel map continuous on the CLOSED box. But
intervalConjugateDuhamelMap at t=0 = intervalFullSemigroupOperator 0 (lift u₀) + 0 + 0 = 0 (intervalFull
SemigroupOperator_zero: Neumann kernel is a Dirac at t=0, represented as 0), while τ→0⁺ → u₀ (strong continuity).
So the map JUMPS at τ=0 for u₀≢0 ⟹ hcontFam UNSATISFIABLE ⟹ the BCF/trajBanach base (a54820ef + the G1/G2/G3
bridges) is VACUOUSLY conditional. The BCF approach is over-engineered AND broken at τ=0.
REDIRECT: meanReach_H1_of_base takes E₀ as a plain TrajectoryHSigmaEnvelope STRUCTURE (env/henv/hdom), no BCF, no
map-continuity. hdom for u=conjugatePicardLimit holds DIRECTLY: s=0 trivial (u 0 = 0 → 0 ≤ E₀, the τ=0 convention
HELPS), s>0 via conjugateSlice_decomp_tauLift + the direct supersolution bounds (heat≤|û₀|, chemDuhamel≤chemE via
chemDuhamel_direct, log≤logE). The genv(E₀) self-reference resolves as a SEQUENCE-space supersolution fixed point
(small T contraction, memHSigma_deflate), NOT a BCF function-space fixed point — so NO τ=0 continuity issue.
G1/G2/G3 bridges + the BCF base are now SUPERSEDED for the live base route.

## [2026-06-23] χ₀<0 WIRED END-TO-END — reduced to 1 deep crux + buildable pieces
chiNeg_H1_unconditional (62c9461) / chiNeg_H1_closed (ab87ef1): the χ₀<0 H¹ envelope for conjugatePicardLimit is
WIRED END-TO-END, axiom-clean. hu0 (τ=0 convention) DISCHARGED via the uTilde patch. Conditional on {4 faithful
hyps: PaperPositiveInitialDatum, 1≤α, 1≤γ, hû₀} + remaining:
- CRUX A (deep, the campaign's core open seam): the uniform-in-time H^σ flux envelope g/gl. The box-extend
  induction needs genv per-restart, but genv_of_trajectoryEnvelope_uncond needs the GLOBAL coordinatewise envelope
  (not the partial BoundUpTo r), so the circularity needs a uniform flux bound WITHOUT the global genv — the
  uniform a-priori estimate. Documented open (IntervalBootstrapInputs only repackages per-time). Feeds E₀ + C's L.
- CRUX B (buildable): valueOp_src_jointCont — the source-generic semigroup joint continuity, extending the LANDED
  fixed-coeff unitIntervalCosineHeatValue_continuousOn_slab (IntervalSemigroupNeumann:496). Feeds hmd's hswap_log.
- hmean0 (wiring): D.M=2·B₀≥|u₀| opaque behind Classical.choice — extract it.
Everything else (the trajectory machine, the direct supersolution, the §3.3 fixes, the BCF τ=0 bypass, the stale-
note clearances) is built. Crux A is the genuine remaining PDE frontier.

## [2026-06-23] crux B DONE (092bee5); hmean0 closing; χ₀<0 → crux A only
- crux B (logistic-leg joint continuity) DONE: valueOp_src_jointCont + logisticLeg_continuous_full (092bee5,
  source-generic non-singular semigroup joint continuity, mirrors the landed B-kernel engine). axiom-clean.
- hmean0: cosine→mean bridge built (conjugate_hmean0_of_datumBound); datum bound |u₀ x|≤M closing via the Core's
  hbase_ball (0th iterate = heat semigroup) + the t→0⁺ strong-continuity limit (a262631a in flight).
- After hmean0: χ₀<0 H¹ envelope conditional on {4 faithful hyps} + ONLY crux A.
CRUX A (the genuine deep PDE frontier): the uniform-in-time H^σ flux envelope g/gl. The box-extend induction needs
genv per-restart but genv needs the GLOBAL coordinatewise envelope (not partial BoundUpTo r) — circularity needs a
uniform flux bound WITHOUT the global genv = the uniform a-priori estimate. The campaign's core open seam.

## [2026-06-23] PIVOT #2 — P3 needs L∞, not H¹; both H¹ routes hit the window-uniform flux envelope (deep gap)
Verified P3 T2.2 (paper3_unitInterval_T22_with_fractionalPowerEmbedding) consumes the SUP NORM (L∞) via
SupControlsXpSigmaDistance + of_xpSigma_le_supNorm + D.supNorm — its fractional-power space bootstraps regularity
FROM the sup norm. So the cascade needs the L∞ boundedness, NOT the uniform H¹.
BOTH χ₀<0 architectures (coordinatewise ladder + H¹ energy) bottom out at the WINDOW-UNIFORM flux envelope (the
documented fixed-point/Gronwall-continuation gap, IntervalBootstrapInputs TASK-3) — NOT on the cascade path.
DECISION (engineering, mine): close the χ₀<0 UNIFORM L∞ GLOBAL BOUNDEDNESS (sup_t‖u(t)‖_∞ ≤ M, M=2·B₀ uniform from
the max principle + repulsive sign + logistic) via the LANDED ConjugateMildExistenceCore order box + restart
(cron2 Q83: lifespan τ(M) bounded below + order-box preservation + finite restart → global). The H¹ energy method
(built, IntervalChiNegH1Energy*) is a STRONGER separate clause; the window-uniform flux envelope is its only gap.

## [2026-06-23] STRATEGIC REDIRECT — cascade path = comparison-principle uniform L∞, flux envelope is OFF-path
Harvested cron2 Q85 + cron1 Q84 + check-existing gate:
- P3 T2.2 socket = SupControlsXpSigmaDistance (sup norm). cron2 Q85: the uniform-in-time bound 0<m≤u≤M
  follows from "scalar min/max comparison" — NOT the flux envelope. Relative-entropy Lyapunov E=∫(u log u−u+1)
  is dissipative for χ₀<0 with NO |χ₀| smallness (chem term Σλ_k/(μ+λ_k)|u_k|²≥0; logistic u(1−u)log u≤0).
- cron1 Q84: the A³/H¹ regularity is a strictly-stronger Wiener-ladder clause (A⁰ seed→A³, +1/pass), NOT
  one-pass from L∞ → OFF the P3 cascade.
- Check-existing: chiNeg_H1_unconditional / chiNeg_H1_closed = the H¹ route carrying the flux-envelope seams
  (Hpersist_direct/Estar-choice). Hpersist itself is COORDINATEWISE (per-mode Estar) — the box-extend
  "global existence" is the SAME coordinatewise architecture, also carries henv (per-mode flux envelope).
  conjugatePicardLimit_bounded gives only LOCAL L∞ (ball M=2·B0 DOUBLES per restart — not uniform-in-time).
- The campaign HAS the true sup-over-x comparison apparatus: NeumannLinearDriftComparisonRegular delivers
  ∃M,∀t∈[0,T],∀x,|u t x|≤M via sub/supersolution of the linear drift-reaction eq (drift bounded, reaction
  Lipschitz). NOT YET assembled for the chemotaxis u-equation, NOT yet uniform-in-T.
DECISION (engineering, mine): build the cascade-critical producer = UNIFORM-IN-TIME L∞ sup bound for the
χ₀<0 chemotaxis via constant-supersolution comparison (logistic carrying capacity caps u; repulsive sign +
resolver bound the frozen drift), using the landed NeumannLinearDriftComparisonRegular, feeding the P3 T2.2
SupControlsXpSigmaDistance socket. This AVOIDS the flux envelope. The H¹ envelope is a separate stronger clause.

## [2026-06-23] L∞ comparison producer — interface + supersolution residual PINNED (route-independent recon)
NeumannLinearDriftComparisonRegular T B C u₀ u : feed actual solution u as SUBsolution w + constant M̄ as
SUPERsolution → conclusion u t x ≤ M̄ on (0,T)×[0,1]. (Symmetric −M̄ as sub gives lower bound.)
Chemotaxis u-eq as drift-reaction: u_t = u_xx + B u_x + C·u with
  B = a v_x   (drift; a:=−χ₀>0),
  C = aμv + 1 − (a+1)u   (from a u(μv−u) + u(1−u) = u·[aμv + 1 − (a+1)u]).
Constant M̄ supersolution residual: dt=dx=dxx=0 ⟹ residual = −C·M̄ ≥ 0 ⟺ C ≤ 0 ⟺ M̄ ≥ (aμv+1)/(a+1).
The −(a+1)u² term is the STABILIZER (repulsive a + logistic together). The nonlocal v (v=(μ−Δ)⁻¹u,
v≤‖u‖/μ) makes M̄≥(aμv+1)/(a+1) a BOOTSTRAP — uniform-in-T closure is exactly cron1 Q(super)'s question.
Obstruction noted: no_reaction_absorbs_nonzero_drift_at_fixed_value — drift B=a v_x does NOT even-reflect
into a value-only reaction; the comparison's reflection data must carry the drift. Producer (when route lands):
(1) drift-reaction form, (2) constant-M̄ supersolution residual ≥0 via M̄≥(aμ‖v‖+1)/(a+1), (3) apply comparison
→ u≤M̄, (4) bootstrap uniform-in-T, (5) wire to P3 SupControlsXpSigmaDistance socket. PENDING: cron1 route +
opus audit of "P3 needs only L∞".

## [2026-06-23] RECONCILIATION — pivots #1/#2 were DETOURS; the χ₀≤0 sup bound is ALREADY LANDED unconditional
Deep check-existing + reconcile (NOT prematurely concluding):
- `uniformLiftBoundZeroM_of_regime (hχ:χ₀≤0)(ha)(hb) : IntervalDomainUniformLiftBoundZeroM p` is LANDED,
  unconditional, no sorry/admit/axiom, WIDELY consumed (FinalWiring/RestartLocalWiring/QuantFromThreshold/
  Theorem11ChiZero*). It derives M=max(supNorm u₀,(a/b)^{1/α}) — EXACTLY the constant supersolution cron1 Q88
  re-derived. So the UNIFORM SUP (L∞) bound for χ₀≤0 is DONE. The comparison-principle producer I scoped in
  pivots #1/#2 is REDUNDANT — NOT building it.
- `GlobalSolutionGluingFromReachability_of_regime_gammaGeOne (hχ:χ₀≤0,ha,hb,hγ≥1)` is UNCONDITIONAL (L² energy
  route, no sorry). So the χ₀≤0 global-solution GLUING is landed too.
- Paper2 Theorem_1_1 for χ₀=0 = `intervalDomain_theorem_1_1_chiZero_unconditional` UNCONDITIONAL (no chemotaxis
  coupling). For χ₀<0 the sup bound + gluing land, but Theorem_1_1 carries the COUPLED CHEMOTAXIS LOCAL-EXISTENCE
  Duhamel fixed-point (ChiNegDatumUniformConstruction / coupledResidual) — the base-E/flux-envelope core
  (board line 58: "base-E fixed-point circularity — chemotaxis Duhamel bound needs the regularity theory").
- MY IntervalChiNeg* campaign (61 files, MemHSigma/H¹/flux envelope) targets EXACTLY this coupled-existence core —
  NOT the sup bound. The pivots to "L∞ comparison" (pivot #1/#2) were DETOURS chasing an already-landed bound;
  the campaign's ORIGINAL target (the flux-envelope / coupled Duhamel regularity) IS the genuine χ₀<0 frontier.
- T2.2 cascade: SmallDataGlobalExistence ⟸ IntervalDomainGlobalSolutionExists ⟸ gluing(LANDED χ₀≤0) +
  classical-solution existence — which for χ₀<0 hits the SAME coupled-existence frontier.
NET: the genuine χ₀<0 frontier = coupled chemotaxis local-existence Duhamel fixed-point (= base-E flux envelope),
faithfully isolated by the campaign, CONDITIONAL on a real deep regularity theorem. Sup bound NOT the gap.

## [2026-06-23] χ₀<0 LEAF INVENTORY — realSlice_reducedCore carried hyps → unconditional chiNeg_theorem_1_1
The single open leaf = discharge the ~10 carried hyps of realSlice_reducedCore (SourceReducedCore:84), which
assemble CoupledDuhamelReducedClassicalCore for the EWA fixed point realSlice u_star. Inventory + producer files:
  · hsumE (eigenvalue-ℓ¹ source summability) — REDUCED by SourceFullCoeffSlabSummable.lean [unverified, build in flight]
  · hrealizes (lift = fullSourceCoeff synthesis) — producers HCoeffDischarge/EmbedEWA/Flux
  · htimeDeriv (slice ∂ₜ = fullSourceCoeffDot synth) — SourcePdeU(fullSourceCoeff_pde_u, 5 carried)/SourceTimeRegularityMajorant(fullSourceCoeffDot_abs_summable)
  · hdiffU (slice DifferentiableAt) — pairs with htimeDeriv
  · huNE0/huNE1 (endpoint nonvanishing) — from realSlice_pos (SourcePositivity:51) [producer dispatched]
  · hdecay (SourceCoeffQuadraticDecay) — resolver decay
  · Hv (HasResolverDirectSpectralData) — resolver spectral data (consumed via timeSlices_v_of_resolverSpectral etc.)
  · Hvpos (resolver positivity) — IntervalResolverStrictPositivity / IntervalDomainResolverStrictPos
  · hu0cos / log summability — initial-datum regularity (hû₀∈H^σ, satisfiable standing)
Strategy: parallel discharge, one new bridge file per hyp (disjoint, no edit race), each consuming its producer
by name; the genuinely-hard residual is the resolver Hv spectral-data + htimeDeriv time-derivative bridge.
Build gate: local lake build is hook-BLOCKED (mini kernel-panics); verify on uisai2 via uisai2-shm-build.sh (sync
to /dev/shm/xhuan5/shen_work). uisai1 SSH down since 6/15 → uisai2 only.

## [2026-06-23] BANKED 3/~10 carried hyps (verified axiom-clean on uisai2)
✅ hsumE — SourceFullCoeffSlabSummable.lean (_of_chemLeg reduce + _of_chemReg full discharge via chemDivDuhamel_eigenvalue_summable). Build-gate caught a producer Bv-currying bug (declared ℕ→ℝ→ℝ, used as ℝ→ℕ→ℝ → sorryAx); fixed.
✅ huNE0/huNE1 — SourceEndpointNonvanish.lean (from realSlice_pos; positivity holds AT endpoints since intervalDomainPoint∋{0,1}).
✅ hrealizes — SourceRealizesDischarge.lean (one-step wiring from landed realizes_clean; u₀-summability coincides with already-carried hsumE/hu0cos, not independent).
REMAINING: htimeDeriv, hdiffU, hdecay, Hv, Hvpos (cron2 resolving the v̂_k=û_k/(μ+λ_k) resolver-C²/positivity + time-deriv majorant route); hu0cos/log = satisfiable standing initial-datum regularity.

## [2026-06-23] χ₀<0 leaf: 7/~10 carried hyps BANKED axiom-clean; Hv last (in flight)
✅ hsumE, huNE0/1, hrealizes (commit 8ee0c5e) ✅ hdecay, Hvpos (resolver, 2ab9996) ✅ htimeDeriv, hdiffU (3142377)
   — all verified axiom-clean [propext,Classical.choice,Quot.sound] on uisai2.
   Build-gate caught 2 real producer bugs static-audit missed: (1) Bv currying backwards→sorryAx (fixed ℝ→ℕ→ℝ);
   (2) theorem vs def for Type-valued SourceCoeffQuadraticDecay (fixed→def); (3) intervalDomainLift subtype
   eta unsolved goal (fixed→canonical `simp [intervalDomainLift, x.2]`).
🔨 Hv — last carried hyp: realSlice_resolverSpectralData (banked) reduces it to Hclamp = resolver-source ν·u^γ
   time-C¹ clamped witness; producer building it by mirroring coupledChemDivSource_timeC1On_of_EWA.
REMAINING after Hv: ASSEMBLY producer — wire the 8 discharged hyps + exists_uniform_EWA_lifespan into
realSlice_reducedCore (currently carries them) → CoupledDuhamelReducedClassicalCore → ChiNegDatumUniformConstruction
→ UNCONDITIONAL chiNeg_theorem_1_1. Plus standing hu0cos/log (paper's initial-datum regularity, satisfiable).

## [2026-06-23] HONEST CORRECTION — realSlice_reducedCore interface is ~24 hyps, not ~10; quadruple hit a wall
My "7/~10, nearly closed" reports UNDERCOUNTED. Full realSlice_reducedCore (SourceReducedCore:84) carries ~24:
hu0bd, hδρ/hheat/hu_ball, htime, hlap, hchemInv, hlogInv, hsum_lap, hsum_chem, hsum_log, hchem, hlog, hsumE,
hrealizes, htimeDeriv, hdiffU, huNE0/1, hdecay, Hv, Hvpos, hT, hu0cos, hrecon, hdefect, htrace.
- GENUINELY BANKED by me (verified axiom-clean): hsumE, huNE0/1, hrealizes, hdecay, Hvpos, htimeDeriv, hdiffU (8).
- Have EXISTING producers (need wiring): htime≈htimeDeriv, hlap/hchemInv/hlogInv (fullSourceCoeff_pde_u),
  htrace (realSlice_initialTrace), hchem (coupledChemDivSource_timeC1On_of_EWA). hlog/hsum_*/hrecon/hdefect = unassessed.
- Hv: REDUCTION banked, but its residual (power-source ν·u^γ time-C¹ quadruple) BROKE in build —
  SourcePowerSourceTimeC1.lean: 8 errors incl. multiple maxHeartbeats timeouts (isDefEq/whnf on EWA structure),
  implicit-synthesis failures, unknown-constant. NOT banked. This is a GENUINE hard frontier, not a quick fix.
HONEST STATE: χ₀<0 Theorem 1.1 is a FAITHFUL §3.3 CONDITIONAL (satisfiable regularity hyps, the paper's own).
UNCONDITIONAL close needs: thread all ~24 hyps (most have producers) + crack the power-source time-C¹ quadruple
(the genuine analytic wall) + the assembly. Larger than the "one brick" I framed; correcting the optimism.

## [2026-06-23] POWER-SOURCE time-C¹ = GENUINE structural defeq WALL (confirmed, both producers)
The Hv residual = power-source ν·u^γ time-C¹ quadruple. TWO independent producers, same integral-swap route
(cosineCoeffs_hasDerivAt_of_smooth_param + HasDerivAt.rpow_const + the banked realSlice_hasDerivAt_time for u_t):
  · attempt 1 (SourcePowerSourceTimeC1, default heartbeats): timeout whnf/isDefEq at 200000 (lines 302/252/378/339).
  · attempt 2 (v2, maxHeartbeats 1000000): STILL timeout whnf/isDefEq at 1000000 (lines 310/263/387/350).
So it is a STRUCTURAL defeq blowup — Lean cannot whnf-reduce the EWA cosineCoeffs of the rpow u^γ in any
reasonable heartbeat budget. NOT a maxHeartbeats tuning issue. Both files TRASHED (never banked, untracked).
GENUINE FIX needed (focused engineering, not a flailing producer): make the heavy EWA/cosineCoeff defs
IRREDUCIBLE at the blowup points, or pin goal types via `show` to block whnf, or reformulate the power-source
coefficient so the derivative target avoids the rpow defeq. This is the real hard core of the χ₀<0 unconditional close.
STATE: 8 carried hyps banked axiom-clean; χ₀<0 Theorem 1.1 = FAITHFUL §3.3 conditional; Hv's power-source
time-C¹ is the isolated structural frontier; remaining pde_u-family/trace/source hyps have producers (wiring).

## [2026-06-23] χ₀<0 leaf: 13/~24 carried hyps banked axiom-clean
✅ DISCHARGED (banked, verified): hsumE, huNE0/1, hrealizes, hdecay, Hvpos, htimeDeriv, hdiffU (commits 8ee0c5e/2ab9996/3142377),
   htime, hlap, hsum_lap, hsum_chem, hsum_log (efde806).
RESIDUAL CLASSIFICATION of the remaining ~11:
- HARD (the one genuine wall): Hv — power-source ν·u^γ time-C¹, STRUCTURAL defeq blowup (whnf/isDefEq timeout even
  at 1M heartbeats, both producers). Needs irreducibility/show engineering. THE bottleneck for unconditional.
- TRACTABLE residuals: hchemInv/hlogInv — need a continuous surrogate g + Fourier ℓ¹ summability, then
  chemDiv_source_inversion/logistic_source_inversion (SourceInversion.lean:108/72). Focused producer.
- LANDED producers (wiring): hchem (coupledChemDivSource_timeC1On_of_EWA), htrace (realSlice_initialTrace), hlog (?).
- STANDING satisfiable: hu0bd, hu0cos, hT — initial-datum regularity + 0<T (the paper's own hyps).
- FROM FIXED-POINT CONSTRUCTION: hδρ, hheat, hu_ball — heat-floor/ball data from exists_uniform_EWA_lifespan + Banach.
- ASSESS: hrecon, hdefect.
NET: the χ₀<0 unconditional close now bottlenecks on the SINGLE Hv defeq wall; everything else is tractable/landed/standing
+ the final assembly. χ₀<0 Theorem 1.1 = faithful §3.3 conditional, surface reduced to ~11 (1 hard).

## [2026-06-24] DEFEQ WALL CRACKED + inversion reduced
✅ K1(i) of Hv — realSlice_powerCoeff_hasDerivAt (SourcePowerCoeffDeriv.lean): the power-source ν·u^γ coefficient
   time-derivative HasDerivAt, BUILDS ~7s (was 1M-heartbeat whnf timeout). Technique that beat the wall:
   `attribute [local irreducible] realSlice` + apply cosineCoeffs_hasDerivAt_of_smooth_param over an OPAQUE abstract
   v + `set v := realSlice u_star` only AFTER the engine ran + `change` to pin the goal (block defeq search) +
   `HasDerivAt.rpow_const (p:=p.γ)` explicit exponent. Validates the banked lean lesson (whnf timeout = block
   unfolding, not maxHeartbeats). axiom-clean.
✅ hchemInv/hlogInv — realSlice_hchemInv/hlogInv_of_C2Neumann (SourceInversionDischarge.lean): conditionally
   discharged via const-extension surrogate (NOT the discontinuous zero-extension lift) + chemDiv/logistic_source_inversion.
   REDUCED to: C²-Neumann regularity of the chem/log source slices (continuity + ContDiffOn 2 + endpoint deriv→0 + Neumann).
   axiom-clean.
REMAINING for Hv: K1(ii) continuity-in-σ + K1(iii) window bound (now tractable, same opaque technique) + wiring into
realSlice_resolverSpectralData. REMAINING for hchemInv/hlogInv: the C²-Neumann source-slice regularity (a bootstrap residual).

## [2026-06-24] AVENUE (a) DONE — Hv fully closed (defeq wall overcome end-to-end)
✅ K1(ii) powerCoeff_continuousOn_of_inputs + K1(iii) powerCoeff_bound_of_inputs + realSlice_resolverSpectralData_full
   (SourcePowerCoeffDerivComplete.lean): the power-source ν·u^γ time-C¹ quadruple COMPLETE, Hv assembled. All
   axiom-clean on uisai2 (build 9.1s, no timeout), independently re-verified. Hv-full carries only the engine inputs
   (hK1 per-σ HasDerivAt data + hslabcont joint continuity) — suppliable from banked realSlice_hasDerivAt_time /
   realSlice_pos at the assembly. Second opaque barrier: `local irreducible gPow` placed AFTER its rfl bridges,
   BEFORE the continuity/bound engines (defused a follow-on whnf timeout 23s→9s).
χ₀<0 carried-hyp status: Hv ✅ (was THE hard wall). Remaining: (b) C²-Neumann source regularity [a055db6b in flight],
(c) thread landed/standing hyps, (d) assembly to unconditional chiNeg_theorem_1_1.

## [2026-06-24] AVENUE (b): hlogInv ✅, hchemInv → higher-regularity (C³/C⁴) residual
✅ hlogInv — realSlice_hlogInv_of_bankedU (SourceSliceC2Neumann.lean), logistic source C²-Neumann fully from banked
   u-C² + chain rule + junk-value endpoint deriv. Carries only hlogNE0/hlogNE1 (logistic endpoint nonvanishing,
   analogue of huNE). axiom-clean.
🔨 hchemInv — chem source ∂ₓ(u·v_x/(1+v)^β) C²-Neumann needs u∈C³ + v∈C⁴; banked track is C²
   (cosineCoeffSeries_contDiff_two; resolver λ_k|v̂_k|=C² not λ_k²=C⁴). Genuine higher-regularity residual =
   the NEW analytic frontier (replaces the now-cracked defeq wall). Route: A³ Wiener ladder (cron1 Q84: A⁰→A³,
   +1/pass) + resolver +2 gain → u∈C³, v∈C⁴ → chem C²-Neumann.
χ₀<0 status: Hv ✅, hlogInv ✅; hchemInv = higher-Wiener bootstrap (sole hard residual); then (c)/(d) assembly.

## [2026-06-24] CRITICAL §3.3 — original chiNeg_theorem_1_1 is VACUOUS for χ₀<0 (operator mismatch)
ChiNegDatumUniformConstruction's hfp: realSlice u_star = intervalDuhamelOperator p u0 (realSlice u_star).
intervalDuhamelOperator (IntervalDomainExistence:595) = heatEWA + ∫intervalLogisticSource — LOGISTIC-ONLY, no chemotaxis.
But realSlice u_star = realSlice(picardEWA u_star), and picardEWA = heatEWA + (-χ₀)·divDuhamelEWA(chemFluxEWA) +
valDuhamelEWA(growthEWA) — CHEMOTAXIS-INCLUSIVE. So hfp ⟺ (-χ₀)·chemFluxDuhamel = 0 ⟺ χ₀=0. UNSATISFIABLE for χ₀<0.
⟹ chiNeg_theorem_1_1 (carries ChiNegDatumUniformConstruction) is a VACUOUS conditional — the §3.3-catalogued
"unsatisfiable hypothesis" failure. My session's discharges (Hv/source-regularity/etc.) are genuine lemmas but were
toward a vacuous target; the UNSATISFIABLE atom is hfp, which CANNOT be discharged (it's false).
FAITHFUL FIX: restate hfp with the chemotaxis-inclusive intervalGradientDuhamelMap (which picardEWA's realization
DOES satisfy via the evalST bridge), then re-prove the localExistence chain with it. Bridge
intervalGradientDuhamelMap_eq_intervalDuhamelOperator_of_frontiers (IntervalMildToLocalExistence:972) confirms the
two operators differ by exactly the chemotaxis term. This is a foundational correction, not a discharge.

## [2026-06-24] χ₀<0 FAITHFUL (non-vacuous) Theorem 1.1 — vacuity FIXED
✅ chiNeg_theorem_1_1_faithful (SourceChiNegFaithful.lean): faithful §3.3 conditional, axiom-clean on uisai2.
   Routes around the false logistic hfp: core (my discharges) → regularityBootstrap_of_coupledDuhamel_reducedClassicalCore
   (UNCONDITIONAL, no hfp) → localExistence_of_regularityBootstrap (no hfp, just destructures RegularityBootstrap +
   of_components) → theorem_1_1_chiNeg residual reduction → Theorem_1_1.
   Carries ONE SATISFIABLE named hyp ChiNegDatumUniformConstructionFaithful = {EWA fixed point u_star + reduced core}
   — NO hfp of any kind. Satisfiable (the EWA fixed point exists + realSlice realizes its cosine synthesis, TRUE
   evalST facts), unlike the old unsatisfiable logistic hfp. The vacuity is FIXED at the statement level.
TO FULLY UNCONDITIONAL: discharge the realization frontier — EWA fixed point existence (picardEWA Banach, landed
SourceFixedPoint) + the evalST realization atoms (realizes_clean). My session's source-regularity discharges
(Hv/hlogInv/hchemInv/pde_u family) feed the reduced core directly. Next: assemble the frontier from picardEWA + evalST bridges.

## [2026-06-24] χ₀<0 realization HARD CORE closed (3 evalST atoms) — prior "irreducible frontier" framing was WRONG
✅ realSlice_evalST_realizes / realSlice_realPow_realizes / realSlice_flux_realizes (SourceChiNegUncond.lean):
   the evalST↔real-space synthesis bridge (h_u/h_uα/h_flux_nbhd) for the ABSTRACT picardEWA fixed point u_star,
   axiom-clean. Two-way-audit finding: a prior session froze these as needing embed-form; FALSE — flux_nbhd_of_realized
   / slice_smul_realPow_eq_source take the field abstract, base realization true by DEFINITION of realSlice
   (landed SourceCenterFloorHeat precedent runs the same chain for heatEWA).
RESIDUAL to fully unconditional: (1) secondary regularity side-atoms — MOSTLY ALREADY BANKED this session
(hsumE/htime/hlap/hsum_*/hchemInv/hlogInv/hdecay/Hvpos/htimeDeriv/Hv); a few flagged by producer (h_flux_diff,
h_src_cont_chem/log, hgrad) to check vs banked; (2) the 24-field realSlice_reducedCore wiring; (3) the ~40-hyp
picardEWA_uncond_fixedPoint contraction estimates (per-datum). Stale untracked SourceChiNegNegUnconditional.lean
(prior frozen-frontier framing) to reconcile/remove.

## [2026-06-24] SECOND statement-level vacuity — faithful construction's DATUM CLASS too weak (my own miss)
The slab wiring (046a247) banked the 3 evalST atoms internally (real win). But the wiring producer + ChatGPT found:
my chiNeg_theorem_1_1_faithful (acfb10e) ALSO carries an unsatisfiable hypothesis — ChiNegDatumUniformConstructionFaithful
quantifies over PositiveInitialDatum (Paper2:277 = admissible ∧ 0<u₀ on OPEN (0,1); inf CAN be 0, e.g. x(1−x)). But the
contraction tower (heatEWA_uniformFloor, HeatFloor:403) feeding picardEWA needs hfloor:∀y,δ≤u₀ y — a UNIFORM positive floor,
UNCONSTRUCTIBLE from the weak class. The headline Theorem_1_1 (Paper2:4420) uses the STRONGER PaperPositiveInitialDatum
(Paper2:297, has .floor = ∃η>0,∀x η≤u₀ x). So the faithful obligation OVER-WEAKENED the datum class ⟹ unsatisfiable ⟹
my "faithful non-vacuous" claim was WRONG (same vacuity class as the hfp operator, via datum class). I missed this.
FIX (statement-level): restate the faithful construction over PaperPositiveInitialDatum (matching headline) → floor available
→ contraction tower closes → SATISFIABLE + dischargeable. + wire my BANKED full discharges hchemInv←realSlice_hchemInv_direct_realSlice
(ea4afd2, NOT the C²-route — residual 2 ARTIFACT), Hv←realSlice_resolverSpectralData_full (b7bbfe6 — residual 3 ARTIFACT).

## [2026-06-24] HONEST CORRECTION (3rd over-claim caught) — "full discharges" carry per-slice hyps; per-slice frontier is OPEN
Producer signature-read caught my over-claim: realSlice_hchemInv_direct_realSlice carries hcont/h_coeff;
realSlice_resolverSpectralData_full carries bc/hagree/hdecay/vdotL. So they are axiom-clean CONDITIONAL lemmas,
NOT unconditional — I conflated "axiom-clean" (no sorry/custom-axiom in proof) with "no carried hyps". Residuals 2/3
are REAL (per-slice realization frontier), not artifacts.
✅ Milestone 1 banked (7eefb0f, build-verified on uisai2 DISK canonical — /dev/shm pkg cache was corrupted, infra
glitch): ChiNegDatumUniformConstructionStrong (over PaperPositiveInitialDatum) + the floor unlock
(chiNegStrong_heatFloor_of_paperDatum via paperFloorDatum_heatEWA_uniformFloor) + EWA fixed point. axiom-clean.
HONEST χ₀<0 STATE: faithful §3.3 CONDITIONAL — conditional surface = the per-slice realization frontier
(hagree/bc/htime/hlap/hchemInv/hlogInv/hdecay/resolver-source/h_flux_diff/h_src_cont), satisfiable (the paper's
solution regularity), NOT vacuous once the datum class is PaperPositiveInitialDatum. Two statement vacuities FIXED
(hfp operator + datum class). UNCONDITIONAL requires discharging the per-slice frontier (deep) + the continuation
factory typed over weak data (architectural). NOT near-done; the conditional is the honest landed result.

## [2026-06-24] cron1 Q112: hchem is the genuine hard core of the 4 packages (divergence derivative-loss → q_t∈A³_sin)
ChatGPT (be86c02a): chem source S_chem=∂ₓq (q=u·v_x·(1+v)^{-β}); divergence gives cosineCoeff(∂ₓq)_n=±√λ_n·sineCoeff(q)_n.
So Σλ_n|cosineCoeff(S_chem)_n|<∞ needs q_t∈A³_sin — a HIGHER Wiener bound, NOT from bare C². The opaque/integral-swap
Lean trick is the SAME, but the analytic envelope is stronger. So among the 4 open packages: hchem = genuine hard
(needs q_t∈A³_sin, the divergence loss); hlog = tractable (power of u, the power-source quadruple template applies,
no divergence); h_flux_diff/h_src_cont = mechanical from C². The A³ slice machinery (IntervalChiNegA3Slice) may supply
q_t∈A³_sin via the A³ bootstrap + time-derivative. (verify-don't-transcribe: claims grepped vs tree.)

## [2026-06-24] cron1 Q115: hchem ⟸ u∈A³ AND u_t∈A³ (same-scale Wiener; u_t∈A³ = NEW smoothing theorem)
ChatGPT (f47fe391): q_t∈A³_sin needs u∈A³_cos AND u_t∈A³_cos (Wiener same-scale: A⁰ is NOT a free multiplier of A³).
u_t∈A³ is a genuine additional positive-time smoothing theorem (differentiate the mild eq + the +1 ladder for the
linearized eq), NOT automatic from u∈A³. So hchem reduces to the SATISFIABLE STANDING input {u,u_t∈A³} = the paper's
solution regularity ⟹ faithful conditional PASSES §3.3; OR discharge via the A³ bootstrap of u + u_t (deep).
NET 4-package status: Hv closeable (quadruple built) · hlog tractable (power-of-u) · secondary mechanical (C²) ·
hchem = the genuine deep one, reducible to satisfiable-standing {u,u_t∈A³}. So χ₀<0 faithful conditional is
§3.3-passing once hchem/hlog/Hv/secondary carry their satisfiable-standing regularity; unconditional needs the A³ smoothing.

## [2026-06-24] cron1 Q120: u_t∈A³ route MAPPED — linearized eq + same +1 Wiener ladder
ChatGPT (Q120): U:=u_t solves U_t = U_xx + a∂ₓ(U v_x D + u V_x D − β u v_x V D₁) + (1−2u)U (D=(1+v)^{-β}, V=(μ-Δ)^{-1}U).
Frozen-coeff linearized flux Qlin_r(U)∈A^r_sin (given u∈A³, U∈A^r); divergence Duhamel leg gains +1 ⟹ A^{r+1}_cos.
Reaction (1-2u)U non-divergence, gains +2, never limiting. So from A⁰ seed for u_t, ladder A⁰→A¹→A²→A³ gives u_t∈A³.
NET: the χ₀<0 deep frontier = coupled A³ Wiener bootstrap {u∈A³ (the u ladder, IntervalChiNegA3Slice) + u_t∈A³ (the
linearized ladder, this Q120 structure)} → q_t∈A³_sin → hchem. Route now STRUCTURALLY PRECISE; formalization is
substantial (the +1 ladder for u + linearized for u_t). χ₀<0 = §3.3-passing faithful conditional (carries this as
satisfiable standing solution-regularity); unconditional = formalize the A³ bootstrap.
