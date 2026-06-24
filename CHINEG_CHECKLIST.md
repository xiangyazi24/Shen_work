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
