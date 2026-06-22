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

## ★★★ TRUE BOTTOM REACHED (win-discharge a3f02ab5, 2026-06-22)
χ₀<0 boundedness traced through ALL reduction layers to its irreducible analytic core:
  END GATE ← win ← ChemDivSolutionRegularityResidual ← IterateSourceTimeData
  = the gradient mild solution D.u is C² in SPACE and TIME (parabolic regularity bootstrap,
    the "G4 frontier / restart cosine representation").
- GradientMildSolutionData carries only CONTINUOUS slices, NOT C². The C² is the genuine analytic content.
- NOT s=0 (handled by .toOn/windows), NOT the envelope leg (h_coeff discharged via chemDiv_coeff_bound_of_EWA),
  NOT the ℓ¹ summability (EWA SourceEnvelope landed). The bottom is purely the C² parabolic bootstrap.
- ⚠️ STRUCTURAL CIRCULARITY: the only existing repo route to this C² regularity
  (ResolverHasSpectralAgreement.exists_data) itself CARRIES a DuhamelSourceTimeC1 — the same class
  of object win produces. So χ₀<0 CANNOT close via the source-package route; the C² regularity must
  be produced DIRECTLY from the fixed point via heat-kernel smoothing (the HSigma machinery, which D's
  earlier finding showed is scaffolding NOT wired to the limit). Breaking this circularity = Paper 2's
  genuine hard theorem.

LANDED (axiom-clean, the final clean reduction): coupledChemDivSource_timeC1On_of_gradientSolution
(win from ChemDivSolutionRegularityResidual; localizes the bottom to IterateSourceTimeData).

GENUINE REMAINING CORE (one thing, Paper 2's hard analytic theorem): a DIRECT parabolic-smoothing
C²-regularity bootstrap for the gradient fixed point (L^∞ → C²(space)+C²(time) for t>0 via heat-kernel
Duhamel smoothing), breaking the source-package circularity. At χ₀=0 the cone produces it in-tower
(logistic); χ₀<0 needs the chemotaxis version. This is substantial (likely multi-session) — surfaced to Xiang.

What is UNCONDITIONAL today: χ₀=0 Paper-2 boundedness (from_cone_construction). χ₀<0 is reduced
(machine-checked, axiom-clean) to the single C²-bootstrap residual, with all bridges/wirings landed.
Updated: 2026-06-22 (TRUE BOTTOM = parabolic C² bootstrap + circularity; all reductions above it landed).

## C²-BOOTSTRAP ROUTE CONFIRMED (cron Q280, 2026-06-22) — the circularity break
cron confirms the direct B-form bootstrap is SOUND + genuinely NON-CIRCULAR (organize per-step:
assume only u∈L^∞_t H^σ ∩ L^∞ → derive v∈H^{σ+2}, Q,L∈H^σ → B-form Duhamel + heat-kernel → u∈H^{σ+ρ};
NO source-C¹ package assumed). Key semigroup estimate: ‖∂ₓS(r)F‖_{H^{σ+ρ}} ≲ r^{−(1+ρ)/2}‖F‖_{H^σ},
integrable for ρ<1 (the B-form derivative-on-kernel is the whole point).
TARGETS (1D Sobolev embedding H^s↪C^k needs s>k+1/2): C²_x = H³ (6 half-steps); C²_t C⁰_x = H⁵ (10);
C²_t C²_x = H⁷ (14). 
- intervalDomainClassicalRegularity demands C²_x + C¹_t → H³ (6 steps).
- IterateSourceTimeData (what win needs) demands C²-in-TIME (time2 = d2u) → H⁵ (10 steps). [possible
  FAC-chain over-demand: DuhamelSourceTimeC1On only needs first-time-deriv adot; a more direct win route
  might need only C¹_t/H³ — optimization to check at harvest.]
ANALYTIC INPUTS (all but #3 landed): (1) heat-kernel/B-form multiplier [HSigma machinery], (2) elliptic
resolver gain H^σ→H^{σ+2} [resolver_memHSigmaPlus2_of_memHSigma], (3) 1D fractional Moser product
‖fg‖_{H^σ}≤‖f‖_∞‖g‖_{H^σ}+‖g‖_∞‖f‖_{H^σ} [may need explicit frontier lemma — Mathlib gap], (4) L^∞ +
positive floor for real powers [keystone hmapsTo_pos].
THE PRIZE: the half-step brick bform_half_step_smoothing (H^σ+L^∞+flux-L² ⟹ u(t)∈H^{σ+ρ}, iterable).
Subagent a6d0852b attacking it; iterate to H⁵ for win. P1 per-step solver attacked in parallel (ab5616bf).
Updated: 2026-06-22 (C²-bootstrap route confirmed non-circular; half-step engine = the prize; targets H³/H⁵).

## WALL-A TRACTABLE via Wiener-algebra escape (cron Q283, 2026-06-22)
cron: naive coeff-convolution proves a Wiener-algebra (ℓ¹) product, NOT the L^∞-Moser (which needs
paraproduct, Mathlib-absent). BUT: H^σ ⊂ ℓ¹ for σ>1/2 (Cauchy-Schwarz, Σ(1+λ_n)^{−σ}<∞ iff σ>1/2), so
for σ>1/2 the EASY convolution route gives the full algebra ‖fg‖_{H^σ}≤C‖f‖_{H^σ}‖g‖_{H^σ}.
ESCAPE: the bootstrap AVOIDS the σ≤1/2 paraproduct by JUMPING H^0→H^{1−ε} in step 1 (engine allows any
ρ<1) using only the ELEMENTARY L² flux bound (u^m,(1+v)^{−β}∈L^∞, v_x∈L² — no algebra); all later product
steps have σ>1/2 ⟹ Wiener algebra. So WALL-A reduces to the σ>1/2 product/composition theory (Mathlib-
tractable). Subagent ae1b702e proving: cosWeight_le_add (Peetre), hSigma_subset_l1_of_gt_half,
memHSigma_mul_of_gt_half, memHSigma_rpow_of_positive_range, chemotaxisFlux_memHSigma (TARGET), +
chemotaxisFlux_L2_of_bounded (step-1 seed).

## P2 χ₀<0 WALL STATUS
✅ ENGINE landed (40c4885): hSigmaEnergy_duhamel_bound_shifted (circularity-free half-step H^r→H^{r+α}).
🔨 WALL-A (flux H^σ regularity): σ>1/2 Wiener-algebra route [ae1b702e attacking] — TRACTABLE.
🔨 WALL-B (spectral repr cosineCoeffs(D.u)=duhamelEnergyCoeff): the engine↔solution link — PENDING.
🔨 WALL-C (MemHSigma σ→ContDiffOn 2, σ>5/2 / H³): cosine-Sobolev embedding [ae44f5eb attacking].
Then: iterate engine (H^0→H^{1−ε}→...→H⁵ via WALL-A flux at each rung) + WALL-C → IterateSourceTimeData
→ win → END GATE → χ₀<0 IsPaper2ClassicalSolution UNCONDITIONAL → P3 PositiveGlobalBoundedSolution cascade.

## P1 STATUS (after 44d209d)
✅ Left floor (StrictlyPositiveAtLeft) proven. ✅ Schauder/Brouwer half unconditional. ✅ per-step LINEAR
Green solve + fixed-source EXISTENCE + max-principle (trap-invariance) layer landed (44d209d).
🔨 Remaining: PaperStepOutput order layer (W≤Z comparison/monotonicity/left-rate) + PerStepBoxZWitness
regularity + Rothe limit (hstationary) → RightVanishingWaveExistence → unconditional Remark_1_3_2.
Updated: 2026-06-22 (WALL-A Wiener-escape; engine+P1-per-step landed; both cores decomposed to named bricks).

## WALL-B χ₀≠0 RESOLVED via divergence-mode identity (cron Q285, 2026-06-22)
The chemotaxis term's spectral form: the flux Q=u^m(1+v)^{−β}v_x VANISHES at the Neumann boundary
(v_x(0)=v_x(1)=0 ⟹ Q(0)=Q(1)=0). For boundary-vanishing Q, IBP gives THE KEY IDENTITY:
  cosineCoeffs(∂ₓQ)_k = √λ_k · sineCoeffs(Q)_k   (k≥1; k=0 auto-zero since ∫∂ₓQ=Q(1)−Q(0)=0).
So the divergence maps SINE flux coeffs → COSINE source coeffs with the √λ_k multiplier = EXACTLY the
engine's diagonal √λ_k factor. The engine source F_k(τ) = sineCoeffs(Q(τ))_k (NOT cosine — the trap).
Correct semigroup object: S_N(∂ₓQ) = B_N(r)Q = −∫∂_yK_N·Q = ∂ₓS_D(r)Q (the repo's kernel operator),
NOT ∂ₓS_N(r)Q. So chemotaxis Duhamel coeff_k = −χ₀∫e^{−(t−τ)λ_k}√λ_k sineCoeffs(Q(τ))_k dτ =
−χ₀·duhamelEnergyCoeff with F=sineCoeffs(Q). Subagent a8f2dbd5 proving the IBP identity + engine connection.

## P2 χ₀<0 STATUS (after 8d956e3 — 5 bricks landed this stretch)
✅ ENGINE (40c4885) · ✅ WALL-C embedding (9ff1fcd) · ✅ WALL-B partial χ₀=0 + engine bridge (8d956e3)
🔨 WALL-A flux H^σ (Wiener-algebra σ>1/2) [ae1b702e] · 🔨 WALL-B χ₀≠0 divergence-mode [a8f2dbd5]
Then: iterate engine (F=sineCoeffs(flux) per WALL-B + flux∈H^σ per WALL-A) H^0→H^{1−ε}→...→H⁵ →
WALL-C → ContDiffOn 2 → IterateSourceTimeData → win → END GATE → χ₀<0 UNCONDITIONAL → P3 cascade.
Updated: 2026-06-22 (WALL-B χ₀≠0 resolved via divergence-mode; 5 bricks landed; 2 walls in flight).

## P2 χ₀<0 — analytic prizes LANDED (2026-06-22, 58d9edd)
✅ ENGINE (40c4885) ✅ WALL-C embedding (9ff1fcd) ✅ WALL-B partial+bridge (8d956e3)
✅ WALL-B chemotaxis divergence-mode (7e795d9) ✅ WALL-A prize: additive discrete-Young H^σ product (58d9edd)
🔨 WALL-A residual: difference-conv 2-cover + cosine product + chemotaxisFlux_memHSigma [acb1bfb6]
🔨 ASSEMBLY: iterate engine H^0→H^{1−ε}→...→H⁵ (flux∈H^σ via WALL-A, F=sineCoeffs via WALL-B) → WALL-C
   ContDiffOn 2 → IterateSourceTimeData → win → END GATE → χ₀<0 unconditional. + bind named flux into hchem.
## P1 — order layer in flight
✅ left floor ✅ Schauder ✅ per-step Green solve + existence + max-principle (44d209d)
🔨 PaperStepOutput order (W≤Z/monotone/left-rate) + Rothe limit [a58db7a2] → RightVanishingWaveExistence.
Updated: 2026-06-22 (8 bricks landed this stretch; analytic prizes done, WALL-A flux residual + assembly remain).

## STATUS 2026-06-22 (fa57fb4) — 10 bricks landed this run
P2 χ₀<0 walls: ✅ ENGINE ✅ WALL-B(full: 8d956e3+7e795d9) ✅ WALL-C ✅ WALL-A(algebra+flux: 58d9edd+fa57fb4)
  🔨 WALL-A connector (function bridge cosineCoeffs(fg)=cosProd + (1+v)^{−β} composition) [ae01c4a4]
  🔨 ASSEMBLY (iterate engine on gradient soln → IterateSourceTimeData → win → END GATE; bind flux hchem)
P1: ✅ left floor ✅ Schauder ✅ per-step(44d209d) ✅ order layer(a15e1e1)
  🔨 chemotaxis quasi-monotonicity flux-diff IBP (stepFlux_diff_ibp) [ab1bde60] 🔨 Rothe limit hstationary
P3: ✅ persistence m=1 ✅ equilibrium witness; cascades from P2 boundedness.
Remaining to all-3-unconditional: WALL-A connector + P2 assembly + P1 IBP/Rothe. All routes dead-end-free.

## ✅ FULL ShenWork BUILD CLEAN (76e3654, 8828 jobs, 2026-06-22)
After fixing the latent dedup breakage (WavePaperTermConvergence never compiled on origin/main), the
ENTIRE library builds end-to-end. Foundation for the playbook audit. 14 bricks landed this run.

## HONEST HEADLINE STATUS (full build ≠ unconditional headlines)
- P2 χ₀=0: ✅ UNCONDITIONAL (from_cone_construction).
- P2 χ₀<0: 🔨 CONDITIONAL — engine + all walls (A/B/C) landed; remaining = WALL-A residuals (CosineMulBridge
  + (1+v)^{−β} composition, in flight a1b105c3) + the ASSEMBLY (iterate engine on D.u → IterateSourceTimeData
  → win → END GATE). Most reachable next milestone.
- P3: 🔨 persistence(m=1)+equilibrium landed, CONDITIONAL on PositiveGlobalBoundedSolution (= P2 χ₀<0). Cascades.
- P1: 🔨 CONDITIONAL on 4 genuine PDE-construction floors: hprodAll (per-step parabolic solver — DEEPEST,
  no producer), hstationary (GreenIdentity), hsmp (ODE-realization), hflat (C³ Green-source-tail). hLU discharged.
Audit (all-3-unconditional) NOT yet reached; library builds, cores landed, residuals named.
Updated: 2026-06-22 (full build clean; honest headline status).

## P2 χ₀<0 — ALL ANALYTIC PIECES LANDED (7b8ebf0, 17 bricks this run)
✅ ENGINE ✅ WALL-A(algebra+flux+bridge+composition; flux LINEAR in u m=1) ✅ WALL-B(coeff↔solution)
✅ WALL-C(C² embedding). KEY: flux φ=u·v_x·(1+v)^{−β} — u linear, (1+v)^{−β} via C^k-decay (v 2-ahead).
🔨 ASSEMBLY (the remaining P2 integration):
  (a) single-step bootstrap on D.u: u∈MemHSigma σ ⟹ u∈MemHSigma(σ+1/2) [flux∈H^σ via WALL-A product +
      composition → F=sineCoeffs → engine → WALL-B coeff identity]. THE CRUX.
  (b) iterate (a) to MemHSigma(>5/2) → WALL-C → ContDiffOn 2 (space C²).
  (c) time regularity du/d2u from the equation ∂ₜu=Δu−χ₀∂ₓ(flux)+logistic.
  (d) assemble IterateSourceTimeData → ChemDivSolutionRegularityResidual → win (landed producer) →
      END GATE (landed) → χ₀<0 IsPaper2ClassicalSolution unconditional → P3 cascade.
Updated: 2026-06-22 (WALL-A complete; assembly is the last P2 integration).

## ★ χ₀<0 REDUCED TO ITS GENUINE PDE HARD CORE (9c4724c, 20 bricks this run)
ENTIRE per-time analytic bootstrap LANDED + WIRED (engine, WALL-A/B/C, composition, single-step,
hdecomp, envelope-packaging, Fubini discharged, iteration→C²). The χ₀<0 boundedness now bottoms out at
TWO genuine PDE pieces (not scaffolding):
  (1) UNIFORM-IN-TIME H^σ flux closure = the L^∞ max-principle a priori bound (‖u‖_∞≤max(‖u₀‖_∞,K),
      favorable χ₀≤0 sign — cron1b) → engine's uniform-on-[c,t] bound → uniform H^σ envelope g. [crux]
  (2) time-regularity (du/d2u from ∂ₜu=Δu−χ₀∂ₓflux+logistic) + IterateSourceTimeData assembly → win → END GATE.
## P1 — genuine PDE floors (parallel hard cores)
hprodAll (per-step parabolic solver), hstationary (GreenIdentity), hsmp (ODE-realization), hflat (C³-tail).
## HONEST: analytic scaffolding 100% landed + full build clean; the genuine PDE hard cores (Gronwall/L^∞
## a priori for P2, parabolic existence for P1) are the substantial remaining work for the unconditional audit.
Updated: 2026-06-22 (χ₀<0 reduced to L^∞/Gronwall crux + time-reg/assembly; P1 to 4 parabolic floors).
