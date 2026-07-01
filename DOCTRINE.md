# Shen Trilogy Formalization — DOCTRINE

## ACTIVE AUTOMODE TARGET (2026-07-01): Close remaining Paper2 headline frontiers

### Completed (this campaign):
- ✅ P3MoserHighExcursionProducer.lean fix (linarith + parenthesization)
- ✅ P3MoserThresholdPlanProducer.lean (threshold plan route, axiom-clean)
- ✅ P3MoserRegularityProducer.lean (frontier data structure, initialPowerBound)
- ✅ P3MoserEnergyContinuity.lean (interior energy continuity via HasDerivAt)
- ✅ IntervalAgmonInterpolation.lean (1D Agmon interpolation, axiom-clean) — by Xiang
- ✅ GagliardoNirenberg.lean + SobolevEmbedding.lean — by Xiang
- ✅ intervalDomain_classicalSolutionPositiveInterpolation — PROVED
- ✅ Paper3 positive chi negative branch discharged
- ✅ Full build green: 8988 jobs, 0 sorry, 0 sorryAx

### Current headline state:
The thinnest χ₀=0 route is ProvedAgmonFrontierData which needs:
1. `section2 : IntervalDomainPaper2BootstrapEstimateThinFrontierData p`
   - lemma26: LpBootstrapEnergyInequality → all Lp (Moser iteration step)
   - lemma27: differential Moser → Lp bound (Gronwall-type)
   - prop22: weighted gradient estimate
   - prop23: weighted signal estimate
2. `localAndMain`: actual Moser atoms (raw drop, mass gradient, terminal endpoint) + local existence

### ACTIVE AVENUE (automode 2026-06-30): Agmon-based mass-gradient route to Prop 2.5

The old MCL route through `OldUnitIntervalPowerGNYoungForMoser` is DEAD (false).
The new route: proved Agmon → mass-gradient conversion → threshold plan → Prop 2.5.

**Chain:**
```
Proved Agmon → LpMassGradientInterpolationEstimate (available)
  + gradient chain comparison (avenue a)
  + mass-to-Lp conversion (avenue b)
  → RelativeMoserInterpolationBefore (via existing P3MoserLemmas bridge)
  + IntegratedMoserDissipationDropBefore (avenue c)
  + regularity/nonneg data
  → IntegratedMoserFirstCrossingStep (threshold plan, proved)
  + quantitative endpoint
  → Proposition_2_5 (via existing P3MoserActualWiring)
```

**STRUCTURAL FINDING (2026-06-30): gradient-exponent mismatch is REAL.**
- `RelativeMoserInterpolationBefore` (∫u^{p+ρ} ≤ ε∫|∇(u^{p/2})|² + C∫u^p) is FALSE
  in general for 1D — same reason OldUnitIntervalPowerGNYoungForMoser is false.
- What holds in 1D: SUPERLINEAR form ∫u^{p+ρ} ≤ ε∫|∇(u^{p/2})|² + C·(∫u^p)^{p/(p-ρ)}.
- The superlinear lower-order term breaks the threshold plan's first-crossing argument
  (the threshold K can't be set because K - C·K^α·T → -∞ for α > 1).
- Therefore: Moser iteration via threshold plan DOES NOT WORK in 1D as-is.

**CORRECTED 1D ROUTE: Uniform Gronwall + 1D Sobolev.**
1. Energy estimate at p=2: integrated bounds ∫_s^{s+r} ∫u² + ∫|u'|² ≤ C
2. Uniform Gronwall lemma (Temam): integrated bounds → pointwise ∫u²(t) ≤ C, ∫|u'|²(t) ≤ C
3. 1D Sobolev (Agmon for u): ‖u(t)‖_∞² ≤ C(∫u² + ∫|u'|²) ≤ C'
4. L∞ → all Lp: ∫u^p ≤ ‖u‖_∞^{p-1} · ∫u ≤ C'
5. This IS Proposition 2.5 for the 1D case.

**Sub-avenues (revised):**
- (a) Prove the superlinear 1D interpolation lemma (architecture done in P3MoserAgmonDirectRoute.lean)
- (b) Implement the Uniform Gronwall Lemma (check if in Mathlib)
- (c) Build the L² energy → integrated bounds → pointwise bounds chain
- (d) Wire pointwise bounds + Agmon → L∞ → all Lp → Prop 2.5

### Previous avenues (reference):
- lemma26: Moser iteration step
- lemma27: Gronwall/ODE from differential Moser inequality
- prop22/prop23: weighted gradient/signal estimates (genuine PDE content)
- actual Moser atoms: raw drop, mass gradient data, terminal endpoint
- local existence: `PicardRestartFrontier` or `quantitativeLocalExistence`

---

**Main goal (one sentence):** Formalize the Chen–Ruau–Shen chemotaxis-growth trilogy
(Paper 1 traveling waves, Paper 2 bounded-domain existence, Paper 3 long-time dynamics)
in Lean 4, landing the headline theorems with NO sorry / axiom / native_decide and NO
vacuity — every carried frontier must be satisfiable and faithful to the paper.

**Hard rules (non-negotiable):** axiom-clean = [propext, Classical.choice, Quot.sound];
no sorryAx; vacuity-check every carried hypothesis against the zero function / a real
solution; faithfulness-check every domination hypothesis against the paper (do not invent
conditions stronger than the paper); build via `lake env lean` on uisai2 (NOT codex,
NOT local lake build). Commits record honest verdicts (reduction ≠ discharge).

## Avenues (ranked by proximity to a headline)

### (a) Headline 1 — Paper 1 wave existence χ≤0 (`b1_chiNeg_existence`)  [PRIMARY, ACTIVE]
The Rothe parabolic-orbit construction is built & axiom-clean; reduces to satisfiable frontiers:
- **R3 → G1** (cx_r3 active): the correct post-projection box/Freudenthal door↔rainbow
  bijection is committed (f9ba007). Remaining: close the recursive `Odd` (induction +
  `sperner_n_dim_combinatorial` + partner involution), then wire G1 via `brouwer_simplex_approx`
  (Sperner label → rainbow → barycenter → approx fixed) + Helly + the existing
  `exists_fixed_of_approx_fixed` bridge. Route: BOX2G1_ROUTE_chatgpt.md.
- **Non-triviality** (cx_pde active): pinned-trap route committed non-vacuous (31d0d04).
  `lowerBarrierPlateau` is NOT a subsolution (plateau chemotaxis, counterexample not_Lemma_4_2).
  Fix: `LowerBarrierData` + smoothed two-exp subsolution under FAITHFUL domination
  (plateau budget C(1-C^α)≥|χ|C^m B₂, tail m·κ≥κtilde, C² edge). Route: SUBSOLUTION_ROUTE_chatgpt.md.
- **StationaryZeroPropagatesByODEUniqueness**: 1-D ODE Cauchy uniqueness (Mathlib Picard–Lindelöf).
- producer/continuous-dependence frontiers.
**Terminal:** `b1_chiNeg_existence` with all frontiers discharged or faithful-conditional, axiom-clean.
**Proof-of-failure:** a frontier proven unsatisfiable (like the floor/bare-trap principle) OR a
faithfulness gap (paper claims existence the barrier cannot give) → report to Xiang.

### (b) Headline 1 positive branch χ≥0 (`b1_chiPos_existence`)
Reuse the Rothe/Schauder + pinned-trap machinery with flipped signs (positive sensitivity).
**Terminal:** `b1_chiPos_existence` axiom-clean, non-vacuous.

### (c) Headline 2 — Paper 2 bounded-domain existence χ₀<0 (`Theorem_1_1`)
Irreducible core = positive-time Hölder bootstrap + singular ∂ₓₓS(t-s) endpoint cancellation
(∫∂ₓₓK_N dy=0 ⟹ C^θ source suffices). Route: HQUANT_ROUTE/HOLDER_CANCELLATION_ROUTE_chatgpt.md.
No codex yet (codex quota focused on (a)). **Terminal:** `hQuant` discharged via the Hölder lemma.

### (d) Paper 2 χ₀=0 — Picard floor
`IntervalDomainMildLocalChi0` clamped-witness machinery largely landed (uisai1 parallel work).
Residuals: `hpde_u` (mild→classical PDE), `Hu` (time-neighborhood spectral agreement).
**CAUTION:** overlaps uisai1's ledger — coordinate, do not clobber.

### (e) Paper 2 a-priori estimates  [HONEST FACTORINGS COMMITTED]
Prop 2.4 (mass) + Prop 2.5 (Moser) reduced to real-solution-gated frontiers (43b1ab4, 38fe33b).
Remaining: discharge the named gated frontiers (no-flux mass identity, Moser bootstrap estimates).

### (f) Paper 3 — long-time dynamics
Rides on Paper 2 existence. Persistence/lower-envelope; deferred until (c)/(d) land.

## Fallbacks
- If a barrier/route fails terminally, switch to the documented alternative in the corresponding
  ChatGPT route doc (each avenue has one saved in-repo).
- Faithful-conditional headlines: if the paper assumes conditions (e.g. chemotaxis budget),
  carry exactly those — a faithful conditional theorem is a valid landing, NOT a vacuity.
- Codex quota exhaustion → ChatGPT (separate quota) advances route docs; resume codex on reset.

## Worker assignment (disjoint files, no conflicts)
- **cx_r3** owns BrouwerNDim* / Brouwer* / Freudenthal (R3→G1). Never touches wave files.
- **cx_pde** owns WaveRothe* / WaveTrapProps (non-triviality). Never touches BrouwerNDim/Paper2.
- **Paper-2 codexes** own Paper2/*. **ChatGPT** = route audit (verify-don't-transcribe).

## Run 2026-06-22 (automode continuation — drive to playbook audit pass, no casual stops)
Goal: all 3 Chen-Ruau-Shen papers UNCONDITIONAL passing playbook §3.3. Avenues = the numbered atoms
(THREE_PAPER_BOARD.md is the live board):
 (a) P2 χ₀<0 → ChiNegDatumUniformConstruction: #1D non-C² Nemytskii (1+v)^{-β} envelope [opus a6eef2b8] →
     closes #1 gW → FluxFactorEnvelopes → trajLadder → regularity chain; then #3 k=0 + Fubini swaps.
 (b) P1 → Paper1MainResultsData: #4A Rothe/Green per-step producer + continuous dependence (the construction
     core); #4B/#4C strong-max upper bound + tail [opus a59e3280]; #5 construction_pos (mirrors #4, sign-
     agnostic); #7 orbital stability.
 (c) P3 → #8 Theorem 2.2 fractional-power frontier (cascades from P2 χ₀≤0 boundedness).
Fallback: each atom that stalls → sharpen to its single named sub-residual, dispatch fresh opus, never defer.
Terminal: headline unconditional + #print axioms clean + §3.3 non-vacuous, per paper.

---
## [2026-06-24 RUN] χ₀<0 unconditional hU — route (B) A³ Wiener (ENGINEERING DECISION, mine)
Goal: discharge hU (ChiNegDatumUniformConstructionFaithful) for large positive C⁰ data via the built A³
Wiener route ⟹ Theorem_1_1 χ₀<0 unconditional (max-principle Lemma_3_1 already real + faithful).
Decision: drive (B) not (A). (A) C⁰ Prop 1.1 contraction needs sectorial/analytic-semigroup/fractional-power
Mathlib stack (deep, nonexistent). (B) is 5 cores + architecture in; diagonal semigroup sidesteps the gap;
both prove the SAME faithful Theorem_1_1 ⟹ engineering call.
Avenues:
 (a) General-data composition (1+v)^{-β}∈A³ for large v≥0 — BOTTLENECK. Moser route B: v∈MemHSob 4∩L^∞,v≥0 ⟹
     (1+v)^{-β}∈MemHSob 4 (order-4 chain rule, g^{(j)}(v) bounded as v≥0 off the -1 singularity, H^4 Moser
     products) → memWNorm_of_memHSob(s=4,σ=3,BANKED) → A³. Reuses banked Sobolev/Heat.
 (b) Recentered-binomial for time-increment (complement, NOT escape — base (1+v₀)^{-β} still needs (a)).
 (c) Wire seed(C⁰→A^σ@t₀, banked)+composition(a)+ladder(banked)+restart → hU unconditional.
 Fallback: route (A) only after (a)(b)(c) documented terminal.
Fork-independent parallel: Paper2 Prop2.x (Prop2.4 brick in flight), Paper1 T11pos/global, Paper3.

---
## [2026-06-24 REFRAME] avenue (a) composition was PHANTOM — REAL frontier = reduced-core realization
Composition (1+v)^{-β}∈MemHSigma is DONE unconditionally (memHSigma_one_add_rpow_neg_of_contDiff_two, σ<3/2,
C²-route). 3 over-builds caught (Prop2.4, MemHSob dup, composition campaign). Abandon avenue (a).
REAL χ₀<0 unconditional frontier (SourceReducedCoreWire.lean §(ii) GENUINELY-OPEN + SourceChiNegNegUncond):
 (a') TIME-C¹ resolver source: realSlice_resolverSpectralData_residual bottoms out at a clamped
     DuhamelSourceTimeC1 witness for the resolver source — OPEN time-C¹. THE deepest real-analysis atom.
 (b') h_src_cont_chem — the C¹-to-boundary secondary regularity (Gap 1, per-slice package #4).
 (c') Realization bridge: ChiNegFaithfulRealizationFrontier = produce u_star:EWA δ 1 with
     CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star); the no-embed (realSlice-definitional) route
     vs the missing picardEWA→embedEWA bridge.
DISCIPLINE: grep the existing ShenWork.Wiener.EWA / IntervalChiNeg* / ShenWork.Paper2.ln namespace BEFORE any
brick (3 over-builds this session from skipping this). Reduced core was 13/24 wired earlier this session
(SourceReducedCoreWire); Hv/h_flux_diff/h_src_cont_log already closed; residual = (a')(b')(c').

---
## [2026-06-26 night] Level0+Tower sorry closure — Option (B) cutoff route

### Goal
Close all 9 remaining sorry in Paper 2 χ₀<0 (Level0 + Tower).

### Root causes (two independent obstacles)
1. Resolver C² scope mismatch: `FlooredSourceTimeData` unfillable (S(0)=0).
   Fix: bypass via restart cutoff (`resolverSpectralJointC2At_of_restartSmoothCutoff`).
2. F1 boundary obstruction: `ContinuousOn (Icc 0 1)` false for zero-extension.
   Fix: weaken to `IntervalIntegrable` (ChatGPT Q1006 confirmed feasibility).

### Avenues
(a) F1 upstream weakening — 4 structures + 1 consumer theorem
(b) Level0 hfluxC2 via restart cutoff (FAC route or inline)
(c) Level0 sorry 1A + 2A-sup from joint continuity + compactness
(d) Tower cascade (base + successor + limit)

---

## [2026-06-25] hlogSrc/hchemSrc production — the LAST frontier

### State
ALL 998 files / 392K LOC sorry-free. Paper 3 done. Paper 1 done. Paper 2 χ₀=0 unconditional.
Paper 2 χ₀<0: BFormBankedInputs has NO false fields (barriers A/B/C resolved 63cc68e/b84ddb3).
Only `hlogSrc` + `hchemSrc` unfilled.

### Route: B-form iterate TimeC1On tower + limit passage
Level 0: FREE (conjugatePicardIter 0 = picardIter 0 definitionally).
Level n+1: need B-form spectral representation + K2 bounds for conjugatePicardIter.
Limit: duhamelSourceTimeC1On_of_uniform_limit (sorry-free, generic).

### REFACTORED (7e90e3d): BFormBankedInputs now needs ONE field `hsrcBDirect`
The old hlogSrc+hchemSrc were ONLY used together to make hsrcB. Collapsed to single field.
Production target: `DuhamelSourceTimeC1On (bFormSourceCoeffs p (conjugatePicardLimit ...)) 0 DB.T`

### Steps
1. [x] Level 0 wrapper (a4575de — definitional bridge from picardIter 0)
2. [ ] Level 0 bForm source TimeC1On (logistic part: existing level0Source_timeC1On;
       chemDiv part: needs H²+decay+adot from heat semigroup C∞ regularity — IN PROGRESS)
3. [ ] Iterate spectral representation (intervalConjugateDuhamelMap_cosineSeries — EXISTS)
4. [ ] G1/G2 bounds from spectral decay (cosineCoeffSeries_contDiff_two — EXISTS, needs wiring)
5. [ ] ChemDiv C² for iterates (GENUINE GAP — repo has no producer, ChatGPT confirmed)
6. [ ] ChemDiv H²+decay+adot for iterates (from C² via existing chain)
7. [ ] bForm source TimeC1On per iterate (logistic via sourceTimeC1On_succ + chemDiv via chain)
8. [ ] Limit passage via duhamelSourceTimeC1On_of_uniform_limit
9. [ ] BFormBankedInputs assembly from all field producers
10. [ ] Theorem 1.1 χ₀<0 unconditional

### GENUINE GAP: chemDiv source H2 Neumann for conjugate iterates
The key composition chain (flux C³ → chemDiv C² → H2) is proved for GLOBAL C⁴ inputs
(chemFlux_contDiff_three, chemFluxDeriv_contDiff_two — both sorry-free). The H2 assembly
via congr_on_Icc is structurally complete (3679 jobs build clean on uisai2).

ARCHITECTURAL ISSUE (2026-06-25 ChatGPT Q489): the `ContDiff ℝ 4 (intervalDomainLift u)`
hypothesis is UNSATISFIABLE for generic heat semigroup data because `intervalDomainLift`
is a ZERO-EXTENSION (= 0 outside [0,1]), which has a jump at the boundary when u(0) ≠ 0.
The correct approach: use the GLOBAL COSINE SERIES function `U_cos = ∑ exp(-tλ_k) û₀_k cos(kπx)`
(which IS even and C∞) as the input to the H2 construction, not `intervalDomainLift`.
The cosine series agrees with `intervalDomainLift u` on [0,1], so `congr_on_Icc` transfers.
The parity argument (flux odd → deriv(flux) even → deriv²(flux)(0) = 0) works for U_cos.

FIX NEEDED: refactor `chemDivSource_weakH2_of_uv_C4_global` to take:
  - `U_cos V_cos : ℝ → ℝ` (the global cosine representatives)
  - `hu_cos : ContDiff ℝ 4 U_cos` (from heatSemigroup_contDiff_four)
  - `hv_cos : ContDiff ℝ 4 V_cos` (from resolver eigenvalue decay)
  - `h_agree_u : ∀ x ∈ Icc 0 1, intervalDomainLift u x = U_cos x`
  - `h_agree_v : ∀ x ∈ Icc 0 1, intervalDomainLift v x = V_cos x`
  - `hu_even : ∀ x, U_cos (-x) = U_cos x` (cosine series is even)
  - `hv_even : ∀ x, V_cos (-x) = V_cos x`
Then: build H2 for F = deriv(chemFluxFun β U_cos V_cos) using parity → deriv F 0 = 0,
transfer to chemDivLift via congr_on_Icc + h_agree.
