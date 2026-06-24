# Shen Trilogy Formalization — DOCTRINE

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
