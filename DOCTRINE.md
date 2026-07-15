# Shen Trilogy Formalization — DOCTRINE

## ACTIVE AUTOMODE TARGET (2026-07-03): Prop 2.5 — close hId + hWindow + hlocal gaps

### Session 2026-07-03 Focus: produce H¹ energy DI from classical solution

The chain to Prop 2.5 is CLEAN except for THREE carried hypotheses in
`produce_pointwiseGradientBound_full` (via `chiNeg_H1_norm_bound`):
  1. **hId** (H1EnergyIdentity) — `HasDerivAt (H1energy u) (derivative_value) τ`
  2. **hWindow** — `∫_{τ-1}^τ H1energy ≤ C` (single-solution dissipation window)
  3. **hlocal** — `H1energy bounded on (0,1]` (parabolic smoothing near t=0)

### Dual-oracle synthesis (2026-07-03, Fable + ChatGPT):

**Decision: Route C (finite-difference + spatial IBP).** Both oracles agreed on
the energy identity value `y'(t) = -∫ u_xx · u_t` but disagreed on route.
ChatGPT's Route C won because it needs NO spectral theory, NO new regularity
fields, and only uses spatial C² + Neumann + joint u_t continuity already in
the 9-conjunct regularity record.

**Route C proof:**
  Step 1: H1energy(s)-H1energy(t) = -½∫(u_xx(s)+u_xx(t))·(u(s)-u(t))
          (spatial IBP, Neumann kills boundary — pure algebra, no time deriv)
  Step 2: divide by (s-t), limit: y'(t) = -∫ u_xx(t)·u_t(t)
          (needs L¹ continuity of u_xx in time — CARRIED)
  Step 3: PDE substitution → H1EnergyIdentity shape

**Files created:**
  - `IntervalChiNegH1EnergyIdentity.lean` — Route C, carries `hUxxL1Cont`
  - `IntervalSingleSolutionL2Window.lean` — L² energy + hWindow (existed prior)

**Status of the THREE carried hypotheses:**
  1. **hId** → Route C reduces to ONE carry: `hUxxL1Cont` (L¹ continuity of
     u_xx in time). Derivable from PDE: u_xx = u_t + F, u_t jointly continuous
     (conj. 8), F involves v_xx = v_t + μv - νu^γ (all jointly continuous),
     then v_x by spatial antiderivative, then u_x by same. Fixed-point argument.
  2. **hWindow** → `singleSolution_H1_window_bound` is now a proved theorem in
     `IntervalSingleSolutionL2Window.lean`. It is not a raw sorry; it consumes
     `IntervalDomainL2AbsorbingDifferentialInequalityResult`,
     `IntervalDomainL2SeedRegularityFrontier`, and a uniform `L2energy` bound.
  3. **hlocal** → H1energy bounded on (0,1]. From: H1energy continuous on
     (0,T) (H1energy is a composition of continuous maps), hence bounded on
     compact [ε,1]. The near-zero behavior uses parabolic smoothing.

### Avenues (revised after oracle synthesis):
(a) **Route C (active)** — finite-difference + spatial IBP → H1EnergyIdentity
    → chiNeg_H1_norm_bound → produce_pointwiseGradientBound_full → Prop 2.5.
    Sole carry: `hUxxL1Cont`. File: `IntervalChiNegH1EnergyIdentity.lean`.
(b) **Spectral route (backup)** — eigenvalue-weighted ℓ¹ summability.
    Harder: needs `Σ λ_k |û_k| < ∞`, which requires C² Neumann + Cauchy-Schwarz
    + Parseval on f'' — but the sum Σ |cosineCoeffs(f'')_k| converges only if
    f'' ∈ BV (need C³ or better), which isn't in the record.
(c) **Hybrid (fallback)** — semigroup + Duhamel for spectral bounds.
Terminal: `intervalDomain_Proposition_2_5_1d` unconditional from `IsPaper2ClassicalSolution`.

---

## Previous ACTIVE TARGET (2026-07-02): Discharge Prop 2.5 conditions via 1D energy + Sobolev route

### Background — what Fable 5 found (2026-07-01)
- `AgmonNoDropEnergyReductionBefore` (AG ≤ KZ + L) is FALSE — interpolation goes Z→G not G→Z.
  High-oscillation functions have bounded Z but unbounded G.
- Algebraic absorption route also failed — gives upper bound on Y', but
  AG ≤ KZ + L needs LOWER bound on Y' (opposite direction).
- `RelativeMoserInterpolationBefore` is FALSE in 1D (superlinear lower-order term).
- Moser iteration via threshold plan DOES NOT WORK in 1D.

### What IS proved
- `AgmonAbsorbedInterpolationBefore` — PRODUCED unconditionally from classical solution
  (P3MoserAgmonDirectRoute.lean:648, `produce_AgmonAbsorbedInterpolationBefore_of_classical`)
- 1D Sobolev: `intervalDomainLift_rpow_agmon_bound` — ‖u‖∞ from ∫u^p + ∫|∇(u^{p/2})|²
- `IntervalDomain1DLinfRoute.lean` has the L∞ → all Lp → Prop 2.5 assembly,
  conditional on `IntervalDomainPointwiseMoserGradientBoundBefore`
- Energy step machinery in `IntervalDomainEnergyStep.lean`:
  `intervalDomain_lp_energy_derivative_le_energy_plus_lower_of_frontiers` gives Y'(t) ≤ Cgr*(Y + lower)
- Mathlib Gronwall: `le_gronwallBound_of_liminf_deriv_right_le` (already used in Paper1)
- Full build green: 0 sorry, 0 sorryAx

### SOLE REMAINING FRONTIER: `IntervalDomainPointwiseMoserGradientBoundBefore`
Produce `∃ M_diss, ∀ t ∈ (0,T), ∫|∇(u^{p/2})|² ≤ M_diss` from `IsPaper2ClassicalSolution`.
Once this is produced, `intervalDomain_Proposition_2_5_1d` closes Prop 2.5.

### CORRECTED 1D ROUTE (Fable oracle 2026-07-02):

**Key insight (Fable)**: the energy identity+inequality cannot produce a pointwise UPPER
bound on G₂ — they only give a lower bound. The paper itself uses semigroup estimates
(Prop 2.5 mild formulation) to get L∞, never proving a pointwise gradient bound.
However, in 1D there is a cleaner route via H¹ energy + Uniform Gronwall:

1. **Y₂ bounded** — L² energy inequality + Gronwall (EXISTING)
2. **∫₀ᵀ G₂ dt bounded** — from L² energy inequality (EXISTING)
3. **H¹ energy DI without ‖u‖_∞** — test PDE with -u_xx:
   G₂' ≤ αG₂ + β (constant coefficients)
   where α,β depend only on params, ‖v_x‖_∞, ‖v‖_∞ (bounded), Y₂ (bounded).
   Key: bound ∫F_x² using v_x∈L∞ + Agmon absorption (∫u^{2+2γ} ≤ εG₂ + C_ε)
   to avoid the ‖u‖_∞ circularity in the existing h1_diffIneq_of_sup_bounds.
4. **Uniform Gronwall** (Temam III.1.1): from G₂'≤αG₂+β + ∫G₂ bounded →
   pointwise G₂(t) ≤ M for t ≥ r. Near t=0: initial H¹ regularity.
5. **1D Sobolev** → ‖u‖_∞² ≤ C(Y₂ + G₂) → L∞ (EXISTING consumer)
6. **L∞ → all Lp → Prop 2.5** (EXISTING: IntervalDomain1DLinfRoute)

### Avenues (ranked — avenue (a) is now the Fable oracle route)
(a) **H¹ + averaging**: build pieces 3-4 above. Artifacts:
    - `ShenWork/Paper2/IntervalDomainH1GradientBound.lean` — NEW
      - `h1_diffIneq_of_agmon_bounds`: DERIVED ✓ (abstract Young, builds clean)
      - `weightedGradDiss_eq_two_mul_H1energy`: CLEAN ✓ (micro-lemma + rw chain)
      - `produce_pointwiseGradientBound_of_H1energy_bound`: CLEAN ✓ (bridge + coefficient simplification)
      - `produce_pointwiseGradientBound_full`: CLEAN ✓ (wires chiNeg_H1_norm_bound)
    - `ShenWork/Analysis/UniformGronwall.lean` — NOT NEEDED (existing averaging suffices)
    - CARRIED hypotheses for full producer: hlocal + havg + hwin
    Terminal: this + existing 1D Linf route → Prop 2.5 unconditional.
(b) **Semigroup/mild route (paper's actual proof)**: bypass gradient bound entirely,
    use mild formulation + heat semigroup estimates for L∞.
    More faithful to paper but heavier infrastructure.

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

---
## [2026-06-30 NIGHT] GN-absorbed interpolation from Agmon — the CORRECT 1D Moser route

### State
Architecture committed in P3MoserAgmonDirectRoute.lean (5 sorry steps).
The earlier diagnosis "1D Moser doesn't work" was WRONG — resolved by reading
the paper's Lemma 2.6, which uses the SEED L^{p₀} norm (not the current L^p)
as the GN lower-order term.

### Route
```
proved Agmon (u^{p/2}) → Hölder with seed norm → sub-additivity + Young
→ GN-absorbed interpolation: ∫u^{p+ρ} ≤ ε·G + C_ε
→ feeds moser_iteration_chain (existing) → all Lp bounds
→ + Agmon L∞ frontier → Proposition 2.5
```

### Key condition
p₀ > ρ (so the exponent α = (p+ρ-p₀)/p < 1 for Young). This is the paper's
p₀ > max{1, ρN/2}, which for N=1 gives p₀ > ρ/2. The AbstractLpBootstrapHypothesis
already requires p₀ > max{1, ρN/2}.

### Sorry inventory (P3MoserAgmonDirectRoute.lean)
1. `intervalDomain_higher_Lp_le_Linf_rpow_mul_seed` — Hölder: ∫f^{p+ρ} ≤ ‖f‖∞^ρ · ∫f^p
2. `intervalDomain_supNorm_rpow_le_energy_plus_gradient` — Agmon → ‖u‖∞^p bound
3. `intervalDomain_gn_absorbed_interpolation_of_agmon` — THE MAIN LEMMA
4. `intervalDomain_all_Lp_of_agmon_bootstrap` — moser_iteration_chain application
5. `intervalDomain_Corollary_2_1_of_agmon` + `..._Proposition_2_5_of_agmon` — wiring

---
## [2026-07-05] Task 41 correction: H¹-only is not a bounded-before interface

The proposed 1D bypass theorem with only a uniform `H1energy` bound is too
strong as an interface: the H¹ seminorm controls the derivative part but not
the spatial constant mode.  The honest reducer is:

```
LpPowerBoundedBefore intervalDomain 2 T u
+ uniform H1energy u τ ≤ Y₁ on (0,T)
→ IsPaper2BoundedBefore intervalDomain T u
```

This is now proved as
`ShenWork.IntervalDomainExistence.P3Moser1DBypassAssembly.intervalDomain_boundedBefore_of_L2bound_and_H1bound`.

The same file also provides upstream combinators from the existing L² absorbing
seed frontiers and H¹ window/local/average package:

```
IntervalDomainL2AbsorbingIntegratedInequalityResult + IntervalDomainL2SeedRegularityFrontier
+ chiNeg_H1_norm_bound inputs
→ IsPaper2BoundedBefore intervalDomain T u
```

Consequences for orchestration:
- If a future route can produce an unconditional `L²`/mass seed and uniform
  H¹ bound, the 1D bounded-before conclusion is closed by this file.
- Do not dispatch workers to prove the H1-only version unless the statement is
  strengthened with a constant-mode/mass/L² hypothesis.

Follow-up window wiring is now proved in
`ShenWork.Paper2.IntervalChiNegH1WindowWiring`:

```
singleSolution_H1_window_bound
+ hlocal on (0,1] restricted by τ < T
+ havg on 1 ≤ τ < T for H1Window
→ ∃ Y₁ ≥ 0, ∀ τ, 0 < τ → τ < T → H1energy u τ ≤ Y₁
```

The final wrapper
`intervalDomain_boundedBefore_of_L2Window_H1local_H1avg_and_Lp2` composes this
with the Task 41 1D bypass while keeping the `p=2` Lp seed explicit.  Remaining
H¹-route carries are now `hlocal` and `havg`; `havg` should be attacked next
through a scalar H¹ differential inequality plus interval FTC.  The new reducer
`H1_avg_of_pointwise_window_bound` already proves the final averaging step from
the pointwise window inequality
`H1energy u τ ≤ H1energy u s + A * H1Window u τ + B`; the next gap is therefore
the scalar FTC theorem producing that pointwise window inequality from the H¹
DI.  Do not attack `hUxxL1Cont` as the next low-risk task; it remains the
upstream analytic regularity frontier behind the H¹ identity route.

That scalar FTC reducer is now proved in
`ShenWork.Paper2.IntervalChiNegH1AverageWiring`:

```
H1ScalarDIOnBefore u T A B
→ ∀ τ, 1 ≤ τ → τ < T →
    H1energy u τ ≤ H1Window u τ + (A * H1Window u τ + B)
```

`H1ScalarDIOnBefore` is intentionally scalar: it carries H¹-energy continuity on
closed nonnegative windows, interval integrability of `deriv (H1energy u)`,
right-derivative FTC data, and the pointwise DI
`deriv (H1energy u) ≤ A * H1energy u + B`.  Remaining low-risk work is now to
produce this scalar package from the landed H¹ identity plus algebraic
cross-term bounds, still carrying `hUxxL1Cont` upstream if needed.  The separate
`hlocal` start on `(0,1]` remains another carried input.

Task 41C scalar-DI producer is now proved in
`ShenWork.Paper2.IntervalChiNegH1ScalarDIProducer`:

```
H1ScalarRegularityBefore u T
+ H1IdentityRHSBoundBefore p u T A B
→ H1ScalarDIOnBefore u T A B
```

The `H1IdentityRHSBoundBefore` package is also produced from explicit
`H1SupBoundDIDataBefore` via the existing `h1_diffIneq_of_sup_bounds` algebraic
theorem.  This is the current honest boundary:

- scalar continuity/integrability of `H1energy` remains a separate FTC
  regularity input;
- pointwise taxis/uvxx/reaction estimates remain explicit in
  `H1SupBoundDIDataBefore`;
- `hUxxL1Cont` is not attacked here and remains upstream of whichever theorem
  produces the pointwise `H1EnergyIdentity`;
- `hlocal` on `(0,1]` is still a separate carried start.

`IntervalChiNegH1AverageWiring` also has the paper-positive wrapper
`intervalDomain_boundedBefore_of_paperPositive_H1scalarDI_local`, so once
`H1ScalarRegularityBefore`, `H1SupBoundDIDataBefore`, and `hlocal` are supplied,
the Task 41 bounded-before route closes through the P3 bypass.

Task 41D scalar-regularity producer is now proved in
`ShenWork.Paper2.IntervalChiNegH1ScalarRegularityProducer`:

```
IsPaper2ClassicalSolution intervalDomain p T u v
+ H1UxxL1ContBefore u T
+ ContinuousWithinAt (H1energy u) (Set.Ici 0) 0
→ ∀ 0 ≤ a ≤ b < T, ContinuousOn (H1energy u) (Set.Icc a b)
```

and the packaging lemma:

```
hcont
+ hderivInt
→ H1ScalarRegularityBefore u T
```

The direct wrapper
`H1ScalarRegularityBefore_of_uxxL1Cont_and_hderivInt` is also available when
the continuity input is to be produced specifically from `H1UxxL1ContBefore`
and time-zero right-continuity.

This deliberately does **not** claim that the pointwise H¹ identity supplies
interval FTC regularity.  Remaining honest scalar-regularity inputs are:

- `IntervalIntegrable (fun r => deriv (H1energy u) r) volume a b` on all
  closed pre-horizon windows;
- time-zero right-continuity of `H1energy`, unless a future theorem derives it
  from initial-trace/parabolic regularity;
- the upstream analytic `H1UxxL1ContBefore` itself.

---

## Avenue (2026-07-14): Paper 1 Prop 1.2(1) — floor campaign (χ ≤ 0 two-sided)

**Goal:** `Proposition_1_2_negative_branch` — for Paper data (BUC, nonneg, uniformly
positive) and χ≤0, the canonical solution converges uniformly to 1 (mirrors the shape of
the proved `Proposition_1_1_negative_branch`; the weak-datum ∀-quantified official def
stays conditional exactly as Prop 1.1's GlobalExistenceField does).

**Design (doubly verified: own derivation + ChatGPT Q5041; both converged):**
- Barrier: `wholeLineCauchyExpFloor c lam t = 1 + (c-1)e^{-lam·t}`, `0 < lam ≤ c ≤ 1`.
  Rate decoupled from level. The naive rate-1 mirror of the ceiling is FALSE at α=1
  (`-(1-B)² ≥ 0`). Key arithmetic `expFloor_reaction_dominates` is machine-checked.
- At almost-min: drift absorbed as in ceiling; nonlocal `−χu^m(V−u^γ) ≥ 0` via
  `frozenElliptic_ge_of_rpow_ge`; reaction dominates `lam(1−B)`.
- No separate positivity-persistence needed (barrier supplies its own floor). Restart
  keeps rate, moves level (`wholeLineCauchyExpFloor_restart`).
- Paper's own §3.2 route (order interval + translate compactness) NOT used — the moving
  barrier avoids compactness, same as the banked ceiling route avoided it for (1.9).

**Terminal conditions:**
- SUCCESS: `wholeLineCauchyGlobal_uniformLiminfGe_one_of_chi_nonpos` clean-3 + the two
  carried hyps of `Proposition_1_2_negative_branch_of_floor` (banked 89875747) discharge.
- FAILURE-PROOF: a specific slab-lemma step where the almost-min machinery genuinely
  lacks a mirror (would surface as a named missing lemma in codex#2's wall report).

**Status:** interface + assembly banked (0f711a67, 89875747, clean-3). Slab mirror +
propagation dispatched to Codex#2 (CODEX_SPEC_paper1_floor.md).

---

## Scope verdict (2026-07-15): Prop 1.2 ∀-form uniqueness = imported [39], NOT dischargeable elementarily

- Paper 1 §1.2 imports existence+uniqueness "by [39, Thm 1.1]" (Salako–Shen JDE 2017,
  arXiv:1608.02031). Uniqueness mechanism = BUC/mild Duhamel + heat-semigroup (t-s)^{-1/2}
  gradient estimate + weakly-singular Volterra inequality on ‖u₁−u₂‖_∞. NO separate numbered
  theorem in Paper 1; NOT a comparison-principle proof. (Source read + ChatGPT Q5047 concur.)
- Our `IsGlobalClassicalSolution` = pointwise-classical only (no BUC time-path / no resolver
  identity for v), so imported uniqueness does NOT apply to this broader class without a
  BUC-mild bridge. → Structurally identical to the Henry 7.1.3 hcore situation: imported
  textbook analytic infra, out of scope for reproducing the paper. Mathlib lacks it.
- DECISION (default, matches repo's existing Prop 1.1 stance where GlobalExistenceField stays
  conditional): canonical-solution branch `Proposition_1_2_negative_branch` is the faithful
  REAL deliverable; official ∀-form stays conditional on the imported uniqueness bridge, now
  machine-explicit as `Proposition_1_2_hconv_neg_of_canonicalUniqueness` (891dd8b7).
- DO NOT open a Grönwall–Volterra uniqueness campaign unless Xiang authorizes it as separate
  infra work (parallel to a hypothetical Henry campaign).
