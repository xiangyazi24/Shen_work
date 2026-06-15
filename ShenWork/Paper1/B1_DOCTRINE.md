# B1 — traveling-wave existence (χ≤0) — DOCTRINE

Goal: prove the exact monotone wave profile `∀ x, frozenWaveOperator p c U U x = 0` (+ endpoint
limits 1/0, monotone) for `α ≤ m+γ−1, χ ≤ 0, c > cStarLower p` — the ONE missing field that
unlocks the whole B1 χ≤0 existence headline (`Theorem_1_1`, Statements.lean:16285). Everything
bracketing it (logistic barrier, Shen bound, tail, monotone-trap, the reassembly
`mk_auto_limits → of_raw_frozen_stationary_branches`) is committed & unconditional.

## Route (ChatGPT-Pro-designed, cron 2477a9f9): SCHAUDER compact fixed point on the monotone trap set
Monotone iteration is BLOCKED — χ≤0 helps the barrier estimates but does NOT give quasi-monotonicity
(the nonlocal `V' = K'*Uᵞ` has a sign-changing kernel, so `V'` is not order-preserving). Shooting is
worse (the coupling V=frozenElliptic p U is nonlocal — no finite phase plane). Schauder is the sound
route; it is NOT in Mathlib (only Schauder *bases* are), so the one honest new brick is a compact
fixed-point theorem.

## 4 sublemmas (the decomposition)
- **L1** auxiliary map `T : K → K` (K = monotone wave-trap set) well-defined + invariant + locally
  smooth — the Green-kernel/linearized-operator map; uses the committed barriers + `frozenElliptic`
  (Statements:2608) resolver bounds. THE analytic crux.
- **L2** `T` continuous (local-uniform) + `T(K)` relatively compact (Arzelà–Ascoli, via uniform local
  C¹/C² bounds from T's smoothing) + the nonlocal-map continuity under local-uniform convergence
  (dominated convergence with the exponential kernel + uniform trap bound).
- **L3** [FOUNDATIONAL, reusable] local-uniform Schauder/compact fixed point: `T:K→K`, K nonempty
  convex closed, `T(K)` relatively compact, `T` continuous ⟹ `∃ U∈K, T U = U`. Build from Mathlib
  Brouwer + finite-dim (Galerkin) approximation, OR a bespoke local-uniform specialization.
- **L4** fixed point ⟹ `frozenWaveOperator p c U U = 0` — via the COMMITTED
  `paperWaveOperator_eq_frozenWaveOperator_at_fixed_point` (Statements:3077). Then package into
  `FrozenStationaryWaveProfile` (Statements:2736) → `IsMonotoneTravelingWave`.

## Terminal conditions
- success: `frozenWaveOperator = 0` profile constructed → B1 χ≤0 headline unconditional.
- proof-of-failure: a precise Mathlib/infra gap blocking L3 (the topological brick) AND a bespoke
  specialization.

## Plan: L3 first (foundational, self-contained, reusable for B2/B4 too), then L1/L2 (the analytic
core), then L4 (mechanical via the committed bridge). Codex out till Jun 18 → Opus carries.

## VERIFIED ASSEMBLY CHAIN (grep+source-confirmed 2026-06-15)
CORRECTION: cron2's bridge name was RIGHT; my first grep was `head -20`-truncated (the
InMonotoneWaveTrapSet matches at 4377-5035 filled it before reaching line 16600). The repo has a
CLEAN committed Schauder scaffold — the whole B1 χ≤0 headline factors mechanically. Top-level:

**`Theorem_1_1.of_assumed_fixed_point_construction_branches`** (Statements:16600) consumes `hneg`/`hpos`.
Negative branch `hneg` (∀ p α≤m+γ−1, χ≤0, c, cStarLower p<c) supplies:
  `∃ κ₀ κtilde D,  NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D  ∧  (5 property-fns)`
where the 5 fns are each `∀U, trap U → aux U U → <P>`:  hstat(frozenWaveOp=0) · hlim_bot(U→1 atBot) ·
hVmono(deriv V≤0) · hupper(ShenUpperBoundNegative) · htail(HasWaveRightTailAsymptotic).
[trap = `InMonotoneWaveTrapSet (kappa c) 1`, aux = `FrozenAuxiliaryLimitOutput p c (kappa c) 1 trap`.]
It calls `…exists_fixed_limit_with_speed_bridge_data` (9879) → extracts U + the full Theorem_1_1 conclusion
(that extractor derives hU_pos / hUmono / hU_bdd / U→0 internally from the construction+aux output).

### THE GATE = `NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D` (def 9005)
= parameter inequalities (mechanical: pick κ₀,κtilde,D in the open windows) + the real content
**`FrozenWaveMapConstruction p c (kappa c) 1 trap`** (def ~5340). That factors (via
`FrozenWaveMapConstruction.of_schauderData`) into EXACTLY TWO obligations:
- **L3 (abstract, reusable):** `LocalUniformSchauderFixedPointPrinciple trap` —
  `∀ Tmap, invariance → LocalUniformContinuousOn → LocalUniformSequentiallyCompactRange → ∃U trap U ∧ Tmap U=U`.
  Needs n-D Brouwer + finite-dim Galerkin. [K2 a18e795a running toward this.]
- **L1+L2 (concrete map):** `FrozenWaveMapSchauderData p c (kappa c) 1 trap Tmap` = the 4 fields of an
  explicit `Tmap` (the committed `auxMap` / Green-resolver, WaveAuxMap.lean):
    (i)  `∀u, trap u → trap (Tmap u)`            INVARIANCE  = ChemotaxisSandwich [cron designing]
    (ii) `∀u, trap u → FrozenAuxiliaryLimitOutput … u (Tmap u)`  L1 aux orbit/limit output
    (iii)`LocalUniformContinuousOn trap Tmap`     L2 continuity
    (iv) `LocalUniformSequentiallyCompactRange trap Tmap`  L2 compactness = WeightedCompactness

### Status of every leaf
- hstat ← L4 GreenIdentity chain — DONE modulo trap decay/C¹ (flux_ibp committed)
- hVmono(V'≤0) ← 🔧 DISPATCHED `frozenElliptic_deriv_nonpos_of_monotone_trap` (a3ea701b); V=G∗Uᵞ ⟹ V'=G∗(Uᵞ)'≤0
- hupper ← ✅ committed logistic Shen bound · htail ← ✅ committed tail theorem
- hlim_bot(U→1 atBot) ← 🔧 fixedPoint_leftLimit_one lower-barrier squeeze [cron2 designing]
- hU_bdd(IsCUnifBdd) ← ✅ COMMITTED `inMonotoneWaveTrapSet_isCUnifBdd` (WaveTrapProps)
- U→0 atTop ← ✅ COMMITTED `inMonotoneWaveTrapSet_tendsto_atTop_zero` (WaveTrapProps); 0<U is NOT a trap
  fact (zero-fn counterexample) — comes from the construction (extractor) pinning above lower barrier.
- L3 Schauder principle ← K2 [a18e795a] · invariance(i) ← cron · (ii)(iii)(iv) aux-map data — PENDING

### COMPLETE FRONTIER (grep-confirmed: NO repo producer of any construction obligation)
B1 χ≤0 negative branch = supply `hneg` to `of_assumed_fixed_point_construction_branches` (16600):
`∃ κ₀ κtilde D, NegativeSensitivityWaveFixedPointConstruction p c κ₀ κtilde D ∧ (5 property-fns)`.

TWO DEEP CONSTRUCTION GATES (the genuine frontier — both from scratch, no Mathlib support):
- **G1** `LocalUniformSchauderFixedPointPrinciple trap` — abstract Schauder (Brouwer + finite-dim
  Galerkin). [K2 a18e795a running: n-D Kuhn incidence → n-D Brouwer → the principle.]
- **G2** explicit `Tmap` + `FrozenWaveMapSchauderData` = 4 fields:
  (i) invariance trap→trap · (ii) `FrozenAuxiliaryLimitOutput` (THE parabolic orbit semiflow:
  z_t=frozenWaveOperator(p,c,u,z), z(0)=Ū, trapped+antitone-in-t+→U) · (iii) LocalUniformContinuousOn ·
  (iv) LocalUniformSequentiallyCompactRange. cron VERDICT: invariance route = the frozen-in-V
  W-comparison (NOT the fully-frozen Green source — that needs uncontrolled u'); the cross-frozen
  super-barrier `frozenWaveOperator(p,c,u,Ū)≤0` cron flagged as hardest is ALREADY COMMITTED
  (Statements:3643/4804/4832). The orbit existence (ii) is the deepest piece [cron orbit-design in flight].

5 BRIDGE PROPERTY-FNS (each `∀U, trap U → aux U U → P`; aux = FrozenAuxiliaryLimitOutput):
- hVmono ✅ DONE wrapper of committed `frozenElliptic_deriv_nonpos_of_monotone_trap`
- hupper(ShenUpperBoundNegative)/htail — committed Shen+tail, wrappers coupled to construction [bw a79d7361]
- hstat(frozenWaveOp=0) — L4 GreenIdentity + FP-IDENTIFICATION (orbit-limit U ↔ auxMap U=U): possible gap
- hlim_bot(U→1 atBot) — limit-equilibrium: Antitone+bdd→ℓ∈[0,1]; plateau→ℓ>0; stationary ODE→ℓ(1−ℓ^a)=0→ℓ=1.
  cron2 CORRECTION: lowerBarrierPlateau is a left CONSTANT clamp (NOT →1), so the squeeze only gives ℓ>0;
  the ℓ=1 step needs the equilibrium lemma (depends on hstat).
RESOLVED: strict positivity 0<U is NOT separately needed — `exists_fixed_limit_with_speed_bridge_data`
derives HasWaveUpperTailBound from hupper's ShenUpperBoundNegative.pos. (So WaveTrapProps #3 stall is moot.)

### 统筹 streams (2026-06-15): K2(G1 Schauder principle,critical) · cron(G2 orbit construction,deepest) ·
bw(a79d7361 the 5 bridge wrappers + stall-locate). Committed this run: hIBP(flux_ibp) · V'≤0 · trap-props×2.
Codex out till Jun 18 → Opus carries.

## G2 REDESIGN — cron verdict (orbit contract is over-strong; use STATIONARY resolvent) ⚠️DECISION FOR XIANG
cron's analysis of the `FrozenAuxiliaryLimitOutput` orbit contract: field (b) demands a GENUINE
continuous-time parabolic solution `deriv(τ↦z τ x) t = frozenWaveOperator(p,c,u,z t) x` — that is a
full global nonlinear parabolic existence theorem on ℝ, which Mathlib v4.29.1 does NOT give and a
Banach-space Picard–Lindelöf CANNOT (the operator has the unbounded `W''+cW'`; C² vector field lands
in C⁰, not back in C²). The mild/semigroup form (route 2) still needs whole-line parabolic semigroup
estimates. Direct-formula (route 5) is circular. So the orbit route is the WRONG, hardest gate.

**RECOMMENDED (route 1): replace the parabolic-orbit map by a STATIONARY Green-resolvent map.**
Define `Tmap u` = solution of the cross-frozen STATIONARY equation `frozenWaveOperator(p,c,u,Tmap u)=0`
in the trap (an elliptic/ODE Green map, no time). New contract (parallel to the committed orbit one):
  `FrozenStationaryMapOutput p c κ M trap u (Tmap u)` := `trap(Tmap u) ∧ ∀x frozenWaveOperator p c u (Tmap u) x=0
       ∧ ContDiff ℝ 2 (Tmap u)` ; and
  `FrozenStationaryMapSchauderData` := `(∀u trap u→FrozenStationaryMapOutput…) ∧ LocalUniformContinuousOn ∧
       LocalUniformSequentiallyCompactRange`.
At a fixed point `Tmap U = U` the stationarity field gives `frozenWaveOperator(p,c,U,U)=0` = **hstat FOR FREE**.
Lean chain (each MUCH smaller than parabolic global existence):
- L1' cross-frozen stationary resolvent exists (elliptic/ODE Green map; order-interval or Green-fixed-point subroute)
- L2' stationary barrier invariance — committed super-barrier(3643/4804/4832) + sub-barrier + STATIONARY max principle
- L3' local-uniform continuity of the stationary solver (frozenElliptic continuous-dependence V_{uₙ}→V_u, V'→V')
- L4' local-uniform compactness — uniform local C¹/C² bounds + existing `LocalUniformSequentiallyCompactRange`
- L5' Schauder fixed point — existing `LocalUniformSchauderFixedPointPrinciple trap` [K2/G1] + a NEW conversion
      theorem `FrozenWaveMapConstruction'.of_stationary_schauderData` (parallel to the committed orbit one).

✅ DECISION 2026-06-15: Xiang approved the STATIONARY resolvent route ("G2 走 stationary resolvent，
别等我") — proceed autonomously, build the parallel stationary bridge (do NOT swap/break the committed
orbit chain; add `FrozenStationaryMapSchauderData` + `FrozenWaveMapConstruction'.of_stationary_schauderData`
alongside). L1' inner-solve subtlety to resolve: the chemotaxis term ∂ₓ(W^m V_u') depends on W' (frozen
V_u but iterate-derivative W'), so naive pointwise monotone iteration on the order interval [sub-barrier,Ū]
may not be order-preserving — needs the precise construction route (cron2 G2-L1' design in flight).

⚠️ COST / NOTE: the committed bridge chain (`FrozenWaveMapConstruction` → …
`of_assumed_fixed_point_construction_branches`) is wired to the ORBIT contract `FrozenAuxiliaryLimitOutput`.
The stationary route needs EITHER (a) a parallel stationary bridge added alongside, OR (b) swapping the
committed contract. This is a structural/architecture change to the committed scaffold — NOT a weakening
(the stationary map yields the exact same traveling wave + hstat), but a route choice that is the SENIOR
AUTHOR'S call (method-flexibility rule). FLAG FOR XIANG before implementing. Until decided, G2 is the gate.

## G1 ROUTE — cron verdict: FINITE-NET SCHAUDER (not Galerkin/Tychonoff/Helly)
Target: `monotoneWaveTrap_schauderPrinciple : LocalUniformSchauderFixedPointPrinciple (InMonotoneWaveTrapSet (kappa c) 1)`.
(NB the bare principle is FALSE for empty trap — prove it AT the concrete monotone trap, using its
nonempty+convex facts; Helly/Tarski ruled out since Tmap is not order-preserving.) Chain:
- Step0/A trap structure: `monotoneWaveTrap_nonempty` (lowerBarrierPlateau member, committed
  exists_D_gt_…:4968) + `monotoneWaveTrap_finite_convex_combo` (convex combo of antitone/≤Ū/≥0 stays in trap — easy).
- Step1 `localUniform_image_finiteNet_on_box` (∀R ε, finite ε-net of image points cᵢ=Tmap vᵢ on [−R,R]):
  via committed `exists_finite_eps_net` (Mathlib finite_cover_balls_of_compact) + `LocalUniformSequentiallyCompactRange`
  (contradiction: ε-separated images can't have a loc-unif-convergent subsequence).
- Step3 barycentric map C(a)=Σ aᵢ cᵢ on stdSimplex ι → Φ:stdSimplex→stdSimplex (continuous via finite sum +
  LocalUniformContinuousOn) → **`brouwer_stdSimplex_n`** [the ONLY new external input — Brouwer subagent
  a6a3c8ae building it] → approx fixed pt xₙ=C(aₙ) with |xₙ−Tmap xₙ|≤εₙ on [−Rₙ,Rₙ], Rₙ=N+1, εₙ=1/(N+1).
- Step4 `locallyUniform_of_approx_on_exhaustion`: extract subseq via LocalUniformSequentiallyCompactRange,
  Tmap(x_{Nⱼ})→U + approx ⟹ x_{Nⱼ}→U loc-unif.
- Step5 committed `LocalUniformContinuousOn.fixed_of_common_limit` (seq→U ∧ Tmap seq→U ∧ cont ⟹ Tmap U=U) ⟹ Tmap U=U.
ALL infinite-dim infra committed; G1 = brouwer_stdSimplex_n [in flight] + the finite-net assembly brick.
This G1 principle is route-AGNOSTIC (serves both the orbit and the stationary G2; reusable for B2/B4).

## PAUSE 2026-06-15: uisai2 down for admin disk expansion (only build machine; Mac kernel-panics on lake
build; Codex also on uisai2 + out of credits till Jun 18). Build-work + Codex-dispatch HALTED by Xiang's
explicit instruction. Design advanced (this G2 verdict) is git-only. RESUME from commit after uisai2 returns:
re-`lake build`-verify the 2 WIP files (WaveBridgeWrappers, PDE/EigenvalueL1Space), then per Xiang's G2
decision either build the stationary-resolvent route (L1'-L5') or the parallel bridge.
