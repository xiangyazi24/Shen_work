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
