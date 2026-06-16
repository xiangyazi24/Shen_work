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

## ★★★★ G2 BREAKTHROUGH (cron Rothe design) — implicit Green orbit, per-step CONTRACTION (tractable!)
The "no parabolic theory" gate is RESOLVED into tractable discrete bricks. Build a FIXED-STEP implicit
Green orbit (NOT continuous-time): large λ, h=1/λ, step `z_{k+1}−hF_u(z_{k+1})=z_k`. Each step is a Green
fixed point `W=Φ_{λ,u,Z}(W)` that is a CONTRACTION for large λ (small nonlinear perturbation of identity
after A_λ^{-1}) → UNIQUELY solvable (unlike the stationary problem — different mechanism). Discrete limit
z_k→U gives U=auxMap_λ(U) → committed `fixedPoint_stationary` → frozenWaveOperator=0. Contract = fixed-step
Rothe (discrete), NOT Duhamel — avoids parabolic semigroup entirely.
BRICK DECOMPOSITION (cron):
 STEP (per-step contraction, self-contained, FOUNDATIONAL): reaction_lipschitz_on_Icc · rpow_m_lipschitz_on_Icc
  · greenKernelDeriv_integrable · greenKernelDeriv_l1_bound · crossImplicitMap_contracting_large_lambda
  (ContractingWith.exists_fixedPoint in BoundedContinuousFunction) · crossImplicitStep_exists_unique.
 TRAP (new max-principle, the real order content): implicitStep_le_of_supersolution (F_u(B)≤0 ∧ Z≤B ∧
  W−hF_u(W)=Z ⟹ W≤B) · implicitStep_ge_of_subsolution · implicitStep_preserves_antitone (sliding/
  differentiated max-principle, K_λ' sign-changes so NOT automatic). Discrete monotone induction: F_u(z_k)≤0
  (k=0 = committed super-barrier) ⟹ z_{k+1}≤z_k ⟹ F_u(z_{k+1})=λ(z_{k+1}−z_k)≤0 closes; U^−≤z_{k+1}≤z_k≤Ū.
 LIMIT+CONTRACT: weakened fixed-step Rothe contract (discrete) → z_k→U loc-unif → U=auxMap_λ U → fixedPoint_stationary.
[Rothe first-brick (STEP 1-6 per-step contraction) DISPATCHED. TRAP 7-9 + limit follow.]

## ★★★ G2 FINAL (cron orbit2, definitive) — no shortcut; faithful route = Rothe MILD cross-frozen orbit
ROUTE A (unique cross-frozen stationary solve W*(u)) is STRUCTURALLY DEAD: the cross-frozen stationary
BVP F_u(W)=0 is NOT uniquely solvable in the order interval. The linearized difference equation for
δ=W₁−W₂ has zero-order coefficient b_α=1−(α+1)W^α which is POSITIVE near the right tail (W small) → no
maximum-principle uniqueness; the operator is not "proper". Confirmed by the paper: Shen uses uniqueness
ONLY at a stricter speed c**>c* (not the existence threshold c*). Perron sub/super gives a SET of
solutions, not a single continuous map → no single-valued Tmap for the outer Schauder. So route A cannot
found G2.
ROUTE B (Rothe / implicit-Euler → cross-frozen orbit) is the FAITHFUL route: z_{k+1}−hF_u(z_{k+1})=z_k
(each step a cross-frozen ELLIPTIC solve, (I−hF_u) better-behaved for small h), trapped U^−≤z_{k+1}≤z_k≤U^+
by elliptic comparison at each step (barriers), monotone-in-k → limit. BUT recovering the EXACT pointwise
t-derivative of `FrozenAuxiliarySolutionFrom` is a classical parabolic regularity theorem. Tractable only
if the contract is WEAKENED to a MILD/integral orbit form, then upgraded to stationary at the fixed point
via the committed Green smoothing (auxMap/GreenIdentity gives classical regularity of the LIMIT).
⟹ G2 = the genuine deepest gate of B1: a from-scratch parabolic-lite (Rothe mild-orbit) construction, no
Mathlib support, no clean shortcut. RECOMMENDATION: drive B1 to "headline REACHED modulo the single honest
FrozenAuxiliaryLimitOutput construction" (the A2-style clean conditional milestone — G1 + bridge wrappers
discharge everything ELSE), then attack the Rothe mild-orbit as the dedicated deepest effort. Pending Xiang.

## ★★ G2 RESOLUTION (cron G2a, read the actual Shen paper) — PARABOLIC ORBIT is faithful; diagonal auxMap fails invariance
DECISIVE: Shen's Section 4.2 construction is the CROSS-FROZEN PARABOLIC map `T(u)=lim_{t→∞} z(t;Ū,u)`,
`z_t = A(z;u)` with V=V_u frozen but the flux on the EVOLVING z (z^m V_u'). Invariance = parabolic
comparison with cross-frozen barriers: testing W=Ū (or e^{−κx}, M) the derivative term is the BARRIER's
explicit W_x=−κW, NEVER u_x — THIS defeats the obstruction (Shen Lemma 4.1 super, 4.2 sub). Key barrier
inequality A(e^{−κx};u)≤0 absorbs −κm|χ|V_x+|χ|V ≤ |χ|(1+mγκ²)/(1−γ²κ²)e^{−γκx} via the explicit V kernel
+ u≤e^{−κx} + speed condition. Convergence = z antitone IN TIME (z_t≤0 from Ū super-solution) bounded below
by sub-barrier → monotone limit ∈ trap. z_x≤0 by differentiating the parabolic eqn + comparison on w=z_x.
⟹ the diagonal `auxMap` (my "collapse") is the WRONG map: fixed-points stationary but NO barrier-invariance.
⟹ the repo's ORIGINAL `FrozenAuxiliaryLimitOutput` (parabolic orbit) contract is the FAITHFUL formalization.
The invariant set is the pointwise order interval U^−≤u≤U^+ + nonincreasing (NOT a weaker norm class).
CLARIFICATION of Xiang's "G2走stationary": cron's route-1 "stationary resolvent" meant the CROSS-frozen
solve A(W;u)=0 (invariance OK via barriers) — NOT the diagonal auxMap. But constructing that W*(u)
continuously-in-u itself reduces to the parabolic time-limit (cron2: monotone-iter fails, Schauder-selection
not continuous). So BOTH faithful routes go through the parabolic orbit. hstat still free via auxMap at the
END (the limit profile is a fixed point of the diagonal too), but the MAP for the Schauder/invariance must be
the parabolic T(u). NEXT: design the Lean construction of the parabolic orbit (time-monotone / implicit-Euler;
the convergence is time-monotonicity, NOT map-order-preservation) — the genuine deepest gate, cron in flight.

## ~~G2 COLLAPSE~~ (SUPERSEDED by G2 RESOLUTION above — kept for the auxMap/hstat facts, which still hold)
## ★ G2 COLLAPSE (2026-06-15, source-verified) — the stationary resolver IS the committed auxMap
The parabolic-orbit `FrozenAuxiliaryLimitOutput` contract is BYPASSED. The committed
`auxMap p c lam u` (WaveAuxMap.lean:234) = `∫ Kλ(x−y)(reaction+λu) − χ∫ Kλ'(x−y)·auxFlux` IS exactly
the divergence-form stationary Green-resolver (chemotaxis folded into greenKernelDeriv via IBP — the
integral form with NO explicit W'). Its FIXED POINTS are stationary:
  `fixedPoint_stationary` (WaveAuxMap:279): `GreenIdentity p c lam u ∧ auxMap…u=u ⟹ ∀x frozenWaveOperator p c u u x=0`. COMMITTED, linarith-clean.
  `fixedPoint_paper_stationary` (:297): same → `paperWaveOperator=0` under trap diff hyps. COMMITTED.
  `GreenIdentity` discharged end-to-end by `greenIdentity_of_convRepr` (WaveConvRepr:242) = auxMap_eq_negGreenConv
  + **flux_ibp** (committed THIS session) + decay tails. So GreenIdentity holds on the trap modulo the
  per-u C¹/decay hyps flux_ibp carries.
⟹ **hstat is essentially COMMITTED** (fixedPoint_paper_stationary), not a frontier. No parabolic existence,
no nested solve, no separate L1' construction — auxMap is Tmap and stationarity is automatic at the fixed point.

### ⚠️ CORRECTION (cron2 G2-L1' verdict): the collapse is PARTIAL — invariance crux REMAINS.
hstat IS free (auxMap explicit, fixedPoint_stationary committed). BUT cron2 confirms the chemotaxis
integral −χ∫Kλ'(x−y)W^m V' is NOT order-preserving (Kλ' sign-changes at y=x → opposite-sign half-lines;
no pointwise sign). So `auxMap(u) ≤ Ū` does NOT follow from the committed super-barrier: the super-barrier
frozenWaveOperator(p,c,u,Ū)≤0 uses the Ū-flux (Ū^m V_u'), while auxMap(u) uses the u-flux (u^m V_u'); the
elliptic-max-principle reduction needs source_u(u) ≤ source_u(Ū) = chemotaxis monotonicity = the false sign
lemma. The orbit route got invariance from the PARABOLIC max principle (comparison on the evolution, no
order-preservation of a map needed) — which the stationary auxMap-direct route LACKS. So G2a invariance is
the genuine deep crux (= ChemotaxisSandwich) in BOTH routes; the stationary route trades parabolic-existence
for this invariance gate. Monotone iteration is doubly blocked (not order-preserving + regularity needs a
separate smoothing pass). [cron G2a invariance design in flight — the real mathematical heart of B1.]

### Real remaining G2 obligations (the auxMap analytic core = old L2, NOT a new gate):
- **G2a invariance**: `∀u, trap u → trap (auxMap p c lam u)` — uses committed cross-frozen super-barrier
  frozenWaveOperator(p,c,u,Ū)≤0 (3643/4804/4832) + sub-barrier + the Green-resolver order structure.
- **G2b** `LocalUniformContinuousOn trap (auxMap …)` — auxMap continuity under loc-unif convergence (Kλ kernel + dominated conv).
- **G2c** `LocalUniformSequentiallyCompactRange trap (auxMap …)` — uniform local C¹/C² bounds on auxMap u + Helly/Arzelà.
- **G2d GreenIdentity trap-discharge**: the per-u flux_ibp C¹/decay hyps (auxFlux C¹, ±∞ decay) for trap u.
- **G2e** new `FrozenStationaryMapSchauderData` contract (= G2a+G2b+G2c) + parallel bridge
  `FrozenWaveMapConstruction'.of_stationary_schauderData` → NegativeSensitivityWaveFixedPointConstruction,
  using the G1 principle to extract the fixed point, then fixedPoint_paper_stationary for hstat.
(cron2 G2-L1' design in flight will confirm/refine; the auxMap=integral-form was exactly its question's hypothesis.)

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

## ★★★★★ B1 FINAL ASSEMBLY ROUTE (cron2, 2026-06-15) — parallel STATIONARY-MAP bridge (bypass orbit contract)
The Rothe construction is NOT forced into the committed continuous-time `FrozenAuxiliaryLimitOutput`
(which demands deriv(z τ)=frozenWaveOp…). Instead Tmap u := `rotheLimit (z(u))` (the monotone-limit of the
implicit-Euler Green orbit, committed WaveRotheLimit), fed through a NEW parallel bridge:
  def FrozenStationaryMapSchauderData (Tmap) :=
    (∀u, trap u → trap (Tmap u))                        -- invariance: max-principle trap (WaveRotheMaxPrinciple) + rotheLimit_mem_trap
    ∧ (∀u, trap u → crossAuxMap p c lam u (Tmap u) = Tmap u)  -- stationary fixed pt [abd71a43: rotheLimit_stationary]
    ∧ LocalUniformContinuousOn trap Tmap                -- continuity-in-u [cron2 equicont design]
    ∧ LocalUniformSequentiallyCompactRange trap Tmap    -- compactness (Helly/Arzelà) [cron2 equicont design]
  theorem FrozenStationaryMapSchauderData.exists_self_frozen_stationary
    (hprinciple : LocalUniformSchauderFixedPointPrinciple trap)  -- = G1 [needs R3]
    (hdata) : ∃ U, trap U ∧ crossAuxMap p c lam U U = U
  → crossImplicitMap_self_eq_auxMap ⟹ auxMap p c lam U = U ⟹ committed fixedPoint_stationary
  ⟹ ∀x frozenWaveOperator p c U U x = 0. Then feed U into the committed raw/profile bridges
  (+ U→1 atBot, V'≤0 [committed frozenElliptic_deriv_nonpos], Shen bound [committed], tail [committed])
  → B1 Theorem_1_1. THIS replaces the FrozenWaveMapConstruction/orbit-contract path entirely.
ASSEMBLY BRICKS: ✅ rotheLimit+trap (WaveRotheLimit) · 🔧 rotheLimit_stationary (abd71a43) ·
  🔧 equicont/uniform-C¹ → continuity+compactness+limit-continuity (cron2 design) ·
  ⬜ the FrozenStationaryMapSchauderData def + exists_self_frozen_stationary bridge (Statements scaffold) ·
  ⬜ final wiring to Theorem_1_1. Gated ultimately on G1 (R3) for the Schauder principle.

## ⚠️⚠️ R3 BASE-PROJECTION IS DEAD (cron, 2026-06-15) — model mismatch, NOT a bijection
cron verdict: the `dropLast` base-projection reduction {rainbow boundary doors}↔{(n-1)-rainbow cells}
CANNOT EXIST in the committed fixed-last-chain Kuhn model. Reason: `chainVZ_last` ⟹ a boundary endpoint
facet's n vertices have DISTINCT last coords, so ≤1 vertex on `{last=0}`; the Sperner label (coordinate
inequalities f(v)_i≤v_i) is NOT invariant under base projection, and `labelN_ne_last_on_face` applies only
to literal-last=0 vertices. So no `card_nbij'` preserves rainbow-ness through dropLast. The dropLast
substrate (dropLast_chainVZ_count etc.) is committed but the BIJECTION on top of it is a dead end.
TWO CORRECT PATHS:
- Path 1: switch to a boundary-compatible Kuhn/Freudenthal triangulation (face = literal (n-1)-subcomplex)
  ⟹ standard Sperner induction. BUT requires rebuilding chainVZ/facetSet/partnerCell/hinterior on the new model.
- Path 2 (LIKELY): keep the model, prove R3 by a DIRECT endpoint-boundary PARITY (boundary-partner involution
  on the face leaving rainbow doors unpaired), NOT dimension-drop. STRONG HINT: committed brouwer_stdSimplex_two
  closes the n=2 boundary count IN this exact model (the "diag/hypotenuse" argument) — if that's a direct parity
  it GENERALIZES. [cron R3-path design in flight: which path + the general-n construction.]
