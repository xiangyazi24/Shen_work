# SHEN TRILOGY — GLOBAL BLUEPRINT (常驻更新 · live top-level view)

Goal: fully formalize the three Chen-Ruau-Shen chemotaxis papers, each headline genuinely
UNCONDITIONAL (conditional only on satisfiable CMParams), passing playbook §3.3 FAITHFUL audit
(no sorry/admit/native_decide/custom axiom; no vacuous/unsatisfiable hypotheses; STATEMENT faithful).
Detailed audit log: `SHEN_AUDIT_CHECKLIST.md`. This file = the global map, updated every round.

Legend: ✅ proven+committed · 🟢 proven in-clone (commit/wire pending) · 🟡 in active work (codex grinding)
· 🔴 genuine hard core (open) · ⚠️ faithfulness note.
Last update: 2026-06-21 — FIRST MILESTONE LANDED.

## ✅✅ MILESTONE #1 LANDED (origin/main c3620c9, 06-21) — Paper 3 Theorem 2.1 persistence (m=1 small-sensitivity)
`IntervalDomainSectorialTheorem21Persistence` via `..._actualLinearSmall`: liminf inf_x u ≥ θ ∧ liminf inf_x v ≥
(ν/μ)θ^γ, θ=((a−Cχ)/b)^{1/α}, Cχ=χ0μΘ_{β-1}, conditional ONLY on satisfiable PositiveGlobalBoundedSolution + params
(m=1, a>Cχ). Dini DERIVED from PDE (interior-argmin u_x=0/u_xx≥0 + theta_linear bound + CompactMinDanskin), NOT
carried. Part3(m>1) vacuous for m=1. HOSTILE-OPUS-AUDITED FAITHFUL. Cold-build green (8718 jobs), axiom-clean.

## ✅ MILESTONE #1.5 LANDED (origin/main b9a4ecc, 06-21) — P3 hypothesis class PROVABLY INHABITED
`intervalDomain_persistingSolution_exists`: constant equilibrium (u≡U*, v≡V*) is a genuine IsPaper2ClassicalSolution
(7 conjuncts genuine, endpoint Neumann via TRUE one-sided derivWithin not junk) + bounded + positive ⇒ ∃ u v,
PositiveGlobalBoundedSolution ∧ persistence. Unconditional ∃-a-persisting-solution. Addresses "don't assume input"
(Xiang). TRIVIAL equilibrium witness (general non-trivial existence = Paper 2 Thm 1.1). Audited FAITHFUL, axiom-clean.
Landed by Opus (Codex usage-limited): codex did the Dini proof pre-limit; Opus did the hostile audit + full-closure
cold-build commit. LANDING MECHANICS: buildserver HTTPS remote has NO push creds → mirror verified ShenWork to mini
(~/repos/Shen_work, has gh auth) → commit + push from mini. Cold-build = mirror p3 clone ShenWork onto fresh
origin/main (rsync --delete, keep .lake) → lake build ShenWork → BS_EXIT=0 gate.
REMAINING (all Opus-driven, Codex out until 06-26): P2 = flux bridge BFormFluxACWeakBridge (≈flux-H¹, needs F∈H^ρ;
content already in BFormSpectralFrontierResidual, wiring path exists); P3 stability Thm 2.2 (route designed); P1 =
route reconciliation (target needs NO monotonicity — Rothe right-vanishing vs fixed-source existence).

## P1 PRECISE BOTTLENECK (Opus exec verified, Pro-checked, P1_BARE_REMARK_DIAGNOSIS.md): genuine core = StrictlyPositiveAtLeft
fixedSourceLowerPinnedBarrier_exists_fixed_of_green_apriori is PROVEN (axiom-clean). IsRightVanishingTravelingWave's
right-vanishing/ode_V/U_pos/tail are FREE from the trap. Two FALSE premises killed the "shortest path": (1)
lowerBarrierRaw φ=e^{−κx}−D·e^{−κtilde x} → −∞ at far left (NOT positive there), so U≥φ gives NO left floor; (2)
brick-1 C² second_bound is FALSE ∀-trap (flux F=u^m V' only C⁰ on C⁰ trap) — but existence uses only value+lipschitz
(Arzelà-Ascoli), so brick 1 REDUCES to value+lipschitz (EASY, lemmas half-exist: greenConv_abs_le_upperBarrier...,
greenConvDeriv_abs_le...). Brick 2 FixedSourceBarrierInvarianceData = MEDIUM (barrier sub/super-sign assembly).
GENUINE BOTTLENECK = StrictlyPositiveAtLeft U (positive floor at −∞) for the NON-MONOTONE fixed point: needs strong
max-principle (U≥0,U≢0⇒U>0) + left-tail Liouville (bounded positive stationary → positive equilibrium at −∞). Same
left-tail stabilization core monotonicity was meant to supply (monotonicity blocked: T doesn't preserve antitone).
P1 = NOT quick; left-floor is a real PDE theorem. greenConv ODE-C² identity (greenConv_variation_negative) IS proven.

## CAMPAIGN HONEST STATE (post milestone #1): each remaining piece has a genuine hard analytic core, none quick.
- P3 persistence (m=1): ✅ LANDED conditional on PositiveGlobalBoundedSolution. Equilibrium-witness (∃ provable
  persisting solution) in progress to make it non-vacuous; full discharge = Paper 2 existence+regularity.
- P1 traveling wave: core = StrictlyPositiveAtLeft (strong-max + left-tail Liouville).
- P2 boundedness: core = flux bridge / F∈H^ρ regularity (= IsPaper2Bounded+classical regularity, the largest piece).
- These three cores (P1 left-tail Liouville, P2 flux-H^ρ, P3-existence=P2) are the real frontier. Codex out till 06-26.

## ROUND 3 (06-21) — each paper at ONE named irreducible wall; all 3 codexes honest-stalled axiom-clean, re-fired
- **P1 wall = FixedSourceStationaryPointwiseStabilization** (genuine Liouville: bounded entire stationary
  W''+cW'−λW+R=0, 0<c1≤W≤C2 ⇒ W≡U_-=(a/b)^{1/α}) + auxRHS still carries deriv(auxFlux) → re-fired P1stab:
  REDEFINE auxMap to TRUE divergence form (−χ·greenConvDeriv on the kernel, NOT deriv of flux) so auxRHS
  continuity comes from the C⁰ trap; + build the no-nonconstant-bounded-entire-solution lemma (z=W−U_- max-principle
  or bounded-inverse contraction). ChatGPT cron1 consulted (git-drop, soundness of two routes + minimal hyps).
- **P2 wall = RestartRepresentativeIdentity** (u-slice = its cosine series). GENUINE WIN: provider + first factor
  ALREADY CONSTRUCTED *given* the identity (bFormFluxH1Constructor_of_restartRepresentativeIdentity,
  p2WeightedRestartCoeffToUFactor_of_restartRepresentativeIdentity, IntervalBFormP2NonCircularRepBridge.lean:56/64).
  Only the identity remains → re-fired P2repid: prove it NON-CIRCULARLY from conjugatePicardLimit's DEFINITION
  (cosine-Duhamel L²-limit ∈ closed cosine span ⇒ equals its cosine series, HilbertBasis.hasSum_repr), NOT from
  flux H¹ (circular). ChatGPT cron2 consulted (git-drop, is the identity automatic-by-construction / hidden circularity).
- **P3 wall = headline field defs are SHARP-mis-stated vs paper liminf** (deepest insight this round). Codex PROVED
  actual m=1-linear min-estimate, CompactMinDanskin→Dini wrapping, faithful u+v liminf. But the headline
  IntervalDomainSectorialTheorem21Persistence demands raw EXACT-eventual parts 1-4 (STRONGER than paper & false,
  z=θ−e^{-t} counterexample). Paper3 Thm 2.1 = liminf. → re-fired P3faith WITH PERMISSION to correct the Part
  field DEFINITIONS to the paper-faithful liminf u+v form (faithfulness fix, not downgrade), then discharge from the
  proven pieces; part3's m>1 branch is VACUOUS for the m=1 interval operator (state faithfully). P3 = closest to landing.

### ROUND 3 harvest (codex stalls audited + ChatGPT routes confirmed)
- **P1: Green route is CIRCULAR — REJECTED, pivoted to MONOTONE.** Codex's residual FixedSourceStationaryLinearGreenIdentity
  asserts (W−Ustar) = greenConv(0) = the Liouville CONCLUSION in disguise (assumed-conclusion §3.3). GENUINE kept:
  the auxRHS true-divergence-form wrapper (WaveFixedSourceTrueDivergence.lean) — REMOVES the C⁰ continuity blocker.
  ChatGPT cron2 (577-line) CONFIRMS the monotone+root-pinning route is the ONLY unconditional internal proof (trap
  IS monotone → Antitone W); refinement: W''→0 comes from "RHS converges ⇒ W''→A finite + W'→0 ⇒ A=0", not a
  generic lemma. P1 codex RE-FIRED on the full monotone chain (limits→W'→0→resolver-at-const→reaction-root→squeeze).
- **P2: gap precisely = P2RestartRepresentativeHasSum.** conjugatePicardLimit = limUnder of Picard ITERATES (not a
  tsum), so no direct unfold. Codex PROVED (axiom-clean) that GIVEN this HasSum, restartRepresentativeIdentity +
  bFormFluxH1Constructor follow. ChatGPT cron2 CONFIRMS non-circular: cosine basis COMPLETE in L² ⇒ hasSum_repr free;
  only coefficient-identification (a_k = ⟪cosBasis k, u_s⟫ via inner-product continuity along iterates' L²-conv).
  P2 codex RE-FIRED on exactly that. Watch: identity is L²/a.e. (HasSum), NOT pointwise EqOn.
- **P3 stability Theorem 2.2 route DESIGNED** (ChatGPT cron1): it's the LOCAL spectral-stability small-data theorem
  (χ<χ* ⇒ exp convergence of small data), NOT global attraction; σ_k = −(d1λ_k+αa) + χ0νγ(u*)^{m+γ−1}λ_k/((1+v*)^β(μ+d2λ_k)),
  σ_0=−αa<0; route = spectral-gap + Duhamel small-data contraction. Ready to dispatch to p3 clone once persistence lands.
- ChatGPT cron1/cron2 kept rolling: 6 git-drop consults this round (P1-Liouville, P2-rep, P3-stability, P1-monotone,
  P3-faithful-stmt, P2-cosine-basis), all in answers/*.md on origin/main.

### ROUND 4 (06-21, Pro greenlit by Xiang) — architecture locked per paper
- **P1 reduced to TWO named atoms: Barbalat + resolver-at-constant.** Codex caught that abstract-∀Ustar monotone
  Liouville is FALSE (constant solution W≡1) → Ustar FIXED = 1 (repo logistic u(1−u^α), no a,b). DONE (axiom-clean):
  auxRHS true-divergence wrapper, root-pin+squeeze under flat tails (fixedSourceLeftLiouvilleMonotone_of_tail_reaction_roots).
  RESIDUAL = Step 2 (W'→0 via BARBALAT: antitone+bdd ⇒ W' integrable, bdd W'' ⇒ W' UC, UC+integrable ⇒ →0; Mathlib
  may lack Barbalat → prove by contradiction) needing the construction's C² regularity THREADED in (satisfiable:
  the Schauder profile IS C² via B_image bound) + Step 3 (resolver V[W]→V[L], ∂_xV→0 at constant limit). Pro P1mono
  consulted. P1 codex grinding regularity-thread + Barbalat.
- **P2 architecture PIVOTED (Pro-driven) + interface FIXED.** Codex Phase-A finding: downstream needs NOT pointwise
  EqOn but the WEAK interface (chemFluxLifted AC on [0,1] + coupledChemDivSourceLift =ᵐ deriv chemFluxLifted), which
  hB_global_of_flux_ac_reconstruction already consumes. Provider REWIRED to bFormFluxH1Constructor_of_p2FluxH1SourceBridge;
  the circular pointwise rep-identity consumer DELETED (genuine cleanup). Pro REVISED the route: partial-sum IBP for
  the NONLINEAR flux is NOT self-sufficient (only "any distributional limit of (P_N F)' is the weak deriv", needs
  Σλ_k|b_k|²<∞); the CLEAN non-circular route = PARABOLIC SMOOTHING (u(s,·)∈H¹, v(s,·)∈H² for s>0 from heat-semigroup/
  elliptic resolver, INDEPENDENT of flux deriv) ⇒ F=u^m(1+v)^{−β}v_x ∈ H¹ by SOBOLEV PRODUCT/chain rule (1D H¹∩L^∞
  Banach algebra). RESIDUAL = P2FluxH1SourceBridge via Sobolev calculus from the smoothing (codex Phase-A checks if
  the repo's solution carries the H¹/H² regularity; if not, that smoothing is the single genuine analytic input).
- **P3: faithful liminf form CONFIRMED by Pro** (sharp-eventual at θ is false, z=θ−e^{−t}; correct eventual = ε-loss
  ∀ε∃T∀t≥T inf u≥θ−ε; both u AND v components). θ=((a−Cχ)/b)^{1/α}, Cχ=χ0μΘ_{β−1}. P3 codex correcting the fields.
  P3 stability Theorem 2.2 = local spectral small-data (χ<χ*, ‖w0‖<ε); Duhamel/mode-wise route consulted on Pro (prep dispatch).
- NOTE: ChatGPT git-drop "[reported]" (vs "[VERIFIED]") = phantom commit (file not actually on main) — re-fire. P1mono-PRO was lost this way.

### ROUND 5 (06-21) — ALL THREE PAPERS CONVERGED TO ONE NAMED GENUINE ANALYTIC CORE EACH (the faithful structure)
Each headline is now conditional ONLY on its single satisfiable PDE lemma; nothing fake landed (every claim hostilely audited).
- **P3 "completion" claim (1.1M tokens) AUDITED → CONDITIONAL (frontier repackaging), NOT a milestone.** Hostile opus
  found: headline IS on real interval [0,1] + statement faithful (liminf u&v, right θ, satisfiable, axiom-clean) BUT
  rests on carried frontier IntervalDomainLogisticPersistenceInputs whose fields ARE the conclusion; the only real
  liminf proof is on the DISCONNECTED singleton unitPointDomain. GENUINE RESIDUAL = the spatial-minimum lower-right
  Dini comparison on the interval. Re-fired P3discharge: at spatial argmin x*, u_xx≥0 & u_x=0 ⇒ chemotaxis term →
  linear Cχ·u(x*) ⇒ D⁺ sInf_x u ≥ (a−Cχ)sInf_x u − b(sInf_x u)^{1+α} ⇒ wire PROVEN-orphan CompactMinDanskin + the
  scalar persistence (proven on singleton, domain-agnostic, LIFT it) ⇒ liminf sInf_x u ≥ θ; v via elliptic transfer.
  Part3 (m>1 superlinear) N/A for the m=1-linear committed operator — state regime split faithfully.
- **P2 genuine core = B-form positive-time H¹ smoothing** (= P2SolutionSpatialH2Regularity / BFormDirectP2FactorSmoothing).
  Codex proved bFormFluxH1Provider follows from it (axiom-clean). Relationship to the repo's existing
  GradientMildHalfStepH2SourceData H² bootstrap is (iii) GENUINELY DIFFERENT (conjugatePicardLimit ≠ gradient-mild;
  uniqueness only compares conjugate-mild; B-form refuses to coerce). Re-fired P2bridge: try GradientToConjugate
  equivalence (if a gradient-mild solution satisfies the conjugate fixed-point eq ⇒ uniqueness ⇒ transfer H²); else
  direct heat-semigroup smoothing (cosine multiplier sup_k (kπ/L)²e^{−2d1(kπ/L)²s} ≤ 1/(2e d1 s) ⇒ L²→H¹ for s>0 +
  Duhamel preserves). Pro consulted in PIPE mode (Xiang switched git-drop→pipe; both modes worked this session).
- **P1 genuine core = Barbalat (W'→0) + C² regularity threading + resolver-at-constant** (Ustar=1; root-pin+squeeze
  DONE under flat tails). Codex grinding; Pro P1mono hard-steps landed (26bd410a3, VERIFIED).
- P3 stability Thm 2.2 Duhamel/mode-wise route landed on Pro (01b23b036) — staged for dispatch after persistence.

### ROUND 6 (06-21) — P2 B-form H¹ OBSTRUCTION (proven false), P1 one regularity-lemma from milestone
- **P1: monotone Liouville analytic core DONE (axiom-clean); ONE step from Remark_1_3_2.** Proven: Barbalat,
  C²-regularity-satisfiability, resolver-at-constant, root-pin+squeeze, antitone-closure of left-translate limits,
  the limit→Liouville→Tendsto U atBot→Remark wiring. REMAINING = the C²-of-left-translate-LIMIT producer
  (FixedSourceLeftTranslateRegularStationaryCompactness): translates share uniform C² bounds ⇒ the locally-uniform
  limit is C² by Arzelà-Ascoli (RotheAACompactnessData). Re-fired P1c2lim. P1 = closest to a real milestone.
- **P2: the B-form L²→H¹ route is PROVEN FALSE for unconditional flux-H¹** (Pro git-drop c0a0ef86a, VERIFIED, with
  explicit lacunary counterexample). The single √λ_k closes the L² mild interp non-circularly ((s−τ)^{−1/2}
  integrable), but H¹ needs a 2nd √λ_k → A·e^{−(s−τ)A} ~ (s−τ)^{−1} NON-integrable, and L^∞_t L²_x → H¹_x is
  UNBOUNDED (not just a bad estimate). ⇒ DO NOT write an unconditional L²→H¹ B-form theorem (false). P2 needs a
  genuine EXTRA regularity input: (A) F∈L^∞_t H^ρ (ρ>0) ⇒ ‖u^B(s)‖_H¹ ≤ C s^{ρ/2}‖F‖_{L^∞ H^ρ}; (B) Dini/Hölder
  time reg; (C) maximal regularity+trace. PLAN (Pro's modular recommendation): prove the linear-semigroup L²→H¹
  bound unconditionally (the proven IntervalBFormDirectSmoothingCalc), formalize the chemotaxis-Duhamel H¹ as a
  CONDITIONAL lemma carrying explicit F∈H^ρ. So P2 headline = CONDITIONAL on a standard satisfiable parabolic-
  regularity input (faithful; NOT the hard content in disguise) — UNLESS we invest in the full maximal-regularity
  bootstrap. Scope decision flagged to Xiang. P2 codex grinding the (valid) linear full-kernel bridge.
- P3: still grinding the genuine spatial-min Dini discharge (Danskin argmin + scalar lift).

### ROUND 7 (06-21) — ALL THREE AT GENUINE FINAL CORE (every hollow conditional caught & rejected)
Pattern confirmed across all 3: codexes wire the downstream scalar/interface chain cleanly, but the genuine analytic
core stays CARRIED until explicitly forced. Caught 2 hollow conditionals this round (grep-audit: a carried Prop with
NO producer = not a result).
- **P1: residual = top-level CONSTRUCTION-PRODUCER assembly.** Monotone Liouville + Barbalat + C²/C³ regularity +
  antitone-closure + C³→Remark wiring ALL proven axiom-clean. But Remark_1_3_2.of_..C3Construction is the construction
  WIRED, not bare — no unconditional producer for raw-compactness/antitone/C³ construction data yet. Re-fired
  P1assemble: apply the proven Schauder principle (localUniformSchauderFixedPointPrinciple_of_brouwer) + barrier trap
  + Tmap continuity + AA compactness + C³ regularity → ∃ fixed point in InLowerPinnedBarrierTrap → bare Remark_1_3_2.
  WATCH: trap-genericity InMonotoneWaveTrap vs InLowerPinnedBarrierTrap (blueprint-flagged). P1 = closest.
- **P2: HOLLOW conditional CAUGHT — root wall is the L² rep-identity (recurring since round 3).** paper2_theorem_1_1
  _conditional_on_flux_Hrho carried THREE Props with NO producers (P2FluxOptionAEstimate, NeumannHeatSemigroupL2ToH1
  SmoothingBound full-kernel ver, FullKernelL2CosineHeatEqOn). The Option-A estimate isn't the wall — the ROOT is:
  conjugatePicardLimit (a limUnder) ↔ its cosine-spectral representation. Repo proves the CONTINUOUS EqOn
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc:108) but not L²/MemLp. Re-fired P2root: extend to L² by
  DENSITY (both sides continuous L²→L², agree on dense continuous set) + the rep identity via the iterates' L²
  convergence. P2 = MOST ENTANGLED (B-form frontier has many interlocking bridges; needs fractional-H^ρ infra too).
- **P3: Part2 scalar chain WIRED to interval (intervalDomain_part2_liminfUV_of_actualLinearDini), core CARRIED.**
  Residual = PROVE ActualLinearSpatialMinimumDini: argmin analysis (at spatial min x*, u_x=0, u_xx≥0 ⇒ chemotaxis →
  linear Cχ·u(x*)) + CompactMinDanskin (proven orphan) ⇒ D⁺ sInf u ≥ (a−Cχ)sInf u − b(sInf u)^{1+α}; + v-cobounded
  input (v bdd from v-eqn). Part3 (m>1) honestly N/A for m=1 operator. Re-fired P3dini.

### ROUND 8 (06-21) — P1 ROUTE REFINEMENT: monotonicity is a genuine SEPARATE analytic core
- **P1: T does NOT preserve antitone (Pro VERIFIED 5556ceda3).** fixed-source existence is PROVEN
  (fixedSourceLowerPinnedBarrier_exists_fixed_of_green_apriori, axiom-clean) but lands in the BARRIER trap (non-
  monotone). The chain u antitone ⇒ V[u] antitone ✓ ⇒ source antitone ✗ (logistic-after-shift sign param-dependent;
  chemotaxis source derivative no one-sided sign) ⇒ T(u) antitone ✗. So monotonicity of the wave is a SEPARATE
  genuine analytic core, NOT wiring/trap-membership. The monotone Liouville (proven) NEEDS antitone ⇒ must prove it.
  CORRECT mechanism (Pro Option B/C): differentiate the profile eqn, w=U' solves a linear (parabolic/elliptic) eqn,
  MAXIMUM PRINCIPLE under paper sign/param assumptions + w→0 at ±∞ ⇒ w≤0 ⇒ U antitone. Does NOT need source-antitone.
  So P1's REAL last core = the U'-max-principle monotonicity theorem (+ then the 2 wiring producers). NOT one-step-away.
  (My round-1 pivot assumed "trap is monotone" per ChatGPT v1 — but fixed-source lands in the barrier trap; monotone
  trap needs T-preserves-mono which is false. Liouville-route correction: prove monotonicity via U' max principle.)
- This puts all 3 papers at one genuine HARD analytic core each: P1 = U'-max-principle monotonicity; P2 = L²
  cosine-spectral rep of conjugatePicardLimit (+ fractional H^ρ); P3 = spatial-min argmin Dini. None is mere wiring;
  each is a real (standard, satisfiable) PDE lemma. Codexes grinding all three.

### ROUND 9 (06-21) — CODEX USAGE LIMIT HIT (resets Jun 26 9:17 PM); P1 target finding; P2 root half-broken
- **⚠️ CODEX PRO OUT OF CREDITS until 2026-06-26 21:17.** New codex runs ERROR immediately; runs started before the
  limit finish normally. P1 dispatch blocked. Awaiting Xiang's call: buy credits / wait / Opus-self. P2+P3 finished
  their pre-limit runs.
- **P1 BIG FINDING (verify-before-claim): IsRightVanishingTravelingWave needs NO monotonicity** — only ode_U/ode_V +
  U_pos + lim_pos_inf (U,V→0 at +∞) + positive_at_left (StrictlyPositiveAtLeft = positive FLOOR at left, NOT U→1).
  The 8 rounds of monotone Liouville/Barbalat/C³/antitonicity solved a HARDER problem than the target. BUT the wrinkle:
  the right-vanishing machinery (WaveLemma42G1Discharge b1_chiPos_rightVanishing_..._of_cubeApproxData) is built on the
  ROTHE route (InLowerPinnedMonotoneTrap + rotheLimit + positiveCoreRotheSeq), NOT the fixed-source barrier route.
  So P1 = reconcile fixed-source existence with Rothe right-vanishing, OR finish the Rothe route (which HAS the
  right-vanishing; was abandoned on "residual→0"). Route-level untangle, not pure wiring. NOT one-step-away, but the
  monotone-Liouville detour is dead — target is weaker.
- **P2 root HALF-BROKEN (genuine progress, 813k):** PROVED axiom-clean FullKernelL2CosineHeatEqOn_by_density +
  neumannHeatSemigroupL2ToH1SmoothingBound_by_density (the L² spectral-rep wall since round 3). Residual narrowed to
  P2ConjugateLimitRestartHasSum (the rep identity), and the missing ingredient is now AVAILABLE:
  conjugatePicardIter_uniform_convergence (IntervalConjugatePicard.lean:93, geometric K^n contraction). Route:
  uniform conv ⇒ L² conv ⇒ ⟪cosBasis k, limit⟫ = lim iterate-coeff ⇒ hasSum_repr. CLEAR path, needs a run (blocked).
- P3: P3dini still running at limit-time (will finish) — proving the argmin spatial-min Dini.

────────────────────────────────────────────────────────────────────────
## PAPER 1 — traveling-wave existence  (Remark_1_3_2 : ∃ U V, IsRightVanishingTravelingWave)
ROUTE DECIDED (Xiang-approved pivot 06-21): **fixed-source linear Schauder** — ABANDON the repo's
semi-implicit crossImplicitMap / Rothe floor (it kept generating relocations + the nonmonotone
residual→0 crux). T(u) := greenConv(−(R(u,V[u])+λu)), R FROZEN by the INPUT u ⇒ inner solve is
LINEAR, "T solves the frozen eq" TRUE BY CONSTRUCTION; outer Schauder fixed point u=T(u) = the wave.

- ✅ field-shrink (10→5), hc3-artifact elimination, C¹ convergence (committed 0eb36e3)
- ✅ barrier route de-monotonized; projection layer (finite-net, no antitone) audit-GENUINE (in-clone)
- 🟢 PROVEN infra reused by the pivot: AA compactness (helly_pointwise_selection, RotheAACompactnessData),
  both barriers (sign cond R+M·upper≥0 lower / R≤q·upper upper), a-priori C² Green bound B_image,
  Tmap continuity (FrozenEllipticDerivDependence proven), nontriviality (lower-pin), left-tail (finite var)
- 🟡 **fixed-source Schauder assembly** (P1fixedsrc grinding): linear map T(u) + trap-inv + continuity +
  AA compactness + Schauder fixed point → IsRightVanishingTravelingWave → wire Remark_1_3_2.
- 🟢 **Schauder/Brouwer core ALREADY PROVEN in-repo, axiom-clean**: full n-dim Brouwer via Sperner/Freudenthal
  (Brouwer.lean, BrouwerNDimFreudenthal/Final/Complete — all forbidden=0) + Schauder principle
  (localUniformSchauderFixedPointPrinciple_of_brouwer, InMonotoneWaveTrapSchauderPrinciple.lean). Mathlib LACKS
  these (cron1) — the repo built them. P1 fixed-source reduces to feeding the barrier-trap ProjectedCubeApproxData
  (already built) + continuity (proven) + AA compactness (proven) into the principle (check trap-genericity: it's
  named "InMonotoneWaveTrap" — may need re-targeting to InLowerPinnedBarrierTrap).
- 🔴 genuine core now = the Schauder fixed-point ASSEMBLY for the barrier trap (clean; Brouwer done, Rothe residual→0 ELIMINATED).
- DEAD (abandoned): crossImplicitMap, rotheLimit, residual→0, anti_k/anti_x, monotone comparison.

────────────────────────────────────────────────────────────────────────
## PAPER 2 — bounded-domain boundedness  (paper2_theorem_1_1_general_chi_via_bform)
ROUTE: BForm spectral frontier, reduced 6→5→3→(target 1).

- ✅ hB_global (2b6e975); 6→5 hVpos+hResolverData (0528f04); 5→3 dropped hGradientBridge+hSupNormDeriv (7cc3ddc)
- ✅ flux bridges 3+4 closed (rpow/reciprocal chain rule + coupledChemDivSourceLift=deriv, in-clone)
- 🟢 actual conjugatePicardLimit gradient coeffs PROVEN weighted-ℓ² summable (P2bridge1)
- 🟡 **BFormFluxH1Provider construction** (P2compose stall): gap = the flux-primitive representative
  `weighted_cosine_l2_to_flux_primitive_slices` — compose u∈H¹ (bridge2, ℓ²→IntervalH1Weak IBP route)
  with bridges 3+4 → flux=chemFluxLifted ∈ H¹ certificate. Provider must be CONSTRUCTED not carried
  (prior relocation into mkFlux REJECTED by audit).
- 🔴 after provider: per cron2 route-audit, ALSO shed hTimeNhd (derive from H¹) + hResolverCoeffTimeC1
  (audit: "not needed"; cron2 P2final pending on whether C⁰ suffices) → P2 ≈ {bank} + the absorbing/Grönwall step.
- genuine residual chain: flux H¹ provider → drop hTimeNhd/hResolverCoeffTimeC1 → bank (Mathlib-provable?) + absorbing inequality.

────────────────────────────────────────────────────────────────────────
## PAPER 3 — persistence + stability  (Theorem_2_2 ∧ Theorem_2_1 ; paper3.pdf = Part II)
⚠️ FAITHFULNESS: headline = persistence (Thm 2.1) ∧ stability (Thm 2.2). Boundedness is a HYPOTHESIS
(from Part I, arXiv 2512.14858); the Moser ladder PROVES that input. FULL target carries THREE frontier
groups — not "one Moser ladder away".

### (a) Boundedness input — Moser L^p→L^∞ ladder  (_of_aprioriFacts path)
- ✅ l2EnergyInequality, sharp L²-absorption threshold, mass bound M1 (Prop_2_4), Agmon, L^p interp
- ✅ **l2BootstrapSeed DISCHARGED+WIRED** (commit 2c58ff5, GENUINE-WIRED-REDUCTION): aprioriBound bundle
  constructed via of_l2RouteData∘to_routeData; 5 atoms discharged
- 🟢 l2SeedRegularity producer PROVEN (closed-time energy id + u(0) trace); RelativeMoserInterpolation
  PROVEN (GN q=4); finite root-tower SCALAR PROVEN (Σ1/2^k≤1, Σk/2^k≤2, ∏≤4C); drift atom PROVEN
  (IntervalDomainChemotacticDriftBound_of_LinfBound); MoserDissipationDrop reshaped to physical B>0
- 🟡 the genuine analytic proofs + WIRING: integrated PDE per-step energy inequality (proof, P3 grinding);
  then wire {l2SeedReg, RelativeMoserInterp, reshaped-dissipation, root-tower} into IntervalDomainMoserActualAtoms
  → switch IntervalDomainMoserLadderHeadline to consume it → DROP bloated Corollary21FrontierData/Prop25MoserFrontiers.
- 🟢 IntervalDomainMoserActualAtoms.lean genuine-partial-reduction (audit) but ORPHAN — needs wiring.
- ⚠️ regime SHARPENED (cron2 Moser-energy full): the clean v_xx IBP route needs only **α>γ**, NOT 2γ<α
  (2γ<α appears only in cruder v_x estimates). So IntervalDomainBoundednessHyp's 2γ<α is OVER-STRONG —
  the headline regime can be STRENGTHENED to α>γ. ⚠️ driftBoundFromMass needs L∞ (from ladder), not mass (1<γ<2 spike).
  Energy ineq constants explicit: c0=2, σ=1, K=a₊+C_abs, C_abs=(1-r)r^q(2/b)^q(χν)^{1+q}, r=γ/α, q=γ/(α-γ).

### (b) Theorem 2.2 stability — Theorem22LocalFrontiers
- 🔴 OPEN, design staged (P3_STABILITY_FINDINGS): per-mode spectral gap λ_k+αa−χ₀νγu*^{m+γ-1}λ_k/(μ+λ_k)≥δ
  + quadratic nonlinear remainder in D(A^σ) (genuine core); orbit bound + small-data global existence (bookkeeping).
- NOT yet dispatched.

### (c) Theorem 2.1 persistence — Theorem21PersistenceFrontiers (UniformPersistencePart1-4Raw)
- 🔴 OPEN, design staged (P3_PERSISTENCE_FINDINGS): spatial-minimum Dini ODE z=inf_x u,
  DiniLower z ≥ a·z−b·z^{1+α}−Cχ·z^m → liminf z ≥ ((a−Cχ)/b)^{1/α} (genuine core); heavier minimal branch
  = time-translate compactness + strong max principle. ⚠️ split a,b>0 (logistic) from a=b=0 (decays).
- NOT yet dispatched.

────────────────────────────────────────────────────────────────────────
## LANDED MILESTONES (committed, cold-verified) — main green @ 486fb4f
0eb36e3 (P1 10→5) · 2b6e975 (P2 hB_global) · 0528f04 (P2 6→5) · 7cc3ddc (P2 5→3) · 2c58ff5 (P3 l2BootstrapSeed) · **486fb4f (P3 6th: Moser frontier shrink, full-closure cold-verified)**.

## 6th REDUCTION (P3 Moser frontier shrink) — LANDED 486fb4f via full-closure cold-build (43-file consistent P3 diff)
opus audit GENUINE-REALIZED-REDUCTION, builds 8700 jobs IN THE CLONE, axiom-clean (drops bloated
Corollary21FrontierData/Prop25MoserFrontiers → 3 smaller per-exponent obligations). Cherry-pick commit
(0a6442e) FAILED the fresh-clone gate: the clone has MODIFIED versions of shared files (e.g. one defining
`resolverGrad_sup_le_sourceL2`) absent from origin/main — full clone-drift (78 new files + modified shared
files). Reverted main to a3118f4 (green). LANDS via FULL-CLOSURE SYNC, not per-file cherry-pick, once the
P3 clone reaches a stable point.

## ROUND 2 audits (06-21, both REJECTED — loop held; genuine infra, named residuals)
- **P2resc0 BForm 2→1: PHANTOM.** The C¹→C⁰ resolver-coeff weakening is GENUINE+honest (BFormResolverSourceCoeffTimeC0
  = the weaker u∈C_tL² content, not relocation), but UNWIRED dead code — headline still 2-field; the C0→frontier
  bridge BFormFluxH1ConstructorC0 is an UNPROVEN Prop. Residual: prove that bridge + rewire headline (P2 follow-up).
- **P3liminf persistence: CONDITIONAL + WEAKER-THAN-PAPER.** Danskin PROVEN (orphan); Dini ineq only def'd not proven.
  KEY: the committed intervalDomainChemotaxisDiv is m-INDEPENDENT + LINEAR-at-critical (loss factor u(x*), = the m=1
  case Cχ·z) — the over-general z^m def mismatched it. Also the liminf defs DROPPED the paper's v-component
  (liminf inf v ≥ (ν/μ)(liminf inf u)^γ). P3actual re-fired: actual m=1-linear Dini + v-component (proven elliptic
  transfer) + wire Danskin/scalar-persistence to discharge the headline part_ULower.
- **P2 basis UNBLOCKED:** Mathlib v4.29.1 HAS fourierBasis (Mathlib.Analysis.Fourier.AddCircle, circle exponential
  HilbertBasis) → Neumann cosine basis by even-reflection. P2fourier building the representative → flux provider.
- P1liou: analytic Liouville (bounded-entire-between-positive-constants ≡ equilibrium, design staged) + payloads → Remark_1_3_2 unconditional.

## COMMIT MECHANICS (lesson 06-21)
The /var/tmp/shen_cx_* clones have DRIFTED far from origin/main (modified shared files, not just new files).
Per-file cherry-pick of a reduction now silently misses modified-shared deps → fresh-clone gate (shenbuild.sh,
git reset --hard origin/main + lake build) catches it. To LAND clone work: at a STABLE clone point (no codex
writing), rsync the reduction's FULL transitive closure (new + modified files, clone versions) → mini → root-build
→ commit. Or periodically full-sync the clone ShenWork tree. NEVER trust a warm/audit build alone for a commit —
the cold fresh-clone build is the real gate (it caught what the audit's in-clone 8700-job build could not).

## DISCIPLINE (every reduction)
proof-term read → #print axioms ⊆ {propext,Classical.choice,Quot.sound} → INDEPENDENT hostile opus audit
(default-distrust: relocation / spatial-antitone-regression / forward-to-bigger-frontier / orphan /
predicate-too-strong) → only GENUINE (obligation count down, CONSTRUCTED not carried, WIRED to real target)
gets rsync→wire-imports→commit→root-build (shenbuild.sh). This session: 7 relocation/fragment/orphan
reductions CAUGHT and rejected; nothing fake landed. "Wire to existing frontier" backfires (frontiers are
themselves carried). Re-attacks must PROVE from staged designs, not forward.

## NEXT ACTIONS
- P1: P1fixedsrc → fixed-source Schauder existence → audit → commit.
- P2: compose flux-primitive H¹ certificate → construct provider → 3→2 → then drop hTimeNhd/hResolverCoeffTimeC1.
- P3(a): prove integrated PDE energy inequality → wire the proven Moser pieces → realized boundedness reduction.
- P3(b),(c): dispatch stability + persistence frontiers (designs staged).

## P2 BOOTSTRAP PROGRESS (06-21, b553e5e) — 4 bricks LANDED, rep-identity crux remains
B1 spectral_multiplier_bound + B2 H^σ cosine scale + B4 elliptic H^σ→H^{σ+2} + B3-scalar kernel ALL on origin/main,
axiom-clean (8739 jobs). Remaining: rep identity (crux, non-circular via HilbertBasis completeness + Picard spectral
recursion coeff identity — NOT flux bridge) + B3-full Minkowski + B5 1D Sobolev product + B6 ladder wiring.
⚠️ STALE-CLONE TRAP: /var/tmp/shen_cx_pde is a no-git snapshot ~22k lines BEHIND origin/main; earlier P2 work there
NEVER pushed. WORKFLOW FIX: all Lean work now on FRESH canonical clone /var/tmp/shen_canon (synced from origin/main,
shares mathlib cache). Old shen_cx_* clones are stale — do NOT trust their builds. [[feedback_fresh_canonical_clone]]

## P2 CLOSURE REFRAMED (06-22, verified by source) — the wall is the BANACH FIXED POINT, not H^σ algebra
8 H^σ-bootstrap bricks landed (B1-B5 + kernelL2/linftyMult/DuhamelMode/DuhamelEnergy, cf4c2d5) — they feed regularity
summabilities but do NOT close paper2_theorem_1_1. The VERIFIED live reduction: FinalWiring.paper2_theorem_1_1_from_two
← hQuant + PerDatumSpectralFrontier. The frontier's hard fields (HasTimeNeighborhoodSpectralAgreement,
HasResolverDirectSpectralData, SourceCoeffQuadraticDecay, PDE-identity, positivity) are ALL DERIVED from a Banach
fixed point ConjugateMildExistenceData + BFormBankedInputs(hB_global = the FP's cosine Duhamel representation). NOW
NON-CIRCULAR at the predicate level (the round-3 "circular rep-identity wall" is resolved). hQuant = the SAME
fixed-point construction packaged uniform-in-datum, NOT a separate parabolic input — closing the FP discharges BOTH.
GENUINE RESIDUAL = instantiate the FP: assemble ConjugateMildExistenceCore (hmapsTo from the landed
intervalConjugateDuhamelMap_sup_bound_of_banked, hcontr from _diff_bound_of_banked, positivity/cont/meas from
B/C/D/O1/glue1/glue2 — all PROVEN) + a CONCRETE complete weighted trajectory metric space + Banach FP + hB_global.
This is local-existence ASSEMBLY (atoms proven) + the metric model, NOT new analysis. InfThreshold dischargeable.
P2 = P3-existence (both = this FP construction). Banach-assembly subagent attacking on shen_canon.
