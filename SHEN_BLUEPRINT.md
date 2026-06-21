# SHEN TRILOGY — GLOBAL BLUEPRINT (常驻更新 · live top-level view)

Goal: fully formalize the three Chen-Ruau-Shen chemotaxis papers, each headline genuinely
UNCONDITIONAL (conditional only on satisfiable CMParams), passing playbook §3.3 FAITHFUL audit
(no sorry/admit/native_decide/custom axiom; no vacuous/unsatisfiable hypotheses; STATEMENT faithful).
Detailed audit log: `SHEN_AUDIT_CHECKLIST.md`. This file = the global map, updated every round.

Legend: ✅ proven+committed · 🟢 proven in-clone (commit/wire pending) · 🟡 in active work (codex grinding)
· 🔴 genuine hard core (open) · ⚠️ faithfulness note.
Last update: 2026-06-21 ~13:40.

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
- 🔴 genuine core now = the Schauder fixed-point assembly (clean; the Rothe residual→0 is ELIMINATED by the pivot).
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
- ⚠️ regime: IntervalDomainBoundednessHyp has redundant 2γ<α conjunct ⇒ covers only damping-dominant
  regime (not full sharp OR-threshold). ⚠️ driftBoundFromMass needs L∞ (from ladder), not mass (1<γ<2 spike).

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
## LANDED MILESTONES (committed, root-verified)
0eb36e3 (P1 10→5) · 2b6e975 (P2 hB_global) · 0528f04 (P2 6→5) · 7cc3ddc (P2 5→3) · 2c58ff5 (P3 l2BootstrapSeed wired).

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
