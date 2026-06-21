# SHEN TRILOGY — GLOBAL BLUEPRINT (常驻更新 · live top-level view)

Goal: fully formalize the three Chen-Ruau-Shen chemotaxis papers, each headline genuinely
UNCONDITIONAL (conditional only on satisfiable CMParams), passing playbook §3.3 FAITHFUL audit
(no sorry/admit/native_decide/custom axiom; no vacuous/unsatisfiable hypotheses; STATEMENT faithful).
Detailed audit log: `SHEN_AUDIT_CHECKLIST.md`. This file = the global map, updated every round.

Legend: ✅ proven+committed · 🟢 proven in-clone (commit/wire pending) · 🟡 in active work (codex grinding)
· 🔴 genuine hard core (open) · ⚠️ faithfulness note.
Last update: 2026-06-21 round-3 dispatch.

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
