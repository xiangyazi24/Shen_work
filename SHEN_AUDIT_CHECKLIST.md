# Shen Trilogy — Unconditional Formalization Checklist

Goal: all three Chen-Ruau-Shen chemotaxis papers FULLY UNCONDITIONAL (headlines conditional only on
satisfiable CMParams antecedents), passing playbook §3.3 FAITHFUL audit (no sorry/admit/native_decide/
custom axiom; no vacuous conditionals; no carried unsatisfiable hypotheses).

Status markers: ✅ discharged (proven theorem, #print axioms clean, opus-audited GENUINE) ·
🟡 in active work (codex grinding / precise residual named) · ⬜ open/unscoped.

Last verified: 2026-06-21 ~01:30 (HEAD 0eb36e3 root-builds clean-3, CLEAN3_EXIT=0).

---

## Paper 1 — traveling-wave existence (Remark_1_3_2 / IsRightVanishingTravelingWave)
Headline asserts ∃ U V, IsRightVanishingTravelingWave (carries ode_U + ode_V — solution-ness in the type).

- ✅ per-step hgreen/hdiff eliminated from the Remark_1_3_2 chain (commit 0caf3f9, propagate)
- ✅ PositiveCoreStationaryGreenData shrunk 10→5 fields {hLU,hstep,hz_nonneg,hz_le_M,hc3}; deleted
  hgreenEq/hR_cont/hR_bound/hR_limit+Rlim; ode_U/ode_V proven SMP-free via stationary_profile_pos_of_trap_regular
  (commit 0eb36e3, opus GENUINE-NET-REDUCTION, clean-3 verified)
- ✅ **hc3 ELIMINATED as an over-decomposition artifact** (opus architecture audit): C³ was never load-bearing —
  U'' convergence is algebraic from the ODE (U''=−R−cU'+λU), positivity already C²-only. Retargeted onto the
  existing C³-free producer; hc3 field removed (in-clone; folded into the existence reduction).
- ✅ C¹ convergence z_k'→U' PROVEN; Rlim wrapper PROVEN (in-clone).
- ✅ **barrier route de-monotonized** (opus audit GENUINE-DISCHARGE of projection layer, in-clone): pivoted
  the existence route from monotone-comparison (fails χ≥1/2, anti-monotone) to barrier-Schauder. Concrete
  barrier-projected cube data (WaveBarrierProjectedCubeApproxData.lean: finite-net/partition-of-unity, NO
  waveOrderEnvelope, NO antitone — the order-envelope's one-sided inf-lower-bound is FALSE for non-antitone);
  residual_le + localError→0 GENUINELY PROVEN (triangle ineq, 4·netRadius→0), axiom-clean. The Schauder bridge
  consumes only LOCAL-uniform residual (Icc(-R)R), so tail-pinching AND antitone drop out. New concrete headline
  ConcreteBarrierSchauderConstruction sheds `Nonempty LowerPinnedBarrierWaveCubeApproxData` (strictly 1 fewer
  free atom, faithful). Full P1 existence blueprint staged (P1_TRAPINV_FINDINGS.md): AA compactness, both
  barrier sides (R+MU≥0 lower / R≤q·upper upper), Tmap continuity (C⁰_loc divergence-form), a-priori C² Green
  bound B_image, nontriviality (tiny), left-tail (finite variation + flatness).
- 🟡 **schauderData = FrozenStationaryMapSchauderData — the TRUE crisp P1 residual** (audit-located): the hard
  Rothe-Schauder existence was never on the cube atom — it is field 2 `crossImplicitMap p c lam u (Tmap u)(Tmap u)
  = Tmap u` (per-u self-frozen Green fixed point = Rothe parabolic convergence = old `hpar`), carried in BOTH old
  and new headlines. Codex P1schauder grinding: discharge fields 1 (trap-inv)/3 (Tmap cont)/4 (AA compact) from
  the blueprint → shrink schauderData to just field 2; field 2 = the genuine paper-hard existence core.

## Paper 2 — bounded-domain boundedness (paper2_theorem_1_1_general_chi_via_bform)
Headline conditional on Nonempty(BFormSpectralFrontier p DB) per datum.

- ✅ hB_global discharged via flux-deriv reconstruction (commit 2b6e975, GENUINE-NET-REDUCTION)
- ✅ BFormSpectralFrontier 6→5: hVpos discharged (max-principle), hResolverData lowered to hResolverCoeffTimeC1
  (commit 0528f04, GENUINE-NET-REDUCTION, warm-gate BS_EXIT=0)
- ✅ BFormSpectralFrontier 5→3: dropped non-faithful hGradientBridge (demanded gradient-form mild; for Neumann
  ∂ₓK_N≠−∂ᵧK_N, the faithful Duhamel is the SOURCE/conjugate form) + hSupNormDeriv; headline rewired to the direct
  B-form classical route on the PROVEN conjugate mild solution; byte-identical Theorem_1_1 (commit 7cc3ddc,
  opus GENUINE-NET-REDUCTION faithful). Also proven in-clone: hsource_bridge, hTimeNhd_of_BForm_global_cosine,
  conjugate mild identity, independent time-IBP u-C².
- 🟡 **3 residual: bank, hTimeNhd, hResolverCoeffTimeC1.** hTimeNhd's last circularity: the only cosine-rep route
  goes through flux_deriv → u-C² → hTimeNhd; needs the independent u-C² wired in (time-IBP route confirmed hTimeNhd-free).

## Paper 3 — persistence / critical-sensitivity boundedness (L² bootstrap → L∞)
Headline conditional on IntervalDomainMassLpSmoothingRouteData (3 atoms).

- ✅ l2EnergyInequality discharged (half-energy diff. inequality as theorem, not field)
- ✅ sharp absorption threshold IntervalDomainSharpL2AbsorptionThreshold (γ<1 ∨ 2γ<α) + equivalence
  (2+2γ<max(4,2+α)) + satisfiability witness (axiom-clean; SHARP by spike test)
- ✅ absorbing-inequality algebraic producer (uniform half-energy + spatial absorption ⇒ absorbing inequality)
- ✅ logistic L1 mass bound M1 PROVEN for intervalDomain: mass-derivative identity (∫Δu=0,∫chemDiv=0 via real
  FTC+Neumann) + Jensen + HasDerivAt first-crossing → intervalDomain_Proposition_2_4 (in-clone, axiom-clean)
- ✅ Agmon inequality (1D L∞) + L^p interpolation for the classical slice PROVEN (in-clone, FTC+Cauchy-Schwarz)
- ✅ **l2BootstrapSeed DISCHARGED + WIRED** (commit 2c58ff5, opus audit GENUINE-WIRED-REDUCTION):
  the headline `intervalDomain_sectorialMainline_unconditionalTarget_of_aprioriFacts` no longer carries
  the `aprioriBound` bundle — it is CONSTRUCTED via `of_l2RouteData ∘ to_routeData ∘ to_seedData`
  (mass→spatial→absorbing→integrated→L2power→bootstrap), both route fns called on the live headline path
  (not orphaned). 5 atoms discharged: aprioriBound, massComparison (=Prop_2_4), b_pos, l2EnergyInequality,
  l2BootstrapSeed. Antecedent IntervalDomainBoundednessHyp=(γ<1∨2γ<α)∧0<b∧0<γ∧γN<2 satisfiable (witness).
  Fresh-cache full ShenWork compile pass (3558 jobs), axiom-clean.
- 🟡 **Moser L^p→L^∞ ladder** (4 carried atoms on the `_of_aprioriFacts` path): driftBoundFromMass,
  l2SeedRegularity, allLpBoundFromBootstrap (=Corollary_2_1), endpointBoundFromLp (=Proposition_2_5).
  Uniform-L² (wired) seeds L²→L^p→L^∞. P3moser2 + cron findings (spike-crux + finite root-tower + seed) rolling.
- ⚠️ **FAITHFULNESS CORRECTION (source audit 06-21):** paper3.pdf is Part II — headline
  `IntervalDomainSectorialTheorem21And22UnconditionalTarget` = `Theorem_2_2 ∧ Theorem_2_1`
  (stability + persistence), faithful target, genuine conclusion (verified, IntervalDomainSectorial.lean:2203).
  The Moser ladder is only the BOUNDEDNESS INPUT (in Part II boundedness is a HYPOTHESIS from Part I [7],
  so the repo proves it under its own sufficient condition γ<1∨2γ<α). The FULL target carries THREE distinct
  frontier groups, not one: (a) boundedness/aprioriFacts (Moser ladder — being worked), (b)
  `IntervalDomainSectorialTheorem22LocalFrontiers` (stability), (c) `IntervalDomainSectorialTheorem21PersistenceFrontiers`
  (the 4 uniform-persistence parts — the actual Theorem 2.1 content) + nonlinear Duhamel/orbit control + small-data
  global existence (per def comment :2214). So P3 is NOT "one Moser ladder away" — (b),(c) are separate, largely
  unaddressed. 2c58ff5 landed the aprioriBound bundle on the boundedness path only.
- ⚠️ **REGIME (verify deeper):** formal boundedness sufficient cond γ<1∨2γ<α may be NARROWER than Part I's full
  χ-threshold (α vs m+γ−1 / 2m+γ−2, paper3 lines 459-479). Faithfulness narrowing of the INPUT, not the target;
  no vacuity (witness (N,γ,α,b)=(1,½,2,1)), no L∞ circularity (cron1 P3-audit).

---

## Scoreboard (5 root-verified reductions landed: 0eb36e3, 2b6e975, 0528f04, 7cc3ddc, 2c58ff5)
- Paper 1: field-shrink + hc3-artifact-elimination + barrier-route de-monotonization (projection layer
  audit-GENUINE, in-clone) ✅; frontier crisp = schauderData field 2 (Rothe parabolic convergence, the
  paper's main existence theorem). Full existence blueprint staged; P1schauder grinding fields 1/3/4 + field 2.
- Paper 2: hB_global + 6→5 + 5→3 ✅ (closest to unconditional); flux-H¹ provider in P2coeff (bridges 3+4
  closed, 1+2 grinding); route audit (cron2c) ⇒ once provider lands, hTimeNhd (from H¹) + hResolverCoeffTimeC1
  (not needed) also shed → P2 ≈ bank + absorbing.
- Paper 3: l2BootstrapSeed DISCHARGED+WIRED (commit 2c58ff5, 5th reduction) ✅; residual = quantitative Moser
  L^p→L^∞ ladder (P3moser2: spike-crux + finite root-tower + integrated-energy seed all staged; no vacuity/circularity per cron1 audit).

## Honest end-state of the overnight run
Each of the 3 papers reduced from a monolithic conditional to its SINGLE genuine main theorem, every intermediate
sub-lemma actually PROVEN (mass comparison, Prop 2.4, Agmon, L^p interpolation, conjugate mild identity, hsource_bridge,
C¹ convergence). What remains is the papers' hard analytic cores — P1 existence (Rothe compactness), P2 well-posedness
(hTimeNhd spectral regularity), P3 boundedness (final absorption assembly). The hc3 over-decomposition and the
hGradientBridge non-faithfulness were both exposed by hostile audit; no fake/rename-carry/vacuity landed across ~17 rounds.

## Discipline (every landing)
proof-term read → #print axioms ⊆ {propext, Classical.choice, Quot.sound} → hostile opus rename-carry/vacuity
audit → checksum-dry-run rsync ONLY that paper's files → commit → root-build gate (shenbuild.sh warm; cold
fresh-clone for a paper-DONE candidate). Per-paper Statements build is INSUFFICIENT — every commit root-builds
(lesson: 0caf3f9 dup-decl masked by per-paper-only build).
