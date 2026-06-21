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
- 🟡 **hc3 (C³ bootstrap)** — the LAST P1 frontier. Codex grinding (/var/tmp/shen_cx_p1) the V-bootstrap route:
  V''=V−U^γ ⟹ U∈C² ⟹ V∈C⁴ ⟹ V''∈C² ⟹ R∈C¹ ⟹ U∈C³ (U>0 from trap; NO extra Schauder hyp needed).
  cron3 cross-checking the derivation. → if hc3 closes, **P1 is FULLY UNCONDITIONAL**.

## Paper 2 — bounded-domain boundedness (paper2_theorem_1_1_general_chi_via_bform)
Headline conditional on Nonempty(BFormSpectralFrontier p DB) per datum.

- ✅ hB_global (global cosine representation) discharged via flux-deriv reconstruction; BFormBankedInputs −1 field
  (commit 2b6e975, opus GENUINE-NET-REDUCTION, Paper2 root-clean)
- 🟡 **BFormSpectralFrontier construction** — 6 fields {bank, hGradientBridge, hTimeNhd, hResolverData,
  hSupNormDeriv, hVpos}. hTimeNhd + hResolverData have producers (need wiring to conjugatePicardLimit); hVpos
  (positivity), hGradientBridge (mild solution), bank (source regularity), hSupNormDeriv (max-principle) need
  proof/wiring. Codex scoping+constructing (/var/tmp/shen_cx_pde). → reduces P2 toward unconditional.

## Paper 3 — persistence / critical-sensitivity boundedness (L² bootstrap → L∞)
Headline conditional on IntervalDomainMassLpSmoothingRouteData (3 atoms).

- ✅ l2EnergyInequality discharged (half-energy diff. inequality as theorem, not field)
- ✅ sharp absorption threshold IntervalDomainSharpL2AbsorptionThreshold (γ<1 ∨ 2γ<α) + equivalence
  (2+2γ<max(4,2+α)) + satisfiability witness (axiom-clean; SHARP by spike test)
- ✅ absorbing-inequality algebraic producer (uniform half-energy + spatial absorption ⇒ absorbing inequality)
- 🟡 **l2BootstrapSeed** — codex grinding (/var/tmp/shen_cx_p3) the close: antecedent IntervalDomainBoundednessHyp
  =(γ<1∨2γ<α)∧0<b + witness, spatial absorption (Young CaseA / 1D-GN CaseB), two scalar Grönwall lemmas
  (integrated-energy first-crossing, dodges AC+uniform-Ceps), Neumann-Poincaré → uniform L².
  P3 counterexample recorded: small-data-around-0 global bootstrap is FALSE (a>0 ⟹ 0 unstable).
- ⬜ **driftBoundFromMass** — the Moser L^p ladder. Honest stall: L1 mass can't control u^γ for γ>1; needs an
  L^p before-bound. The new uniform-L² (from l2BootstrapSeed) seeds the iteration L²→L^p→L^∞. Next after l2BootstrapSeed.

---

## Scoreboard
- Paper 1: 2/3 layers ✅, hc3 grinding → 1 frontier from unconditional.
- Paper 2: 1 reduction ✅, BFormSpectralFrontier (6 fields) grinding.
- Paper 3: 3 bricks ✅, l2BootstrapSeed grinding + driftBoundFromMass open.

## Discipline (every landing)
proof-term read → #print axioms ⊆ {propext, Classical.choice, Quot.sound} → hostile opus rename-carry/vacuity
audit → checksum-dry-run rsync ONLY that paper's files → commit → root-build gate (shenbuild.sh warm; cold
fresh-clone for a paper-DONE candidate). Per-paper Statements build is INSUFFICIENT — every commit root-builds
(lesson: 0caf3f9 dup-decl masked by per-paper-only build).
