# UNDERSTANDING.md — Shen_work (2026-06-28 automode session)

## CURRENT STATE (2026-06-28)

1001+ files, ~393K LOC. Papers 1, 3: 0 sorry. Paper 2 χ₀=0: 0 sorry (UNCONDITIONAL).
Paper 2 χ₀<0: **42 sorry** across 8 files (was 43; hresolver_series filled).

### Architecture decision: DIRECT CUTOFF PATH is critical
Direct cutoff (IntervalHeatResolverJointC2, 5 sorry) bypasses
ResolverLevel0SpectralC2Coeff (DuhamelSourceTimeC2Coeff is 16+ fields, no producer)
and HeatSemigroupHighRegularity (FlooredSourceTimeData hyps are on separate path).

### 2026-06-28 progress:
- **hresolver_series FILLED** (310bc27): cosine reconstruction via coupledChemical_lift_eq_series
- **heatSemigroup_pos_of_pos ADDED** (571ab1d): S(t)u₀ > 0 from u₀ > 0 via lower bound
- Codex grinding heatLevel0_srcTimeCoeff_contDiffAt_two (adding hfloor chain)

### 2026-06-27 night session progress:
- **hfloor hypothesis added** to heatSemigroup_flooredSourceTimeData (heat positivity at t > 0)
- **heatDu_eq_secondValue bridge** — LaplacianValue = SecondValue by ring (definitional bridge)
- **d0 FILLED** (extracted as heatSemigroup_d0, pending build verify):
  - d0(a): heat profile joint continuity → rpow → srcSlice ContinuousOn
  - d0(b): HasDerivWithinAt → HasDerivAt via Icc_mem_nhds + hasDerivAt_srcSlice under floor
  - d0(c): rpow^(γ-1) × heatDu joint continuity from profile + secondValue
- **srcTimeCoeff_iteratedDeriv2 FILLED** (build-verified):
  iteratedDeriv_succ + EventuallyEq.deriv_eq on Ioi 0 + cosS1_hasDerivAt.deriv
- ChatGPT Q1224-Q1231: bridge verification, srcTimeCoeff proof, API discovery

### Learned: where-syntax ⟨⟩ elaboration pitfall
The `where` syntax for structure fields prevents `refine ⟨...⟩` from determining
the expected type when `have`-bindings are present. Fix: extract the proof into a
separate private theorem and call it from the `where` block.

### 2026-06-27 session progress:
- **3E-bdd filled** (b661bcd): intervalDomainLift u₀ bounded from Continuous u₀ on compact
- **3E-nonneg filled** (388ca89): added hu₀_nonneg hypothesis, propagated to callers
- **cutoffResolverTerm_contDiff_two decomposed** (7bb2f45): 4-layer structure —
  srcTimeCoeff ContDiffAt → resolverTimeCoeff ContDiffAt → cutoff global C² → (t,x) C²
  Single remaining sorry: heatLevel0_srcTimeCoeff_contDiffAt_two
- Level0: 7 → 5 sorry (3E-bdd and 3E-nonneg eliminated)
- ChatGPT Q1116-Q1122: resolver C² strategy, eigenvalue summability route, hu₀_nonneg design
- IntervalHeatResolverJointC2.lean: build-verified on uisai2 (axioms: propext/sorryAx/choice/sound)

### Per-sorry status (Level0, 5 remaining):
| Sorry | Line | Route | Status |
|-------|------|-------|--------|
| 1A (secondDeriv uniform bound) | 755 | joint C² on closed slab + compactness | BLOCKED on resolver C² |
| 2A-sup (uniform sup bound) | 893 | smooth representative + compactness | BLOCKED on resolver C² |
| eigenvalue summability | 1086 | depth-2 NeumannTower for ν·(S(r)u₀)^γ | ChatGPT route ready (Q1119) |
| resolver nonneg | 1101 | need S(r)u₀ ≥ 0 → source nonneg → resolver nonneg | needs hu₀_nonneg (same as 3E) |
| 3C+3D+3F (chain rule) | 1253 | direct resolver C² + inner commute | BLOCKED on resolver C² |
| 3G (time-deriv continuity) | 1262 | Level0HeatMixedRepr scaffold | separate path |

### MILESTONE: srcTimeCoeff_contDiffAt FILLED (127dcce, build-verified)
The assembly theorem connecting HasDerivAt×2 + ContinuousAt → ContDiffAt ℝ 2.
Key API: contDiffOn_succ_of_fderivWithin + ContDiffOn.smulRight (with StrongDual) +
smulRight_one_eq_toSpanSingleton + toSpanSingleton_deriv bridge.
IntervalPhysicalSourceTimeC2Concrete: 4 → 3 sorry.
Sub-lemmas (srcTimeCoeff_hasDerivAt, cosS1_hasDerivAt, cosS2_continuousAt) all sorry-free.
Also fixed: pass ContinuousOn (not IntervalIntegrable) to cosineCoeffs_hasDerivAt_of_smooth_param.

### What this session did (8 commits):
1. **F1 upstream weakening** (c2dfd86, e766768): ContinuousOn → IntervalIntegrable
   in 6 structures + consumer + 6 downstream callers. Boundary obstruction resolved.
2. **Architectural fix** (9dd3a4b): eliminated by_cases hτ : 0 < τ (τ ≤ 0 branch
   was mathematically impossible — heat semigroup discontinuous at t=0).
   15 sorry → 5 sorry.
3. **New infrastructure** (cfcb6de, 365db15, be5bf6b, 4a6740e):
   - variation-of-constants identity for localRestartCoeff
   - direct resolver inner commute WITHOUT PhysicalResolverJointC2Data
   - ResolverHasSpectralAgreementC2Coeff assembly (4 sorry)
   - Level0 ChemDivMixedTimeDerivClosedRepr skeleton (for 3G)

### Remaining 5 Level0 sorry:
- **1A** (line ~755): uniform ptwise bound of secondDeriv via joint continuity + compactness
- **2A-sup** (line ~893): uniform sup bound for coupledChemDivSourceLift
- **3A**: IntervalIntegrable from interior smoothness + sup bound (provable, no obstruction)
- **3C+3D+3F** (combined): chain rule HasDerivAt — blocked on resolver joint C² + bridge
- **3G**: time-derivative joint continuity on slab — blocked on mixed repr witnesses

### Root cause resolution status:
1. ~~Resolver C² scope mismatch~~: RESOLVED via Option B — direct cutoff resolver C²
   (IntervalHeatResolverJointC2.lean, 5 sorry, build-verified on uisai2).
   Option A (floor-weakening) also landed (4000f01) as backup.
   Option B infrastructure: variation-of-constants (0 sorry), direct inner commute (0 sorry),
   ResolverLevel0SpectralC2Coeff (assembly skeleton), Level0HeatMixedRepr (3G scaffold).
2. ~~F1 boundary obstruction~~: RESOLVED (ContinuousOn → IntervalIntegrable, 12+ files).
3. ~~τ ≤ 0 impossible branch~~: ELIMINATED (9dd3a4b, 15→5 sorry).

### Current state (end of 2026-06-26 night session):
Level0: **8 sorry** (from 15). Full project build-verified on uisai2 (3640 jobs).
34 commits, 25+ ChatGPT rounds, 10 subagents.

### Per-sorry closure map (Q1090 + Q1102):
- **3C+3D+3F** (chain rule HasDerivAt): CLOSES from direct resolver C² + inner commute
- **3E/positivity**: CLOSES with existing coupledChemical_floor_pos wiring
- **3A** (IntervalIntegrable): FILLED (9566859), 2 sub-sorry remain
- **3G** (time-deriv continuity): via Level0HeatMixedRepr scaffold (Q1102 confirmed no IteratePicardJointC2Data needed)
- **1A** (secondDeriv uniform bound): NEEDS WORK — joint continuity of cosine representative on closed slab
- **2A-sup** (source sup bound): NEEDS WORK — closed-slab source representative

### Next session priorities:
1. Fill 5 analytic sorry in IntervalHeatResolverJointC2.lean (per-term ContDiff + majorant)
2. Wire 3C+3D+3F from direct resolver C² (Q1066 has exact proof body)
3. Wire 3G from Level0HeatMixedRepr (fill 12 sorry for 10 smooth representatives)
4. Close 1A + 2A-sup from joint continuity + compactness

### Remaining 3 Level0 sorry (all blocked on resolver joint C²):
- 1A (line 755): joint pointwise bound of secondDeriv via compactness
- 2A-sup (line 804): uniform sup bound for coupledChemDivSourceLift
- 3A-sub (line 989): per-slab source continuity (upstream ContinuousOn weakening needed)

ALL THREE share the same blocker: resolver joint C² is proved INSIDE
FluxJointC2Hyp (sub-sorry 3C was filled via coupledChemical_jointContDiffAt_two +
PhysicalResolverJointC2Data), but NOT available as a standalone theorem for the
envelope construction.

### ROOT CAUSE: ∀ τ : ℝ scope mismatch (STRUCTURAL)
IterateSourceTimeData.floor requires positivity ∀ t : ℝ, but S(0)=0 (Lean
convention). The PhysicalResolverJointC2Data chain through FlooredSourceTimeData
is UNFILLABLE for the raw heat semigroup.

### NEXT SESSION OPTIONS (pick one):
(A) Weaken IterateSourceTimeData.floor to ∀ t, 0 < t → positivity
    (cross-cutting change across ~11 files, each ~1 line)
(B) Bypass the chain entirely: prove heatResolverJointContDiffAt_two
    DIRECTLY using cutoff approach (same as heatSemigroup_jointContDiffAt_two)
    — needs ContDiff of cutoff resolver term, which needs srcTimeCoeff C²
    for t > 0 (via cosineCoeffs_hasDerivAt_of_smooth_param)
(C) Build a positive-window-only IterateSourceTimeDataOn structure

Option (B) is the most self-contained. The existing cutoff heat semigroup
proof is the template — adapt it for the resolver series.

### 0-sorry infrastructure landed this session:
- IntervalSourceDecayQuantitative: quartic decay + eigenvalue L¹ summability
- IntervalResolverHighRegularity: global resolver positivity (period/even/reflect)
- Level0: slab inclusion (ContinuousWithinAt.mono_of_mem_nhdsWithin)
- Level0: resolver positivity (nonneg source → global nonneg → 1+V > 0)
- Level0: source eigenvalue summability (7-step chain: H2 certs + quartic decay)
- HeatRegularity: cutoff heat series global C² (contDiff_tsum via smoothRightCutoff)
- HeatRegularity: Leibniz main theorem (norm_iteratedFDeriv_mul_le applied + wired)

### Single key blocker: cutoffHeatTerm_iteratedFDeriv_bound (1 sorry)
In IntervalHeatSemigroupHighRegularity.lean. The cutoff approach is LANDED:
smoothRightCutoff kills t < 0, contDiff_tsum gives global C² of cutoff series,
eventual equality gives ContDiffAt at positive times. Only the Leibniz product
rule bound for ‖iteratedFDeriv k (φ·exp·â·cos)‖ remains.
Pattern: cutoffValueTerm_leibniz_bound (IntervalResolverSpectralJointC2CutoffBounds.lean:52)
uses norm_iteratedFDeriv_mul_le (Mathlib Leibniz rule).
Once proved → heatSemigroup_jointContDiffAt_two fully sorry-free →
unlocks sub-sorry 3B → 3C/3D → 2A-core → 1A.

### Sub-sorry with existing producers (found by cron analysis):
- 3F: coupledChemDivFlux_timeBridge_of_physicalJointC2 EXISTS (IntervalChemDivFACCommuteDischarge)
- 3G: chemDivMixedTimeDeriv_jointContinuousOn_closed EXISTS (IntervalChemDivTimeDerivClosed)
  Both need upstream PhysicalResolverJointC2Data → needs PhysicalSourceTimeC2 → needs heat wiring.

### Sub-sorry independent of joint C²:
- 2A-agree: definitional unfolding (coupledChemDivSourceLift_eq_deriv_fluxLift_interior exists)
- 3E: resolver positivity floor (τ > 0: nonneg source → nonneg resolver; τ ≤ 0: degenerate/sorry)

### Paper 2 χ₀<0 sorry breakdown

**IntervalConjugateLevel0BFormSourceOn.lean (4 sorry):**
1. Line 278: Source eigenvalue summability — `Summable (λ_k |sourceCoeff_k|)`.
   Route: depth-2 IBP via `intervalWeakH4Neumann_eigenvalue_L1_summable` (sorry'd
   in IntervalSourceDecayQuantitative.lean, reduces to cosineCoeffs-Laplacian identity).
2. Line 468: L1 uniform bound — joint continuity of deriv²(chemDiv) on [c,T]×[0,1] + compactness.
3. Line 514: Sup bound + per-slice continuity — same joint continuity difficulty.
4. Line 615: CoupledChemDivFluxJointC2Hyp — 5 fields of regularity for heat semigroup trajectory.

**IntervalConjugateBFormSourceTower.lean (5 sorry):** All downstream of Level0.

### Infrastructure built this session (sorry-free, axiom-clean)
- `IntervalResolverHighRegularity.lean`: global resolver nonneg from [0,1] via
  period-2 + even + reflect-one (intervalResolverLiftR_nonneg_of_nonneg_on_Icc),
  plus `0 < 1 + V(x)` wrapper.
- `IntervalConjugateLevel0BFormSourceOn.lean`: slab inclusion fix via
  ContinuousWithinAt.mono_of_mem_nhdsWithin; resolver positivity via nonneg source
  → nonneg resolver on [0,1] → global nonneg by symmetry.
- `IntervalSourceDecayQuantitative.lean`: depth-2 quartic decay + eigenvalue L¹
  summability — FULLY PROVED (0 sorry, axiom-clean, build verified on uisai2).
  `intervalWeakH4Neumann_cosineCoeff_quartic_decay_of_bound`: |c_k| ≤ 2B/(kπ)⁴
  `intervalWeakH4Neumann_eigenvalue_L1_summable`: Summable (λ_k |c_k|)
  Both proved via depth-2 IBP identity cosineCoeffs(f'') = -(kπ)² cosineCoeffs(f).

### FluxJointC2Hyp route (from ChatGPT analysis Q684/Q688)
The shortest path to CoupledChemDivFluxJointC2Hyp for the heat semigroup is:
  Physical source-time-C² data + summability
  → IntervalPhysicalResolverDataConcrete → CoupledChemDivFluxFactorJointC2Inputs
  → coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs → FluxJointC2Hyp
Hardest field: (b) joint C² of uncurried flux (resolver joint C² burden).
Second: (e) time-derivative ContinuousOn (spectral representative on closed slab).

### NeumannTower for source eigenvalue summability (line 278)
Existing tool: IntervalIBPCoeffExtraction.lean has NeumannTower + cosineCoeffs_decay.
Need: build NeumannTower at depth j=2 for ν·u^γ where u = heat semigroup.
Requires: C⁴ of ν·u^γ (chain rule) + depth-2 Neumann BCs (u' and u''' vanish at endpoints).

### Paper 1 (traveling waves): SORRY-FREE, unconditional infrastructure landed.
### Paper 2 χ₀=0: `intervalDomain_theorem_1_1_chiZero_unconditional` — UNCONDITIONAL, axiom-clean.
### Paper 3 (long-time dynamics): SORRY-FREE, linear dichotomy unconditional.

### χ₀ < 0 PRODUCTION FRONTIER
`BFormBankedInputs` fields — all satisfiable, all but 2 have sorry-free producers:
- `huPaper`, `Hinf`, `hsmall`, `MInit`, `haInit`: from existence data + ball estimates
- `hB_global`: from `conjugatePicardLimit_cosineSeries` (sorry-free)
- `hlogCont`, `hlogFourier`: Fields 9/10 from `IntervalBankSourceSliceLeaves` (sorry-free)
- `hchemIoo`: from `IntervalBankChemSliceFix` (sorry-free, replaces false `hchemCont`)
- **`hlogSrc`**: NEEDS PRODUCTION — `DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs ...)`
- **`hchemSrc`**: NEEDS PRODUCTION — `DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs ...)`

Production route for `hlogSrc`/`hchemSrc`:
1. `sourceTimeC1On_succ_of_sourceTimeC1On` (IntervalPicardSourceTimeC1OnRecursion) — GENERIC
2. `duhamelSourceTimeC1On_of_uniform_limit` (IntervalMildPicardLimitRegularityOn) — limit passage
3. Need: K1/K2 properties (representation, G1/G2 bounds, positivity) for `conjugatePicardIter`

---

## HISTORICAL (2026-06-10/11 — kept for reference, superseded by above)

## ⛔ FIDELITY CORRECTION (2026-06-11 ~04:00 — READ FIRST, supersedes all "done"/"unconditional"/"sorry-free" language below)
An independent adversarial audit (HANDOFF/FIDELITY-AUDIT.md) found this campaign
OVERSTATED its results. The honest status:
- What is in Lean is a **FRAGMENT** of the paper's Theorem 1.1: only χ₀=0 (the
  degenerate decoupled slice — NOT a chemotaxis system), N=1 (intervalDomain),
  a,b>0, 1≤α, 1≤γ. Untouched: χ₀<0 (the real case), a=b=0, N≥2, Thms 1.2/1.3.
- It is **CONDITIONAL** on `hsrc0` (TowerConeAnalyticResidual), which is the
  paper's hard analytic content relocated into a hypothesis AND plausibly
  unsatisfiable as typed (the s=0 ℓ¹-envelope t→0 disease). So there is NO
  unconditional result yet, even for the χ₀=0 fragment.
- The "#print axioms = clean" claims below were run on a DIVERGENT remote olean
  tree (/dev/shm/shen_work @ 6d2f95a, dirty), never on a clean f93cbda checkout.
  Clean-tree certification is in progress.
- Genuine positive: the STATEMENT layer is FAITHFUL (non-hollow) — the PDE, both
  equations, Neumann BC, real C² regularity, exact (1.21) bound.
The strong-language sections below describe real engineering progress on the
fragment, but their "done"/"prize"/"unconditional" framing is corrected here.

## ⭐⭐⭐ K1 ENDGAME STATE (2026-06-11 00:4x — engineering log, see FIDELITY CORRECTION above)
The hsrc0 endgame (waves W1a/W1b/W2/W3/W4, commits 085a3ad…7b424e2) built the
COMPLETE satisfiable replacement stack for the per-level source K1 package:
iterate initial approach (hand-written, χ₀=0), patched-coefficient continuity
+ per-level DuhamelSourceBddOn (no t→0 disease), the σ/2-shifted clamped
DuhamelSourceTimeC1 from winAdot data, consumer variants (hbsum/G2/hagree
_of_window/_of_sourceBdd), and assembled tower replacement legs — all
axiom-clean, all σ < T.

W4 verdict (rigorous): **σ = T is genuinely consumed** by three FROZEN
limit-side capstone feeders (IterateWindowC2Data closed-T quantifiers,
henv_iter at s ≤ D.T, hiter_cont at [D.T/2, D.T]), and every hsrc0-free route
is structurally σ < T strict (clamp pad headroom; WindowAdotLegs hi < T).
**TowerConeAnalyticResidual = { hsrc0 } is the honest irreducible minimum**
under the current frozen capstone surface.  Emptying it needs ONE of:
(i) a T-endpoint one-sided DuhamelSourceTimeC1 construction (the soft clamp
structurally cannot reach the endpoint), or (ii) a BddOn→λ-weighted upgrade
lemma, or (iii) unfreezing the capstone feeders to σ < T quantifiers.
Recorded in HANDOFF/k1-wall-plan.md W4 STATUS.

Also this campaign: the hL_cont VACUITY BUG (false zero-extension global
continuity field — residual was unsatisfiable as published) found and fixed
(c09aaca); hG2base + hG1all fake walls demolished by hand (7083684, 8f7987f).

## ⭐⭐ RESIDUAL SHRINK UPDATE (2026-06-10 19:30 — newest)
After the sorry-free capstone (32c8fee), two more residual legs fell — both
previously reported as BLOCKED by agents, both blockers shown ILLUSORY,
both proofs hand-written:
* **hG2base** (7083684, IntervalHomogeneousG2Base.lean): the gate at t := σ
  already forces homWeightBound = 32M/(eπ²σ²) ≤ A₂/σ², and the homogeneous
  slice's true spectral bound M·eigExpWeight σ ≤ 4M/(eπ²σ²) is 8× smaller —
  the gate's A₂ ≥ 64M/(eπ²) head-room was designed for this. No calibration
  hypothesis needed.
* **hG1all** (8f7987f, IntervalPicardG1All.lean): the split machinery's
  ∀ s : ℝ source sup is over-quantified — the Duhamel integrand reads
  s ∈ Ioc 0 t only. The windowed family wSrc satisfies the global sup by
  construction and the same value EqOn by integral congruence; the existing
  interior split + g1_kernel_bound apply verbatim. Bonus infrastructure:
  picardIter_hasJointMeasurability_all, u₀_lift_abs_le. HCone gained the
  cone-returned hlim_ball conjunct (precedent: hub's hball).
**TowerConeAnalyticResidual is now 7 fields: hsrc0, hL_cont, adot,
hadot_deriv, hadot_cont, adotBound, hadot_bound — ALL rooted in per-iterate
source K1 regularity (the project's one genuine remaining analytic wall;
see UNPROVED_TARGETS.md for the documented producer circularity).**
Axioms unchanged: both capstone theorems = [propext, Classical.choice,
Quot.sound].

## ⭐ FINAL STATE (2026-06-10 18:15 — supersedes everything below)
**THE CAPSTONE IS SORRY-FREE.** Commit 32c8fee:
`#print axioms` on BOTH `paper2_theorem_1_1_chiZero_unconditional` and
`paper2_theorem_1_1_chiZero_from_coneSupply` = `[propext, Classical.choice,
Quot.sound]` — NO sorryAx (independently re-verified on uisai2; full build
8547 jobs EXIT 0; md5 local=remote). The `hinterior` circularity (hcontP →
hsliceTC → restart-rep → BddOn → hcontP) was broken on the iterate side:
s-uniform geometric convergence (PicardConvFacts.hgeom) transfers per-iterate
coefficient time-continuity to the limit (IntervalPicardLimitCoeffTimeCont);
hinterior itself proved via the spectral restart series subtraction with the
λ-cancelling Duhamel bound + heat-damped homogeneous sum
(IntervalRestartSeriesLipschitz / IntervalRestartSliceLipschitz). The capstone
gained ONE hypothesis (`IterCoeffTimeContProvider`), discharged inside
`from_coneSupply` from the tower (`hiter_cont_of_tower`) — the acceptance
surface `from_coneSupply` is UNCHANGED. Tower residual
(`TowerConeAnalyticResidual`, the from_coneSupply hypothesis surface) is now
9 fields: hsrc0, hL_cont, hG1all, hG2base, adot(+4 legs). Honest blockers
recorded: hG1all needs a global all-s iterate source sup (truncated-source
rebuild = new analytic content); hG2base needs a homogeneous heat ∂²ₓ estimate
calibrated to the gate budget A₂. Design verdicts in
HANDOFF/chatgpt-hinterior-break-verdict.md.

## START HERE
Read `HANDOFF/CODEX-HANDOFF.md` — the complete execution handoff for the
Tower campaign (environment rules, current state, stage 1/2 plans, verdict
index). Build is REMOTE ONLY (uisai2:/dev/shm/shen_work; local builds are
blocked and would kernel-panic the mini). Acceptance = #print axioms.

## THE CURRENT STATE (one paragraph)
Paper 2 Theorem 1.1 (χ₀ = 0) capstone
`paper2_theorem_1_1_chiZero_unconditional`:
regime constants (χ₀=0, a>0, b>0, α≥1, γ≥1) + HWdata ⟹ Theorem_1_1,
axioms [propext, sorryAx, Classical.choice, Quot.sound]; the single sorryAx
is `hinterior` (IntervalPicardLimitSliceTimeContinuity). HWdata (per-datum
window iterate-C² provider) and hinterior share ONE root: the per-iterate
source-package production tower. The tower is fully designed and externally
audited (HANDOFF/chatgpt-tower-verdict.md); stage 1 (lemma layer, 4 files)
may already be landed by an in-flight agent — CHECK git log/status first.
Tower lands ⟹ both close ⟹ capstone carries regime constants only.

## What the 2026-06-09/10 campaign did (~40h, ~70 commits, all pushed)
Started at 21 sorries, 14 UNSATISFIABLE AS TYPED (global time quantifiers
vs (0,T]-only data; uniform gradient bounds false at t→0 by parabolic
smoothing; no ℓ¹ envelope at s=0 for continuous data; the s=T jump; two
genuine circularities). Dissolved via: C¹ soft clamp + existential clamped
witnesses; weak-chain horizon retype (DuhamelSourceL1ContOn) then the final
DuhamelSourceBddOn patched-family interface; ledger V2 (per-compact K2,
(0,T) K1, shifted fields deleted); K1 proved WITHOUT new analysis (weak
restart identity + per-mode FTC + fixed-split series differentiation);
iterate-side bootstrap breaking the hsrc0 circularity; hybrid weighted C²
(kernel G1 + t²-weighted spectral G2, gate SOLVED explicitly in
IntervalPicardGateSolve); cone _with_gate_data (returns exact hDu,
discharged GateCondition, hcont_iterates, PicardConvFacts, strict iterate
positivity); Hvsrc per-t₀ retype + clamped ν·u^γ witness; hpde_u via the
continuous-surrogate retype; Hvpos proved; capstone narrowed to
HWdata-only via fact-carrying bridges (the hPLF ∀-D route superseded).
Six external design audits (HANDOFF/chatgpt-*-verdict.md); three caught
real errors (the G1 spectral recursion non-closure, a circular k1_quadruple,
the hDu EqOn trap).

## Historical notes below (pre-campaign architecture, mostly still accurate
## for layers 1-2; the Paper2 layer-3 description is superseded by the above)

## Build invariant

```bash
lake build  # 8409 jobs, 0 sorry, 0 admit, 0 custom axiom
```

## Architecture: three layers

### Layer 1: PDE infrastructure (COMPLETE, 0 sorry)
All spectral, semigroup, kernel, Duhamel, resolver, energy, IBP, and
measurability infrastructure is proved. Key files:
- IntervalNeumannFullKernel, IntervalFullKernel*, IntervalDuhamel*
- IntervalResolverPositivity (O1: heat-Laplace nonneg, unconditional)
- IntervalChemFluxLipschitz (glue1+glue2: contraction estimates)
- IntervalGradDuhamelBound (Atom D: gradient sqrt-T estimates)
- IntervalLogisticLipschitz (Atom C: logistic Lipschitz, one-sided α>0)
- IntervalSourceCoefficientTimeC1 (G3: DuhamelSourceTimeC1 algebra)
- IntervalResolverSpatialC2 (G4q: resolver C² + Neumann + weight summability)

### Layer 2: Mild solution + regularity bootstrap (COMPLETE, 0 sorry)
- IntervalMildPicard: Picard iteration → GradientMildSolutionData (mild FP)
- IntervalMildSourceDecay: SourceCoeffQuadraticDecay (unconditional)
- IntervalMildToClassical: all 9 regularity conjuncts (unconditional)
- IntervalMildRegularityBootstrap: half-step restart C² + Neumann
- IntervalSemigroupNeumann: semigroup conjuncts 3/6/7/8/9 + composition
- IntervalMildPicardRegularity: Picard iterate induction (base + step)
- IntervalMildPicardLimitRegularity (G2.5): DuhamelSourceTimeC1 limit passage
- IntervalMildTimeRegularity (G4j): time DifferentiableAt from spectral
- IntervalMildTimeDerivContinuity (G4 fields): HasDerivAt + joint continuity
- IntervalMildFrontierFromSpectral (G4r): closed-slab joint continuity
- IntervalMildRegularityFrontierAssembly: u-side frontier field wiring
- IntervalResolverTimeRegularity: v-side frontier field wiring
- IntervalResolverDirectTimeRegularity (F2): resolver direct time regularity
- IntervalMildSourceDecayHelper: Sobolev chain rule / weak H² Neumann
- IntervalWeakCosineIBP: cosine coefficient decay infrastructure
- IntervalMildToLocalExistence: bridge to localExistence

### Layer 3: Paper-level theorem assembly (NEAR COMPLETE)
- IntervalDomainTheorem11Umbrella: γ≥1 umbrella (hposWit eliminated, G6)
- IntervalDomainThm11Assembly: final wiring, 15/15 frontier fields proved
- IntervalDomainStatementAssembly: Paper2 Thm 1.1/1.2/1.3 targets
- Paper1/Statements, Paper2/Statements, Paper3/Statements

## G0–G7 + G2.5 status (all committed, 0 sorry)

| Gap | Description | Status | Commits |
|-----|-------------|--------|---------|
| G0 | Continuous u₀ in initialAdmissible | ✓ DONE | 5343c18 |
| G1a | One-sided logistic Lipschitz α>0 | ✓ DONE | 5f94ba0 |
| G2a+G2b | Spatial IBP for Duhamel source | ✓ DONE | 5bf3fb5 |
| G2.5 | DuhamelSourceTimeC1 limit passage | ✓ DONE | e5da4dc |
| G3 | Total-source DuhamelSourceTimeC1 | ✓ DONE | b2b4b66+ |
| G4a–G4i | Spectral time derivatives (ODE→series) | ✓ DONE | 355f14d–356dd4e |
| G4j | Time DifferentiableAt of mild solution | ✓ DONE | e138bfa |
| G4k–G4m | Joint continuity (Duhamel+hom+restart) | ✓ DONE | cfa96ab–665367d |
| G4n–G4p | Spectral PDE identity + Laplacian | ✓ DONE | a1ce482–c7db735 |
| G4q | Resolver spatial C² + weight summability | ✓ DONE | 7c0dd7b |
| G4r | Closed-slab joint continuity | ✓ DONE | 8e8b1ae |
| G5 | Uniform S(t)u₀→u₀ for continuous u₀ | ✓ DONE | 809f1ac |
| G6 | PID-gate L² chain + eliminate hposWit | ✓ DONE | 25da5b3+2d8cdcf |
| G7 | ReachableArbitrarilyLong from hlocal+hUniform | ✓ DONE | 625fa56 |
| F2 | Resolver direct time regularity | ✓ DONE | a32f923 |

## Remaining frontier for unconditional Paper 2 Theorem 1.1

### Proved chain (axiom-clean)
```
Picard FP → iterate C² induction → DuhamelSourceTimeC1 limit (G2.5)
→ regularity bootstrap → localExistence
→ γ≥1 umbrella (no hposWit, G6) → L² uniqueness (PID-gated)
→ δ-iteration (G7) → Theorem_1_1
```

### Assembly theorem
```lean
paper2_theorem_1_1_of_frontier:
  hUniform + hMildLocal → Theorem_1_1 intervalDomain p
```

### Regularity frontier data: 15/15 fields proved
- 12 unconditional (u-side time + spatial, v-side spatial, sup-norm)
- 3 from ResolverHasSpectralAgreement (v-side time, constructible from F2)

### Two genuine remaining hypotheses

**F1: IntervalDomainUniformLocalExistence** (textbook continuation δ(M))
- For every M>0, ∃ δ>0 such that any classical solution with |u₀|≤M extends by δ
- Standard PDE (Henry/Amann); requires restart-before-end + overlap glue
- Estimated ~200 lines

**F2 (partially resolved): DuhamelSourceTimeC1 for the Picard limit**
- G2.5 reduces to uniform convergence of iterate source coefficient derivatives
- F2 direct resolver regularity proved (IntervalResolverDirectTimeRegularity)
- Remaining: instantiate the uniform convergence hypothesis from Picard data
- Estimated ~150 lines

## Other paper theorems

### Gap 2: Paper1 Theorem 1.1 (traveling wave existence)
Requires Schauder fixed point on the whole line (not interval domain).
Mathematically hardest gap.

### Gap 3: Paper1 Thm 1.2/1.3 (stability/uniqueness)
Depends on Gap 2.

### Gap 4: Paper2/Paper3 semigroup estimates (Lemma 2.1-2.4)
Mechanical but large. Zero-data branches proved.

## Priority order
1. F1 + F2 instantiation → Paper2 Thm 1.1 unconditional (~350 lines)
2. Gap 4 (semigroup estimates): mechanical
3. Gap 2 (whole-line Schauder): mathematically hardest
4. Gap 3 (weighted stability): depends on Gap 2

## Build
On uisai1: `PATH=$HOME/.elan/bin:$PATH lake build`

## 2026-06-06 night update — hQuant driven to a single shared residual

The "Two genuine remaining hypotheses" section above is STALE. Current map:

### hQuant (uniform δ(M) local existence) — Session B campaign, all green/axiom-clean
- **χ₀ = 0 (cone route, COMPLETE modulo one hypothesis):**
  `ConeQuantBridge.quantitativeLocalExistence_chiZero` — Picard contraction
  AND positivity proved (exponential cone invariance, uniform δ(p,M),
  no inf-threshold). Residual: `PicardLimitRestartFrontier` only.
  End-to-end: `paper2_theorem_1_1_chiZero_of_frontier` (+ hlocal).
- **General χ₀ ≤ 0 (threshold route, conditional):**
  `QuantFromThreshold` + `ThresholdQuantBridge`: hQuant ⟸ proved-δ(M,c)
  threshold Picard + `ClassicalMinPersistence` (min principle, open) +
  `PicardLimitRestartFrontier` + hlocal.
- **Key new infrastructure** (axiom-clean): Chapman–Kolmogorov
  `IntervalSemigroupComposition` (S(s)S(t)=S(s+t) via S1 spectral identity),
  cone atoms (mono/Duhamel-eval/kernel strict positivity), generic
  `gradientMildSolutionData_initialApproach` (hInitialApproach is no longer
  part of any per-datum frontier for continuous data).

### Unified residual
`PicardLimitRestartFrontier p` (ConeQuantBridge): restart source data +
frontier core for every packaged D with `D.u = picardLimit p u₀ D.T`.
One S-construction discharge (Session A's M-line, in flight) closes
hQuant(χ₀=0), the threshold route's Picard half, and hlocal(χ₀=0).

## 2026-06-09 — Thm 1.1 chain compilation green

### Chain status (ContinuousExtension → … → Provider)
Full 7-file chain compiles end-to-end on uisai2 (lake build green):
```
IntervalDomainContinuousExtension (0 sorry)
→ IntervalPicardLimitRestartWeak (0 sorry, eigenvalue summability proved)
→ IntervalDomainConstExtendAdapter (1 sorry: adapter body)
→ IntervalDomainMildLocalChi0 (1 sorry: restartData_of_inputs)
→ IntervalDomainThm11ChiZeroFinal (0 sorry)
→ IntervalDomainLedgerSweep (2 sorry: time-quantified → global adapters)
→ IntervalDomainThm11ChiZeroCoreProvider (17 sorry: analytic estimates)
```

### Key fix: namespace opens for `intervalLogisticSource` / `cosineMode`
Six files needed `open ShenWork.IntervalDomainExistence (intervalLogisticSource)`
and `open ShenWork.CosineSpectrum (cosineMode)`. Without these, all definitions
using these names silently became autoImplicit variables, cascading "Function
expected" errors.

### RestartWeak eigenvalue summability (NEW, 0 sorry)
`summable_eigenvalue_mul_abs_limitCoeff_weak`: proved via FTC envelope
computation + triangle split + `Summable.of_nonneg_of_le`. The proof handles:
`abs_add` → `abs_add_le` rename, `gcongr` → explicit `add_le_add` /
`mul_le_mul_of_nonneg_left`, `continuous_const` domain inference in tactic mode,
`-(t-s)*λ_k` parse order, `neg_zero` in simp set.

### Provider sorry inventory (17 items)
- G1, G2 — gradient/Hessian bound VALUES
- hG1t, hG2t — gradient/Hessian bound PROOFS
- adott family (5) + adotS family (5) — K1 time-C¹ data
- hpde_u, Hvsrc, Hvpos — PDE/resolver residuals
- hsrc0 (×2 in final wiring) — DuhamelSourceL1Cont

### LedgerSweep interface gap — RESOLVED 2026-06-09 night (horizon localization)
See HANDOFF/horizon-localization-design.md + HANDOFF/horizon-retype-status.md.
Landed (all green, 8521 jobs): C¹ soft clamp (IntervalTimeSoftClamp) +
clamped-witness TimeC1 producer (IntervalDomainClampedSourceRepresentation) +
weak-chain horizon retype (DuhamelSourceL1ContOn) + Hu_of_restart_localized
(0 sorry) + ledger V2 (per-compact hG1t/hG2t/hMdott, (0,T) K1, 5 shifted-K1
fields deleted, hsrc0 field) + K2 gradient producers wired + Hvpos proved
(mildChemicalConcentration_pos) + hpde_u producer (IntervalDomainPdeUProducer).

Sorry inventory end of 2026-06-09 (8, all satisfiable types; see
HANDOFF/horizon-retype-status.md header for the live ledger):
- Provider: hsrc0F (BddOn patched-family migration pass; producer is DONE
  0-sorry in IntervalPicardLimitBddProducer), K1 quadruple ×4 (R2 weak spine
  — NOT uniform-convergence/F2 after all; ChatGPT-verified route: weak
  restart identity → c_k' = −λ_k c_k + A_k by FTC → term-wise diff; first
  attempt was circular, fix in flight), Hvsrc
- PdeUWiring: 1 K1 bundle (same data as the quadruple)
- restartData_of_inputs + hasRestartData_of_subtypeCont (restart packaging)
Discharged today beyond the 10-list: Hu_of_reduced (subtype variant),
hpde_u (surrogate retype killed the false lift-continuity field).

### Option A SETBACK (Q1076): floor-weakening alone insufficient
FlooredSourceTimeData's 6 sorry are NOT trivially fillable after weakening:
- d0-d1: need positivity floor (0 < u(t,x)) for rpow chain rule
- zerothBound/laplBound: need UNIFORM bounds ∀ t > 0, but source derivatives
  blow up as t → 0 for merely continuous initial data
NEXT: further weaken zerothBound/laplBound to per-compact-window (∀ t ∈ [c,T]),
or restructure the consumer chain to accept window-local data directly.
