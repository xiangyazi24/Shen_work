# Shen formalization — HEADLINE THEOREMS 清单 (逐个击破)

Status as of 2026-06-15. The repo spans MULTIPLE papers. Two models:
`CM2Params` (chemotaxis-growth on a bounded interval), `CMParams` (traveling waves).

Legend: ✅ done (modulo standard carried inputs, like every local-existence theorem) ·
🔧 active · ⬜ TODO/stub · ⚠️ conditional (carries an assumed branch).

---

## A. Chemotaxis-growth (CM2Params) — Paper2 `Theorem_1_1 (D) (p)` (Statements.lean:4359)
The headline: for `χ₀ ≤ 0`, a POSITIVE classical solution + InitialTrace + supNorm bound
`≤ max(‖u₀‖, (a/b)^{1/α})` + (`m≥1` → GLOBAL). `Theorem_1_1` is NOT just local existence.

### A1. χ₀ = 0  — ✅ `paper2_theorem_1_1_chiZero_final` (IntervalDomainThm11ChiZeroFinal:204)
Produces `Theorem_1_1 intervalDomain p` for χ₀=0, carrying `hPLF` (PicardLimitRestartFrontier)
+ `Hcore` (LimitRegularityInputsCore). Done.

### A2. χ₀ < 0  — the active thread (EWA route). `IsPaper2ClassicalSolution` = regularity + 0<u + 0≤v + PDE.
- ✅ spatial C² + Neumann classical slice (`sourceClassical_spatial_existence_clean`, 1d64c9b)
- ✅ time C¹ classical slice / u_t (`isClassicalTimeSlice`, 7606541)
- 🔧 pointwise PDE (`fullSourceCoeff_pde_u`, 4f) — bricks 4a-4e committed (bb97141/f9a74de/4d4e),
      4f assembling. = the PDE field of IsPaper2ClassicalSolution.
- ✅ POSITIVITY `0 < u` (`realSlice_pos`, 6f35363) via uniformFloor_on_ball
- ✅ `0 ≤ v` (resolver nonneg, O1)
- ✅ pointwise PDE (`fullSourceCoeff_pde_u`, dbb7197) — 4a-4f
- ✅ joint (t,x)-regularity (`jointSolutionClosed`/`jointTimeDerivClosed`, 5326a04)
- ✅ classicalRegularity all 7 fields (`realSlice_classicalRegularity`, 701005e)
- ✅ InitialTrace (`realSlice_initialTrace`)
- ✅ **PER-DATUM LOCAL CLASSICAL SOLUTION** (`realSlice_localClassicalSolution`, 5250b21):
      `∃ Tmax>0, ∃ u v, IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧ InitialTrace`,
      via reduced core (generic in u) → RegularityBootstrap → localExistence. All regularity/PDE/
      positivity supplied; the v-side resolver machinery is χ₀-agnostic (reused).

  ⬜ **FULL `Theorem_1_1` (the headline) — the genuine remaining frontier**: wired via
     `theorem_1_1_chiNeg_of_…Residual` (ChiNegResidual:199; boundedness Lemma 3.1 + global are
     χ₀-agnostic, REUSABLE) modulo the DATUM-UNIFORM residual
     `CoupledFluxClassicalLocalExistenceResidual` = `∀M>0 ∃δ>0 ∀u0(|u0|≤M), local-solution-on-δ`.
     Two genuine pieces remain (NOT plug-ins):
     (1) datum-uniform lifespan δ(M) — the EWA `hK` smallness is uniform over `|u0|≤M` (constants
         bounded), but not yet extracted into the `∀M ∃δ ∀u0` order; + exact-horizon vs ∃Tmax.
     (2) per-datum discharge of the carried χ₀<0 frontier atoms (`realizes_clean` ← the realized-
         track frontier ResolverSourceSummable/surrogate/hrep; `hfp` EWA↔real-space FP identity;
         `htrace`) for each `u_star(u0)` — the realized-track frontier, ∀-datum.

  HONEST: the per-datum local classical solution is DONE modulo the standard χ₀<0 frontier atoms.
  The full `Theorem_1_1` carries that frontier ∀-datum + the uniform construction — a real
  analytic frontier (bottoms at ResolverSourceSummable etc.), not a quick assembly.

---

## B. Traveling waves (CMParams) — Paper1
### B1. ⚠️ `Theorem_1_1` (Paper1/Statements.lean:16285) — monotone traveling-wave existence + Shen
    upper bounds + right-tail asymptotics. Has `of_assumed_frozenStationaryProfile_branches` /
    `of_assumed_uniqueness_branch` — CONDITIONAL on assumed branches. ⬜ unconditionalize.
### B2. ⚠️ `Theorem_1_3` (profile uniqueness, Lemma25Helpers:2053) — `of_assumed_uniqueness_branch`.
    ⬜ the unconditional uniqueness branch (Lemma25Helpers:2286 lists what's needed).
### B3. ⬜ Global existence / boundedness / stabilization (Section 3) — `GlobalExistence.lean` STUB
    ("not currently formalized"; fake constant-solution wrappers were removed).
### B4. ⬜ Stability / uniqueness of traveling waves (Section 5) — `StabilityUniqueness.lean` STUB
    (only logistic-profile facts recorded).

---

## Grind order (recommended)
1. 🔧 Finish A2 χ₀<0: 4f PDE → positivity 0<u → assemble `IsPaper2ClassicalSolution` →
   InitialTrace → boundedness → global → `Theorem_1_1` (χ₀<0). [active]
2. ⬜ B1/B2 unconditionalize the traveling-wave existence + uniqueness (Paper1 branches).
3. ⬜ B3/B4 the Section-3 / Section-5 paper-level theorems (the hardest; paper-level analysis).

Codex out of credits till Jun 18 → Opus carries labor.
