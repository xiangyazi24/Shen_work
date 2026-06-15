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
- ⬜ POSITIVITY `0 < u t x` of the SOLUTION (distinct from the 1+v floor we discharged — VERIFY:
      the fixed point u* close-to-heat in the ball; heat ≥ δ floor ⇒ u>0? needs the argument).
- ✅ `0 ≤ v` (resolver of nonneg source ≥ 0, O1).
- ⬜ InitialTrace (t→0 limit = u₀: heat leg → u₀, Duhamel legs → 0).
- ⬜ supNorm boundedness `≤ max(‖u₀‖,(a/b)^{1/α})` — logistic-damping / maximum principle. HARD.
- ⬜ global existence (`m≥1`) — boundedness ⇒ no blowup ⇒ global. HARD.
- ⬜ ASSEMBLE `Theorem_1_1 intervalDomain p` for χ₀<0 (mirror A1, carrying the analogous inputs).

  Carried analytic atoms in the χ₀<0 local solution (the frontier, same kind χ₀=0 carries):
  `ResolverSourceSummary` (ℓ¹), the realized-source flux atoms, the continuous-surrogate +
  Fourier-ℓ¹ for the source-inversions, the `hrep` representations (← realizes_clean).

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
