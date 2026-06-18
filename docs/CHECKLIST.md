# Shen Trilogy — Formalization Checklist (按图索骥)

> Persistent map. We check off one box at a time. Every `[x]` is **full-build verified +
> axiom-clean** (`[propext, Classical.choice, Quot.sound]`) before it gets ticked — no
> overclaiming. `[~]` = in progress. `[ ]` = not started.
> Last updated: commit `1a38d95` (Lemma 1 holder_kernel landed).

---

## Progress at a glance

| Layer | Status |
|---|---|
| **Paper 1** (χ≤0 traveling wave) — headline | `[~]` gated on per-step floor `hprodAll` |
| ↳ Per-step conceptual core | `[x]` DONE (the hardest part) |
| ↳ Per-step regularity bricks | `[~]` 1 of ~6 done (Hölder ✓, left-tail in progress) |
| ↳ Per-step assembly + cube witness | `[ ]` not started |
| ↳ Secondary orbit floors (hstep/htail) | `[ ]` vestigial, deferrable |
| **Paper 2** (Schauder) | `[x]` DONE |
| **Paper 3** | `[ ]` scoped, not started |

---

## PAPER 1 — headline: `b1_chiNeg_existence_paper_clean_of_cubeApproxData`

The headline is a clean assembly. Everything below `hprodAll` is the ONLY substantive open math.

### A. Already-discharged floors (closed, internal to the headline)
- [x] Outer G1 Schauder (cube route, unconditional shape)
- [x] `hflat` — FrozenStationaryFlatAtLeft (5febb74 / 6955957)
- [x] `hsmp` / `hrealize` — strong max principle via Green-rep threaded from Rothe limit, real exponents (df65097)
- [x] `hstationary` — rotheLimit fixed ⟹ frozenWaveOp U U = 0 (26cbe80)
- [x] `hstationary` uniform-bounds — C²-compact, non-circular green-thread (cx_r3, 7909e75)
- [x] `hlim_neg` — left limit U(−∞)=1 via equilibrium + lower-pin (62e5c09)
- [x] antitone — RouteA sliding max-principle (committed)

### B. `hprodAll` (per-step producer) — THE sole substantive floor

#### B.1 Conceptual core — DONE
- [x] Route diagnosis: raw-mapsTo is FALSE (chemotaxis transport); truncated fixed-source box is the route (22aaae2)
- [x] Weighted-Hölder source box — ψ=upperBarrier weight, spatial clamp, β case-split 0<β≤1 (9b9a2b1)
- [x] Weighted-bound machinery + `hu` threading (~1000 lemmas) (2e84641)
- [x] greenConv / greenConvDeriv left-tail-from-source limits; `leftTail_Icc` (L_u, NOT u→1) (07acb81)
- [x] **Truncated-operator max-principle** `paperImplicitStep_truncated_le/ge_of_paperBarrier` — breaks the circularity (43971ef)
- [x] **`truncation_inactive`** — 0≤W≤U⁺ for the truncated fixed point, non-circular (43971ef)
- [x] Iterate-regularity threading — PaperIterateBase diff/deriv_le, additive `produce_regular` (bd5c52f)

#### B.2 Box self-invariance — the regularity bricks
- [x] `map_bound` — weighted sup bound (in `paperFixedSourceMapBoxBounds_of_trap`)
- [x] **Lemma 1** `paperFixedSourceMap_holder_kernel` — β-Hölder modulus H₀ (1a38d95)
- [~] **Lemma 2** `greenConv_leftTailCauchy_uniform` + `paperFixedSourceMap_leftTailCauchy_kernel` — uniform left-tail Cauchy modulus ω₀ → 0  *(cx_pde grinding now)*
- [ ] `map_leftTail` — image has a left limit (composes from greenConv left-tail + V/Z left limits)
- [ ] `continuousOn` — source-map continuous dependence (LocalUniformContinuousOn)
- [ ] `ascoliCompactRange` — Arzelà-Ascoli on the compactified line (from uniform bound + Hölder + left-tail)

#### B.3 Barrier super-solution — DIRECT (dodge the 2nd circularity)
- [ ] `hupper` / `hlower` — construct directly via `Lemma_4_1_neg_holds_away_from_interface` + `upperBarrier_BC2_atMax_dischargeable` (root found; NOT via the circular `hrest`)

#### B.4 Assemble the concrete producer
- [ ] `paperFixedSourceMapBoxBounds_of_trap` — choose B/H/ω internally (kernel-derived), discharge all box fields
- [ ] `paperTruncatedFixedSourceBoxData_of_trap` — fully concrete, only `boxCubeData` carried
- [ ] `boxCubeData` — finite-net cube witness for the source box (mirror outer G1's `ProjectedCubeApproxData`) **or** accept as the same carried shared floor the outer G1 carries
- [ ] Final wire: `of_truncated_sourceBox` → `PaperStepFixedSourceExistsForSuperTrap` → `paperGreenStepInputRouteACore` → `paperRotheStepProducer_of_routeA_greenCore` ⟹ **`hprodAll` unconditional**

### C. Secondary headline floors (deferrable; vestigial under the direct route)
- [ ] `hstep` — PaperRotheSeqStepDependence (orbit step-dependence)
- [ ] `htail` — PaperRotheTailUniform (orbit tail-uniformity)
- [ ] cube data — outer G1 `ProjectedCubeApproxData` (same finite-net floor as B.4's boxCubeData)
- [ ] scalars — hcond/hD/hbarLip concrete witnesses (paper's parameter hypotheses; mostly trivial)

### D. Headline closes
- [ ] `b1_chiNeg_existence_paper_clean` unconditional (modulo the finite-net cube witness shared with outer G1)

---

## PAPER 2 — Schauder
- [x] Complete (0 real sorry, builds, axiom-clean)

## PAPER 3
- [ ] Scope / bottom out the底 (one codex scout pass)
- [ ] (decomposition TBD after scoping)

---

### How we use this
1. cx_pde closes a brick → I **full-build-verify** (`lake build WaveLemma42G1Discharge` green + axiom-clean) → tick the box → commit.
2. The next `[ ]` in B.2 → B.3 → B.4 order is the next dispatch.
3. `boxCubeData` (B.4) is the one item that may stay carried as a recognized shared floor (the outer G1 carries the same kind) — flagged, not faked.
