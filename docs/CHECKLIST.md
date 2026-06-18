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
| **Paper 3** (persistence/stabilization) | `[~]` statement-complete & build-clean; headline conditional on ~6 PDE floors (P3.1–P3.6) |

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
- [x] **Lemma 2** `greenConv_leftTailCauchy_uniform` + `paperFixedSourceMap_leftTailCauchy_kernel` — uniform left-tail Cauchy modulus ω₀ → 0 (b93cf67)
- [x] `continuousOn` — source-map continuous dependence (`paperFixedSourceMap_continuousOn_of_boxBounds`, internal) (820f55b)
- [x] paperDiff-free truncated max-principle + **direct** `truncation_inactive_direct_of_trap` (820f55b) — bypasses the record (upperBarrier non-diff at kink)
- [~] `map_leftTail` / `ascoliCompactRange` — GATED on the ω self-consistency below
- [x] **ω self-consistency** — RESOLVED via the exponential left-rate majorant (A+): `ExpLeftRate` predicate + kernel moments (m_σ=O(λ⁻¹)) + greenConv/frozenElliptic rate preservation + two-orbit (Z inner, u outer) left-rate threading. (d774b63 + 9a40dbd, full-build verified)
- [~] **box-close assembly** — discharge hmap_holder/leftTailCauchy/rate/lower/upper via the proven kernels → constructor needs ONLY hboxCubeData. *cx_pde now*
- [ ] **boxCubeData** — route (c): carry as the one permitted finite-net floor (same as outer G1) for hprodAll close; full McShane discharge blueprint in docs/boxCubeData-mcshane-blueprint.md for later full-unconditional

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

## PAPER 3 — "Persistence and stabilization" (CM with χ(v)=χ₀/(1+v)^β + logistic source)

- [x] Scoped (full survey done). **Statement-complete & build-clean**: all of Thm 2.1–2.5, Props 1.2–1.4,
  Remark 2.1, Lemmas A.6–A.8 stated + wired into `Paper3MainlineTargets`; **0 sorries / 0 admits / 0 axioms**,
  full build 3700 jobs. Every paper result has a faithful Lean Prop — NO missing statements.

### Unconditionally PROVEN (no work)
- [x] Unit-point logistic bridge — Props 1.2–1.4 + Thm 2.1 on the degenerate 1-point (ODE) domain, incl. the
  negative result `not_Theorem_2_1_part1_when_a_zero_b_pos`
- [x] Remark 2.1 — exact critical sensitivity `χ* = paperFormula(λ₁)` in regime `aαμ ≤ λ₁²` (formula/spectral)
- [x] Lemma A.7 + threshold ordering `chiStrong1/3Formula ≤ χ*` (spectrum-free floor)

### Headline `Paper3MainlineTargets` — conditional on ~6 unproven PDE floors (the real remaining work)
> Same pattern as Paper 1: hard N-dimensional analysis is carried in `*RawData/*BranchData/*FrontierData`
> hypothesis structures, proven only on the degenerate unit point. To pass playbook audit these must be
> discharged on a genuine bounded domain (the `intervalDomain`) — or honestly remain labeled conditional.
- [ ] **P3.1** Core existence/boundedness (Props 1.2–1.4) — `Paper3Proposition1FrontierData` →
  `NegativeSensitivityGlobalEventualBound` + global classical-solution package (§3 + Part I). *Everything below consumes this.*
- [ ] **P3.2** Uniform persistence (Thm 2.1) — `UniformPersistencePart{1,2,3,4}Raw` (time-translate compactness,
  strong max principle, ODE-subsolution lower bound, elliptic Neumann transfer) (§4)
- [ ] **P3.3** Linear stability dichotomy (Thm 2.2) — `Paper3Theorem22BranchData` over `SpectralData` (stable/unstable decay) (§5)
- [ ] **P3.4** Sectorial local exponential decay — `SectorialLocalExponentialRaw` (H3.1 framework) on the interval (§5/App A.1)
- [ ] **P3.5** Compactness/regularization (Lemmas 3.1–3.5, 7.1) — `Paper3CompactnessRegularizationRawData` (§3, §7)
- [ ] **P3.6** Global stability Thms 2.3–2.5 — `Paper3Stability23To25BranchData` (Lyapunov / rectangle-ODE / `corollary51` dissipation) (§6–8)
- [ ] **P3.7** Threshold-ordering tails (small) — route `chiStrong2/4Formula` to the spectrum-free floor (App A.3)

### Paper 3 STRATEGY (ChatGPT triage, full detail in docs/paper3-strategy.md)
GOAL (corrected, Xiang): BUILD the parabolic PDE library over months and GENUINELY DISCHARGE every floor.
NOT harvest-easy + label-frontiers. The heavy PDE floors ARE the targets. Build bottom-up (see
docs/paper3-strategy.md PDE-library build plan, layers 1-7). Per-floor difficulty (for BUILD ORDER, not deferral):
- P3.1 existence: heavy-defer (restricted negative-sensitivity/eventual-bound branch plausible via Paper2 reuse)
- P3.2 persistence: partial (ODE-comparison tractable; compactness/SMP heavy)
- P3.3 linear stability: **TRACTABLE** (spectral-formula dichotomy mostly in repo) — best leverage
- P3.4 sectorial: heavy-defer (interval spectral-decay DONE; nonlinear orbit bound remains)
- P3.5 compactness: mixed (interval max-principle/bookkeeping tractable; time-translate compactness heavy)
- P3.6 global stability: partial (Lyapunov algebra tractable; moment-to-uniform + C¹ upgrade heavy)
ATTACK ORDER: (1) P3.3 formula/spectral partial targets → (2) interval concrete bookkeeping wrappers →
(3) explicit 1D Neumann resolvent gradient estimate (Lemma 7.1) → (4) P3.2 ODE-comparison subpieces →
(5) restricted P3.1 via Paper2; LAST: P3.4 + full P3.6 (keep as named frontiers).
Add honest PARTIAL umbrellas: Paper3FormulaSpectralTargets, IntervalDomainSpectralDecayTargets,
IntervalDomainConcreteBookkeepingTargets, Paper3ConditionalPDEFrontiers.
- [ ] **P3.D** `Paper3MainlineTargets`: honest partial-unconditional report (formula/spectral/ODE branches
  unconditional; named PDE frontiers conditional) — NOT all-unconditional (infeasible without a parabolic library)

---

### How we use this
1. cx_pde closes a brick → I **full-build-verify** (`lake build WaveLemma42G1Discharge` green + axiom-clean) → tick the box → commit.
2. The next `[ ]` in B.2 → B.3 → B.4 order is the next dispatch.
3. `boxCubeData` (B.4) is the one item that may stay carried as a recognized shared floor (the outer G1 carries the same kind) — flagged, not faked.
