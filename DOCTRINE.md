# Shen Trilogy Formalization — DOCTRINE

**Main goal (one sentence):** Formalize the Chen–Ruau–Shen chemotaxis-growth trilogy
(Paper 1 traveling waves, Paper 2 bounded-domain existence, Paper 3 long-time dynamics)
in Lean 4, landing the headline theorems with NO sorry / axiom / native_decide and NO
vacuity — every carried frontier must be satisfiable and faithful to the paper.

**Hard rules (non-negotiable):** axiom-clean = [propext, Classical.choice, Quot.sound];
no sorryAx; vacuity-check every carried hypothesis against the zero function / a real
solution; faithfulness-check every domination hypothesis against the paper (do not invent
conditions stronger than the paper); build via `lake env lean` on uisai2 (NOT codex,
NOT local lake build). Commits record honest verdicts (reduction ≠ discharge).

## Avenues (ranked by proximity to a headline)

### (a) Headline 1 — Paper 1 wave existence χ≤0 (`b1_chiNeg_existence`)  [PRIMARY, ACTIVE]
The Rothe parabolic-orbit construction is built & axiom-clean; reduces to satisfiable frontiers:
- **R3 → G1** (cx_r3 active): the correct post-projection box/Freudenthal door↔rainbow
  bijection is committed (f9ba007). Remaining: close the recursive `Odd` (induction +
  `sperner_n_dim_combinatorial` + partner involution), then wire G1 via `brouwer_simplex_approx`
  (Sperner label → rainbow → barycenter → approx fixed) + Helly + the existing
  `exists_fixed_of_approx_fixed` bridge. Route: BOX2G1_ROUTE_chatgpt.md.
- **Non-triviality** (cx_pde active): pinned-trap route committed non-vacuous (31d0d04).
  `lowerBarrierPlateau` is NOT a subsolution (plateau chemotaxis, counterexample not_Lemma_4_2).
  Fix: `LowerBarrierData` + smoothed two-exp subsolution under FAITHFUL domination
  (plateau budget C(1-C^α)≥|χ|C^m B₂, tail m·κ≥κtilde, C² edge). Route: SUBSOLUTION_ROUTE_chatgpt.md.
- **StationaryZeroPropagatesByODEUniqueness**: 1-D ODE Cauchy uniqueness (Mathlib Picard–Lindelöf).
- producer/continuous-dependence frontiers.
**Terminal:** `b1_chiNeg_existence` with all frontiers discharged or faithful-conditional, axiom-clean.
**Proof-of-failure:** a frontier proven unsatisfiable (like the floor/bare-trap principle) OR a
faithfulness gap (paper claims existence the barrier cannot give) → report to Xiang.

### (b) Headline 1 positive branch χ≥0 (`b1_chiPos_existence`)
Reuse the Rothe/Schauder + pinned-trap machinery with flipped signs (positive sensitivity).
**Terminal:** `b1_chiPos_existence` axiom-clean, non-vacuous.

### (c) Headline 2 — Paper 2 bounded-domain existence χ₀<0 (`Theorem_1_1`)
Irreducible core = positive-time Hölder bootstrap + singular ∂ₓₓS(t-s) endpoint cancellation
(∫∂ₓₓK_N dy=0 ⟹ C^θ source suffices). Route: HQUANT_ROUTE/HOLDER_CANCELLATION_ROUTE_chatgpt.md.
No codex yet (codex quota focused on (a)). **Terminal:** `hQuant` discharged via the Hölder lemma.

### (d) Paper 2 χ₀=0 — Picard floor
`IntervalDomainMildLocalChi0` clamped-witness machinery largely landed (uisai1 parallel work).
Residuals: `hpde_u` (mild→classical PDE), `Hu` (time-neighborhood spectral agreement).
**CAUTION:** overlaps uisai1's ledger — coordinate, do not clobber.

### (e) Paper 2 a-priori estimates  [HONEST FACTORINGS COMMITTED]
Prop 2.4 (mass) + Prop 2.5 (Moser) reduced to real-solution-gated frontiers (43b1ab4, 38fe33b).
Remaining: discharge the named gated frontiers (no-flux mass identity, Moser bootstrap estimates).

### (f) Paper 3 — long-time dynamics
Rides on Paper 2 existence. Persistence/lower-envelope; deferred until (c)/(d) land.

## Fallbacks
- If a barrier/route fails terminally, switch to the documented alternative in the corresponding
  ChatGPT route doc (each avenue has one saved in-repo).
- Faithful-conditional headlines: if the paper assumes conditions (e.g. chemotaxis budget),
  carry exactly those — a faithful conditional theorem is a valid landing, NOT a vacuity.
- Codex quota exhaustion → ChatGPT (separate quota) advances route docs; resume codex on reset.

## Worker assignment (disjoint files, no conflicts)
- **cx_r3** owns BrouwerNDim* / Brouwer* / Freudenthal (R3→G1). Never touches wave files.
- **cx_pde** owns WaveRothe* / WaveTrapProps (non-triviality). Never touches BrouwerNDim/Paper2.
- **Paper-2 codexes** own Paper2/*. **ChatGPT** = route audit (verify-don't-transcribe).
