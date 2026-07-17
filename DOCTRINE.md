# DOCTRINE — Shen_work 5-frontier grind (2026-07-17)

## Main goal
Close all 5 remaining open frontiers (1D) sequentially.

## Avenues (in order)

### (a) Paper 1 Theorem 1.2 — tail asymptotics
Terminal: sorry count in ShenWork/Paper1/ reduced; capstone wired or carried only on Henry-class imported infra.
Attack: audit sorry in Paper1/, identify leaf sorry, grind each.
**STATUS: AT TERMINAL CONDITION.**
- Paper1/ has 0 sorry (all matches are in docstring comments).
- χ≤0 branch: `paper1_Theorem_1_2_chi_nonpos_paperDatum` — UNCONDITIONAL, axiom-clean.
- Full theorem: `paper1_Theorem_1_2_amended_of_wholeLineCauchyEnergyStep4` — CONDITIONAL on Henry semigroup smoothing (sectorial operator infrastructure absent from Mathlib, out of scope per THEOREM12_ERRATA.md).
- All 7 paper errata certified with Lean theorems (Theorem12RootObstruction.lean, Theorem12CoordinateAudit.lean, Theorem12MeanCoefficients.lean, Theorem12WeightedEnergy.lean).
- Novel §5.2 content (Steps 1–4, Lemma 5.3, Grönwall closure, (1.21)⇒(1.22)) all proved unconditionally.

### (b) Paper 3 Theorem 2.3 — χ₀≤0 global stability, general-m
Terminal: unconditional on intervalDomainM (no hm : p.m = 1).
Attack: port m=1 proof using Thm 2.4 general-m infrastructure from 07-16.
**STATUS: DONE (0 sorry). Commit 1897737a.**
- Both branches (nonminimal + minimal) fully proved and axiom-clean.
- IntervalDomainMMinimalChiNonposConvergence.lean (1045 lines): full convergence chain.
- IntervalDomainMTheorem23Eventual.lean: capstone wiring, all 5 theorems clean.

### (c) Paper 3 Theorem 2.5 — minimal a=b=0 stability
**STATUS: ALREADY DONE (0 sorry, faithful to paper — m=1 is the paper's own statement).**

### (d) Paper 2 supporting — Prop 2.2/2.4/2.5, Lem 2.6, Cor 2.1
Terminal: each stated + proved or carried on headline-level hypotheses.
Attack: audit each statement, find producers, wire.
**STATUS: DONE (all 5 already proved and axiom-clean).**
- Prop 2.2: `intervalDomain_Proposition_2_2` (IntervalDomainWeightedGradientEstimate.lean:827), clean-3.
- Prop 2.4: `intervalDomain_Proposition_2_4` (IntervalDomainMass.lean:888), clean build.
- Prop 2.5: Multiple routes (MoserActualAtoms, 1DLinfRoute, MoserLadderAtoms), all clean.
- Lemma 2.6: `Lemma_2_6_intervalDomain_of_mass_gradient_frontier` (IntervalDomainTheorem11.lean:110), clean.
- Cor 2.1: `Corollary_2_1_intervalDomain_of_mass_gradient_frontier` (IntervalDomainTheorem11.lean:278), clean.

### (e) General-N infrastructure
Terminal: architectural plan + partial infrastructure beyond 1D.
Attack: abstract intervalDomain to general bounded domain.
**STATUS: AT TERMINAL CONDITION.**
- Architectural plan written: HANDOFF/GENERAL_N_PLAN.md (4 phases, gap table).
- Partial infrastructure exists: abstract `BoundedDomainData` (BoundedDomainData.lean) already dimension-agnostic; all theorem statements use it.
- Gap assessment: Mathlib lacks Neumann eigenvalues, heat semigroup, trace theorem, Green's formula, Schauder estimates — all C3 difficulty.
- Phase 1 (add algebraic axioms to BoundedDomainData) is the next actionable step; deferred as it touches every file in the project.

## Constraints
- mini DOWN — uisai1 only
- Build: /dev/shm/lean/Shen_work-active (lake build in progress)
- Working copy: /home/xhuan5/Shen_work (synced, no warm build)
