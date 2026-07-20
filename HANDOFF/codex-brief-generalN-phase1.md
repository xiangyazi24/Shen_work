# Codex Brief — General-N, Phase 1: the smooth bounded domain instance

Repo ~/Shen_work (HEAD c8d9e1fb). Rules: 0 sorry, 0 axiom, NEW files only under
ShenWork/PDE/, `lake build` green per file, APPEND imports to ShenWork.lean at
the end. Do NOT commit. Do NOT edit existing files.

READ FIRST: HANDOFF/GENERAL_N_PLAN.md (the architecture survey) and
ShenWork/PDE/BoundedDomainData.lean (the abstract layer).

## Why this is tractable

Papers 2 and 3 are stated on "a bounded smooth domain Ω ⊂ R^N" (verified: both
PDFs, abstract). Our formalization proved them for N = 1 via the instances
`intervalDomain` / `intervalDomainM` (ShenWork/PDE/IntervalDomain.lean:3011,3035).
Crucially, **all Paper2/Paper3 theorem statements are already written against the
abstract `BoundedDomainData`, which does not fix the dimension** — so General-N
is an INSTANTIATION problem, not a restatement problem. Every abstract theorem
we already proved transfers the moment a legitimate N-dimensional instance
exists and its structural hypotheses are discharged.

## Phase 1 goal (this task)

Build a concrete `BoundedDomainData` instance for a bounded open set
`Ω ⊆ EuclideanSpace ℝ (Fin N)` with the regularity we actually need, and prove
the structural fields. Do NOT attempt the Neumann boundary theory yet.

Deliverables, in order, each building green:

G1. `ShenWork/PDE/EuclideanDomainData.lean`
    - a structure bundling `Ω : Set (EuclideanSpace ℝ (Fin N))` with
      `IsOpen Ω`, `Bornology.IsBounded Ω`, `(volume Ω).toReal > 0`, and whatever
      minimal regularity the fields below need;
    - the `BoundedDomainData` instance: Point := ↥Ω (or ↥(closure Ω) — pick the
      one the existing abstract theorems actually consume; READ BoundedDomainData
      first and say which and why), integral := ∫ over Ω w.r.t. volume,
      gradNorm := ‖fderiv ℝ f x‖, and the remaining fields.
    - Report exactly which fields you could discharge and which need boundary
      theory.

G2. `ShenWork/PDE/EuclideanDomainBasic.lean`
    - the basic facts the Paper2/3 abstract proofs consume from the instance:
      integral monotonicity/linearity, finiteness of the volume, the constant
      function's integral, and the Cauchy–Schwarz / Hölder forms IF the abstract
      layer requires them (check by grepping which `D.` fields and which
      `BoundedDomainData` lemmas the Paper2 headline proofs actually use —
      `Lemma_2_6`, `intervalDomain_Proposition_2_2`, etc.).

G3. A REPORT (as a markdown file HANDOFF/generalN-phase1-report.md, plus your
    console summary) listing, for the N-dimensional instance:
    - which abstract Paper2/Paper3 theorems become available IMMEDIATELY,
    - which need only structural fields you could not yet discharge,
    - which genuinely need Neumann boundary theory (normal derivative, trace,
      divergence theorem) that Mathlib lacks — with the exact missing API named.

This last report is the real deliverable of Phase 1: an evidence-based map of
what General-N costs, replacing the current survey-level estimate. Be precise
and do not overstate what transfers.
