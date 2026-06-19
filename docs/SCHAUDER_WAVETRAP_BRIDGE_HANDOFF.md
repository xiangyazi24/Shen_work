# Schauder-for-WaveTrap bridge — handoff for the next codex run (blocked on codex quota 2026-06-19)

## The gap (from the final assembly 1c52a40)
The headline `wholeLine_travelingWave_exists` needs `LocalUniformSchauderFixedPointPrinciple
(fun U => U ∈ WaveTrap κ κt D)`. We PROVED (axiom-clean, our own Brouwer): `inMonotoneWaveTrap_schauderPrinciple`
for `InMonotoneWaveTrapSet κ 1`. Need to bridge to `WaveTrap κ κt D`.

## KEY SIMPLIFICATION (verified this session)
- `upperBarrier κ 1` (2-arg, Statements.lean:3497, = min 1 (exp(−κx))) IS DEFINITIONALLY `upperBarrier κ`
  (1-arg, WholeLineExponentialBarriers.lean:8, = min 1 (exp(−κx))). The UPPER bounds are IDENTICAL.
- So `WaveTrap κ κt D ⊆ InMonotoneWaveTrapSet κ 1`: WaveTrap's `lowerBarrier κ κt D ≤ u` is STRONGER than the
  `0 ≤ u` of InMonotone (since lowerBarrier ≥ 0), and InMonotone's `IsCUnifBdd u` follows from `u ≤ upperBarrier κ
  = min 1 (exp(−κx)) ≤ 1` + `0 ≤ u`. The `Antitone`/`NonincreasingProfile` parts coincide.

## Why the subset doesn't directly transfer (so the construction must re-target)
The Schauder principle gives a fixed point IN the trap of the construction. For the fixed point to land in
WaveTrap (needed for the headline's U(−∞)=1 via the lowerBarrier), the construction's net must be drawn from
T(WaveTrap) ⊆ WaveTrap and the lift ∑aᵢyᵢ must land in WaveTrap by `WholeLineWaveTrap.waveTrap_convex`. So the
ProjectedCubeApproxData must be built FOR the WaveTrap predicate.

## The task (codex, when quota refreshes)
Adapt `WaveTrapProjectedCubeApproxData.waveTrapProjectedCubeApproxData` (1727 lines, 154 InMonotoneWaveTrapSet
refs) to `WaveTrap κ κt D`. The generic pieces REUSE directly: `schauderBump` (PseudoMetricSpace-generic), the
partition-of-unity weights, the Brouwer/_of_brouwer chain. Trap-specific pieces needing WaveTrap versions: the
image-restrict totally-bounded/compact-closure lemmas, `lift_trap` (from waveTrap_convex), `proj_trap`. Then
`waveTrap_schauderPrinciple := localUniformSchauderFixedPointPrinciple_of_brouwer (the WaveTrap construction)`.
Spec: /tmp/shen_schwavetrap.md. Then the headline's Hschauder_waveTrap discharges; remaining = the concrete
aux-flow inputs (Hclassical/Hweak/Hflow_lip/… — satisfiable real-solution regularity, the aux-flow
local/global/classical/equicontinuity pieces are built, just need wiring).
