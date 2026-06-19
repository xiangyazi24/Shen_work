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

## COMPLETE DIAGNOSIS (solo, 2026-06-19) — the obstruction is CONTINUITY, inherent to the construction
Attempted the retraction bridge (WaveTrapSchauderViaRetraction.lean, a6abb04 — the antitone-majorant foundation
is built + reusable). Found + confirmed the real obstruction:
- `InMonotoneWaveTrapSet` requires `IsCUnifBdd` (= Continuous ∧ IsBddFun); `WaveTrap κ κt D` does NOT require
  continuity. So `WaveTrap ⊄ InMonotone`, and the retraction `T'=Tmap∘r` can't be shown InMonotone→InMonotone.
- Route (a) [re-prove ProjectedCubeApproxData for WaveTrap] is ALSO blocked by continuity: the construction's
  `profileRestrictIcc (hu : Continuous u)` (WaveTrapProjectedCubeApproxData.lean:15) restricts profiles to
  [−R,R] ASSUMING continuity — the Fréchet-metric ε-net machinery fundamentally needs continuous members.
- CONCLUSION: the Schauder construction inherently needs CONTINUOUS trap members. The correct fix (math is fine —
  wave profiles ARE continuous) is to make the headline's trap continuity-required:
  **add `Continuous u` to `WaveTrap` (WholeLineWaveTrap.lean:13)**, then `WaveTrap ⊆ InMonotoneWaveTrapSet κ 1`
  and the retraction (a6abb04) closes the principle — needing only `Lstar` continuous (running-sup of a
  continuous bounded function, doable). This CASCADES: every WaveTrap-construction site (bricks 2/3/9/12, the
  barriers, the long-time limit) must also supply `Continuous` (all true — the objects are continuous). A
  structural change to a foundational def → codex-shaped cascade, OR Xiang's authorization to modify brick-3.
This is the precise, complete resolution path; blocked only on codex quota (purchase-cap) / the brick-3 decision.

## Cascade scope MEASURED (solo, 2026-06-19)
Adding `Continuous` to `WaveTrap` (brick 3): only ~4-5 CONSTRUCTION sites (waveTrap_upper_mem [upperBarrier
continuous — easy], longTimeMap mapsTo [the long-time limit continuous — needs Dini/loc-unif from brick 9],
WaveResidualLastTwo, WholeLineWaveTrap:71 [already a ContinuousMap]). BUT the def-structure change (2-conjunct →
3-conjunct) breaks ALL ~40 CONSUMPTION sites that extract antitone via `hu.2` (become `hu.2.1`). So it IS a
~40-site systematic refactor — codex-shaped. Cleanest for codex: change WaveTrap to carry Continuous, then
fix the ~40 `.2`→`.2.1` extractions + supply Continuous at the ~5 construction sites (all true: barriers/limits
are continuous; the long-time-limit continuity from the monotone loc-unif Dini limit). The banked retraction
(a6abb04) then closes the principle modulo Lstar continuity. Blocked on codex quota / Xiang's nod for the refactor.

## RESOLVED IN PRINCIPLE (solo, 2026-06-19) — no cascade needed
The Schauder-for-WaveTrap gap is now PROVEN, axiom-clean, WITHOUT the WaveTrap-continuity cascade:
- `waveTrap_fixedPoint_of_continuousImage` (WaveTrapSchauderViaRetraction.lean, dec57b1): ∃ U∈WaveTrap, Tmap U=U
  from mapsTo+cont+compact + the CONTINUOUS-IMAGE hyp (∀u∈WaveTrap, Continuous(Tmap u)), via the antitone-
  majorant retraction + our own Brouwer. The continuity is supplied by the map's IMAGE, not the trap def.
- `wholeLine_wave_fixedPoint_exists_of_continuousImage` (WaveFixedPointContinuousImage.lean, 6751c20): the
  brick-12 drop-in. Its hTimg = `LongTimeMapImageContinuity` = `longTime_image_continuity`, ALREADY a
  WholeLineTravelingWaveData field.
REMAINING (mechanical re-threading, ~4 files — codex-clean or careful solo):
1. WholeLineTravelingWaveExistence.lean:156 — swap `wholeLine_wave_fixedPoint_exists ... H.schauder_principle`
   → `wholeLine_wave_fixedPoint_exists_of_continuousImage (waveExponent_pos hc) hκt hD hmapsTo hcont hcompact
   H.longTime_image_continuity`. Then `schauder_principle` is unused.
2. Remove `schauder_principle` field from `WholeLineTravelingWaveData` (Existence.lean:7).
3. Remove the providers: WholeLineWaveExistenceReduced.lean:498, WholeLineWaveExistenceConsolidated.lean
   :410/418/451/463, WholeLineTravelingWaveAssembled.lean:311/413 (drop the `Hschauder*` hyp + provision).
After this, the wave headline carries NO Schauder-principle residual — it is proved from our own Brouwer; only
the concrete aux-flow inputs (incl. longTime_image_continuity, itself dischargeable from the banked parabolic
equicontinuity) remain. So Paper-1 wave reduces to the aux-flow regularity alone — no Mathlib gap, no abstract
Schauder hypothesis.
