# Liang shifting-habitat project

This directory contains Liang Kong's CMBE 2026 proposal and the accompanying
formalization audit.

- `CMBE_2026.pdf`: source proposal.
- `FORMALIZATION_AUDIT.md`: corrected model, exact Lean proof status, strict
  limitations of the certified theorems, and the bridge to ShenWork.
- `CORRECTED_THEOREMS.tex` / `CORRECTED_THEOREMS.pdf`: standalone
  mathematical note, with the defects in the original statements separated
  into an appendix.

## Current top-level results

- Corrected Theorem 2.1 is proved by
  `correctedIDEOrbit_fastHabitat_extinction` in
  `ShenWork/Liang/FastHabitatExtinction.lean`. It gives uniform extinction
  above both admissible variational speeds for unit-square initial data that
  vanish to the right of finite bounds.
- The most general proved version of Corrected Theorem 2.2 is
  `correctedIntermediateSpeedExclusion_of_finiteBlockCertificate` in
  `ShenWork/Liang/IntermediateSpeedExclusion.lean`. A finite iterate of the
  low-density linear recursion is certified to reproduce a translated,
  enlarged interval floor. Lean then proves that this finite linear
  certificate lies below the nonlinear corrected IDE, supplies a positive
  floor at all sufficiently large times, and forces the fast component to
  converge to one after the slow component becomes uniformly extinct.
  `finiteBlockCertificate_of_reference_interval_and_power_bound` reduces
  nonnegativity and all integrability obligations to automatic facts, reduces
  the upper bound to one terminal scalar check, and by
  `finiteBlockCertificate_of_unit_reference` reduces the substantive
  expansion check to a dimensionless unit-height standard interval. The
  exact identities `integral_intervalFloor` and
  `integral_finiteLinearOrbit_intervalFloor` also prove that total linear
  mass is precisely multiplied by the appropriate power of the low-density
  slope. This mass growth does not imply a pointwise moving-interval floor.
  The remaining analytic gap is to derive that one local reference
  convolution-power estimate from the variational speed inequality. The
  older one-step minorization theorem is
  retained as a stronger special route; its certificate forces a favorable
  lower growth bound greater than one. The attempted sequential
  transport-then-recovery route is now formally proved incompatible with a
  nonempty positive corridor for compactly supported kernels.
- The main proved version of Corrected Theorem 2.3 is
  `certified_weak_competition_spatial_coexistence` in
  `ShenWork/Liang/SpatialCoexistenceCertificate.lean`. It proves uniform
  weak-competition coexistence on a one-sided corridor from compact kernels,
  exact favorable tails, and eventual positive floors for both species on a
  wider corridor. The corollary
  `certified_weak_competition_spatial_coexistence_of_finiteBlockCertificates`
  replaces those floors by one finite linear block certificate per species.
  It covers the full weak-competition parameter range whenever those two
  finite certificates are supplied. The older corollary
  `certified_weak_competition_spatial_coexistence_of_minorization` uses a
  stronger one-step numerical certificate. In fact,
  `corridorFloorCertificate_forces_growth_restriction` proves that each such
  certificate forces \(\alpha_i<1/2\) and \(\rho_i^+>1\); hence this
  particular one-step route is impossible when \(\alpha_i\ge 1/2\).
  Neither result identifies `front` with the sharp reduced threshold.

## Lean files and direct dependencies

Mathlib imports are omitted below.

- `ShenWork/Liang/ModelAudit.lean`
- `ShenWork/Liang/CorrectedModel.lean`
  → `ModelAudit`
- `ShenWork/Analysis/DispersalKernel.lean`
- `ShenWork/Liang/LinearDeterminacy.lean`
  → `DispersalKernel`, `ModelAudit`, existing `WaveRotheTrap`
- `ShenWork/Liang/IDEComparison.lean`
  → `DispersalKernel`, `CorrectedModel`
- `ShenWork/Liang/StateSpace.lean`
  → `IDEComparison`, existing `WaveRotheTrap`
- `ShenWork/Liang/MovingCorridor.lean`
  → `ModelAudit`
- `ShenWork/Liang/GlobalDynamicsTools.lean`
  → `CorrectedModel`
- `ShenWork/Liang/FastHabitatExtinction.lean`
  → `StateSpace`, `LinearDeterminacy`
- `ShenWork/Liang/ScalarPersistence.lean`
  → `IDEComparison`
- `ShenWork/Liang/MultistepPersistence.lean`
  → `ScalarPersistence`
- `ShenWork/Liang/FiniteBlockSpreading.lean`
  → `ScalarPersistence`, `MovingCorridor`
- `ShenWork/Liang/IntermediateSpeedExclusion.lean`
  → `MultistepPersistence`, `FiniteBlockSpreading`, `MovingCorridor`,
  `StateSpace`
- `ShenWork/Liang/SeededEnvelope.lean`
  → `GlobalDynamicsTools`
- `ShenWork/Liang/WeakCompetitionCoexistence.lean`
  → `GlobalDynamicsTools`, `LinearDeterminacy`, `MovingCorridor`,
  `SeededEnvelope`
- `ShenWork/Liang/SpatialCoexistenceCertificate.lean`
  → `IntermediateSpeedExclusion`, `WeakCompetitionCoexistence`

The abstract 2.3 interface theorem
`corrected_weak_competition_uniform_corridor_convergence` remains useful, but
it assumes a global fixed-depth seeded-envelope comparison. The explicit
spatial certificate file discharges that interface from finite range, exact
tails, and eventual wider-corridor floors. Its finite-block corollary is the
main constructive route to those floors; the one-step minorization corollary
is only a stronger numerical special case.
