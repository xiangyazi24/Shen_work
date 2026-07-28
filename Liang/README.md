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
- Corrected Theorem 2.2 currently means the certified assembly
  `correctedIntermediateSpeedExclusion_of_bcf_extinction_and_minorization`
  in `ShenWork/Liang/IntermediateSpeedExclusion.lean`. It takes the slow
  component's bounded-continuous norm limit—the exact output shape of the
  component extinction theorem—and internally obtains uniform pointwise
  extinction. It then proves convergence of the fast component to one from a
  compact-support, seed, kernel-minorization, and favorable-tail certificate.
  Its `front` is not identified with the sharp \(c_2^*\). The proved
  feasibility obstruction shows that this particular one-step certificate
  requires a favorable lower growth bound greater than one.
- The main proved version of Corrected Theorem 2.3 is
  `certified_weak_competition_spatial_coexistence` in
  `ShenWork/Liang/SpatialCoexistenceCertificate.lean`. It proves uniform
  weak-competition coexistence on a one-sided corridor from compact kernels,
  exact favorable tails, and eventual positive floors for both species on a
  wider corridor. The corollary
  `certified_weak_competition_spatial_coexistence_of_minorization` replaces
  those floors by one explicit numerical certificate per species. That
  one-step certificate is an extra sufficient condition, not a theorem for
  the whole weak regime. In fact,
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
- `ShenWork/Liang/IntermediateSpeedExclusion.lean`
  → `ScalarPersistence`, `MovingCorridor`, `StateSpace`
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
tails, and eventual wider-corridor floors; its minorization corollary is only
one stronger numerical route to those floors.
