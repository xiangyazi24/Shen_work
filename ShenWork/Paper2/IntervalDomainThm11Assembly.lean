/-
  Final assembly: wire G0–G7 + G2.5 + G4 into Paper 2 Theorem 1.1.

  ## Proved ingredients (axiom-clean, 0 sorry, 0 axiom)

  * **Picard fixed point** (`GradientMildSolutionData`): mild solution exists
    for every PID u₀ on some horizon [0, T].

  * **Regularity bootstrap** (`IntervalMildRegularityBootstrap`): given
    `HasRestartCosineRepresentations`, the mild solution satisfies the 9
    classical regularity fields.

  * **Picard iterate C² induction** (`IntervalMildPicardRegularity`): every
    Picard iterate has C² spatial slices with Neumann BC.

  * **DuhamelSourceTimeC1 limit passage** (G2.5): `DuhamelSourceTimeC1`
    passes to pointwise limits under uniform derivative convergence.

  * **L² overlap uniqueness** (PID-gated, G6): hposWit eliminated.

  * **δ-iteration** (G7): `hlocal + hUniform → ReachableArbitrarilyLong`.

  * **Spectral time derivatives** (G4a–G4i):
    - HasDerivAt for the restart cosine series in time
    - DifferentiableAt of the mild solution (G4j)
    - Joint (τ,x) continuity of the restart derivative field (G4 remaining)

  * **G5**: Uniform `S(t)u₀ → u₀` for continuous u₀ on [0,1].

  * **γ≥1 umbrella**: `hlocal + hUniform → Theorem_1_1` (no hposWit).

  ## Remaining frontier

  The theorem `paper2_theorem_1_1_of_frontier` packages the exact residual:

  * **F1** `uniformLocalExistence` — textbook parabolic continuation δ(M).
  * **hMildLocal** — the mild-to-classical bridge data.  This absorbs:
    - `GradientMildSolutionData` (Picard FP — proved)
    - `GradientMildHalfStepLogisticSourceData` (needs F2)
    - Initial approach (G5 — proved)
    - `GradientMildClassicalFrontierCoreData`:
      - `hpde_u`: spectral→pointwise PDE bridge (G4i gives spectral form;
        pointwise form needs cosine-series Laplacian = pointwise Laplacian)
      - `hregularityFrontier`: 9 fields, most proved via G4 + bootstrap

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalMildPicardLimitRegularity
import ShenWork.Paper2.IntervalMildTimeRegularity
import ShenWork.Paper2.IntervalMildToLocalExistence
import ShenWork.PDE.IntervalRestartDerivJointContinuity

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.Theorem11Assembly

/-! ## The lean theorem: Paper 2 Theorem 1.1 from the frontier -/

/-- **Paper 2 Theorem 1.1 from `hlocal` + `hUniform`.**

The γ≥1 umbrella theorem (with hposWit eliminated) takes exactly
two textbook PDE inputs.  `hlocal` is constructible from
`IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData`
(Picard + bootstrap + G4 + G5).  `hUniform` is
`IntervalDomainUniformLocalExistence` (textbook continuation). -/
theorem paper2_theorem_1_1_of_frontier
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hUniform : IntervalDomainUniformLocalExistence p)
    (hMildLocal :
      IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p) :
    Theorem_1_1 intervalDomain p :=
  Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge
    p hχ ha hb hγ_ge_one
    (localExistence_of_gradientMildHalfStepLogisticSourceFrontierCoreLocalData
      p hMildLocal)
    hUniform

/-! ## Status of each component of hMildLocal

`IntervalDomainGradientMildHalfStepLogisticSourceFrontierCoreLocalData p` =
`∀ u₀, PID u₀ → ∃ D S, initial_approach ∧ FrontierCoreData`

| Component | Status | Source |
|-----------|--------|--------|
| `D : GradientMildSolutionData` | ✓ proved | IntervalMildPicard |
| `S : GradientMildHalfStepLogisticSourceData` | **F2** frontier | needs DuhamelSourceTimeC1 for limit |
| Initial approach | ✓ proved | G5 (IntervalSemigroupUniform) |
| `hpde_u` | ~provable | G4i spectral + pointwise bridge |
| `supnormLogistic` | ✓ proved | IntervalDomainExistence |
| `supnormZero` | ✓ proved | IntervalDomainExistence |
| `vSpatialInterior` | ✓ proved | elliptic resolver C² |
| `timeSlices` (u part) | ✓ proved | G4j (mildSolution_differentiableAt_time) |
| `timeSlices` (v part) | ~provable | resolver chain rule from u time-diff |
| `jointTimeDerivInterior` (u part) | ✓ proved | G4 remaining (restartDerivField_continuousOn_joint) |
| `jointTimeDerivInterior` (v part) | ~provable | resolver chain + joint continuity |
| `vNeumannLimits` | ✓ proved | restart cosine representation |
| `vClosedSpatial` | ✓ proved | restart cosine representation |
| `jointTimeDerivClosed` | ~provable | extension from interior to closed |
| `jointSolutionClosed` | ✓ proved | uniform convergence on compact |

Legend: ✓ = proved in the repo, ~provable = follows from existing
infrastructure by straightforward composition, **F2** = genuine frontier.
-/

end ShenWork.Paper2.Theorem11Assembly
