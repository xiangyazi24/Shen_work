/-
  F1 Assembly: wire proved F1 components into unconditional
  `RestartAndGlueWorks p` and update end-to-end theorem.

  ## Chain (all 0 sorry, 0 axiom)

  `IntervalDomainL2JointTimeRegularity p`
    → `intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTime`
    → `intervalDomainClassicalUniquenessL2EnergyMethod_concrete`
    → `GlueExtension.overlapUniqueForPID_of_l2EnergyMethod`
    → `GlueLargeCase.restartAndGlueWorks_of_piecewise`
        (+ `piecewiseClassicalWorks` + `regularityTimeShiftWorks`
         + `timeShiftInitialTraceWorks`)
    → `RestartAndGlueWorks p`

  ## Theorems

  1. `restartAndGlueWorks_of_jointTimeRegularity`: derives
     `RestartAndGlueWorks p` from `IntervalDomainL2JointTimeRegularity p`
     + `PiecewiseClassicalWorks p`.

  2. `paper2_theorem_1_1_reduced`: end-to-end `Theorem_1_1` with
     `hRestart` eliminated — `hjoint` + `hPCW` replace it.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.Paper2.IntervalDomainGlueLargeCase
import ShenWork.Paper2.IntervalDomainPiecewiseGlue
import ShenWork.Paper2.IntervalDomainTimeShift
import ShenWork.Paper2.IntervalDomainGlueExtension
import ShenWork.Paper2.IntervalDomainL2EnergyInequality
import ShenWork.Paper2.IntervalDomainL2UniquenessCertificate
import ShenWork.Paper2.IntervalDomainEndToEnd

open ShenWork.IntervalDomain
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalMildPicard
open ShenWork.Paper2
open ShenWork.Paper2.EndToEnd
open ShenWork.Paper2.RestartExtension
open ShenWork.Paper2.Theorem11Assembly

noncomputable section

namespace ShenWork.Paper2.F1Assembly

/-! ## Theorem 1: RestartAndGlueWorks from joint time regularity

All inputs to `GlueLargeCase.restartAndGlueWorks_of_piecewise` except
`PiecewiseClassicalWorks` are proved unconditionally:
  - `TimeShift.regularityTimeShiftWorks`
  - `GlueExtension.timeShiftInitialTraceWorks`
  - `GlueExtension.overlapUniqueForPID_of_l2EnergyMethod` (from the
    L² energy method, which is derived from `hjoint`)

`PiecewiseClassicalWorks p` (splice regularity) is taken as a hypothesis.
-/

/-- **`RestartAndGlueWorks p` from `IntervalDomainL2JointTimeRegularity p`
+ `PiecewiseClassicalWorks p`.**

Chain:
  hjoint
  → `intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTime`
  → `intervalDomainClassicalUniquenessL2EnergyMethod_concrete`
  → `GlueExtension.overlapUniqueForPID_of_l2EnergyMethod`
  → `GlueLargeCase.restartAndGlueWorks_of_piecewise`
      (with `hPCW`, `regularityTimeShiftWorks`,
       `timeShiftInitialTraceWorks`) -/
theorem restartAndGlueWorks_of_jointTimeRegularity
    (p : CM2Params)
    (hjoint : IntervalDomainL2JointTimeRegularity p)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p) :
    RestartAndGlueWorks p :=
  GlueLargeCase.restartAndGlueWorks_of_piecewise p
    hPCW
    TimeShift.regularityTimeShiftWorks
    (GlueExtension.overlapUniqueForPID_of_l2EnergyMethod
      (intervalDomainClassicalUniquenessL2EnergyMethod_concrete p
        (intervalDomainL2DifferenceEnergyFrontierBuilder_of_jointTime
          hjoint)))
    GlueExtension.timeShiftInitialTraceWorks

/-! ## Theorem 2: End-to-end with `hRestart` eliminated

The existing `paper2_theorem_1_1_endToEnd` takes `hRestart` as an
explicit hypothesis.  We eliminate it: given `hjoint` and `hPCW`, the
restart hypothesis is derived internally via
`restartAndGlueWorks_of_jointTimeRegularity`. -/

/-- **Paper 2 Theorem 1.1 — reduced frontier.**

Compared to `paper2_theorem_1_1_endToEnd`, the `hRestart` hypothesis is
eliminated: `hjoint : IntervalDomainL2JointTimeRegularity p` provides
the overlap uniqueness (via L² energy method) and, together with `hPCW`,
the restart-and-glue extension.

### Remaining genuine hypotheses
- `hQuant` : quantitative local existence delta(M)
- `hjoint` : L² joint time regularity (Leibniz + domination)
- `hPCW` : splice regularity (PiecewiseClassicalWorks)
- `hSupNorm` : interior sup-norm preservation (Lemma 3.1)
- `hPerDatum` : per-datum spectral frontier -/
theorem paper2_theorem_1_1_reduced
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ : 1 ≤ p.γ)
    (hQuant : ∀ M : ℝ, 0 < M → ∃ δ : ℝ, 0 < δ ∧
      ∀ {u₀ : intervalDomain.Point → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
        ∃ u v,
          IsPaper2ClassicalSolution intervalDomain p δ u v ∧
          InitialTrace intervalDomain u₀ u)
    (hjoint : IntervalDomainL2JointTimeRegularity p)
    (hPCW : PiecewiseGlue.PiecewiseClassicalWorks p)
    (hSupNorm : ∀ {M : ℝ}, 0 < M →
      ∀ {u₀}, PositiveInitialDatum intervalDomain u₀ →
        (∀ x, |u₀ x| ≤ M) →
      ∀ {T₀}, 0 < T₀ →
      ∀ {u v},
        IsPaper2ClassicalSolution intervalDomain p T₀ u v →
        InitialTrace intervalDomain u₀ u →
        ∀ t, 0 < t → t < T₀ →
          ∀ x : intervalDomainPoint, |u t x| ≤ M)
    (hPerDatum : ∀ u₀ : intervalDomainPoint → ℝ,
      PositiveInitialDatum intervalDomain u₀ →
        ∃ D : GradientMildSolutionData p u₀,
          PerDatumSpectralFrontier p D) :
    Theorem_1_1 intervalDomain p :=
  paper2_theorem_1_1_endToEnd p hχ ha hb hγ
    hQuant
    (restartAndGlueWorks_of_jointTimeRegularity p hjoint hPCW)
    hSupNorm
    hPerDatum

end ShenWork.Paper2.F1Assembly
