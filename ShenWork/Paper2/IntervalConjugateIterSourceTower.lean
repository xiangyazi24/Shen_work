/-
  ShenWork/Paper2/IntervalConjugateIterSourceTower.lean

  Conjugate (B-form) iterate logistic source `DuhamelSourceTimeC1On` tower.

  Defines the per-level source package aliases and provides the Level 0 base case.
  Level 0 is definitionally `picardIter 0` (both are `S(t)u₀`), so the existing
  `level0Source_timeC1On` applies directly.

  The successor step and limit passage are in separate files.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardLevel0SourceTimeC1On
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalBankInfAndLogSrcWiring

open MeasureTheory Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter HasContinuousSlices)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter conjugatePicardLimit ConjugateMildExistenceData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (level0Source_timeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledChemDivSourceCoeffs)

noncomputable section

namespace ShenWork.Paper2.ConjugateIterSourceTower

/-! ## Type aliases -/

abbrev ConjLogSourceTimeC1On
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (n : ℕ) (c T : ℝ) :=
  DuhamelSourceTimeC1On
    (fun s k => cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ n s)) k)
    c T

abbrev ConjLogSourceTimeC1OnUpTo
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ) (T : ℝ) :=
  ∀ c, 0 < c → c < T → ConjLogSourceTimeC1On p u₀ n c T

/-! ## Level 0 base case

`conjugatePicardIter p u₀ 0 = picardIter p u₀ 0` definitionally (both are
`fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1`),
so the existing `level0Source_timeC1On` applies directly. -/

theorem conjLogLevel0_eq_gradLevel0 (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (s : ℝ) (k : ℕ) :
    cosineCoeffs (logisticLifted p (conjugatePicardIter p u₀ 0 s)) k =
    cosineCoeffs (logisticLifted p (picardIter p u₀ 0 s)) k := by
  rfl

theorem conjLogSourceTimeC1On_level0
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M G1 G2 Udot M₀ : ℝ}
    (hc : 0 < c) (hcT : c < T)
    (hα : 1 ≤ p.α) (ha : 0 ≤ p.a) (hb : 0 ≤ p.b)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    (hG1 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ)) x| ≤ G1)
    (hG2 : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |deriv (deriv (intervalDomainLift (conjugatePicardIter p u₀ 0 σ))) x| ≤ G2)
    (hUdot : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatSecondValue
        σ (ShenWork.IntervalPicardLevel0SourceTimeC1On.heatCoeff u₀) x| ≤ Udot) :
    ConjLogSourceTimeC1On p u₀ 0 c T :=
  level0Source_timeC1On p hc hcT hα ha hb hu₀_cont hu₀_bound hpos hub hG1 hG2 hUdot

#print axioms conjLogSourceTimeC1On_level0

end ShenWork.Paper2.ConjugateIterSourceTower
