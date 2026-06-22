import ShenWork.Paper2.Brick2ShiftedGlobalize
import ShenWork.Paper2.IntervalMildRegularityBootstrap
import ShenWork.PDE.IntervalCoupledSourceTimeC1

/-!
# Chem-div half-step wiring — Bricks 1, 4, and the χ₀<0 END GATE feed

Bricks 1/4/5 of the χ₀<0 gradient-path route, built on the landed Brick 2
(`duhamelSourceTimeC1_of_shifted_On`).

* **Brick 1** (`chemDivShiftedSource_duhamelSourceTimeC1_of_windowOn`): instantiate
  Brick 2 at a windowed chem-div EWA package, producing the GLOBAL
  `DuhamelSourceTimeC1` for the soft-clamped `t/2`-shifted chem-div source family.
* **Brick 4** (`gradientMildHalfStepRestartData_of_chemDivSourceData`): the chem-div
  analogue of `gradientMildHalfStepRestartData_of_logisticSourceData`.  It packages
  the per-`t` windowed EWA deliverables and the carried restart-series agreement
  into a `GradientMildHalfStepRestartData`, the `src` leg supplied by Brick 1.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalDuhamelSourceTimeC1On
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemDivSourceCoeffs)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildRegularityBootstrap
  (restartDuhamelCoeff gradientMildHalfStepInitialCoeff GradientMildHalfStepRestartData)
open ShenWork.IntervalTimeSoftClamp

noncomputable section

namespace ShenWork.IntervalChemDivHalfStepWiring

variable {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}

/-- **Brick 1 — global shifted chem-div source from a windowed EWA package.**

Instantiate Brick 2 (`duhamelSourceTimeC1_of_shifted_On`) at a windowed chem-div
source package on `[c', d']` with `τ := t/2`.  The resulting GLOBAL
`DuhamelSourceTimeC1` family is the soft-clamped `t/2`-shifted chem-div source
`σ ↦ coupledChemDivSourceCoeffs p u (φ c' c d d' (t/2 + σ))`. -/
noncomputable def chemDivShiftedSource_duhamelSourceTimeC1_of_windowOn
    {t c' c d d' : ℝ}
    (src : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) c' d')
    (hc' : c' < c) (hcd : c ≤ d) (hd' : d < d') :
    DuhamelSourceTimeC1
      (fun σ k => coupledChemDivSourceCoeffs p u (φ c' c d d' (t / 2 + σ)) k) :=
  duhamelSourceTimeC1_of_shifted_On (τ := t / 2) src hc' hcd hd'

/-- Per-`t` windowed chem-div source data plus the carried restart agreement —
the chem-div analogue of `GradientMildHalfStepLogisticSourceData`.

The source-regularity leg is the committed *windowed* EWA deliverable
`DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) (c' t) (d' t)` (off the
`t=0` wall, with `0 < c' t < c t ≤ d t < d' t`); the `t/2`-shifted, soft-clamped
global package is produced internally by Brick 1.  The restart-series agreement
`hagree` is carried (the genuinely algebraic restart obligation). -/
structure ChemDivHalfStepSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (u : ℝ → intervalDomainPoint → ℝ) where
  c' : ℝ → ℝ
  c : ℝ → ℝ
  d : ℝ → ℝ
  d' : ℝ → ℝ
  hc' : ∀ t, 0 < t → t < D.T → c' t < c t
  hcd : ∀ t, 0 < t → t < D.T → c t ≤ d t
  hd' : ∀ t, 0 < t → t < D.T → d t < d' t
  win : ∀ t, 0 < t → t < D.T →
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) (c' t) (d' t)
  hagree : ∀ t, 0 < t → t < D.T →
    Set.EqOn (intervalDomainLift (D.u t))
      (fun x : ℝ =>
        ∑' n : ℕ,
          restartDuhamelCoeff (gradientMildHalfStepInitialCoeff D t)
            (fun σ n =>
              coupledChemDivSourceCoeffs p u
                (φ (c' t) (c t) (d t) (d' t) (t / 2 + σ)) n)
            (t / 2) n * cosineMode n x)
      (Set.Icc (0 : ℝ) 1)

/-- **Brick 4 — chem-div half-step restart data.**

The chem-div analogue of `gradientMildHalfStepRestartData_of_logisticSourceData`:
the `src` field is the GLOBAL soft-clamped shifted chem-div source produced by
Brick 1 from the per-`t` windowed EWA deliverable; `hagree` is carried. -/
noncomputable def gradientMildHalfStepRestartData_of_chemDivSourceData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : ChemDivHalfStepSourceData D u) :
    GradientMildHalfStepRestartData D where
  a := fun t σ n =>
    coupledChemDivSourceCoeffs p u
      (φ (S.c' t) (S.c t) (S.d t) (S.d' t) (t / 2 + σ)) n
  src := by
    intro t ht htT
    exact chemDivShiftedSource_duhamelSourceTimeC1_of_windowOn (t := t)
      (src := S.win t ht htT) (S.hc' t ht htT) (S.hcd t ht htT) (S.hd' t ht htT)
  hagree := S.hagree

end ShenWork.IntervalChemDivHalfStepWiring

#print axioms
  ShenWork.IntervalChemDivHalfStepWiring.chemDivShiftedSource_duhamelSourceTimeC1_of_windowOn
#print axioms
  ShenWork.IntervalChemDivHalfStepWiring.gradientMildHalfStepRestartData_of_chemDivSourceData
