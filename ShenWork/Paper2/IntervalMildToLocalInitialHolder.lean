/-
  ShenWork/Paper2/IntervalMildToLocalInitialHolder.lean

  Initial-Holder entry points for the mild-to-local-existence bridge.
-/
import ShenWork.Paper2.IntervalMildToLocalExistence
import ShenWork.Paper2.IntervalInitialHolderFoldedKernel
import ShenWork.Paper2.IntervalMildPicardThreshold

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.IntervalDomainExistence (RegularityBootstrap)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap
  (GradientMildHalfStepRestartData HasRestartCosineRepresentations)
open ShenWork.Paper2
  (InitialDatumHolder InitialTrace IsPaper2ClassicalSolution PositiveInitialDatum
   initialDatumHolder_continuous)

namespace ShenWork.IntervalMildToLocalExistence

noncomputable section

/-- Initial Holder data discharge the uniform initial-approach input consumed by
the gradient mild local-existence bridge. -/
theorem gradientMildInitialApproach_of_initialDatumHolder
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    {θ H0 : ℝ} (hθ0 : 0 < θ) (hH0 : 0 ≤ H0)
    (hholder : InitialDatumHolder u0 θ H0) :
    GradientMildInitialApproach p D :=
  ShenWork.IntervalMildPicardThreshold.gradientMildSolutionData_initialApproach
    p (initialDatumHolder_continuous hθ0 hH0 hholder) D

/-- Restart-cosine `RegularityBootstrap` from the reduced frontier core, with
initial approach produced from initial Holder data. -/
theorem
    regularityBootstrap_of_restartCosine_initialHolder_frontierCore
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    {θ H0 : ℝ} (hθ0 : 0 < θ) (hH0 : 0 ≤ H0)
    (hholder : InitialDatumHolder u0 θ H0)
    (C : GradientMildClassicalFrontierCoreData p D) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMildSolutionData_of_restartCosineRepresentations_and_frontierCore
    p D H
    (gradientMildInitialApproach_of_initialDatumHolder p D hθ0 hH0 hholder)
    C

/-- Half-step restart `RegularityBootstrap` from the reduced frontier core, with
initial approach produced from initial Holder data. -/
theorem
    regularityBootstrap_of_halfStepRestart_initialHolder_frontierCore
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    {θ H0 : ℝ} (hθ0 : 0 < θ) (hH0 : 0 ≤ H0)
    (hholder : InitialDatumHolder u0 θ H0)
    (C : GradientMildClassicalFrontierCoreData p D) :
    RegularityBootstrap p D.T u0 D.u :=
  regularityBootstrap_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
    p D R
    (gradientMildInitialApproach_of_initialDatumHolder p D hθ0 hH0 hholder)
    C

/-- Restart-cosine local existence from the reduced frontier core, with initial
approach produced from initial Holder data. -/
theorem
    localExistence_of_restartCosine_initialHolder_frontierCore
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (H : HasRestartCosineRepresentations D.T D.u)
    {θ H0 : ℝ} (hθ0 : 0 < θ) (hH0 : 0 ≤ H0)
    (hholder : InitialDatumHolder u0 θ H0)
    (C : GradientMildClassicalFrontierCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_of_restartCosineRepresentations_and_frontierCore
    p hu0 D H
    (gradientMildInitialApproach_of_initialDatumHolder p D hθ0 hH0 hholder)
    C

/-- Half-step restart local existence from the reduced frontier core, with
initial approach produced from initial Holder data. -/
theorem
    localExistence_of_halfStepRestart_initialHolder_frontierCore
    (p : CM2Params) {u0 : intervalDomainPoint → ℝ}
    (hu0 : PositiveInitialDatum intervalDomain u0)
    (D : GradientMildSolutionData p u0)
    (R : GradientMildHalfStepRestartData D)
    {θ H0 : ℝ} (hθ0 : 0 < θ) (hH0 : 0 ≤ H0)
    (hholder : InitialDatumHolder u0 θ H0)
    (C : GradientMildClassicalFrontierCoreData p D) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
        InitialTrace intervalDomain u0 u :=
  localExistence_of_gradientMildSolutionData_of_halfStepRestartData_and_frontierCore
    p hu0 D R
    (gradientMildInitialApproach_of_initialDatumHolder p D hθ0 hH0 hholder)
    C

end

end ShenWork.IntervalMildToLocalExistence
