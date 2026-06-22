import ShenWork.Paper2.Brick4ChemDivHalfStep
import ShenWork.Paper2.IntervalMildToLocalExistence

/-!
# Brick 5 — the χ₀<0 END GATE

Wires the chem-div half-step restart data (Brick 4, built on Brick 2) into the
source-agnostic classical-regularity engine
`isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData`.

If this compiles, χ₀<0 `IsPaper2ClassicalSolution` is produced from:
* the gradient mild data `D`,
* the chem-div half-step source data `S` (windowed EWA deliverable + carried
  restart agreement) — whose global `src` leg is the soft-clamped shifted
  chem-div `DuhamelSourceTimeC1` of Brick 1/2,
* the remaining classical core `C` (carrying `hpde_u` with `−χ₀·chemotaxisDiv`
  for ALL `χ₀`, including `χ₀<0`, via the gradient `hpde_u` field).

No `sorry`, no `axiom`, no `native_decide`.
-/

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.Paper2 (IsPaper2ClassicalSolution)
open ShenWork.IntervalMildToClassical (mildChemicalConcentration)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildToLocalExistence
open ShenWork.IntervalChemDivHalfStepWiring

noncomputable section

namespace ShenWork.IntervalChemDivEndGate

/-- **END GATE (χ₀<0).**  From gradient mild data `D`, chem-div half-step source
data `S` (Brick 4 ⟸ Brick 2), and the remaining classical core `C`, produce the
full `IsPaper2ClassicalSolution` package.  The `hpde_u` core field already carries
`−p.χ₀·chemotaxisDiv` for ALL `p.χ₀`, so this is unconditional in the sign of χ₀;
the chem-div source-regularity leg is supplied through the gradient path. -/
theorem isPaper2ClassicalSolution_of_chemDivSourceData_chiNeg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (S : ChemDivHalfStepSourceData D D.u)
    (C : GradientMildClassicalCoreData p D) :
    IsPaper2ClassicalSolution intervalDomain p D.T D.u
      (mildChemicalConcentration p D.u) :=
  isPaper2ClassicalSolution_of_gradientMildSolutionData_of_halfStepRestartData
    p D (gradientMildHalfStepRestartData_of_chemDivSourceData D S) C

end ShenWork.IntervalChemDivEndGate

#print axioms
  ShenWork.IntervalChemDivEndGate.isPaper2ClassicalSolution_of_chemDivSourceData_chiNeg
