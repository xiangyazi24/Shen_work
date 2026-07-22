import ShenWork.Paper1.WholeLineMaximalBUCConstruction
import ShenWork.Paper1.WholeLineChiLargeMaximalStage1
import ShenWork.Paper1.WholeLineChiLargeResidualClosure

/-!
# Unconditional closure of Paper 1 Proposition 1.1

The whole-line maximal BUC construction supplies continuation for every
parameter tuple.  In the residual large-critical window, the nonnegative
local-moment energy estimate supplies Stage 1.  These are exactly the two
components of `WholeLineLargeChiCriticalContinuationBootstrap`.
-/

noncomputable section

namespace ShenWork.Paper1

/-- The residual continuation/bootstrap hypothesis is fully discharged. -/
theorem wholeLineLargeChiCriticalContinuationBootstrap_unconditional :
    WholeLineLargeChiCriticalContinuationBootstrap := by
  intro p _hwindow hχ hcritical
  exact ⟨wholeLineMaximalBUCImport_constructed p,
    wholeLineLargeChiCriticalStage1Producer_nonnegative
      p (zero_le_one.trans hχ) hcritical⟩

/-- Paper 1 Proposition 1.1, with no residual hypotheses and for the entire
committed parameter range. -/
theorem paper1_Proposition_1_1_unconditional : Proposition_1_1 :=
  paper1_Proposition_1_1_of_largeChi_continuationBootstrap
    wholeLineLargeChiCriticalContinuationBootstrap_unconditional

section AxiomAudit

#print axioms wholeLineMaximalBUCImport_constructed
#print axioms wholeLineLargeChiCriticalStage1Producer_nonnegative
#print axioms wholeLineLargeChiCriticalContinuationBootstrap_unconditional
#print axioms paper1_Proposition_1_1_unconditional

end AxiomAudit

end ShenWork.Paper1
