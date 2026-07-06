/-
  ShenWork/Paper2/ChemMildC1etaPositiveTime.lean

  Positive-time assembly wrappers for the intrinsic C1/eta route.
-/
import ShenWork.Paper2.ChemMildC1etaCommonFoldWrappers

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard (GradientMildSolutionData)
open ShenWork.IntervalMildRegularityBootstrap (HasRestartCosineRepresentations)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

namespace ShenWork.Paper2

noncomputable section

/-- Intrinsic common-fold C1/eta route: every positive-time true mild slice has
summable cosine coefficients.  This hides the canonical cutoff representative,
endpoint no-flux transfer, logistic cutoff source, and intrinsic initial-data
packaging behind one stable positive-time interface. -/
theorem gradientMild_trueLift_coeffs_summable_positiveTime_of_initialHolder_intrinsic
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (Dsol : GradientMildSolutionData p u₀)
    (H : HasRestartCosineRepresentations Dsol.T Dsol.u)
    {θ η H₀ : ℝ}
    (hη0 : 0 < η) (hθη : η < θ) (hθlt : θ < (1 / 2 : ℝ))
    (hH₀_nonneg : 0 ≤ H₀)
    (hholder : InitialDatumHolder u₀ θ H₀) :
    ∀ t : ℝ, 0 < t → t < Dsol.T →
      Summable (fun n : ℕ => |cosineCoeffs (intervalDomainLift (Dsol.u t)) n|) := by
  intro t ht htT
  exact
    gradientMild_trueLift_coeffs_summable_of_phase1CutoffRep_initialHolder_intrinsic
      Dsol H hη0 hθη hθlt hH₀_nonneg hholder ht htT

end

end ShenWork.Paper2
