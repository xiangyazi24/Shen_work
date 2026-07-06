/-
  ShenWork/Paper2/IntervalHuRestartCoeffIdentity.lean

  Coefficient extraction for the restart coefficients selected from
  `HasTimeNeighborhoodSpectralAgreement`.

  This file introduces no new assumptions.
-/
import ShenWork.Paper2.IntervalResolverSourceWindowHuCoeffInputs
import ShenWork.Paper2.IntervalPicardIterateRestart

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalMildTimeDerivContinuity (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalPicardIterateRestart (cosineCoeffs_of_l1_cosineSeries)

noncomputable section

namespace ShenWork.Paper2.ResolverSourceWindowInput

/-- Eigenvalue-weighted summability implies raw `ℓ¹` summability of the same
coefficients, since every Neumann eigenvalue is at least `1`. -/
theorem summable_abs_of_eigenvalue_abs_summable
    {bc : ℕ → ℝ}
    (hbsum : Summable (fun n => unitIntervalCosineEigenvalue n * |bc n|)) :
    Summable (fun n => |bc n|) := by
  exact (ShenWork.IntervalDuhamelClosedC2.cosineCoeff_summable_of_eigenvalue_summable
    hbsum).2

/-- The cosine coefficients of the represented slice are exactly the
`Hu`-selected restart coefficients.  This removes the later finite-cover
obstruction caused by independently chosen local restart charts. -/
theorem cosineCoeffs_eq_huRestartCoeff
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hu : HasTimeNeighborhoodSpectralAgreement T u) :
    ∀ σ, 0 < σ → σ < T → ∀ k,
      cosineCoeffs (intervalDomainLift (u σ)) k = huRestartCoeff Hu σ k := by
  intro σ hσ0 hσT k
  have hagree := huRestartCoeff_agree Hu σ hσ0 hσT
  have hbsum := huRestartCoeff_hbsum Hu σ hσ0 hσT
  have habs : Summable (fun n => |huRestartCoeff Hu σ n|) :=
    summable_abs_of_eigenvalue_abs_summable hbsum
  rw [ShenWork.Paper2.cosineCoeffs_congr_on_Icc hagree k]
  exact cosineCoeffs_of_l1_cosineSeries habs k

end ShenWork.Paper2.ResolverSourceWindowInput
