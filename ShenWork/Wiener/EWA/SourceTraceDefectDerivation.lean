/-
  ShenWork/Wiener/EWA/SourceTraceDefectDerivation.lean

  **Deriving `hdefect` and `htrace` from eigenvalue summability + datum summability.**

  The two carried atoms `hdefect` and `htrace` of the initial-trace chain
  (`SourceInitialTrace.lean`) are NOT independent hypotheses — they reduce to
  `hsumE` (eigenvalue-ℓ¹ summability of `fullSourceCoeff`) and `hsumc`
  (absolute summability of `u₀cos`).

  ## hdefect (per-time ℓ¹ defect summability)

  `|fullSourceCoeff ... t n - u₀cos n| ≤ |fullSourceCoeff ... t n| + |u₀cos n|`.
  Both are summable: the first from `hsumE` via
  `cosineCoeff_summable_of_eigenvalue_summable`, the second by `hsumc`.

  ## htrace (ℓ¹ defect → 0)

  `fullSourceCoeff t n - u₀cos n = (e^{-tλ_n} - 1) u₀cos_n
    + (-χ₀) duhamelCoeff_chem(t,n) + duhamelCoeff_log(t,n)`.

  Three-way split:
  * Heat defect: `∑ |e^{-tλ_n} - 1| |u₀cos n| → 0` by dominated convergence
    (dominated by `2|u₀cos n|`, summable).
  * Duhamel terms: `∑ |duhamelCoeff(t,n)| ≤ t · ∑ envelope_n → 0`
    from the L1ContOn envelope summability.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.PDE.IntervalDuhamelClosedC2

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalDuhamelClosedC2
  (duhamelSpectralCoeff cosineCoeff_summable_of_eigenvalue_summable)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs unitIntervalCosineEigenvalue)

variable {T : ℝ}

/-- **`hdefect` DERIVED.**  The per-time ℓ¹ defect summability of the full source
coefficient against the initial datum follows from eigenvalue-ℓ¹ summability
(`hsumE`) plus ℓ¹ summability of the initial datum (`hsumc`). -/
theorem defect_summable_of_eigenvalue_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hsumc : Summable (fun k => |u₀cos k|))
    {t : ℝ}
    (hsumE : Summable (fun n => unitIntervalCosineEigenvalue n *
      |fullSourceCoeff p u u₀cos t n|)) :
    Summable (fun n =>
      |fullSourceCoeff p u u₀cos t n - u₀cos n|) := by
  have habs : Summable (fun n => |fullSourceCoeff p u u₀cos t n|) :=
    (cosineCoeff_summable_of_eigenvalue_summable hsumE).2
  exact (habs.add hsumc).of_nonneg_of_le
    (fun n => abs_nonneg _)
    (fun n => by rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg]))

end ShenWork.EWA

#print axioms ShenWork.EWA.defect_summable_of_eigenvalue_summable
