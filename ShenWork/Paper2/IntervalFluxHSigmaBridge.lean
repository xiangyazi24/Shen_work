import ShenWork.Paper2.IntervalBFormHSigmaLinftyL2Smoothing
import ShenWork.Paper2.IntervalSineCoeffL2Bound

/-!
# Positive-time H-sigma smoothing for a bounded flux

This file combines spatial Fourier Bessel with the genuine
`L∞_t ℓ²_k → H^σ_k` divergence-Duhamel estimate.  It removes the
mode-by-mode `ℓ¹` source envelope from the positive-time bootstrap.
-/

noncomputable section

namespace ShenWork.Paper2.IntervalFluxHSigmaBridge

open ShenWork.Paper2.HSigmaScale
open ShenWork.Paper2.BFormHSigmaDuhamelEnergy
open ShenWork.Paper2.BFormHSigmaLinftyMultiplier
open ShenWork.Paper2.BFormHSigmaLinftyL2Smoothing
open ShenWork.Paper2.IntervalDivergenceModeIdentity
open ShenWork.Paper2.IntervalSineCoeffL2Bound

/-- A bounded continuous spatial flux has enough uniform `ℓ²` coefficient
control for divergence-form Duhamel smoothing. -/
theorem hSigmaEnergy_duhamel_sineCoeffs_of_bounded_flux
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    {d : ℝ} (hd : 0 < d) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {Q : ℝ → ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQspace : ∀ τ ∈ Set.Icc (0 : ℝ) s, Continuous (Q τ))
    (hQbound : ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |Q τ x| ≤ B)
    (hcoeffCont : ∀ k, Continuous (fun τ => sineCoeffs (Q τ) k)) :
    MemHSigma σ
        (duhamelEnergyCoeff d (fun k τ => sineCoeffs (Q τ) k) s) ∧
      hSigmaEnergy σ
          (duhamelEnergyCoeff d (fun k τ => sineCoeffs (Q τ) k) s) ≤
        (Classical.choose (linfty_multiplier_bound hσ0 hσ1 d hd)) ^ 2 *
          (16 * B ^ 2) *
            (s ^ ((1 - σ) / 2) / ((1 - σ) / 2)) ^ 2 := by
  apply hSigmaEnergy_duhamel_bound_of_slice_l2
    hσ0 hσ1 hd hs hs1 hcoeffCont
  · intro τ hτ
    exact (sineCoeffs_sq_summable_and_tsum_le
      hB (hQspace τ hτ) (hQbound τ hτ)).1
  · intro τ hτ
    exact (sineCoeffs_sq_summable_and_tsum_le
      hB (hQspace τ hτ) (hQbound τ hτ)).2

#print axioms hSigmaEnergy_duhamel_sineCoeffs_of_bounded_flux

end ShenWork.Paper2.IntervalFluxHSigmaBridge
