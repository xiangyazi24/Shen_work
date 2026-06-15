/-
# Summable majorant for `fullSourceCoeffDot` (Brick 2 of the χ₀<0 u_t construction)

  Absolute summability of the per-mode time-derivative coefficient
  `fullSourceCoeffDot p u u₀cos t n` (SourceTimeRegularity.lean) for interior
  time `t > 0`.

  `fullSourceCoeffDot n = HEAT + (−χ₀)·CHEMderiv + LOGderiv` where
  - HEAT     = `−λₙ·e^{−tλₙ}·u₀cos n`,
  - CHEMderiv = `aₙ(t) − λₙ·duhamelSpectralCoeff a t n`  (chem coeffs),
  - LOGderiv  = same with logistic coeffs.

  Each leg is `|·|`-summable; the triangle inequality dominates
  `|fullSourceCoeffDot|` by the sum of the three legs.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularity

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalSourceCoefficientTimeC1 (duhamelSpectralCoeff_deriv_abs_summable)
open ShenWork.IntervalMildRegularityBootstrap
  (unitIntervalCosineEigenvalue_mul_exp_summable)

/-- **HEAT leg majorant.**  `∑ₙ |−λₙ·e^{−tλₙ}·u₀cos n| < ∞` for `t > 0`,
dominated by `Mu0 · (λₙ·e^{−tλₙ})` via heat smoothing. -/
theorem heatLeg_abs_summable (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => |(-(unitIntervalCosineEigenvalue n)
      * Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n)|) := by
  have hMu0 : 0 ≤ Mu0 := le_trans (abs_nonneg _) (hu0bd 0)
  have hbase := (unitIntervalCosineEigenvalue_mul_exp_summable ht).mul_left Mu0
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hbase
  have hlam_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
    unfold unitIntervalCosineEigenvalue; positivity
  calc |(-(unitIntervalCosineEigenvalue n)
          * Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n)|
      = unitIntervalCosineEigenvalue n
          * Real.exp (-t * unitIntervalCosineEigenvalue n) * |u₀cos n| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hlam_nn,
          abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Mu0 * (unitIntervalCosineEigenvalue n
          * Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
        have hfac_nn : 0 ≤ unitIntervalCosineEigenvalue n
            * Real.exp (-t * unitIntervalCosineEigenvalue n) :=
          mul_nonneg hlam_nn (Real.exp_nonneg _)
        rw [mul_comm Mu0]
        exact mul_le_mul_of_nonneg_left (hu0bd n) hfac_nn

/-- **Summable majorant for `fullSourceCoeffDot`.**  For interior time `t > 0`
the per-mode time-derivative coefficient is absolutely summable.  Triangle-combine
the heat leg (heat smoothing) with the two spectral-Duhamel derivative legs
(the ℓ¹ envelopes of `DuhamelSourceTimeC1`). -/
theorem fullSourceCoeffDot_abs_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n => |fullSourceCoeffDot p u u₀cos t n|) := by
  -- The three legs, each `|·|`-summable.
  have hheat := heatLeg_abs_summable u₀cos hu0bd ht
  have hchemD : Summable (fun n => |(-p.χ₀) *
      (coupledChemDivSourceCoeffs p u t n - unitIntervalCosineEigenvalue n
        * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)|) := by
    simpa [abs_mul] using
      (duhamelSpectralCoeff_deriv_abs_summable hchem ht).mul_left |(-p.χ₀)|
  have hlogD := duhamelSpectralCoeff_deriv_abs_summable hlog ht
  -- Triangle-dominate `|fullSourceCoeffDot|` by the sum of the three legs.
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    ((hheat.add hchemD).add hlogD)
  exact (abs_add_three _ _ _)

end ShenWork.EWA
