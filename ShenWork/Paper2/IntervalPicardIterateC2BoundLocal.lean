/-
  ShenWork/Paper2/IntervalPicardIterateC2BoundLocal.lean

  **Tower campaign stage 1 — File C (item 7).**

  Local-witness variant of the next-iterate second-derivative sup bound
  `iterate_abs_deriv2_le`.  The source package is the `ShiftedSourceWitness` (read
  only on `[0, t/2]`); the explicit `M₁·eigExpWeight(t/2) + C₂·(t/2)^{1/4}·Benv`
  bound for the CANONICAL `restartIterateCoeff` series follows because the witness
  agrees with the canonical σ-shifted source on `[0, t/2]`
  (`duhamelSpectralCoeff_congr_on_Icc`, File A), so the two restart coefficient
  series coincide termwise, and the witness-fed
  `restartSeries_abs_deriv2_le` (family-generic) bound transfers.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalPicardIterateRestartLocal

open MeasureTheory Filter Topology
open scoped Real
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1 duhamelSpectralCoeff)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff)
open ShenWork.IntervalHomogeneousQuantBound (eigExpWeight)
open ShenWork.IntervalPicardIterateC2Bound (restartIterateCoeff restartSeries_abs_deriv2_le)
open ShenWork.IntervalPicardIterateUniform (Benv)
open ShenWork.IntervalDuhamelSourceShift (duhamelSpectralCoeff_congr_on_Icc)
open ShenWork.IntervalPicardIterateRestartLocal
  (ShiftedSourceWitness canonicalShiftedSource)

noncomputable section

namespace ShenWork.IntervalPicardIterateC2BoundLocal

/-- **(7) Witness variant of `iterate_abs_deriv2_le`.**
The explicit second spatial-derivative sup bound for the next-iterate restart
series, with the canonical σ-shifted logistic source package replaced by a
`ShiftedSourceWitness`.  The conclusion is the *canonical* `restartIterateCoeff`
series (so it slots into the C² assembler unchanged); the witness only enters the
estimate, transferred via the `[0, t/2]` coefficient congruence. -/
theorem iterate_abs_deriv2_le_of_shiftedWitness
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (n : ℕ)
    {t M M₁ A₂ : ℝ} (ht : 0 < t) (hBenv : 0 ≤ Benv p M A₂ t)
    (hM₁ : ∀ k,
      |cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))) k| ≤ M₁)
    (W : ShiftedSourceWitness p u₀ n t M A₂)
    (x : ℝ) :
    |deriv (deriv (fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x)) x|
      ≤ M₁ * eigExpWeight (t / 2)
        + (2 * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ ((3 : ℝ) / 2)) /
            Real.pi ^ ((3 : ℝ) / 2)) * (t / 2) ^ ((1 : ℝ) / 4) * Benv p M A₂ t := by
  have hτ : 0 < t / 2 := by positivity
  have hτnn : (0 : ℝ) ≤ t / 2 := le_of_lt hτ
  -- σ-continuity of each witness coefficient (from time-C¹).
  have hacont : ∀ k, Continuous (fun σ => W.a σ k) := fun k =>
    continuous_iff_continuousAt.2 (fun σ => (W.src.hderiv σ k).continuousAt)
  -- The witness restart series coincides termwise with the canonical one
  -- (coefficients read the source only on [0, t/2], where the witness agrees).
  have hcoeff : ∀ k,
      restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
          W.a (t / 2) k
        = restartIterateCoeff p u₀ n t k := by
    intro k
    have hcong := duhamelSpectralCoeff_congr_on_Icc (a := W.a)
      (a' := canonicalShiftedSource p u₀ n t) hτnn
      (fun s hs m => W.hagree_window s hs m) k
    simp only [restartIterateCoeff, restartDuhamelCoeff]
    rw [hcong]
    rfl
  -- Witness-fed generic second-derivative bound.
  have hbound := restartSeries_abs_deriv2_le
    (a₀ := cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
    (a := W.a) (Benv := Benv p M A₂ t)
    hτ hBenv hM₁ W.src W.hdecay hacont x
  -- Transfer the bound along the coefficient identity.
  have hfun : (fun x => ∑' k,
        restartDuhamelCoeff
          (cosineCoeffs (intervalDomainLift (picardIter p u₀ (n + 1) (t / 2))))
          W.a (t / 2) k * cosineMode k x)
      = fun x => ∑' k, restartIterateCoeff p u₀ n t k * cosineMode k x := by
    funext x
    exact tsum_congr (fun k => by rw [hcoeff k])
  rw [hfun] at hbound
  exact hbound

end ShenWork.IntervalPicardIterateC2BoundLocal
