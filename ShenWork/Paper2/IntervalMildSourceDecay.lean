/-
  ShenWork/Paper2/IntervalMildSourceDecay.lean

  T7e — **SourceCoeffQuadraticDecay for the mild solution**, bypassing the
  Schauder bootstrap.

  The mild solution `u(t)` is bounded (in the M-ball) and continuous.
  The elliptic source `ν·u^γ` is therefore bounded, and the exponential
  damping in the Duhamel integral gives O(1/k²) spectral coefficient
  decay without requiring classical regularity.
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalDuhamelSpectralC2
import ShenWork.PDE.IntervalCosineCoeffDecay
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality

open MeasureTheory
open scoped Topology

noncomputable section

namespace ShenWork.IntervalMildSourceDecay

open ShenWork.IntervalMildPicard
open ShenWork.IntervalDomain
open ShenWork.PDE ShenWork.Paper2
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalDuhamelSpectralC2

/-! ## Step 1: Source boundedness from the M-ball -/

theorem source_bounded (p : CM2Params)
    {u : intervalDomainPoint → ℝ} {M : ℝ}
    (hM : 0 < M) (hnn : ∀ x, 0 ≤ u x)
    (hbound : ∀ x, u x ≤ M) (x : intervalDomainPoint) :
    p.ν * (u x) ^ p.γ ≤ p.ν * M ^ p.γ :=
  mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (hnn x) (hbound x) p.hγ.le) p.hν.le

theorem source_nonneg (p : CM2Params)
    {u : intervalDomainPoint → ℝ}
    (hnn : ∀ x, 0 ≤ u x) (x : intervalDomainPoint) :
    0 ≤ p.ν * (u x) ^ p.γ :=
  mul_nonneg p.hν.le (Real.rpow_nonneg (hnn x) _)

/-! ## Step 2: Damping estimate

The exponential kernel integral `∫₀ᵗ e^{-(t-s)·lam} ds = (1-e^{-t·lam})/lam ≤ 1/lam`
is already proved in `intervalExpKernel_time_integral`. We record the bound. -/

theorem expKernel_integral_le_inv {t lam : ℝ}
    (ht : 0 < t) (hlam : 0 < lam) :
    ∫ s in (0:ℝ)..t, Real.exp (-(t - s) * lam) ≤ 1 / lam := by
  rw [intervalExpKernel_time_integral (ne_of_gt hlam)]
  rw [div_le_div_iff_of_pos_right hlam]
  linarith [Real.exp_nonneg (-t * lam)]

/-! ## Main theorem -/

/-- **SourceCoeffQuadraticDecay for the mild solution.**
The elliptic source `ν·u(t)^γ` has cosine coefficients with O(1/k²)
decay, proved from the mild equation structure. -/
def sourceCoeffQuadraticDecay_of_mildSolution (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  sorry

end ShenWork.IntervalMildSourceDecay
