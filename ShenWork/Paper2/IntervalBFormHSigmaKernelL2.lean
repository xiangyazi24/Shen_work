import ShenWork.Paper2.IntervalSpectralMultiplierBound
import ShenWork.Paper2.IntervalHSigmaScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
  Brick 3 — corrected kernel L² core for the parabolic-smoothing bootstrap.

  ## Correction of the originally-planned B3-full statement

  The originally-planned "B3-full" estimate
    `‖Bduhamel F s‖²_{H^σ} ≤ C·M·s^{(1−σ)/2}`  from the `L²_t L²_x` datum
    `∑_k ∫₀ˢ F_k(τ)² dτ ≤ M`
  is **FALSE** for every `σ > 0`.  Single-mode counterexample (verified):
  freeze all modes except `N`, set `F_N(τ) = √M · g_N(τ)/‖g_N‖_{L²(0,s)}` with
  `g_N(r) = √λ_N exp(−d λ_N (s−τ))`.  Then `∫₀ˢ F_N(τ)² dτ = M` (datum holds) but
  `B_N(s) = √M ‖g_N‖` and `‖g_N‖² = ∫₀ˢ λ_N e^{−2dλ_N r} dr → 1/(2d)`, so
  `(1+λ_N)^σ B_N(s)² → ∞` as `λ_N → ∞`.  The `L²_t L²_x → H^σ_x` map with a
  positive fractional gain simply does not hold; the `B`-divergence kernel only
  has `L²_t L²_x → L²_x` pointwise-in-time smoothing.

  The two TRUE bricks (this file proves the scalar cores of both):

  * **Weighted-source, no `s`-gain** (`σ = 0` exact, general `σ` with weighted RHS):
      `∑_k (1+λ_k)^σ B_k(s)² ≤ (1/(2d)) · ∑_k (1+λ_k)^σ ∫₀ˢ F_k(τ)² dτ`.
    Scalar core: the per-mode kernel-`L²` constant `∫₀ˢ λ e^{−2dλr} dr ≤ 1/(2d)`.

  * **`L∞_t L²_x → H^σ_x` smoothing** (the genuine fractional gain, rate `s^{1−σ}`):
    this is the brick the landed scalar multiplier (θ = (σ+1)/2) is designed for;
    its terminal-singularity scalar core is already in `IntervalBFormHSigmaSmoothing`.

  This file lands the kernel-`L²` constant `∫₀ˢ λ e^{−2dλr} dr ≤ 1/(2d)` exactly,
  as a clean axiom-clean scalar brick.  `d := d1 > 0`.
-/

noncomputable section

namespace ShenWork.Paper2.BFormHSigmaKernelL2

open ShenWork.Paper2.HSigmaScale
open Real intervalIntegral

/-- Antiderivative identity: `r ↦ −exp(−2 d λ r)/(2d)` has derivative
`λ · exp(−2 d λ r)` (the `λ` reappears from the chain rule, the `2d` cancels). -/
theorem hasDerivAt_kernel_antideriv {d lam : ℝ} (hd : 0 < d) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -Real.exp (-(2 * d * lam) * r) / (2 * d))
      (lam * Real.exp (-(2 * d * lam) * r)) r := by
  have harg : HasDerivAt (fun r : ℝ => -(2 * d * lam) * r) (-(2 * d * lam)) r := by
    simpa using (hasDerivAt_id r).const_mul (-(2 * d * lam))
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-(2 * d * lam) * r))
      (Real.exp (-(2 * d * lam) * r) * (-(2 * d * lam))) r := harg.exp
  have hscaled : HasDerivAt (fun r : ℝ => -Real.exp (-(2 * d * lam) * r) / (2 * d))
      ((-(Real.exp (-(2 * d * lam) * r) * (-(2 * d * lam)))) / (2 * d)) r := by
    exact (hexp.neg).div_const (2 * d)
  convert hscaled using 1
  field_simp

/-- **Kernel-`L²` integral, exact value.**  For `d > 0`, `λ ≥ 0`, `s ≥ 0`:
`∫₀ˢ λ · exp(−2 d λ r) dr = (1 − exp(−2 d λ s)) / (2 d)`. -/
theorem integral_kernel_L2_eq {d lam s : ℝ} (hd : 0 < d) :
    (∫ r in (0:ℝ)..s, lam * Real.exp (-(2 * d * lam) * r))
      = (1 - Real.exp (-(2 * d * lam) * s)) / (2 * d) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r : ℝ => -Real.exp (-(2 * d * lam) * r) / (2 * d))
    (fun r _ => hasDerivAt_kernel_antideriv hd r)
    (by
      have : Continuous (fun r : ℝ => lam * Real.exp (-(2 * d * lam) * r)) := by fun_prop
      exact this.intervalIntegrable 0 s)
  rw [hFTC]
  simp only []
  have h0 : Real.exp (-(2 * d * lam) * (0:ℝ)) = 1 := by simp
  rw [h0]
  field_simp
  ring

/-- **Kernel-`L²` bound.**  For `d > 0`, `λ ≥ 0`, `s ≥ 0`:
`∫₀ˢ λ · exp(−2 d λ r) dr ≤ 1 / (2 d)`.  This is the sharp per-mode constant for
the weighted-source `B`-Duhamel estimate (the `(1+λ)^σ` weight does NOT cancel —
see the file docstring for the impossibility of the originally-planned form). -/
theorem integral_kernel_L2_le {d lam s : ℝ} (hd : 0 < d) (_hlam : 0 ≤ lam)
    (_hs : 0 ≤ s) :
    (∫ r in (0:ℝ)..s, lam * Real.exp (-(2 * d * lam) * r)) ≤ 1 / (2 * d) := by
  rw [integral_kernel_L2_eq hd]
  have hexp_nonneg : 0 ≤ Real.exp (-(2 * d * lam) * s) := (Real.exp_pos _).le
  have h2d : 0 < 2 * d := by positivity
  rw [div_le_div_iff₀ h2d h2d]
  nlinarith [hexp_nonneg, Real.exp_pos (-(2 * d * lam) * s)]

/-- **Kernel-`L²` nonnegativity.**  `0 ≤ ∫₀ˢ λ exp(−2dλr) dr` for `λ ≥ 0`, `s ≥ 0`. -/
theorem integral_kernel_L2_nonneg {d lam s : ℝ} (_hd : 0 < d) (hlam : 0 ≤ lam)
    (hs : 0 ≤ s) :
    0 ≤ ∫ r in (0:ℝ)..s, lam * Real.exp (-(2 * d * lam) * r) := by
  apply intervalIntegral.integral_nonneg hs
  intro r _
  have := Real.exp_nonneg (-(2 * d * lam) * r)
  positivity

#print axioms integral_kernel_L2_eq
#print axioms integral_kernel_L2_le
#print axioms integral_kernel_L2_nonneg

end ShenWork.Paper2.BFormHSigmaKernelL2
