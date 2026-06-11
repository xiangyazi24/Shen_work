import ShenWork.Paper2.IntervalPicardIterateTimeC1
import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint
import ShenWork.Paper2.IntervalPicardLimitK1WeakEndpoint

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildPicardRegularity
  (logisticSourceFun)
open ShenWork.IntervalPicardIterateTimeC1
  (restartFieldTimeDeriv logisticSourceDot)
open ShenWork.IntervalPicardLimitK1WeakEndpoint
  (restartCosineSeries_hasDerivWithinAt_time_bdd_on)

noncomputable section

namespace ShenWork.IntervalPicardIterateTimeC1Endpoint

/-- Window-local coefficient continuity extracted from `DuhamelSourceTimeC1On`. -/
theorem source_coeff_continuousOn_of_timeC1On
    {a : ℝ → ℕ → ℝ} {W : ℝ} (src : DuhamelSourceTimeC1On a 0 W) (n : ℕ) :
    ContinuousOn (fun s : ℝ => a s n) (Set.Icc (0 : ℝ) W) := by
  intro s hs
  exact (src.hderiv s hs n).continuousWithinAt

/-- One-sided version of the pointwise logistic time chain rule. -/
theorem logisticSourceFun_hasDerivWithinAt_time
    {a b α : ℝ} (_hα : 0 < α)
    {f : ℝ → ℝ} {f' σ : ℝ} {S : Set ℝ}
    (hf_pos : 0 < f σ)
    (hf_deriv : HasDerivWithinAt f f' S σ) :
    HasDerivWithinAt (fun r => f r * (a - b * (f r) ^ α))
      (f' * (a - b * (1 + α) * (f σ) ^ α)) S σ := by
  have hf_ne : f σ ≠ 0 := ne_of_gt hf_pos
  have hpow : HasDerivWithinAt (fun r => (f r) ^ α)
      (f' * α * (f σ) ^ (α - 1)) S σ :=
    hf_deriv.rpow_const (Or.inl hf_ne)
  have hh_deriv : HasDerivWithinAt (fun r => a - b * (f r) ^ α)
      (0 - b * (f' * α * (f σ) ^ (α - 1))) S σ :=
    (hasDerivAt_const σ a).hasDerivWithinAt.sub (hpow.const_mul b)
  have hprod := hf_deriv.mul hh_deriv
  suffices heq : f' * (a - b * (f σ) ^ α) +
      f σ * (0 - b * (f' * α * (f σ) ^ (α - 1))) =
      f' * (a - b * (1 + α) * (f σ) ^ α) by
    rwa [heq] at hprod
  have hrpow : f σ * (f σ) ^ (α - 1) = (f σ) ^ α := by
    rw [mul_comm, ← Real.rpow_add_one hf_ne]
    congr 1
    ring
  linear_combination f' * (-b * α) * hrpow

/-- Shifted closed-window field derivative.

This is the non-circular W8e composition step: differentiate the coefficient
series in `τ`, then compose with `s ↦ s - offset`.  The explicit `hshift`
assumption is exactly what is needed to use the coefficient-time atom on the
physical closed window. -/
theorem restartField_hasDerivWithinAt_endpoint_shift
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (_hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    {a' σ : ℝ} (ha'pos : 0 < a') (ha'τ : a' ≤ σ - offset)
    (hτW : σ - offset ≤ W) (hσ : σ ∈ Set.Icc a' W)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc a' W) (Set.Icc a' W))
    (hagree : ∀ s ∈ Set.Icc a' W, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun r => intervalDomainLift (w r) x)
      (restartFieldTimeDeriv a₀ a offset σ x) (Set.Icc a' W) σ := by
  have hcont_a : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 W) :=
    source_coeff_continuousOn_of_timeC1On src
  have hseries : HasDerivWithinAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (restartFieldTimeDeriv a₀ a offset σ x)
      (Set.Icc a' W) (σ - offset) := by
    simpa [restartFieldTimeDeriv] using
      restartCosineSeries_hasDerivWithinAt_time_bdd_on
        (a₀ := a₀) (M := M₀) ha₀ src hcont_a ha'pos ha'τ hτW x
  have hlin : HasDerivWithinAt (fun r : ℝ => r - offset) 1
      (Set.Icc a' W) σ := by
    exact ((hasDerivAt_id σ).sub_const offset).hasDerivWithinAt
  have hcomp : HasDerivWithinAt
      ((fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x) ∘
        fun r : ℝ => r - offset)
      (restartFieldTimeDeriv a₀ a offset σ x) (Set.Icc a' W) σ := by
    simpa [one_mul] using hseries.comp σ hlin hshift
  exact hcomp.congr_of_mem (fun r hr => hagree r hr ⟨x, hx⟩) hσ

/-- Shifted closed-window field derivative with distinct physical and coefficient
windows.

The coefficient time `τ = σ - offset` is differentiated on `[aτ, W]`, while the
represented physical field is restricted to `[lo, hi]`. -/
theorem restartField_hasDerivWithinAt_endpoint_shift_window
    {w : ℝ → intervalDomainPoint → ℝ}
    {a₀ : ℕ → ℝ} {M₀ : ℝ} (_hM₀ : 0 ≤ M₀) (ha₀ : ∀ n, |a₀ n| ≤ M₀)
    {a : ℝ → ℕ → ℝ} {offset W lo hi aτ σ : ℝ}
    (src : DuhamelSourceTimeC1On a 0 W)
    (haτpos : 0 < aτ) (hτmem : σ - offset ∈ Set.Icc aτ W)
    (hσ : σ ∈ Set.Icc lo hi)
    (hshift : Set.MapsTo (fun s : ℝ => s - offset)
      (Set.Icc lo hi) (Set.Icc aτ W))
    (hagree : ∀ s ∈ Set.Icc lo hi, ∀ x : intervalDomainPoint,
      intervalDomainLift (w s) x.1 = ∑' n,
        localRestartCoeff a₀ a (s - offset) n * cosineMode n x.1)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun r => intervalDomainLift (w r) x)
      (restartFieldTimeDeriv a₀ a offset σ x) (Set.Icc lo hi) σ := by
  have hcont_a : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 W) :=
    source_coeff_continuousOn_of_timeC1On src
  have hseries : HasDerivWithinAt
      (fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x)
      (restartFieldTimeDeriv a₀ a offset σ x)
      (Set.Icc aτ W) (σ - offset) := by
    simpa [restartFieldTimeDeriv] using
      restartCosineSeries_hasDerivWithinAt_time_bdd_on
        (a₀ := a₀) (M := M₀) ha₀ src hcont_a haτpos hτmem.1 hτmem.2 x
  have hlin : HasDerivWithinAt (fun r : ℝ => r - offset) 1
      (Set.Icc lo hi) σ :=
    ((hasDerivAt_id σ).sub_const offset).hasDerivWithinAt
  have hcomp : HasDerivWithinAt
      ((fun τ => ∑' n, localRestartCoeff a₀ a τ n * cosineMode n x) ∘
        fun r : ℝ => r - offset)
      (restartFieldTimeDeriv a₀ a offset σ x) (Set.Icc lo hi) σ := by
    simpa [one_mul] using hseries.comp σ hlin hshift
  exact hcomp.congr_of_mem (fun r hr => hagree r hr ⟨x, hx⟩) hσ

/-!
The requested theorem
`logisticSource_adot_hasDerivWithinAt_endpoint` cannot be proved from the stated
hypotheses as written.  The endpoint series atom
`restartCosineSeries_hasDerivWithinAt_time_bdd_on` applies to the coefficient
time variable `τ` with assumptions `0 < a'`, `a' ≤ τ`, and `τ ≤ W`.

In the requested statement, the represented field is evaluated at coefficient
time `τ = s - offset`, but the closed window assumptions only give
`s ∈ Icc a' W`.  They do not imply `0 ≤ s - offset`, `a' ≤ s - offset`, or
`s - offset ≤ W`.  Consequently the field derivative step cannot be assembled
without an additional shifted-window hypothesis such as
`Set.MapsTo (fun s => s - offset) (Set.Icc a' W) (Set.Icc a' W)`, or the
special case `offset = 0`.
-/

end ShenWork.IntervalPicardIterateTimeC1Endpoint
