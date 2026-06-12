import ShenWork.PDE.IntervalResolverJointC2
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1
  cosineCoeffSeries_contDiff_two)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalMildRegularityBootstrap (restartDuhamelCoeff
  restartDuhamelCoeff_eigenvalue_summable)
open ShenWork.IntervalResolverJointC2
open ShenWork.CosineSpectrum (cosineMode)
open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Producer

/-- Local time shift used by the restart-series joint regularity producer. -/
def restartShift (offset : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun q => (q.1 - offset, q.2)

theorem restartShift_continuous (offset : ℝ) :
    Continuous (restartShift offset) := by
  unfold restartShift
  exact (continuous_fst.sub continuous_const).prodMk continuous_snd

/-- The committed restart majorant in the `localRestartCoeff` spelling. -/
theorem localRestartCoeff_eigenvalue_summable
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    Summable (fun n : ℕ =>
      unitIntervalCosineEigenvalue n * |localRestartCoeff a₀ a τ n|) := by
  simpa [restartDuhamelCoeff, localRestartCoeff] using
    restartDuhamelCoeff_eigenvalue_summable (τ := τ) (M := M)
      (a₀ := a₀) (a := a) hτ ha₀ src

/-- Spatial `C²` of every positive-time restart slice, from the committed
`∑ λₙ |cₙ|` majorant. -/
theorem localRestartCoeff_cosineSeries_contDiff_two
    {τ M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < τ)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    ContDiff ℝ 2
      (fun y : ℝ => ∑' n : ℕ,
        localRestartCoeff a₀ a τ n * cosineMode n y) :=
  cosineCoeffSeries_contDiff_two
    (localRestartCoeff_eigenvalue_summable hτ ha₀ src)

/-- The spatial slice of `resolverSpectralSeries` is `C²` at positive restart
time. -/
theorem resolverSpectralSeries_spatial_contDiff_two
    {s offset M : ℝ} {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ}
    (hτ : 0 < s - offset)
    (ha₀ : ∀ n, |a₀ n| ≤ M)
    (src : DuhamelSourceTimeC1 a) :
    ContDiff ℝ 2
      (fun y : ℝ => resolverSpectralSeries a₀ a offset (s, y)) := by
  simpa [resolverSpectralSeries] using
    localRestartCoeff_cosineSeries_contDiff_two
      (τ := s - offset) (M := M) (a₀ := a₀) (a := a)
      hτ ha₀ src

end ShenWork.IntervalResolverSpectralJointC2Producer
