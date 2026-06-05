/-
  G4 remaining fields: time differentiability of the mild solution from
  spectral neighborhood agreement + G4i.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalSourceCoefficientTimeC1
import ShenWork.Paper2.IntervalMildRegularityBootstrap

open ShenWork.IntervalDomain
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalMildRegularityBootstrap
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff
  restartCosineSeries_hasDerivAt_time)
open Filter Topology

noncomputable section

namespace ShenWork.IntervalMildTimeRegularity

/-- Time differentiability of the mild solution at an interior point,
given spectral agreement in a neighborhood.

If `u s x = ∑' cₙ(s) cos(nπx)` holds for all `s` near `t₀` (with
coefficients from a restart cosine representation), then G4i gives
`HasDerivAt` for the series, which transfers to `u` by `eventuallyEq`. -/
theorem mildSolution_differentiableAt_time
    {u : ℝ → intervalDomainPoint → ℝ}
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    {a₀ : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (ha₀ : ∀ n, |a₀ n| ≤ M)
    {a : ℝ → ℕ → ℝ} (src : DuhamelSourceTimeC1 a)
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀)
    {offset : ℝ}
    (hagree_nhd : ∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
      u s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x.1)
    (hoffset : t₀ - offset = τ₀)
    (x : intervalDomainPoint) :
    DifferentiableAt ℝ (fun s => u s x) t₀ := by
  have hspec := restartCosineSeries_hasDerivAt_time hM ha₀ src hτ₀ x.1
  have hshift : HasDerivAt
      (fun s => ∑' n, localRestartCoeff a₀ a (s - offset) n *
        cosineMode n x.1)
      (∑' n, (a τ₀ n - unitIntervalCosineEigenvalue n *
        localRestartCoeff a₀ a τ₀ n) * cosineMode n x.1) t₀ := by
    have : HasDerivAt (· - offset) 1 t₀ :=
      (hasDerivAt_id t₀).add_const (-offset)
    rw [← hoffset] at hspec
    have hcomp := hspec.scomp t₀ this
    simp only [smul_eq_mul, one_mul, hoffset] at hcomp
    exact hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.refl _ _)
  exact (hshift.congr_of_eventuallyEq
    (hagree_nhd.mono (fun s hs => (hs x)))).differentiableAt

end ShenWork.IntervalMildTimeRegularity
