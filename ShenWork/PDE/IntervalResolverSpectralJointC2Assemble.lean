import Mathlib.Analysis.Calculus.SmoothSeries
import ShenWork.PDE.IntervalResolverSpectralJointC2Closed

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Assemble

open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalResolverSpectralJointC2Closed
open ShenWork.IntervalResolverSpectralTimeC2
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)

/-- The `n`th value term in the local two-variable restart series. -/
def resolverSpectralValueTerm
    (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => localRestartCoeff a₀ a (q.1 - offset) n * cosineMode n q.2

/-- Non-circular `contDiff_tsum` assembly for the resolver spectral certificate.

The remaining analytic work is exactly to instantiate the two termwise
`ContDiff` packages and their order `0,1,2` summable iterated-derivative
majorants from the restart coefficient estimates. -/
theorem resolverSpectralJointC2At_of_contDiff_tsum
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (gradTerm : ℕ → ℝ × ℝ → ℝ)
    (vValue vGrad : ℕ → ℕ → ℝ)
    (hValueTerm :
      ∀ n : ℕ,
        ContDiff ℝ (2 : ℕ∞)
          (resolverSpectralValueTerm a₀ a offset n))
    (hValueSumm :
      ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vValue k))
    (hValueBound :
      ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
        ‖iteratedFDeriv ℝ k
          (resolverSpectralValueTerm a₀ a offset n) q‖ ≤ vValue k n)
    (hGradTerm : ∀ n : ℕ, ContDiff ℝ (2 : ℕ∞) (gradTerm n))
    (hGradSumm :
      ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vGrad k))
    (hGradBound :
      ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
        ‖iteratedFDeriv ℝ k (gradTerm n) q‖ ≤ vGrad k n)
    (hGradEq :
      resolverSpectralGradSeries a₀ a offset =ᶠ[𝓝 (s, x)]
        fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q) :
    ResolverSpectralJointC2At a₀ a offset s x := by
  have hValue : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ =>
        ∑' n : ℕ, resolverSpectralValueTerm a₀ a offset n q) :=
    contDiff_tsum
      (𝕜 := ℝ)
      (f := fun n : ℕ => resolverSpectralValueTerm a₀ a offset n)
      (v := vValue)
      hValueTerm hValueSumm hValueBound
  have hGrad : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q) :=
    contDiff_tsum
      (𝕜 := ℝ)
      (f := gradTerm)
      (v := vGrad)
      hGradTerm hGradSumm hGradBound
  refine ⟨?_, ?_⟩
  · simpa [resolverSpectralSeries, resolverSpectralValueTerm] using
      hValue.contDiffAt
  · exact hGrad.contDiffAt.congr_of_eventuallyEq hGradEq

end ShenWork.IntervalResolverSpectralJointC2Assemble
