import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import ShenWork.PDE.IntervalResolverSpectralJointC2Closed

open Filter Topology Set

noncomputable section

namespace ShenWork.IntervalResolverSpectralJointC2Cutoff

open ShenWork.IntervalResolverJointC2
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)

/-- Smooth right cutoff equal to `0` on `(-∞, c']` and `1` on `[c, ∞)`. -/
def smoothRightCutoff (c' c : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition ((c - c')⁻¹ * (t - c'))

theorem smoothRightCutoff_contDiff {c' c : ℝ} :
    ContDiff ℝ (2 : ℕ∞) (smoothRightCutoff c' c) := by
  unfold smoothRightCutoff
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem smoothRightCutoff_eq_zero_of_le {c' c t : ℝ} (hc : c' < c)
    (ht : t ≤ c') :
    smoothRightCutoff c' c t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos
    (inv_nonneg.2 (sub_pos.2 hc).le) (sub_nonpos.2 ht)

theorem smoothRightCutoff_eq_one_of_ge {c' c t : ℝ} (hc : c' < c)
    (ht : c ≤ t) :
    smoothRightCutoff c' c t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hpos : 0 < c - c' := sub_pos.2 hc
  have hle : c - c' ≤ t - c' := by linarith
  calc 1
      = (c - c')⁻¹ * (c - c') := by
          field_simp [ne_of_gt hpos]
    _ ≤ (c - c')⁻¹ * (t - c') :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hpos.le)

theorem smoothRightCutoff_eventually_eq_one {c' c s : ℝ}
    (hc : c' < c) (hs : c < s) :
    smoothRightCutoff c' c =ᶠ[𝓝 s] fun _ : ℝ => 1 := by
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact smoothRightCutoff_eq_one_of_ge hc (le_of_lt ht)

/-- Cutoff-localized value term. -/
def cutoffValueTerm
    (φ : ℝ → ℝ) (a₀ : ℕ → ℝ) (a : ℝ → ℕ → ℝ) (offset : ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * localRestartCoeff a₀ a (q.1 - offset) n *
    cosineMode n q.2

/-- Cutoff-localized gradient term. -/
def cutoffGradTerm (φ : ℝ → ℝ) (gradTerm : ℕ → ℝ × ℝ → ℝ)
    (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => φ q.1 * gradTerm n q

/-- Local `ResolverSpectralJointC2At` from global `contDiff_tsum` applied after
inserting a smooth time cutoff equal to one near the target point. -/
theorem resolverSpectralJointC2At_of_smooth_cutoff_contDiff_tsum
    {a₀ : ℕ → ℝ} {a : ℝ → ℕ → ℝ} {offset s x : ℝ}
    (φ : ℝ → ℝ) (gradTerm : ℕ → ℝ × ℝ → ℝ)
    (vValue vGrad : ℕ → ℕ → ℝ)
    (hφ_one : φ =ᶠ[𝓝 s] fun _ : ℝ => 1)
    (hValueTerm :
      ∀ n : ℕ,
        ContDiff ℝ (2 : ℕ∞) (cutoffValueTerm φ a₀ a offset n))
    (hValueSumm :
      ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vValue k))
    (hValueBound :
      ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
        ‖iteratedFDeriv ℝ k (cutoffValueTerm φ a₀ a offset n) q‖ ≤
          vValue k n)
    (hGradTerm : ∀ n : ℕ, ContDiff ℝ (2 : ℕ∞) (cutoffGradTerm φ gradTerm n))
    (hGradSumm :
      ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) → Summable (vGrad k))
    (hGradBound :
      ∀ (k n : ℕ) (q : ℝ × ℝ), (k : ℕ∞) ≤ (2 : ℕ∞) →
        ‖iteratedFDeriv ℝ k (cutoffGradTerm φ gradTerm n) q‖ ≤
          vGrad k n)
    (hGradEq :
      resolverSpectralGradSeries a₀ a offset =ᶠ[𝓝 (s, x)]
        fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q) :
    ResolverSpectralJointC2At a₀ a offset s x := by
  have hφ_prod :
      (fun q : ℝ × ℝ => φ q.1) =ᶠ[𝓝 (s, x)] fun _ : ℝ × ℝ => 1 :=
    hφ_one.comp_tendsto continuous_fst.continuousAt
  have hValue : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, cutoffValueTerm φ a₀ a offset n q) :=
    contDiff_tsum
      (𝕜 := ℝ) (f := fun n : ℕ => cutoffValueTerm φ a₀ a offset n)
      (v := vValue) hValueTerm hValueSumm hValueBound
  have hGrad : ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, cutoffGradTerm φ gradTerm n q) :=
    contDiff_tsum
      (𝕜 := ℝ) (f := fun n : ℕ => cutoffGradTerm φ gradTerm n)
      (v := vGrad) hGradTerm hGradSumm hGradBound
  have hValueEq :
      resolverSpectralSeries a₀ a offset =ᶠ[𝓝 (s, x)]
        fun q : ℝ × ℝ => ∑' n : ℕ, cutoffValueTerm φ a₀ a offset n q := by
    filter_upwards [hφ_prod] with q hq
    simp [resolverSpectralSeries, cutoffValueTerm, hq]
  have hGradCutEq :
      (fun q : ℝ × ℝ => ∑' n : ℕ, gradTerm n q) =ᶠ[𝓝 (s, x)]
        fun q : ℝ × ℝ => ∑' n : ℕ, cutoffGradTerm φ gradTerm n q := by
    filter_upwards [hφ_prod] with q hq
    simp [cutoffGradTerm, hq]
  refine ⟨?_, ?_⟩
  · exact hValue.contDiffAt.congr_of_eventuallyEq hValueEq
  · exact hGrad.contDiffAt.congr_of_eventuallyEq (hGradEq.trans hGradCutEq)

end ShenWork.IntervalResolverSpectralJointC2Cutoff
