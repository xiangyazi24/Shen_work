/-
  ShenWork/PDE/IntervalFullKernelInitialIBP.lean

  **T2 — conjugate kernel `K̃` for the full-kernel initial-data IBP bound.**

  The full Neumann kernel `K_full(t,x,y) = ∑ₖ(heat(x−y+2k)+heat(x+y+2k))` has
  `∂ₓK_full = ∂_y K̃`, where the conjugate kernel

    `K̃(t,x,y) := ∑ₖ (−heat(x−y+2k) + heat(x+y+2k))`

  satisfies `K̃(t,x,0)=0` (the boundary cancellation that kills the IBP boundary
  term at `y=0`) and `|K̃| ≤ K_full` (so `∫₀¹|K̃| ≤ ∫₀¹ K_full = 1`, the uniform
  `L¹` mass bound).  These are the inputs to the initial-data IBP gradient bound
  `|deriv(S_full(t)u₀)x| ≤ ‖u₀'‖∞`.

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelMass

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- The **conjugate kernel** `K̃(t,x,y) = ∑ₖ(−heat(x−y+2k)+heat(x+y+2k))`.
Its `y`-derivative is `∂ₓK_full`, and it vanishes at `y=0`. -/
noncomputable def intervalNeumannConjugateKernel (t x y : ℝ) : ℝ :=
  ∑' k : ℤ, (-heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)))

/-- Summability of the conjugate-kernel lattice. -/
theorem conjugateKernel_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (fun k : ℤ =>
      -heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ))) :=
  (latticeGaussianSummable ht (x - y)).neg.add (latticeGaussianSummable ht (x + y))

/-- **Boundary cancellation: `K̃(t,x,0) = 0`.**  At `y = 0` the reflected and
direct lattice points coincide, so the signed terms cancel.  This kills the
`y = 0` boundary term in the IBP. -/
theorem conjugateKernel_at_zero {t : ℝ} (x : ℝ) :
    intervalNeumannConjugateKernel t x 0 = 0 := by
  rw [intervalNeumannConjugateKernel]
  rw [show (fun k : ℤ =>
      -heatKernel t (x - 0 + 2 * (k : ℝ)) + heatKernel t (x + 0 + 2 * (k : ℝ)))
      = fun _ : ℤ => (0 : ℝ) from by
    funext k; rw [sub_zero, add_zero]; ring]
  exact tsum_zero

/-- **Pointwise domination `|K̃| ≤ K_full`.**  Each signed term
`|−heat(x−y+2k)+heat(x+y+2k)|` is `≤ heat(x−y+2k)+heat(x+y+2k)` (triangle,
heat `≥ 0`); summing gives `|K̃| ≤ K_full`. -/
theorem abs_conjugateKernel_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |intervalNeumannConjugateKernel t x y| ≤ intervalNeumannFullKernel t x y := by
  rw [intervalNeumannConjugateKernel, intervalNeumannFullKernel]
  have hsumA := conjugateKernel_summable ht x y
  have hsumB : Summable (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ))) :=
    (latticeGaussianSummable ht (x - y)).add (latticeGaussianSummable ht (x + y))
  calc |∑' k : ℤ, (-heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)))|
      ≤ ∑' k : ℤ, |(-heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)))| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun k : ℤ =>
            -heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)))
            (by simpa [Real.norm_eq_abs] using hsumA.abs)
    _ ≤ ∑' k : ℤ, (heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ))) := by
        refine Summable.tsum_le_tsum (fun k => ?_) hsumA.abs hsumB
        have h1 := heatKernel_nonneg ht (x - y + 2 * (k : ℝ))
        have h2 := heatKernel_nonneg ht (x + y + 2 * (k : ℝ))
        rw [abs_le]
        constructor <;> linarith [abs_nonneg (-heatKernel t (x - y + 2 * (k : ℝ))
          + heatKernel t (x + y + 2 * (k : ℝ)))]

/-- Continuity of `y ↦ K̃(t,x,y)` on `[0,1]` (same `2·heatKernelWindowBound`
majorant as `K_full`; the signs do not affect the bound). -/
theorem continuousOn_conjugateKernel_snd {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (fun y : ℝ => intervalNeumannConjugateKernel t x y) (Set.Icc 0 1) := by
  have hh : Continuous (fun w : ℝ => heatKernel t w) := by unfold heatKernel; fun_prop
  have hsum : Summable (fun k : ℤ => 2 * heatKernelWindowBound t x 1 k) :=
    (summable_heatKernelWindowBound ht x 1).mul_left 2
  show ContinuousOn (fun y : ℝ => ∑' k : ℤ,
    (-heatKernel t (x - y + 2 * (k : ℝ)) + heatKernel t (x + y + 2 * (k : ℝ)))) (Set.Icc 0 1)
  refine continuousOn_tsum
    (fun k => (((hh.comp (by fun_prop)).neg).add (hh.comp (by fun_prop))).continuousOn) hsum
    (fun k y hy => ?_)
  have h1 : heatKernel t (x - y + 2 * (k : ℝ)) ≤ heatKernelWindowBound t x 1 k :=
    heatKernel_le_windowShift ht x 1 k
      (by rw [show x - y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = -y by ring, abs_neg]
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have h2 : heatKernel t (x + y + 2 * (k : ℝ)) ≤ heatKernelWindowBound t x 1 k :=
    heatKernel_le_windowShift ht x 1 k
      (by rw [show x + y + 2 * (k : ℝ) - (x + 2 * (k : ℝ)) = y by ring]
          exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  rw [Real.norm_eq_abs]
  have hA := heatKernel_nonneg ht (x - y + 2 * (k : ℝ))
  have hB := heatKernel_nonneg ht (x + y + 2 * (k : ℝ))
  rw [abs_le]
  constructor <;> linarith [h1, h2]

/-- **Uniform `L¹` mass bound `∫₀¹ |K̃(t,x,·)| ≤ 1`.**  From the pointwise
`|K̃| ≤ K_full` and mass conservation `∫₀¹ K_full = 1`. -/
theorem conjugateKernel_L1_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, |intervalNeumannConjugateKernel t x y|) ≤ 1 := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hKfull_int : IntervalIntegrable
      (fun y : ℝ => intervalNeumannFullKernel t x y) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact continuousOn_intervalNeumannFullKernel_snd ht x
  have hKtilde_int : IntervalIntegrable
      (fun y : ℝ => |intervalNeumannConjugateKernel t x y|) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact (continuousOn_conjugateKernel_snd ht x).abs
  calc (∫ y in (0 : ℝ)..1, |intervalNeumannConjugateKernel t x y|)
      ≤ ∫ y in (0 : ℝ)..1, intervalNeumannFullKernel t x y :=
        intervalIntegral.integral_mono_on h01 hKtilde_int hKfull_int
          (fun y _ => abs_conjugateKernel_le ht x y)
    _ = 1 := intervalNeumannFullKernel_integral_eq_one ht x

end ShenWork.IntervalNeumannFullKernel
