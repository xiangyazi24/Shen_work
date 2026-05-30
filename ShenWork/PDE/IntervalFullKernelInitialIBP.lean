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

/-- **`∂_y K̃ = ∂ₓ K_full`.**  The conjugate kernel's `y`-derivative is the full
kernel's `x`-derivative (the identity powering the IBP).  `K̃` splits into the
reflected (`−∑ₖ heat(x−y+2k)`) and direct (`∑ₖ heat(x+y+2k)`) lattice families;
the direct family differentiates by `hasDerivAt_heatKernel_lattice_tsum` (6.3),
the reflected one by the same composed with `y ↦ −y`. -/
theorem hasDerivAt_conjugateKernel_snd {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => intervalNeumannConjugateKernel t x y)
      ((∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)))
        + (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ)))) y := by
  -- direct family: 6.3 with shift `b = x`, point `y`, after `add_comm` in the arg.
  have hDir : HasDerivAt (fun y' : ℝ => ∑' k : ℤ, heatKernel t (x + y' + 2 * (k : ℝ)))
      (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ))) y := by
    have hfeq : (fun y' : ℝ => ∑' k : ℤ, heatKernel t (x + y' + 2 * (k : ℝ)))
        = fun w : ℝ => ∑' k : ℤ, heatKernel t (w + x + 2 * (k : ℝ)) := by
      funext y'; refine tsum_congr (fun k => ?_); congr 1; ring
    have hdeq : (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x + y + 2 * (k : ℝ)))
        = ∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (y + x + 2 * (k : ℝ)) := by
      refine tsum_congr (fun k => ?_); congr 1; ring
    rw [hfeq, hdeq]
    exact hasDerivAt_heatKernel_lattice_tsum ht x y
  -- reflected family: 6.3 (at `-y`) composed with `y' ↦ -y'`.
  have hRefl : HasDerivAt (fun y' : ℝ => ∑' k : ℤ, heatKernel t (x - y' + 2 * (k : ℝ)))
      (-(∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)))) y := by
    have h := hasDerivAt_heatKernel_lattice_tsum ht x (-y)
    have hneg : HasDerivAt (fun y' : ℝ => -y') (-1) y := by simpa using (hasDerivAt_id y).neg
    have hcomp := h.comp y hneg
    have hfeq : (fun y' : ℝ => ∑' k : ℤ, heatKernel t (x - y' + 2 * (k : ℝ)))
        = (fun w : ℝ => ∑' k : ℤ, heatKernel t (w + x + 2 * (k : ℝ))) ∘ fun y' : ℝ => -y' := by
      funext y'; simp only [Function.comp]; refine tsum_congr (fun k => ?_); congr 1; ring
    have hdeq : -(∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (x - y + 2 * (k : ℝ)))
        = (∑' k : ℤ, deriv (fun u : ℝ => heatKernel t u) (-y + x + 2 * (k : ℝ))) * (-1) := by
      rw [mul_neg_one]; congr 1; refine tsum_congr (fun k => ?_); congr 1; ring
    rw [hfeq, hdeq]
    exact hcomp
  -- assemble: K̃ = −(reflected) + (direct).
  have hfun : (fun y : ℝ => intervalNeumannConjugateKernel t x y)
      = fun y : ℝ => -(∑' k : ℤ, heatKernel t (x - y + 2 * (k : ℝ)))
          + (∑' k : ℤ, heatKernel t (x + y + 2 * (k : ℝ))) := by
    funext y'
    rw [intervalNeumannConjugateKernel,
      Summable.tsum_add (latticeGaussianSummable ht (x - y')).neg (latticeGaussianSummable ht (x + y')),
      tsum_neg]
  rw [hfun]
  convert (hRefl.neg).add hDir using 1
  rw [neg_neg]

/-- **Full-kernel initial-data IBP gradient bound.**  For `t > 0` and globally
bounded C¹ data `u₀` with `u₀(1)=0` and `|u₀'| ≤ G_init`,

  `|deriv (z ↦ intervalFullSemigroupOperator t u₀ z) x| ≤ G_init`,

uniformly in `t` (no `t^{−1/2}` blow-up).  Differentiation under the integral
(`intervalFullSemigroupOperator_hasDerivAt_fst`) gives `deriv = ∫₀¹ ∂ₓK_full·u₀`;
`∂ₓK_full = ∂_y K̃` (`hasDerivAt_conjugateKernel_snd`) and integration by parts
(`integral_mul_deriv_eq_deriv_mul`) move the derivative onto `u₀`, the boundary
term vanishing (`K̃(·,0)=0`, `u₀(1)=0`); finally `|∫₀¹ K̃·u₀'| ≤ G_init·∫₀¹|K̃| ≤
G_init` by the uniform `L¹` mass bound `conjugateKernel_L1_bound`.  This discharges
the `hInit_grad` hypothesis of `intervalFullCoupledDuhamel_grad_estimate_of_leibniz`. -/
theorem intervalFullCoupledDuhamel_grad_initial_bound {t : ℝ} (ht : 0 < t)
    {u₀ u₀' : ℝ → ℝ}
    (hu₀_meas : AEStronglyMeasurable u₀ (intervalMeasure 1))
    {Cu₀ : ℝ} (hu₀_bound : ∀ y, |u₀ y| ≤ Cu₀)
    (hu₀ : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt u₀ (u₀' y) y)
    (hu₀'_int : IntervalIntegrable u₀' MeasureTheory.volume 0 1)
    (hu₀_one : u₀ 1 = 0)
    {G_init : ℝ} (hG_init_nn : 0 ≤ G_init)
    (hu₀'_sup : ∀ y, |u₀' y| ≤ G_init) (x : ℝ) :
    |deriv (fun z : ℝ => intervalFullSemigroupOperator t u₀ z) x| ≤ G_init := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [(intervalFullSemigroupOperator_hasDerivAt_fst ht hu₀_meas hu₀_bound x).deriv]
  -- pass to the interval integral, commute, and integrate by parts.
  have hμconv :
      (∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x * u₀ y ∂(intervalMeasure 1))
        = ∫ y in (0 : ℝ)..1, u₀ y * deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x := by
    simp only [intervalMeasure, intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h01]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    ring
  rw [hμconv]
  have hvderiv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => intervalNeumannConjugateKernel t x y)
        (deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x) y := by
    intro y _
    have h := hasDerivAt_conjugateKernel_snd ht x y
    rwa [← (hasDerivAt_intervalNeumannFullKernel_fst ht x y).deriv] at h
  have hDii : IntervalIntegrable
      (fun y : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x)
      MeasureTheory.volume 0 1 :=
    intervalIntegrable_deriv_intervalNeumannFullKernel_fst ht x
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu₀ hvderiv hu₀'_int hDii,
    hu₀_one, conjugateKernel_at_zero, zero_mul, mul_zero, sub_zero, zero_sub, abs_neg]
  -- bound `|∫₀¹ u₀'·K̃| ≤ G_init·∫₀¹|K̃| ≤ G_init`.
  have hKcont : ContinuousOn (fun y : ℝ => intervalNeumannConjugateKernel t x y) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le h01]; exact continuousOn_conjugateKernel_snd ht x
  have hKabs_ii : IntervalIntegrable
      (fun y : ℝ => |intervalNeumannConjugateKernel t x y|) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le h01]
    exact (continuousOn_conjugateKernel_snd ht x).abs
  have hprod_ii : IntervalIntegrable
      (fun y : ℝ => u₀' y * intervalNeumannConjugateKernel t x y) MeasureTheory.volume 0 1 :=
    hu₀'_int.mul_continuousOn hKcont
  calc |∫ y in (0 : ℝ)..1, u₀' y * intervalNeumannConjugateKernel t x y|
      ≤ ∫ y in (0 : ℝ)..1, |u₀' y * intervalNeumannConjugateKernel t x y| :=
        intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, G_init * |intervalNeumannConjugateKernel t x y| := by
        refine intervalIntegral.integral_mono_on h01 hprod_ii.abs (hKabs_ii.const_mul G_init)
          (fun y _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hu₀'_sup y) (abs_nonneg _)
    _ = G_init * ∫ y in (0 : ℝ)..1, |intervalNeumannConjugateKernel t x y| := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ G_init * 1 := mul_le_mul_of_nonneg_left (conjugateKernel_L1_bound ht x) hG_init_nn
    _ = G_init := mul_one G_init

end ShenWork.IntervalNeumannFullKernel
