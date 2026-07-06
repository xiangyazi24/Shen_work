/-
  ShenWork/PDE/IntervalFullKernelSourceIBP.lean

  **G2a+G2b — Spatial IBP for the Duhamel source integral.**

  Convention decision (G2a): keep `∂ₓ S_N` in the gradient mild map and use
  the conjugate kernel `K̃` for IBP.  The identity `∂ₓ K_N = ∂_y K̃` (proved
  in `IntervalFullKernelInitialIBP`) plus the boundary cancellations
  `K̃(t,x,0) = 0` and `K̃(t,x,1) = 0` kill both IBP boundary terms, giving

      ∂ₓ [S_N(t) Q](x) = − ∫₀¹ K̃(t,x,y) · Q'(y) dy

  for any C¹ source Q on [0,1] — NO boundary condition on Q required.
  This is equivalent to `∂ₓ S_N Q = S_D Q'` where `S_D` is the Dirichlet
  semigroup, but no separate Dirichlet infrastructure is needed.

  Contents:
  1. `conjugateKernel_at_one`: boundary cancellation `K̃(t,x,1) = 0`
  2. `deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral`:
     the spatial IBP identity for the Duhamel source

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalFullKernelInitialIBP
import ShenWork.PDE.IntervalFullKernelGradientLinfty

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-! ## Boundary cancellation at y = 1 -/

/-- **Boundary cancellation: `K̃(t,x,1) = 0`.**  At `y = 1` the two lattice
families `{x − 1 + 2k}` and `{x + 1 + 2k}` are related by the index shift
`k ↦ k + 1`, so the signed sum telescopes to zero. -/
theorem conjugateKernel_at_one {t : ℝ} (ht : 0 < t) (x : ℝ) :
    intervalNeumannConjugateKernel t x 1 = 0 := by
  rw [intervalNeumannConjugateKernel]
  have hsum_neg : Summable (fun k : ℤ => heatKernel t (x - 1 + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x - 1)
  have hsum_pos : Summable (fun k : ℤ => heatKernel t (x + 1 + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (x + 1)
  rw [Summable.tsum_add hsum_neg.neg hsum_pos, tsum_neg]
  suffices h : (∑' k : ℤ, heatKernel t (x + 1 + 2 * (k : ℝ))) =
      ∑' k : ℤ, heatKernel t (x - 1 + 2 * (k : ℝ)) by linarith
  set f : ℤ → ℝ := fun k => heatKernel t (x - 1 + 2 * (k : ℝ)) with hf
  have hfun : (fun k : ℤ => heatKernel t (x + 1 + 2 * (k : ℝ))) = f ∘ (· + 1) := by
    funext k; simp only [hf, Function.comp]; congr 1; push_cast; ring
  rw [hfun, show tsum (f ∘ (· + 1)) = ∑' k : ℤ, f (k + 1) from rfl]
  exact (Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) f)

/-! ## Boundary cancellation at x = 0 and x = 1 -/

/-- **Endpoint cancellation in the spatial variable: `K̃(t,0,y) = 0`.**
The two lattice families `{−y + 2k}` and `{y + 2k}` are related by
`k ↦ -k` and the evenness of the heat kernel. -/
theorem conjugateKernel_at_x_zero {t : ℝ} (ht : 0 < t) (y : ℝ) :
    intervalNeumannConjugateKernel t 0 y = 0 := by
  rw [intervalNeumannConjugateKernel]
  have hsum_neg : Summable (fun k : ℤ => heatKernel t (0 - y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (0 - y)
  have hsum_pos : Summable (fun k : ℤ => heatKernel t (0 + y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (0 + y)
  rw [Summable.tsum_add hsum_neg.neg hsum_pos, tsum_neg]
  suffices h : (∑' k : ℤ, heatKernel t (0 + y + 2 * (k : ℝ))) =
      ∑' k : ℤ, heatKernel t (0 - y + 2 * (k : ℝ)) by linarith
  set f : ℤ → ℝ := fun k => heatKernel t (0 + y + 2 * (k : ℝ)) with hf
  have hfun : (fun k : ℤ => heatKernel t (0 - y + 2 * (k : ℝ))) =
      f ∘ Equiv.neg ℤ := by
    funext k
    simp only [hf, Function.comp, Equiv.neg_apply]
    rw [← heatKernel_neg t (0 + y + 2 * ((-k : ℤ) : ℝ))]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact (Equiv.tsum_eq (Equiv.neg ℤ) f).symm

/-- **Endpoint cancellation in the spatial variable: `K̃(t,1,y) = 0`.**
The two lattice families `{1 − y + 2k}` and `{1 + y + 2k}` are related by
`k ↦ -k-1` and the evenness of the heat kernel. -/
theorem conjugateKernel_at_x_one {t : ℝ} (ht : 0 < t) (y : ℝ) :
    intervalNeumannConjugateKernel t 1 y = 0 := by
  rw [intervalNeumannConjugateKernel]
  have hsum_neg : Summable (fun k : ℤ => heatKernel t (1 - y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (1 - y)
  have hsum_pos : Summable (fun k : ℤ => heatKernel t (1 + y + 2 * (k : ℝ))) :=
    latticeGaussianSummable ht (1 + y)
  rw [Summable.tsum_add hsum_neg.neg hsum_pos, tsum_neg]
  suffices h : (∑' k : ℤ, heatKernel t (1 + y + 2 * (k : ℝ))) =
      ∑' k : ℤ, heatKernel t (1 - y + 2 * (k : ℝ)) by linarith
  let e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight (-1 : ℤ))
  set f : ℤ → ℝ := fun k => heatKernel t (1 - y + 2 * (k : ℝ)) with hf
  have hfun : (fun k : ℤ => heatKernel t (1 + y + 2 * (k : ℝ))) = f ∘ e := by
    funext k
    simp only [hf, Function.comp]
    rw [← heatKernel_neg t (1 - y + 2 * ((e k : ℤ) : ℝ))]
    congr 1
    simp [e]
    ring
  rw [hfun]
  exact (Equiv.tsum_eq e f)

/-- The conjugate-kernel operator vanishes exactly at the left endpoint. -/
theorem conjugateKernel_integral_at_x_zero {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) :
    (∫ y in (0 : ℝ)..1, f y * intervalNeumannConjugateKernel t 0 y) = 0 := by
  rw [show (fun y : ℝ => f y * intervalNeumannConjugateKernel t 0 y) =
      fun _ : ℝ => 0 from by
    funext y
    rw [conjugateKernel_at_x_zero ht y, mul_zero]]
  simp

/-- The conjugate-kernel operator vanishes exactly at the right endpoint. -/
theorem conjugateKernel_integral_at_x_one {t : ℝ} (ht : 0 < t) (f : ℝ → ℝ) :
    (∫ y in (0 : ℝ)..1, f y * intervalNeumannConjugateKernel t 1 y) = 0 := by
  rw [show (fun y : ℝ => f y * intervalNeumannConjugateKernel t 1 y) =
      fun _ : ℝ => 0 from by
    funext y
    rw [conjugateKernel_at_x_one ht y, mul_zero]]
  simp

/-! ## Spatial IBP for the Duhamel source integral -/

/-- **Spatial IBP theorem (G2b).**  For `t > 0` and C¹ source `Q` on `[0,1]`
with derivative `Q'` and pointwise bound `|Q| ≤ CQ`,

    `deriv (z ↦ S_N(t) Q z) x = − ∫₀¹ Q'(y) · K̃(t,x,y) dy`.

Both IBP boundary terms vanish: `K̃(t,x,0) = 0` (`conjugateKernel_at_zero`)
and `K̃(t,x,1) = 0` (`conjugateKernel_at_one`).  No boundary condition on Q
is required.

This is the kernel-level identity behind the gradient-to-standard Duhamel
conversion: `∂ₓ S_N Q = −∫ K̃ · Q'`, which is equivalently `S_D Q'` where
`S_D` is the Dirichlet semigroup (since `K̃ = −K_D`). -/
theorem deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' y) y)
    (hQ'_int : IntervalIntegrable Q' MeasureTheory.volume 0 1) (x : ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x =
      -(∫ y in (0 : ℝ)..1, Q' y * intervalNeumannConjugateKernel t x y) := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [(intervalFullSemigroupOperator_hasDerivAt_fst ht hQ_meas hQ_bound x).deriv]
  -- Step 1: pass from the measure integral to an interval integral and commute.
  have hμconv :
      (∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x * Q y
        ∂(intervalMeasure 1))
        = ∫ y in (0 : ℝ)..1,
            Q y * deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x := by
    simp only [intervalMeasure, intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h01]
    exact intervalIntegral.integral_congr (fun y _ => by ring)
  rw [hμconv]
  -- Step 2: the kernel identity ∂_y K̃(t,x,y) = ∂_x K_N(t,x,y).
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
  -- Step 3: integration by parts.  Both boundary terms vanish.
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hQ_deriv hvderiv hQ'_int hDii]
  simp [conjugateKernel_at_one ht x, conjugateKernel_at_zero]

/-- **Spatial IBP bound.**  Under the hypotheses of the IBP identity, the
gradient of the semigroup applied to a C¹ source is bounded by
`‖Q'‖∞ · ∫₀¹|K̃|`:

    `|deriv (z ↦ S_N(t) Q z) x| ≤ sup|Q'| · ∫₀¹|K̃(t,x,y)|dy ≤ sup|Q'|`.

The last inequality uses the `L¹` mass bound `∫₀¹|K̃| ≤ 1`
(`conjugateKernel_L1_bound`). -/
theorem abs_deriv_intervalFullSemigroupOperator_le_of_source_deriv_bound
    {t : ℝ} (ht : 0 < t)
    {Q Q' : ℝ → ℝ}
    (hQ_meas : AEStronglyMeasurable Q (intervalMeasure 1))
    {CQ : ℝ} (hQ_bound : ∀ y, |Q y| ≤ CQ)
    (hQ_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt Q (Q' y) y)
    (hQ'_int : IntervalIntegrable Q' MeasureTheory.volume 0 1)
    {G : ℝ} (hG_nn : 0 ≤ G)
    (hQ'_sup : ∀ y, |Q' y| ≤ G) (x : ℝ) :
    |deriv (fun z : ℝ => intervalFullSemigroupOperator t Q z) x| ≤ G := by
  rw [deriv_intervalFullSemigroupOperator_eq_neg_conjugateKernel_source_integral
    ht hQ_meas hQ_bound hQ_deriv hQ'_int x]
  rw [abs_neg]
  have hKcont : ContinuousOn
      (fun y : ℝ => intervalNeumannConjugateKernel t x y) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le h01]; exact continuousOn_conjugateKernel_snd ht x
  have hprod_ii : IntervalIntegrable
      (fun y : ℝ => Q' y * intervalNeumannConjugateKernel t x y)
      MeasureTheory.volume 0 1 :=
    hQ'_int.mul_continuousOn hKcont
  have hKabs_ii : IntervalIntegrable
      (fun y : ℝ => |intervalNeumannConjugateKernel t x y|)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; rw [Set.uIcc_of_le h01]
    exact (continuousOn_conjugateKernel_snd ht x).abs
  calc |∫ y in (0 : ℝ)..1, Q' y * intervalNeumannConjugateKernel t x y|
      ≤ ∫ y in (0 : ℝ)..1, |Q' y * intervalNeumannConjugateKernel t x y| :=
        intervalIntegral.abs_integral_le_integral_abs h01
    _ ≤ ∫ y in (0 : ℝ)..1, G * |intervalNeumannConjugateKernel t x y| := by
        apply intervalIntegral.integral_mono_on h01 hprod_ii.abs
          (hKabs_ii.const_mul G) (fun y _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hQ'_sup y) (abs_nonneg _)
    _ = G * ∫ y in (0 : ℝ)..1, |intervalNeumannConjugateKernel t x y| :=
        intervalIntegral.integral_const_mul G _
    _ ≤ G * 1 := by
        exact mul_le_mul_of_nonneg_left (conjugateKernel_L1_bound ht x) hG_nn
    _ = G := mul_one G
  where h01 : (0 : ℝ) ≤ 1 := by norm_num

end ShenWork.IntervalNeumannFullKernel
