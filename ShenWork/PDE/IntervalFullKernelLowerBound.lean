/-
  ShenWork/PDE/IntervalFullKernelLowerBound.lean

  **Full Neumann kernel lower bound.**

  If `c ≤ f(y)` for all `y ∈ [0,1]`, `0 ≤ c`, and `f` is bounded, then
  `c ≤ intervalFullSemigroupOperator t f x`.

  Uses: `intervalNeumannFullKernel_nonneg` (K ≥ 0),
        `intervalNeumannFullKernel_intervalMeasure_integral_eq_one` (∫K = 1).

  Same integral-comparison pattern as `intervalFullSemigroupOperator_Linfty_bound`.
  **Target: 0 sorry.**
-/
import ShenWork.PDE.IntervalFullKernelSupBound

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- Auxiliary: the semigroup integral is nonneg when the source is nonneg
on `[0,1]` (weaker than `intervalFullSemigroupOperator_nonneg` which needs
`f ≥ 0` everywhere). Since `intervalMeasure 1 = volume.restrict [0,1]`, only
the values on `[0,1]` matter. -/
theorem intervalFullSemigroupOperator_nonneg_of_nonneg_on_Icc {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → 0 ≤ f y) (x : ℝ) :
    0 ≤ intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  apply integral_nonneg_of_ae
  show 0 ≤ᶠ[ae (intervalMeasure 1)] fun y => intervalNeumannFullKernel t x y * f y
  simp only [intervalMeasure, intervalSet]
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  apply Filter.Eventually.of_forall
  intro y hy
  exact mul_nonneg (intervalNeumannFullKernel_nonneg ht x y) (hf y hy)

/-- **Full Neumann semigroup lower bound.**  If `c ≤ f(y)` for all `y ∈ [0,1]`
and `|f(y)| ≤ B`, then `c ≤ S(t)f(x)`.

Proof: `c = c·∫K = ∫(K·c) ≤ ∫(K·f) = S(t)f(x)`, the inequality using `K ≥ 0`
and `c ≤ f` on the support `[0,1]` of `intervalMeasure 1`. -/
theorem intervalFullSemigroupOperator_lower_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {c B : ℝ} (hc : 0 ≤ c) (hcB : c ≤ B)
    (hf_lower : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → c ≤ f y)
    (hf_bound : ∀ y, |f y| ≤ B) (x : ℝ) :
    c ≤ intervalFullSemigroupOperator t f x := by
  unfold intervalFullSemigroupOperator
  have hK_nn := fun y => intervalNeumannFullKernel_nonneg ht x y
  have hK_int := intervalNeumannFullKernel_integrable ht x
  have hmass := intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  -- K·f is integrable (bounded by B·K, same proof as in Linfty_bound)
  have hKf_int : Integrable (fun y => intervalNeumannFullKernel t x y * f y)
      (intervalMeasure 1) := by
    apply Integrable.mono (hK_int.mul_const B)
    · sorry -- AEStronglyMeasurable
    · apply Filter.Eventually.of_forall
      intro y
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn y)]
      exact mul_le_mul_of_nonneg_left (le_trans (hf_bound y) (le_abs_self B)) (hK_nn y)
  calc c = c * 1 := (mul_one c).symm
    _ = c * ∫ y, intervalNeumannFullKernel t x y ∂(intervalMeasure 1) := by rw [hmass]
    _ = ∫ y, c * intervalNeumannFullKernel t x y ∂(intervalMeasure 1) :=
        (integral_const_mul c _).symm
    _ = ∫ y, intervalNeumannFullKernel t x y * c ∂(intervalMeasure 1) := by
        congr 1; ext y; ring
    _ ≤ ∫ y, intervalNeumannFullKernel t x y * f y ∂(intervalMeasure 1) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y => mul_nonneg (hK_nn y) hc)
        · exact hKf_int
        · show ∀ᵐ y ∂(intervalMeasure 1), _
          unfold intervalMeasure intervalSet
          rw [ae_restrict_iff' measurableSet_Icc]
          exact Filter.Eventually.of_forall fun y hy =>
            mul_le_mul_of_nonneg_left (hf_lower y hy) (hK_nn y)

end ShenWork.IntervalNeumannFullKernel
