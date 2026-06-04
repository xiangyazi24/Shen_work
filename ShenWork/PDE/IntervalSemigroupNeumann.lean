import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalResolverPositivity

/-!
# Neumann boundary conditions for the interval semigroup

The full Neumann heat semigroup `S(t)f` satisfies homogeneous Neumann
boundary conditions `∂ₓS(t)f(0) = ∂ₓS(t)f(1) = 0` for any bounded
continuous input `f` and `t > 0`.

No `sorry`/`admit`/custom `axiom`.
-/

open MeasureTheory
open scoped Topology

namespace ShenWork.IntervalSemigroupNeumann

open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.IntervalResolverPositivity
open ShenWork.IntervalDomainRegularityBootstrap
open ShenWork.CosineSpectrum (cosineMode)

theorem heatCoeff_eigenvalue_summable {t : ℝ} (ht : 0 < t)
    {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |Real.exp (-t * unitIntervalCosineEigenvalue n) * a n|) := by
  have ht2 : 0 < t / 2 := by linarith
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg
      (by simp [unitIntervalCosineEigenvalue]; positivity)
      (abs_nonneg _))
  · intro n
    simp only [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hMn : |a n| ≤ |M| := le_trans (hM n) (le_abs_self M)
    have heig_nn : (0 : ℝ) ≤ unitIntervalCosineEigenvalue n := by
      simp [unitIntervalCosineEigenvalue]; positivity
    calc unitIntervalCosineEigenvalue n *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) * |a n|)
        ≤ unitIntervalCosineEigenvalue n *
          (Real.exp (-t * unitIntervalCosineEigenvalue n) * |M|) := by
          apply mul_le_mul_of_nonneg_left _ heig_nn
          exact mul_le_mul_of_nonneg_left hMn (Real.exp_nonneg _)
      _ = (unitIntervalCosineEigenvalue n *
            Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) *
          (|M| * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) := by
          rw [show -t * unitIntervalCosineEigenvalue n =
            -(t / 2) * unitIntervalCosineEigenvalue n +
              -(t / 2) * unitIntervalCosineEigenvalue n by ring,
            Real.exp_add]; ring
      _ ≤ (1 / (t / 2)) *
          (|M| * Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
          rw [le_div_iff₀ ht2]
          have hcx_nn : 0 ≤ (t / 2) * unitIntervalCosineEigenvalue n :=
            mul_nonneg ht2.le heig_nn
          calc unitIntervalCosineEigenvalue n *
                  Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) * (t / 2)
              = ((t / 2) * unitIntervalCosineEigenvalue n) *
                  Real.exp (-((t / 2) * unitIntervalCosineEigenvalue n)) := by ring
            _ ≤ 1 := real_mul_exp_neg_le_one hcx_nn
      _ = (|M| / (t / 2)) *
          Real.exp (-(t / 2) * unitIntervalCosineEigenvalue n) := by ring
  · exact (unitIntervalCosineHeatTrace_single_exp_summable ht2).mul_left (|M| / (t / 2))

theorem unitIntervalCosineHeatValue_eq_cosineCoeffSeries
    (t : ℝ) (a : ℕ → ℝ) :
    unitIntervalCosineHeatValue t a =
      fun x => ∑' n, (Real.exp (-t * unitIntervalCosineEigenvalue n) * a n) *
        cosineMode n x := by
  funext x
  simp only [unitIntervalCosineHeatValue, unitIntervalCosineHeatPointWeight,
    unitIntervalCosineMode]
  congr 1; funext n
  simp only [cosineMode]; ring

theorem unitIntervalCosineHeatValue_deriv_at_zero
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    deriv (unitIntervalCosineHeatValue t a) 0 = 0 := by
  rw [unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
  exact cosineCoeffSeries_deriv_at_zero (heatCoeff_eigenvalue_summable ht hM)

theorem unitIntervalCosineHeatValue_deriv_at_one
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ} {M : ℝ} (hM : ∀ n, |a n| ≤ M) :
    deriv (unitIntervalCosineHeatValue t a) 1 = 0 := by
  rw [unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
  exact cosineCoeffSeries_deriv_at_one (heatCoeff_eigenvalue_summable ht hM)

theorem deriv_eq_left_of_eqOn_Ioo_of_contDiff
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (heq : Set.EqOn f g (Set.Ioo a b)) :
    deriv f a = deriv g a := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdg : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdeq : ∀ x ∈ Set.Ioo a b, deriv f x = deriv g x := fun x hx =>
    Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun z hz => heq hz))
  have heq_filter : (deriv f) =ᶠ[nhdsWithin a (Set.Ioi a)] (deriv g) := by
    filter_upwards [Ioo_mem_nhdsGT hab] with x hx
    exact hdeq x hx
  exact tendsto_nhds_unique
    ((hdf.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    (((hdg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds).congr' heq_filter.symm)

theorem deriv_eq_right_of_eqOn_Ioo_of_contDiff
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (heq : Set.EqOn f g (Set.Ioo a b)) :
    deriv f b = deriv g b := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hdg : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdeq : ∀ x ∈ Set.Ioo a b, deriv f x = deriv g x := fun x hx =>
    Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) (fun z hz => heq hz))
  have heq_filter : (deriv f) =ᶠ[nhdsWithin b (Set.Iio b)] (deriv g) := by
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact hdeq x hx
  exact tendsto_nhds_unique
    ((hdf.continuousAt).tendsto.mono_left nhdsWithin_le_nhds)
    (((hdg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds).congr' heq_filter.symm)

theorem intervalFullSemigroupOperator_neumann_at_zero
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    deriv (fun x => intervalFullSemigroupOperator t f x) 0 = 0 := by
  have hkernel := fun x y => intervalNeumannFullKernel_cosineKernel_identity ht x y
  have hC2_S := intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => hkernel x)
  have hC2_H := unitIntervalCosineHeatValue_contDiff_two ht hM
  have heq_Ioo : Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (unitIntervalCosineHeatValue t (cosineCoeffs f)) (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
      t ht f hf x hx (hkernel x)
  rw [deriv_eq_left_of_eqOn_Ioo_of_contDiff (by norm_num : (0:ℝ) < 1)
    (hC2_S.of_le (by norm_num)) (hC2_H.of_le (by norm_num)) heq_Ioo]
  exact unitIntervalCosineHeatValue_deriv_at_zero ht hM

theorem intervalFullSemigroupOperator_neumann_at_one
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs f n| ≤ M) :
    deriv (fun x => intervalFullSemigroupOperator t f x) 1 = 0 := by
  have hkernel := fun x y => intervalNeumannFullKernel_cosineKernel_identity ht x y
  have hC2_S := intervalFullSemigroupOperator_contDiff_two_unconditional
    t ht f hf hM (fun x => hkernel x)
  have hC2_H := unitIntervalCosineHeatValue_contDiff_two ht hM
  have heq_Ioo : Set.EqOn (fun x => intervalFullSemigroupOperator t f x)
      (unitIntervalCosineHeatValue t (cosineCoeffs f)) (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => intervalFullSemigroupOperator_eq_cosineHeatValue_unconditional
      t ht f hf x hx (hkernel x)
  rw [deriv_eq_right_of_eqOn_Ioo_of_contDiff (by norm_num : (0:ℝ) < 1)
    (hC2_S.of_le (by norm_num)) (hC2_H.of_le (by norm_num)) heq_Ioo]
  exact unitIntervalCosineHeatValue_deriv_at_one ht hM

end ShenWork.IntervalSemigroupNeumann
