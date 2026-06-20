import ShenWork.Paper2.IntervalBFormCron2MildToWeak
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalMeasure intervalSet
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator)

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

/-- First-variable derivative series for the full Neumann kernel, used only for
regular Fubini integrability of the concrete flux/test pair. -/
def regularFluxKernelDerivSeries (τ x y : ℝ) : ℝ :=
  (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (x - y + 2 * (k : ℝ))) +
    (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (x + y + 2 * (k : ℝ)))

theorem regularFluxKernelDerivSeries_joint_measurable :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      regularFluxKernelDerivSeries q.1.1 q.1.2 q.2) := by
  set g₁ : ℤ → (ℝ × ℝ) × ℝ → ℝ :=
    fun k q => deriv (fun z : ℝ => heatKernel q.1.1 z)
      (q.1.2 - q.2 + 2 * (k : ℝ)) with hg₁_def
  set g₂ : ℤ → (ℝ × ℝ) × ℝ → ℝ :=
    fun k q => deriv (fun z : ℝ => heatKernel q.1.1 z)
      (q.1.2 + q.2 + 2 * (k : ℝ)) with hg₂_def
  have hg₁_meas : ∀ k, Measurable (g₁ k) := by
    intro k
    have heq : g₁ k =
        fun q : (ℝ × ℝ) × ℝ =>
          -((q.1.2 - q.2 + 2 * (k : ℝ)) / (2 * q.1.1)) *
            heatKernel q.1.1 (q.1.2 - q.2 + 2 * (k : ℝ)) := by
      funext q
      simp only [hg₁_def]
      exact deriv_heatKernel_global q.1.1 (q.1.2 - q.2 + 2 * (k : ℝ))
    rw [heq]
    unfold heatKernel
    fun_prop
  have hg₂_meas : ∀ k, Measurable (g₂ k) := by
    intro k
    have heq : g₂ k =
        fun q : (ℝ × ℝ) × ℝ =>
          -((q.1.2 + q.2 + 2 * (k : ℝ)) / (2 * q.1.1)) *
            heatKernel q.1.1 (q.1.2 + q.2 + 2 * (k : ℝ)) := by
      funext q
      simp only [hg₂_def]
      exact deriv_heatKernel_global q.1.1 (q.1.2 + q.2 + 2 * (k : ℝ))
    rw [heq]
    unfold heatKernel
    fun_prop
  have hsum_aux : ∀ (z : ℝ) (q : (ℝ × ℝ) × ℝ),
      Summable (fun k : ℤ => deriv (fun u : ℝ => heatKernel q.1.1 u)
        (z + 2 * (k : ℝ))) := by
    intro z q
    rcases lt_or_ge 0 q.1.1 with hτ | hτ
    · exact latticeGaussianGradSummable hτ z
    · have hz : (fun k : ℤ => deriv (fun u : ℝ => heatKernel q.1.1 u)
          (z + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun u : ℝ => heatKernel q.1.1 u) = fun _ : ℝ => (0 : ℝ) := by
          funext u
          exact heatKernel_of_nonpos hτ u
        rw [hzero, deriv_const]
      rw [hz]
      exact summable_zero
  have hg₁_sum : ∀ q, Summable (fun k : ℤ => g₁ k q) :=
    fun q => hsum_aux (q.1.2 - q.2) q
  have hg₂_sum : ∀ q, Summable (fun k : ℤ => g₂ k q) :=
    fun q => hsum_aux (q.1.2 + q.2) q
  have hmeas := (measurable_tsum_int_of_summable hg₁_meas hg₁_sum).add
    (measurable_tsum_int_of_summable hg₂_meas hg₂_sum)
  simpa [regularFluxKernelDerivSeries, g₁, g₂] using hmeas

theorem regularFluxKernelDerivSeries_eq_deriv_fst
    {τ : ℝ} (hτ : 0 < τ) (x y : ℝ) :
    regularFluxKernelDerivSeries τ x y =
      deriv (fun z : ℝ => intervalNeumannFullKernel τ z y) x := by
  simp [regularFluxKernelDerivSeries,
    (hasDerivAt_intervalNeumannFullKernel_fst hτ x y).deriv]

end ShenWork.IntervalNeumannFullKernel

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)

private lemma intervalMeasure_prod_mem_unit :
    ∀ᵐ p : ℝ × ℝ ∂((intervalMeasure 1).prod (intervalMeasure 1)),
      p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hx : ∀ᵐ x : ℝ ∂(intervalMeasure 1), x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, intervalSet]
    exact ae_restrict_mem measurableSet_Icc
  have hy : ∀ᵐ y : ℝ ∂(intervalMeasure 1), y ∈ Set.Icc (0 : ℝ) 1 := hx
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae]
  · filter_upwards [hx] with x hxmem
    filter_upwards [hy] with y hymem
    exact ⟨hxmem, hymem⟩
  · exact measurableSet_Icc.prod measurableSet_Icc

/-- A bounded measurable real function on `[0,1]`, represented against the
project's concrete interval measure. -/
structure BoundedMeasurableInterval (f : ℝ → ℝ) where
  measurable : AEStronglyMeasurable f (intervalMeasure 1)
  boundConstant : ℝ
  bound : ∀ x, |f x| ≤ boundConstant

def BoundedMeasurableInterval.integrable
    {f : ℝ → ℝ} (H : BoundedMeasurableInterval f) :
    Integrable f (intervalMeasure 1) :=
  intervalMeasure_integrable_of_abs_bound H.measurable H.bound

def BoundedMeasurableInterval.integrableOn_unit
    {f : ℝ → ℝ} (H : BoundedMeasurableInterval f) :
    IntegrableOn f (Set.Icc (0 : ℝ) 1) volume := by
  simpa [IntegrableOn, intervalMeasure, intervalSet] using H.integrable

/-- Fubini integrability for the regular B_N identity, from L¹ flux and test
data on the finite interval. -/
theorem regularFlux_bN_fubini_integrable_of_integrable
    {τ : ℝ} (hτ : 0 < τ) {g ψ : ℝ → ℝ}
    (hg : Integrable g (intervalMeasure 1))
    (hψ : Integrable ψ (intervalMeasure 1)) :
    Integrable
      (fun p : ℝ × ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ p.1 y') p.2
          * g p.2 * ψ p.1)
      ((intervalMeasure 1).prod (intervalMeasure 1)) := by
  let μ := intervalMeasure 1
  set C : ℝ := ∑' k : ℤ,
    (heatGradWindowBound τ 0 2 k + heatGradWindowBound τ 0 2 k) with hC_def
  have hC_nonneg : 0 ≤ C := by
    rw [hC_def]
    exact tsum_nonneg fun k => by
      unfold heatGradWindowBound heatGradPointwiseBound
      positivity
  have hψg : Integrable (fun p : ℝ × ℝ => ψ p.1 * g p.2) (μ.prod μ) :=
    hψ.mul_prod hg
  have hmap : Measurable (fun p : ℝ × ℝ => ((τ, p.2), p.1)) := by
    exact (measurable_const.prodMk measurable_snd).prodMk measurable_fst
  have hseries_meas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => regularFluxKernelDerivSeries τ p.2 p.1)
        (μ.prod μ) :=
    (regularFluxKernelDerivSeries_joint_measurable.comp hmap).aestronglyMeasurable
  have hpre_meas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          regularFluxKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2))
        (μ.prod μ) :=
    hseries_meas.mul hψg.aestronglyMeasurable
  have hdom : Integrable (fun p : ℝ × ℝ => C * ‖ψ p.1 * g p.2‖) (μ.prod μ) :=
    hψg.norm.const_mul C
  have hpre_int : Integrable
      (fun p : ℝ × ℝ =>
        regularFluxKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2))
      (μ.prod μ) := by
    refine Integrable.mono' hdom hpre_meas ?_
    filter_upwards [intervalMeasure_prod_mem_unit] with p hp
    have hxabs : |p.2 - (0 : ℝ)| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hyabs : |p.1| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    have hK :
        |regularFluxKernelDerivSeries τ p.2 p.1| ≤ C := by
      rw [regularFluxKernelDerivSeries_eq_deriv_fst hτ, hC_def]
      exact abs_deriv_intervalNeumannFullKernel_fst_le_const
        (t := τ) hτ (0 : ℝ) (z := p.2) (y := p.1) hxabs hyabs
    calc ‖regularFluxKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2)‖
        = |regularFluxKernelDerivSeries τ p.2 p.1| * ‖ψ p.1 * g p.2‖ := by
          simp [Real.norm_eq_abs]
      _ ≤ C * ‖ψ p.1 * g p.2‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  have htarget_eq :
      (fun p : ℝ × ℝ =>
        regularFluxKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2))
        =
      (fun p : ℝ × ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ p.1 y') p.2
          * g p.2 * ψ p.1) := by
    funext p
    rw [regularFluxKernelDerivSeries_eq_deriv_fst hτ]
    rw [← deriv_intervalNeumannFullKernel_snd_eq_fst_swap hτ p.1 p.2]
    ring
  rwa [htarget_eq] at hpre_int

/-- Regular B_N data for exactly one chemotaxis flux slice and one test. -/
structure BNDualityForFluxTestAt
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (t s : ℝ) (φ : ℝ → ℝ) where
  flux_bounded :
    BoundedMeasurableInterval (truncatedChemFluxLifted p (u s))
  test_bounded :
    BoundedMeasurableInterval φ

def BNDualityForFluxTestAt.flux_integrableOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t s : ℝ} {φ : ℝ → ℝ}
    (H : BNDualityForFluxTestAt p u t s φ) :
    IntegrableOn (truncatedChemFluxLifted p (u s))
      (Set.Icc (0 : ℝ) 1) volume :=
  H.flux_bounded.integrableOn_unit

def BNDualityForFluxTestAt.test_integrableOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t s : ℝ} {φ : ℝ → ℝ}
    (H : BNDualityForFluxTestAt p u t s φ) :
    IntegrableOn φ (Set.Icc (0 : ℝ) 1) volume :=
  H.test_bounded.integrableOn_unit

/-- The bounded/measurable flux and test data give the concrete regular B_N
duality by applying `bN_duality_regular` to this pair only. -/
theorem BNDualityForFluxTestAt.duality
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t s : ℝ} {φ : ℝ → ℝ}
    (H : BNDualityForFluxTestAt p u t s φ) (hst : s < t) :
    TruncatedBNDualityForTestAt p u t s φ := by
  have hτ : 0 < t - s := sub_pos.mpr hst
  have hflux_int :
      Integrable (truncatedChemFluxLifted p (u s)) (intervalMeasure 1) :=
    H.flux_bounded.integrable
  have htest_int : Integrable φ (intervalMeasure 1) :=
    H.test_bounded.integrable
  have hF_int :
      Integrable
        (fun q : ℝ × ℝ =>
          deriv
              (fun y' : ℝ =>
                intervalNeumannFullKernel (t - s) q.1 y') q.2
            * truncatedChemFluxLifted p (u s) q.2 * φ q.1)
        ((intervalMeasure 1).prod (intervalMeasure 1)) :=
    regularFlux_bN_fubini_integrable_of_integrable
      (τ := t - s) hτ hflux_int htest_int
  simpa [TruncatedBNDualityForTestAt] using
    (bN_duality_regular (τ := t - s) hτ
      (truncatedChemFluxLifted p (u s)) φ hF_int
      (fun y =>
        (intervalFullSemigroupOperator_hasDerivAt_fst
          hτ H.test_bounded.measurable H.test_bounded.bound y).deriv))

end ShenWork.Paper2.BFormPositiveDatumNegPart
