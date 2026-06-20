import ShenWork.Paper2.IntervalBFormCron2BNDuality
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable

open MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)

noncomputable section

namespace ShenWork.IntervalNeumannFullKernel

open ShenWork.IntervalDomain

/-- Closed-form first-variable derivative series for the full Neumann kernel.

This is the non-private version of the local helper used in
`IntervalMildPicard`; it is needed to expose product measurability for the
regular `B_N` duality integrand. -/
def intervalNeumannFullKernelDerivSeries (τ x y : ℝ) : ℝ :=
  (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (x - y + 2 * (k : ℝ))) +
    (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (x + y + 2 * (k : ℝ)))

theorem intervalNeumannFullKernelDerivSeries_joint_measurable :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      intervalNeumannFullKernelDerivSeries q.1.1 q.1.2 q.2) := by
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
  simpa [intervalNeumannFullKernelDerivSeries, g₁, g₂] using hmeas

theorem intervalNeumannFullKernelDerivSeries_eq_deriv_fst
    {τ : ℝ} (hτ : 0 < τ) (x y : ℝ) :
    intervalNeumannFullKernelDerivSeries τ x y =
      deriv (fun z : ℝ => intervalNeumannFullKernel τ z y) x := by
  simp [intervalNeumannFullKernelDerivSeries,
    (hasDerivAt_intervalNeumannFullKernel_fst hτ x y).deriv]

/-- L1 version of the first-variable differentiation-under-the-integral
representation for `intervalFullSemigroupOperator`.

The bounded-data version is already public as
`intervalFullSemigroupOperator_hasDerivAt_fst`; this is the non-private L1
variant copied from the Picard measurability file. -/
theorem intervalFullSemigroupOperator_hasDerivAt_fst_of_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1)) (x : ℝ) :
    HasDerivAt (fun z : ℝ => intervalFullSemigroupOperator t f z)
      (∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x * f y
        ∂(intervalMeasure 1)) x := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨intervalMeasure_univ_lt_top 1⟩
  set M : ℝ := ∑' k : ℤ,
    (heatGradWindowBound t x 2 k + heatGradWindowBound t x 2 k) with hM_def
  have hMnn : 0 ≤ M := by
    rw [hM_def]
    exact tsum_nonneg fun k => by
      unfold heatGradWindowBound heatGradPointwiseBound
      positivity
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := x)
    (bound := fun y => M * ‖f y‖)
    (F := fun z y => intervalNeumannFullKernel t z y * f y)
    (F' := fun z y => deriv (fun z' : ℝ => intervalNeumannFullKernel t z' y) z * f y)
    (Metric.ball_mem_nhds x one_pos)
    ?hFmeas ?hFint ?hF'meas ?hbound ?hbdint ?hdiff).2
  case hFmeas =>
    exact Filter.Eventually.of_forall fun z => by
      have hcont := continuousOn_intervalNeumannFullKernel_snd ht z
      exact (hcont.aestronglyMeasurable measurableSet_Icc).mul
        hf_int.aestronglyMeasurable
  case hFint =>
    obtain ⟨CK, hCK⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        (continuousOn_intervalNeumannFullKernel_snd ht x)
    have hK_bound : ∀ᵐ y ∂(intervalMeasure 1),
        ‖intervalNeumannFullKernel t x y‖ ≤ CK := by
      change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ‖intervalNeumannFullKernel t x y‖ ≤ CK
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun y hy => hCK y hy
    have hcont := continuousOn_intervalNeumannFullKernel_snd ht x
    exact hf_int.bdd_mul (hcont.aestronglyMeasurable measurableSet_Icc) hK_bound
  case hF'meas =>
    have hcont := continuousOn_deriv_intervalNeumannFullKernel_fst ht x
    exact (hcont.aestronglyMeasurable measurableSet_Icc).mul
      hf_int.aestronglyMeasurable
  case hbound =>
    change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ z ∈ Metric.ball x 1,
        ‖deriv (fun z' : ℝ => intervalNeumannFullKernel t z' y) z * f y‖ ≤ M * ‖f y‖
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy z hz => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hz1 : |z - x| ≤ 1 := by
      rw [← Real.dist_eq]
      exact le_of_lt (Metric.mem_ball.mp hz)
    have hy1 : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact mul_le_mul_of_nonneg_right
      (abs_deriv_intervalNeumannFullKernel_fst_le_const ht x hz1 hy1)
      (norm_nonneg (f y))
  case hbdint =>
    exact hf_int.norm.const_mul M
  case hdiff =>
    refine Filter.Eventually.of_forall fun y z _ => ?_
    have hderiv := hasDerivAt_intervalNeumannFullKernel_fst ht z y
    simpa [hderiv.deriv] using hderiv.mul_const (f y)

end ShenWork.IntervalNeumannFullKernel

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

open ShenWork.IntervalNeumannFullKernel

private lemma intervalMeasure_prod_mem_Icc :
    ∀ᵐ p : ℝ × ℝ ∂((intervalMeasure 1).prod (intervalMeasure 1)),
      p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 := by
  have hx : ∀ᵐ x : ℝ ∂(intervalMeasure 1), x ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    exact ae_restrict_mem measurableSet_Icc
  have hy : ∀ᵐ y : ℝ ∂(intervalMeasure 1), y ∈ Set.Icc (0 : ℝ) 1 := hx
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae]
  · filter_upwards [hx] with x hxmem
    filter_upwards [hy] with y hymem
    exact ⟨hxmem, hymem⟩
  · exact measurableSet_Icc.prod measurableSet_Icc

theorem bN_fubini_integrable_of_integrable
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
        (fun p : ℝ × ℝ => intervalNeumannFullKernelDerivSeries τ p.2 p.1)
        (μ.prod μ) :=
    (intervalNeumannFullKernelDerivSeries_joint_measurable.comp hmap).aestronglyMeasurable
  have hpre_meas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          intervalNeumannFullKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2))
        (μ.prod μ) :=
    hseries_meas.mul hψg.aestronglyMeasurable
  have hdom : Integrable (fun p : ℝ × ℝ => C * ‖ψ p.1 * g p.2‖) (μ.prod μ) :=
    hψg.norm.const_mul C
  have hpre_int : Integrable
      (fun p : ℝ × ℝ =>
        intervalNeumannFullKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2))
      (μ.prod μ) := by
    refine Integrable.mono' hdom hpre_meas ?_
    filter_upwards [intervalMeasure_prod_mem_Icc] with p hp
    have hxabs : |p.2 - (0 : ℝ)| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
    have hyabs : |p.1| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    have hK :
        |intervalNeumannFullKernelDerivSeries τ p.2 p.1| ≤ C := by
      rw [intervalNeumannFullKernelDerivSeries_eq_deriv_fst hτ, hC_def]
      exact abs_deriv_intervalNeumannFullKernel_fst_le_const
        (t := τ) hτ (0 : ℝ) (z := p.2) (y := p.1) hxabs hyabs
    calc ‖intervalNeumannFullKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2)‖
        = |intervalNeumannFullKernelDerivSeries τ p.2 p.1| * ‖ψ p.1 * g p.2‖ := by
          simp [Real.norm_eq_abs]
      _ ≤ C * ‖ψ p.1 * g p.2‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg _)
  have htarget_eq :
      (fun p : ℝ × ℝ =>
        intervalNeumannFullKernelDerivSeries τ p.2 p.1 * (ψ p.1 * g p.2))
        =
      (fun p : ℝ × ℝ =>
        deriv (fun y' : ℝ => intervalNeumannFullKernel τ p.1 y') p.2
          * g p.2 * ψ p.1) := by
    funext p
    rw [intervalNeumannFullKernelDerivSeries_eq_deriv_fst hτ]
    rw [← deriv_intervalNeumannFullKernel_snd_eq_fst_swap hτ p.1 p.2]
    ring
  rwa [htarget_eq] at hpre_int

theorem bN_duality_L1
    {τ : ℝ} (hτ : 0 < τ) (g ψ : ℝ → ℝ)
    (hg : Integrable g (intervalMeasure 1))
    (hψ : Integrable ψ (intervalMeasure 1)) :
    (∫ x, intervalConjugateKernelOperator τ g x * ψ x ∂ intervalMeasure 1)
      =
    -(∫ y, g y *
        deriv (fun z : ℝ => intervalFullSemigroupOperator τ ψ z) y
        ∂ intervalMeasure 1) :=
  bN_duality_regular hτ g ψ
    (bN_fubini_integrable_of_integrable hτ hg hψ)
    (fun y =>
      (intervalFullSemigroupOperator_hasDerivAt_fst_of_integrable
        hτ hψ y).deriv)

/-- Exact remaining non-L1 closure for extending the L1 theorem beyond the
regular functions used by the current cron2 route.

This is deliberately not asserted as a hypothesis-free fact: the problematic
branch is the `B_N` kernel-derivative side, where boundedness of `∂K` alone
does not imply that multiplying a non-L1 function remains non-integrable. -/
def BNNonL1Closure : Prop :=
  ∀ ⦃τ : ℝ⦄, 0 < τ → ∀ g ψ : ℝ → ℝ,
    (¬ Integrable ψ (intervalMeasure 1) →
      (∫ x, intervalConjugateKernelOperator τ g x * ψ x ∂ intervalMeasure 1) = 0)
    ∧
    (Integrable ψ (intervalMeasure 1) → ¬ Integrable g (intervalMeasure 1) →
      (∫ x, intervalConjugateKernelOperator τ g x * ψ x ∂ intervalMeasure 1)
        =
      -(∫ y, g y *
          deriv (fun z : ℝ => intervalFullSemigroupOperator τ ψ z) y
          ∂ intervalMeasure 1))

end ShenWork.Paper2.BFormPositiveDatumNegPart
