/-
  A full-Neumann-semigroup restart identity for bounded measurable sources.

  The main point is that no spatial continuity of the source slices is needed.
  We first extend Chapman--Kolmogorov from the existing continuous-input theorem
  to bounded measurable inputs, by proving the kernel convolution identity and
  applying Fubini.  A second Fubini interchange then pulls the fixed outer
  semigroup through the head of a Duhamel integral.
-/
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.PDE.IntervalFullKernelSDependentMeasurable
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.IntervalConjugateKernelIBP
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.Paper2.IntervalMildPicardThreshold

open MeasureTheory Set Filter

noncomputable section

namespace ShenWork.Paper2.IntervalFullDuhamelRestart

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalNeumannFullKernel intervalFullSemigroupOperator
   intervalNeumannFullKernel_integrable intervalNeumannFullKernel_nonneg
   cosineCoeffs)
open ShenWork.IntervalSemigroupComposition
  (cosineCoeffs_unitIntervalCosineHeatValue
   unitIntervalCosineHeatValue_exp_damped)
open ShenWork.IntervalFullKernelSpectralClean
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)
open ShenWork.IntervalConjugateCosineSeries
  (neumannCosineWeight intervalSineInner
   intervalNeumannFullKernel_eq_cosineKernel_nat
   deriv_intervalNeumannFullKernel_eq_cosineKernel_snd)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_eq_neg_derivSeries_integral
   intervalNeumannFullKernelDerivSeries_eq_zero_of_nonpos
   intervalConjugateKernelOperator_s_param_joint_measurable)
open ShenWork.CosineSpectrum (cosineMode)

private theorem neumannCosineWeight_mul_cosineMode_abs_le_two
    (n : ℕ) (z : ℝ) :
    |neumannCosineWeight n * cosineMode n z| ≤ (2 : ℝ) := by
  have hw : |neumannCosineWeight n| ≤ (2 : ℝ) := by
    unfold neumannCosineWeight
    by_cases hn : n = 0 <;> simp [hn]
  have hc : |cosineMode n z| ≤ (1 : ℝ) := by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  rw [abs_mul]
  calc
    |neumannCosineWeight n| * |cosineMode n z| ≤ 2 * 1 :=
      mul_le_mul hw hc (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

private theorem intervalNeumannFullKernel_eq_cosineHeatValue
    {t : ℝ} (ht : 0 < t) (x z : ℝ) :
    intervalNeumannFullKernel t x z =
      unitIntervalCosineHeatValue t
        (fun n => neumannCosineWeight n * cosineMode n z) x := by
  rw [intervalNeumannFullKernel_eq_cosineKernel_nat ht x z]
  unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
  apply tsum_congr
  intro n
  simp only [cosineMode, unitIntervalCosineMode]
  ring

private theorem cosineCoeffs_intervalNeumannFullKernel_column
    {t : ℝ} (ht : 0 < t) (z : ℝ) (n : ℕ) :
    cosineCoeffs (fun y => intervalNeumannFullKernel t y z) n =
      Real.exp (-t * unitIntervalCosineEigenvalue n) *
        (neumannCosineWeight n * cosineMode n z) := by
  have hfun :
      (fun y => intervalNeumannFullKernel t y z) =
        fun y => unitIntervalCosineHeatValue t
          (fun k => neumannCosineWeight k * cosineMode k z) y := by
    funext y
    exact intervalNeumannFullKernel_eq_cosineHeatValue ht y z
  rw [hfun]
  exact cosineCoeffs_unitIntervalCosineHeatValue ht
    (fun k => neumannCosineWeight_mul_cosineMode_abs_le_two k z) n

/-- Kernel Chapman--Kolmogorov identity on the unit interval. -/
theorem intervalNeumannFullKernel_comp
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) :
    (∫ y, intervalNeumannFullKernel s x y *
        intervalNeumannFullKernel t y z ∂(intervalMeasure 1)) =
      intervalNeumannFullKernel (s + t) x z := by
  let a : ℕ → ℝ := fun n => neumannCosineWeight n * cosineMode n z
  have ha : ∀ n, |a n| ≤ (2 : ℝ) := fun n =>
    neumannCosineWeight_mul_cosineMode_abs_le_two n z
  have hkernel_fun :
      (fun y => intervalNeumannFullKernel t y z) =
        fun y => unitIntervalCosineHeatValue t a y := by
    funext y
    exact intervalNeumannFullKernel_eq_cosineHeatValue ht y z
  have hcont : Continuous (fun y => intervalNeumannFullKernel t y z) := by
    rw [hkernel_fun]
    exact
      (ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatValue_contDiff_two
        ht ha).continuous
  have hcoeff : ∀ n,
      |cosineCoeffs (fun y => intervalNeumannFullKernel t y z) n| ≤ (2 : ℝ) := by
    intro n
    rw [cosineCoeffs_intervalNeumannFullKernel_column ht z n, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-t * unitIntervalCosineEigenvalue n) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue
        positivity
      nlinarith [mul_nonneg ht.le hlam]
    exact (mul_le_mul he (ha n) (abs_nonneg _) (by norm_num)).trans_eq
      (one_mul 2)
  change intervalFullSemigroupOperator s
      (fun y => intervalNeumannFullKernel t y z) x = _
  calc
    intervalFullSemigroupOperator s
        (fun y => intervalNeumannFullKernel t y z) x
        = unitIntervalCosineHeatValue s
            (cosineCoeffs (fun y => intervalNeumannFullKernel t y z)) x :=
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc hs hcont hcoeff hx
    _ = unitIntervalCosineHeatValue s
          (fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) * a n) x := by
      unfold unitIntervalCosineHeatValue
      apply tsum_congr
      intro n
      rw [cosineCoeffs_intervalNeumannFullKernel_column ht z n]
    _ = unitIntervalCosineHeatValue (s + t) a x :=
      unitIntervalCosineHeatValue_exp_damped s t a x
    _ = intervalNeumannFullKernel (s + t) x z :=
      (intervalNeumannFullKernel_eq_cosineHeatValue (by linarith) x z).symm

private theorem intervalNeumannFullKernel_symm
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalNeumannFullKernel t x y = intervalNeumannFullKernel t y x := by
  rw [intervalNeumannFullKernel_eq_cosineKernel_nat ht x y,
    intervalNeumannFullKernel_eq_cosineKernel_nat ht y x]
  apply tsum_congr
  intro n
  ring

private theorem intervalNeumannFullKernel_joint_measurable
    {t : ℝ} (ht : 0 < t) :
    Measurable (fun p : ℝ × ℝ => intervalNeumannFullKernel t p.1 p.2) := by
  set g : ℤ → ℝ × ℝ → ℝ := fun k p =>
    heatKernel t (p.1 - p.2 + 2 * (k : ℝ)) +
      heatKernel t (p.1 + p.2 + 2 * (k : ℝ)) with hg
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    simp only [g]
    unfold heatKernel
    fun_prop
  have hg_sum : ∀ p, Summable (fun k : ℤ => g k p) := by
    intro p
    exact
      (ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable ht (p.1 - p.2)).add
        (ShenWork.IntervalNeumannFullKernel.latticeGaussianSummable ht (p.1 + p.2))
  have hmeas :=
    ShenWork.IntervalNeumannFullKernel.measurable_tsum_int_of_summable hg_meas hg_sum
  have hfun :
      (fun p : ℝ × ℝ => intervalNeumannFullKernel t p.1 p.2) =
        fun p => ∑' k : ℤ, g k p := by
    funext p
    rfl
  rw [hfun]
  exact hmeas

set_option maxHeartbeats 2000000 in
/-- Chapman--Kolmogorov for bounded measurable inputs.  Unlike
`IntervalSemigroupComposition.intervalFullSemigroupOperator_comp`, this version
does not require spatial continuity of the input. -/
theorem intervalFullSemigroupOperator_comp_of_bounded
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_int : Integrable f (intervalMeasure 1))
    {C : ℝ} (hC : 0 ≤ C) (hf_bound : ∀ z, |f z| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator s
        (fun y => intervalFullSemigroupOperator t f y) x =
      intervalFullSemigroupOperator (s + t) f x := by
  let μ := intervalMeasure 1
  let F : ℝ × ℝ → ℝ := fun p =>
    intervalNeumannFullKernel s x p.1 *
      intervalNeumannFullKernel t p.1 p.2 * f p.2
  have hK_s_ae : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      intervalNeumannFullKernel s x p.1) (μ.prod μ) := by
    have hy : AEStronglyMeasurable (fun y => intervalNeumannFullKernel s x y) μ := by
      simpa [μ, ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet] using
        (ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
          hs x).aestronglyMeasurable measurableSet_Icc
    exact hy.comp_fst
  have hK_t_meas : Measurable (fun p : ℝ × ℝ =>
      intervalNeumannFullKernel t p.1 p.2) :=
    intervalNeumannFullKernel_joint_measurable ht
  have hF_meas : AEStronglyMeasurable F (μ.prod μ) := by
    exact (hK_s_ae.mul hK_t_meas.aestronglyMeasurable).mul hf_meas.comp_snd
  have hF_int : Integrable F (μ.prod μ) := by
    refine (MeasureTheory.integrable_prod_iff' hF_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall (fun z => ?_)
      have hcont_s : ContinuousOn
          (fun y => intervalNeumannFullKernel s x y) (Set.Icc (0 : ℝ) 1) :=
        ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd hs x
      have hcont_t : ContinuousOn
          (fun y => intervalNeumannFullKernel t y z) (Set.Icc (0 : ℝ) 1) := by
        have h :=
          ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd ht z
        exact h.congr (fun y _hy => intervalNeumannFullKernel_symm ht y z)
      have hprod : Integrable
          (fun y => intervalNeumannFullKernel s x y *
            intervalNeumannFullKernel t y z) μ := by
        simpa [μ, ShenWork.IntervalDomain.intervalMeasure,
          ShenWork.IntervalDomain.intervalSet] using
          (hcont_s.mul hcont_t).integrableOn_Icc
      simpa [F, mul_assoc] using hprod.mul_const (f z)
    · have habs_int : Integrable (fun z =>
          intervalNeumannFullKernel (s + t) x z * |f z|) μ := by
        exact
          ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
            (by linarith) x hf_int.norm hC (fun z => by
              simpa [Real.norm_eq_abs] using hf_bound z)
      have hinner :
          (fun z => ∫ y, ‖F (y, z)‖ ∂μ) =
            fun z => intervalNeumannFullKernel (s + t) x z * |f z| := by
        funext z
        calc
          (∫ y, ‖F (y, z)‖ ∂μ) =
              ∫ y, (intervalNeumannFullKernel s x y *
                intervalNeumannFullKernel t y z) * |f z| ∂μ := by
            apply integral_congr_ae
            refine Filter.Eventually.of_forall (fun y => ?_)
            simp only [F, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (intervalNeumannFullKernel_nonneg hs x y),
              abs_of_nonneg (intervalNeumannFullKernel_nonneg ht y z)]
          _ = (∫ y, intervalNeumannFullKernel s x y *
                intervalNeumannFullKernel t y z ∂μ) * |f z| := by
            rw [integral_mul_const]
          _ = intervalNeumannFullKernel (s + t) x z * |f z| := by
            rw [intervalNeumannFullKernel_comp hs ht hx z]
      rw [hinner]
      exact habs_int
  unfold intervalFullSemigroupOperator
  have hswap := MeasureTheory.integral_integral_swap
    (μ := μ) (ν := μ) (f := fun y z => F (y, z)) hF_int
  calc
    (∫ y, intervalNeumannFullKernel s x y *
        (∫ z, intervalNeumannFullKernel t y z * f z ∂μ) ∂μ) =
        ∫ y, ∫ z, F (y, z) ∂μ ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      change intervalNeumannFullKernel s x y *
          (∫ z, intervalNeumannFullKernel t y z * f z ∂μ) =
        ∫ z, F (y, z) ∂μ
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [F]
      ring
    _ = ∫ z, ∫ y, F (y, z) ∂μ ∂μ := hswap
    _ = ∫ z, intervalNeumannFullKernel (s + t) x z * f z ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun z => ?_)
      calc
        (∫ y, F (y, z) ∂μ) =
            (∫ y, intervalNeumannFullKernel s x y *
              intervalNeumannFullKernel t y z ∂μ) * f z := by
          simp only [F]
          rw [integral_mul_const]
        _ = intervalNeumannFullKernel (s + t) x z * f z := by
          rw [intervalNeumannFullKernel_comp hs ht hx z]

private theorem intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator intervalNeumannFullKernel
  simp [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht]

set_option maxHeartbeats 2000000 in
/-- Pull a fixed positive outer semigroup through the head of a bounded
measurable Duhamel integral.  The exceptional time `s = a`, where the concrete
kernel convention has `S(0) = 0`, is discarded as a null singleton. -/
theorem intervalFullSemigroupOperator_duhamel_head
    {a τ : ℝ} (ha : 0 < a) (haτ : a < τ)
    {q : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {C : ℝ} (hC : 0 ≤ C) (hq_bound : ∀ s y, |q s y| ≤ C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator (τ - a)
        (fun y => ∫ s in (0 : ℝ)..a,
          intervalFullSemigroupOperator (a - s) (q s) y) x =
      ∫ s in (0 : ℝ)..a,
        intervalFullSemigroupOperator (τ - s) (q s) x := by
  let μ := intervalMeasure 1
  let ν := volume.restrict (Set.Ioc (0 : ℝ) a)
  let G : ℝ × ℝ → ℝ := fun p =>
    intervalFullSemigroupOperator (a - p.2) (q p.2) p.1
  let F : ℝ × ℝ → ℝ := fun p =>
    intervalNeumannFullKernel (τ - a) x p.1 * G p
  have houter : 0 < τ - a := sub_pos.mpr haτ
  have hG_meas : Measurable G := by
    have hbase :=
      ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
        hq_meas
    have hmap : Measurable (fun p : ℝ × ℝ => ((a, p.1), p.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    simpa [G] using hbase.comp hmap
  have hG_bound : ∀ p, |G p| ≤ C := by
    intro p
    by_cases htime : 0 < a - p.2
    · exact
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
          htime hC (hq_bound p.2) p.1
    · rw [show G p = 0 by
          simp only [G]
          exact intervalFullSemigroupOperator_eq_zero_of_nonpos
            (not_lt.mp htime) (q p.2) p.1, abs_zero]
      exact hC
  have hK_ae : AEStronglyMeasurable
      (fun p : ℝ × ℝ => intervalNeumannFullKernel (τ - a) x p.1)
      (μ.prod ν) := by
    have hy : AEStronglyMeasurable
        (fun y => intervalNeumannFullKernel (τ - a) x y) μ := by
      simpa [μ, ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet] using
        (ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
          houter x).aestronglyMeasurable measurableSet_Icc
    exact hy.comp_fst
  have hF_meas : AEStronglyMeasurable F (μ.prod ν) := by
    exact hK_ae.mul hG_meas.aestronglyMeasurable
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hmajorant : Integrable
      (fun p : ℝ × ℝ => intervalNeumannFullKernel (τ - a) x p.1 * C)
      (μ.prod ν) := by
    have hy : Integrable
        (fun y => intervalNeumannFullKernel (τ - a) x y * C) μ :=
      (intervalNeumannFullKernel_integrable houter x).mul_const C
    exact hy.comp_fst ν
  have hF_int : Integrable F (μ.prod ν) := by
    refine Integrable.mono hmajorant hF_meas
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [F, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (intervalNeumannFullKernel_nonneg houter x p.1)]
    rw [abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (hG_bound p)
      (intervalNeumannFullKernel_nonneg houter x p.1)
  have hswap := MeasureTheory.integral_integral_swap
    (μ := μ) (ν := ν) (f := fun y s => F (y, s)) hF_int
  have hhead :
      (fun y => ∫ s in (0 : ℝ)..a,
          intervalFullSemigroupOperator (a - s) (q s) y) =
        fun y => ∫ s, G (y, s) ∂ν := by
    funext y
    rw [intervalIntegral.integral_of_le ha.le]
  rw [hhead, intervalIntegral.integral_of_le ha.le]
  change (∫ y, intervalNeumannFullKernel (τ - a) x y *
      (∫ s, G (y, s) ∂ν) ∂μ) =
    ∫ s, intervalFullSemigroupOperator (τ - s) (q s) x ∂ν
  calc
    (∫ y, intervalNeumannFullKernel (τ - a) x y *
        (∫ s, G (y, s) ∂ν) ∂μ) =
        ∫ y, ∫ s, F (y, s) ∂ν ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      change intervalNeumannFullKernel (τ - a) x y *
          (∫ s, G (y, s) ∂ν) = ∫ s, F (y, s) ∂ν
      rw [← integral_const_mul]
    _ = ∫ s, ∫ y, F (y, s) ∂μ ∂ν := hswap
    _ = ∫ s, intervalFullSemigroupOperator (τ - a) (fun y => G (y, s)) x ∂ν := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun s => ?_)
      rfl
    _ = ∫ s, intervalFullSemigroupOperator (τ - s) (q s) x ∂ν := by
      apply integral_congr_ae
      have hmem : ∀ᵐ s : ℝ ∂ν, s ∈ Set.Ioc (0 : ℝ) a := by
        simpa [ν] using
          (ae_restrict_mem measurableSet_Ioc :
            ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) a)),
              s ∈ Set.Ioc (0 : ℝ) a)
      have hne_vol : ∀ᵐ s : ℝ ∂volume, s ≠ a := by
        rw [ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton]
        exact Real.volume_singleton
      have hne : ∀ᵐ s : ℝ ∂ν, s ≠ a :=
        ae_mono (Measure.restrict_le_self) hne_vol
      filter_upwards [hmem, hne] with s hs hsa
      have hs_lt : s < a := lt_of_le_of_ne hs.2 hsa
      have hq_slice_meas : AEStronglyMeasurable (q s) μ := by
        have hm : Measurable (q s) :=
          hq_meas.comp (measurable_const.prodMk measurable_id)
        exact hm.aestronglyMeasurable
      have hcomp := intervalFullSemigroupOperator_comp_of_bounded
        houter (sub_pos.mpr hs_lt) hq_slice_meas (hq_int s) hC (hq_bound s) hx
      simpa [G, show (τ - a) + (a - s) = τ - s by ring] using hcomp

set_option maxHeartbeats 2000000 in
/-- Full Neumann-semigroup Duhamel restart at a positive intermediate time.

The assumptions are exactly the bounded-measurable data used by the full-kernel
Duhamel estimates: the datum and every source slice are integrable against the
unit-interval measure, the source is jointly measurable, and both are uniformly
bounded. -/
theorem intervalFullDuhamel_restart
    {a τ : ℝ} (ha : 0 < a) (haτ : a < τ)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_int : Integrable f (intervalMeasure 1))
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    {q : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_bound : ∀ s y, |q s y| ≤ Cq)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x +
        ∫ s in (0 : ℝ)..τ,
          intervalFullSemigroupOperator (τ - s) (q s) x =
      intervalFullSemigroupOperator (τ - a)
          (fun y => intervalFullSemigroupOperator a f y +
            ∫ s in (0 : ℝ)..a,
              intervalFullSemigroupOperator (a - s) (q s) y) x +
        ∫ s in a..τ,
          intervalFullSemigroupOperator (τ - s) (q s) x := by
  let μ := intervalMeasure 1
  let H : ℝ → ℝ := fun y =>
    ∫ s in (0 : ℝ)..a, intervalFullSemigroupOperator (a - s) (q s) y
  have houter : 0 < τ - a := sub_pos.mpr haτ
  have hSf_cont : Continuous (fun y => intervalFullSemigroupOperator a f y) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ha hCf hf_bound hf_meas
  have hSf_bound : ∀ y, |intervalFullSemigroupOperator a f y| ≤ Cf := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ha hCf hf_bound y
  have hSf_int : Integrable (fun y => intervalFullSemigroupOperator a f y) μ :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hSf_cont.measurable.aestronglyMeasurable hSf_bound
  have hbase_meas :=
    ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
      hq_meas
  have hH_meas : Measurable H := by
    have hv :=
      ShenWork.IntervalMildPicardThreshold.variable_interval_integral_measurable'
        hbase_meas
    have hmap : Measurable (fun y : ℝ => (a, y)) :=
      measurable_const.prodMk measurable_id
    simpa [H] using hv.comp hmap
  have hH_bound : ∀ y, |H y| ≤ a * Cq := by
    intro y
    exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      ha le_rfl hCq hq_bound y
  have haCq : 0 ≤ a * Cq := mul_nonneg ha.le hCq
  have hH_int : Integrable H μ :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hH_meas.aestronglyMeasurable hH_bound
  have hKSf : Integrable (fun y => intervalNeumannFullKernel (τ - a) x y *
      intervalFullSemigroupOperator a f y) μ :=
    ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
      houter x hSf_int hCf hSf_bound
  have hKH : Integrable (fun y => intervalNeumannFullKernel (τ - a) x y * H y) μ :=
    ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
      houter x hH_int haCq hH_bound
  have hadd :
      intervalFullSemigroupOperator (τ - a)
          (fun y => intervalFullSemigroupOperator a f y + H y) x =
        intervalFullSemigroupOperator (τ - a)
            (fun y => intervalFullSemigroupOperator a f y) x +
          intervalFullSemigroupOperator (τ - a) H x := by
    change (∫ y, intervalNeumannFullKernel (τ - a) x y *
        (intervalFullSemigroupOperator a f y + H y) ∂μ) =
      (∫ y, intervalNeumannFullKernel (τ - a) x y *
        intervalFullSemigroupOperator a f y ∂μ) +
      ∫ y, intervalNeumannFullKernel (τ - a) x y * H y ∂μ
    have hfun :
        (fun y => intervalNeumannFullKernel (τ - a) x y *
          (intervalFullSemigroupOperator a f y + H y)) =
        (fun y => intervalNeumannFullKernel (τ - a) x y *
            intervalFullSemigroupOperator a f y +
          intervalNeumannFullKernel (τ - a) x y * H y) := by
      funext y
      ring
    rw [hfun, integral_add hKSf hKH]
  have hcomp_f :
      intervalFullSemigroupOperator (τ - a)
          (fun y => intervalFullSemigroupOperator a f y) x =
        intervalFullSemigroupOperator τ f x := by
    have h := intervalFullSemigroupOperator_comp_of_bounded
      houter ha hf_meas hf_int hCf hf_bound hx
    simpa [show (τ - a) + a = τ by ring] using h
  have hhead :
      intervalFullSemigroupOperator (τ - a) H x =
        ∫ s in (0 : ℝ)..a,
          intervalFullSemigroupOperator (τ - s) (q s) x := by
    simpa [H] using intervalFullSemigroupOperator_duhamel_head
      ha haτ hq_meas hq_int hCq hq_bound hx
  have hI0τ : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (τ - s) (q s) x)
      volume (0 : ℝ) τ :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      (lt_trans ha haτ) hq_meas hCq hq_bound x
  have hI0a : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (τ - s) (q s) x)
      volume (0 : ℝ) a := by
    refine hI0τ.mono_set ?_
    rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le (lt_trans ha haτ).le]
    exact Set.Icc_subset_Icc le_rfl haτ.le
  have hIaτ : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (τ - s) (q s) x)
      volume a τ := by
    refine hI0τ.mono_set ?_
    rw [Set.uIcc_of_le haτ.le, Set.uIcc_of_le (lt_trans ha haτ).le]
    exact Set.Icc_subset_Icc ha.le le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI0a hIaτ
  change intervalFullSemigroupOperator τ f x +
      (∫ s in (0 : ℝ)..τ,
        intervalFullSemigroupOperator (τ - s) (q s) x) =
    intervalFullSemigroupOperator (τ - a)
      (fun y => intervalFullSemigroupOperator a f y + H y) x +
      ∫ s in a..τ, intervalFullSemigroupOperator (τ - s) (q s) x
  rw [hadd, hcomp_f, hhead, ← hsplit]
  ring

/-! ## Conjugate-kernel head restart -/

private theorem eigen_linear_exp_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ =>
      ((n : ℝ) * Real.pi) *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
  have hc : 0 < t * Real.pi ^ 2 := by positivity
  have hbase : Summable (fun n : ℕ =>
      Real.pi * ((n : ℝ) ^ 1 * Real.exp (-(t * Real.pi ^ 2) * (n : ℝ)))) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 hc).mul_left Real.pi
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  have hnle : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · exact le_self_pow₀ (Nat.one_le_cast.2 hn) (by norm_num)
  calc
    ((n : ℝ) * Real.pi) * Real.exp (-t * unitIntervalCosineEigenvalue n) =
        Real.pi * ((n : ℝ) ^ 1 *
          Real.exp (-(t * Real.pi ^ 2) * (n : ℝ) ^ 2)) := by
      simp only [unitIntervalCosineEigenvalue]
      ring_nf
    _ ≤ Real.pi * ((n : ℝ) ^ 1 *
          Real.exp (-(t * Real.pi ^ 2) * (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp_of_le
      nlinarith

private theorem intervalMeasure_integral_eq_intervalIntegral
    (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [ShenWork.IntervalDomain.intervalMeasure,
    ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) =
    ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem neumannCosineWeight_abs_le_two (n : ℕ) :
    |neumannCosineWeight n| ≤ (2 : ℝ) := by
  unfold neumannCosineWeight
  by_cases hn : n = 0 <;> simp [hn]

set_option maxHeartbeats 2000000 in
/-- The B-kernel cosine representation for a merely integrable, uniformly
bounded source.  This removes the spatial-continuity assumption of the older
`intervalConjugateKernelOperator_cosineSeries` theorem. -/
theorem intervalConjugateKernelOperator_cosineSeries_of_bounded
    {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg_int : Integrable g (intervalMeasure 1))
    {Cg : ℝ} (hg_bound : ∀ y, |g y| ≤ Cg)
    (x : ℝ) :
    intervalConjugateKernelOperator t g x =
      ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          (((n : ℝ) * Real.pi) * intervalSineInner g n)) * cosineMode n x := by
  classical
  unfold intervalConjugateKernelOperator
  set D : ℕ → ℝ → ℝ := fun n y =>
    (neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
      cosineMode n x) *
      (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) with hD
  set F : ℕ → ℝ → ℝ := fun n y => D n y * g y with hF
  have hD_bound : ∀ n y, ‖D n y‖ ≤
      2 * (((n : ℝ) * Real.pi) *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
    intro n y
    rw [hD, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have hw := neumannCosineWeight_abs_le_two n
    have he_nn : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) := Real.exp_nonneg _
    have hcx : |cosineMode n x| ≤ (1 : ℝ) := by
      simp only [cosineMode]
      exact Real.abs_cos_le_one _
    have hsy : |Real.sin ((n : ℝ) * Real.pi * y)| ≤ (1 : ℝ) :=
      Real.abs_sin_le_one _
    have hnpi : 0 ≤ (n : ℝ) * Real.pi := by positivity
    rw [abs_of_nonneg he_nn, abs_mul, abs_neg, abs_of_nonneg hnpi]
    calc
      (|neumannCosineWeight n| * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          |cosineMode n x|) *
          (((n : ℝ) * Real.pi) * |Real.sin ((n : ℝ) * Real.pi * y)|)
          ≤ (2 * Real.exp (-t * unitIntervalCosineEigenvalue n) * 1) *
              (((n : ℝ) * Real.pi) * 1) := by
            gcongr
      _ = 2 * (((n : ℝ) * Real.pi) *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring
  have hFint : ∀ n, Integrable (F n) (intervalMeasure 1) := by
    intro n
    have hD_meas : AEStronglyMeasurable (D n) (intervalMeasure 1) := by
      have hc : Continuous (D n) := by
        simp only [D]
        fun_prop
      exact hc.aestronglyMeasurable
    exact hg_int.bdd_mul hD_meas
      (Filter.Eventually.of_forall (fun y => hD_bound n y))
  have hF_bound : ∀ n y, ‖F n y‖ ≤
      (2 * Cg) * (((n : ℝ) * Real.pi) *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
    intro n y
    rw [hF, norm_mul, Real.norm_eq_abs]
    calc
      ‖D n y‖ * |g y| ≤
          (2 * (((n : ℝ) * Real.pi) *
            Real.exp (-t * unitIntervalCosineEigenvalue n))) * Cg :=
        mul_le_mul (hD_bound n y) (hg_bound y) (abs_nonneg _) (by positivity)
      _ = (2 * Cg) * (((n : ℝ) * Real.pi) *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring
  have hFsum : Summable (fun n : ℕ =>
      ∫ y, ‖F n y‖ ∂ intervalMeasure 1) := by
    have hmass : (intervalMeasure 1).real Set.univ = 1 := by
      rw [ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet,
        measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
      simp
    have hle : ∀ n, (∫ y, ‖F n y‖ ∂ intervalMeasure 1) ≤
        (2 * Cg) * (((n : ℝ) * Real.pi) *
          Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
      intro n
      calc
        (∫ y, ‖F n y‖ ∂ intervalMeasure 1) ≤
            ∫ _y, (2 * Cg) * (((n : ℝ) * Real.pi) *
              Real.exp (-t * unitIntervalCosineEigenvalue n))
              ∂ intervalMeasure 1 := by
          apply integral_mono_ae (hFint n).norm (integrable_const _)
          exact Filter.Eventually.of_forall (fun y => hF_bound n y)
        _ = (2 * Cg) * (((n : ℝ) * Real.pi) *
              Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
          rw [integral_const, hmass]
          simp
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun y => norm_nonneg _)) hle ?_
    exact (eigen_linear_exp_summable ht).mul_left (2 * Cg)
  have hderiv_eq : ∀ y,
      deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y = ∑' n, D n y := by
    intro y
    rw [deriv_intervalNeumannFullKernel_eq_cosineKernel_snd ht x y]
  have hintegrand : ∀ y,
      deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * g y =
        ∑' n, F n y := by
    intro y
    rw [hderiv_eq y, ← tsum_mul_right]
  rw [show (fun y => deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * g y)
      = fun y => ∑' n, F n y from by funext y; exact hintegrand y]
  have hswap :=
    (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  rw [hswap, ← tsum_neg]
  refine tsum_congr (fun n => ?_)
  rw [hF, hD, intervalMeasure_integral_eq_intervalIntegral]
  simp only
  set A : ℝ :=
    neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
      cosineMode n x with hA
  rw [show (fun y : ℝ =>
      A * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) * g y) =
      fun y : ℝ => A * (-((n : ℝ) * Real.pi) *
        (Real.sin ((n : ℝ) * Real.pi * y) * g y)) from by
      funext y
      ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  by_cases hn : n = 0
  · subst n
    simp [A, intervalSineInner, neumannCosineWeight,
      unitIntervalCosineEigenvalue, cosineMode]
  · simp only [intervalSineInner, hn, if_false]
    rw [hA, show neumannCosineWeight n = 2 by
      simp [neumannCosineWeight, hn]]
    ring

private theorem intervalSineInner_abs_le_of_bound
    {g : ℝ → ℝ} {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hg_bound : ∀ y, |g y| ≤ Cg) (n : ℕ) :
    |intervalSineInner g n| ≤ 2 * Cg := by
  by_cases hn : n = 0
  · simp [intervalSineInner, hn, hCg]
  · have hpoint : ∀ y ∈ Set.uIoc (0 : ℝ) 1,
        ‖Real.sin ((n : ℝ) * Real.pi * y) * g y‖ ≤ Cg := by
      intro y _hy
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |Real.sin ((n : ℝ) * Real.pi * y)| * |g y| ≤ 1 * Cg :=
          mul_le_mul (Real.abs_sin_le_one _) (hg_bound y)
            (abs_nonneg _) zero_le_one
        _ = Cg := one_mul _
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) hpoint
    have hI : |∫ y in (0 : ℝ)..1,
        Real.sin ((n : ℝ) * Real.pi * y) * g y| ≤ Cg := by
      simpa [Real.norm_eq_abs] using hnorm
    rw [intervalSineInner, if_neg hn]
    calc
      |2 * ∫ y in (0 : ℝ)..1,
          Real.sin ((n : ℝ) * Real.pi * y) * g y| =
          2 * |∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * Cg := mul_le_mul_of_nonneg_left hI (by norm_num)

set_option maxHeartbeats 2000000 in
/-- Mixed Chapman--Kolmogorov identity
`S(r) (B(t) g) = B(r+t) g` for bounded measurable/integrable `g`. -/
theorem intervalFullSemigroupOperator_comp_conjugate_of_bounded
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    {g : ℝ → ℝ} (hg_int : Integrable g (intervalMeasure 1))
    {Cg : ℝ} (hCg : 0 ≤ Cg) (hg_bound : ∀ y, |g y| ≤ Cg)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator r
        (fun z => intervalConjugateKernelOperator t g z) x =
      intervalConjugateKernelOperator (r + t) g x := by
  let b : ℕ → ℝ := fun n =>
    ((n : ℝ) * Real.pi) * intervalSineInner g n
  let half : ℝ := t / 2
  have hhalf : 0 < half := by simp only [half]; linarith
  let bp : ℕ → ℝ := fun n =>
    Real.exp (-half * unitIntervalCosineEigenvalue n) * b n
  let lin : ℕ → ℝ := fun n =>
    ((n : ℝ) * Real.pi) *
      Real.exp (-half * unitIntervalCosineEigenvalue n)
  have hlin_sum : Summable lin := by
    simpa [lin] using eigen_linear_exp_summable hhalf
  let M : ℝ := (2 * Cg) * ∑' n, lin n
  have hlin_nonneg : ∀ n, 0 ≤ lin n := fun n => by
    simp only [lin]
    positivity
  have hlin_tsum_nonneg : 0 ≤ ∑' n, lin n := tsum_nonneg hlin_nonneg
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by norm_num) hCg) hlin_tsum_nonneg
  have hbp_bound : ∀ n, |bp n| ≤ M := by
    intro n
    have hsine := intervalSineInner_abs_le_of_bound hCg hg_bound n
    have hterm : lin n ≤ ∑' k, lin k := by
      simpa using hlin_sum.sum_le_tsum ({n} : Finset ℕ)
        (fun k _hk => hlin_nonneg k)
    simp only [bp, b, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
    have hpabs : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
    rw [hnabs, hpabs]
    calc
      Real.exp (-half * unitIntervalCosineEigenvalue n) *
          ((n : ℝ) * Real.pi * |intervalSineInner g n|) ≤
          Real.exp (-half * unitIntervalCosineEigenvalue n) *
            (((n : ℝ) * Real.pi) * (2 * Cg)) := by
        have hnpi : 0 ≤ (n : ℝ) * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsine hnpi) (Real.exp_pos _).le
      _ = (2 * Cg) * lin n := by ring
      _ ≤ (2 * Cg) * (∑' k, lin k) := by
        exact mul_le_mul_of_nonneg_left hterm (mul_nonneg (by norm_num) hCg)
      _ = M := rfl
  have hB_heat :
      (fun z => intervalConjugateKernelOperator t g z) =
        fun z => unitIntervalCosineHeatValue half bp z := by
    funext z
    rw [intervalConjugateKernelOperator_cosineSeries_of_bounded ht hg_int hg_bound z]
    unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
    apply tsum_congr
    intro n
    simp only [bp, b, cosineMode, unitIntervalCosineMode]
    have he :
        Real.exp (-half * unitIntervalCosineEigenvalue n) *
            Real.exp (-half * unitIntervalCosineEigenvalue n) =
          Real.exp (-t * unitIntervalCosineEigenvalue n) := by
      rw [← Real.exp_add]
      congr 1
      simp only [half]
      ring
    rw [← he]
    ring
  have hB_cont : Continuous (fun z => intervalConjugateKernelOperator t g z) := by
    rw [hB_heat]
    exact
      (ShenWork.IntervalDomainRegularityBootstrap.unitIntervalCosineHeatValue_contDiff_two
        hhalf hbp_bound).continuous
  have hB_coeff : ∀ n,
      cosineCoeffs (fun z => intervalConjugateKernelOperator t g z) n =
        Real.exp (-t * unitIntervalCosineEigenvalue n) * b n := by
    intro n
    rw [hB_heat, cosineCoeffs_unitIntervalCosineHeatValue hhalf hbp_bound n]
    simp only [bp]
    have he :
        Real.exp (-half * unitIntervalCosineEigenvalue n) *
            Real.exp (-half * unitIntervalCosineEigenvalue n) =
          Real.exp (-t * unitIntervalCosineEigenvalue n) := by
      rw [← Real.exp_add]
      congr 1
      simp only [half]
      ring
    calc
      Real.exp (-half * unitIntervalCosineEigenvalue n) *
          (Real.exp (-half * unitIntervalCosineEigenvalue n) * b n) =
          (Real.exp (-half * unitIntervalCosineEigenvalue n) *
            Real.exp (-half * unitIntervalCosineEigenvalue n)) * b n := by ring
      _ = Real.exp (-t * unitIntervalCosineEigenvalue n) * b n := by rw [he]
  have hB_coeff_bound : ∀ n,
      |cosineCoeffs (fun z => intervalConjugateKernelOperator t g z) n| ≤ M := by
    rw [hB_heat]
    intro n
    rw [cosineCoeffs_unitIntervalCosineHeatValue hhalf hbp_bound n,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    have he_le : Real.exp (-half * unitIntervalCosineEigenvalue n) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hlam : 0 ≤ unitIntervalCosineEigenvalue n := by
        unfold unitIntervalCosineEigenvalue
        positivity
      nlinarith [mul_nonneg hhalf.le hlam]
    exact (mul_le_mul he_le (hbp_bound n) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul M)
  have hBout :
      intervalConjugateKernelOperator (r + t) g x =
        unitIntervalCosineHeatValue (r + t) b x := by
    rw [intervalConjugateKernelOperator_cosineSeries_of_bounded
      (by linarith) hg_int hg_bound x]
    unfold unitIntervalCosineHeatValue unitIntervalCosineHeatPointWeight
    apply tsum_congr
    intro n
    simp only [b, cosineMode, unitIntervalCosineMode]
    ring
  calc
    intervalFullSemigroupOperator r
        (fun z => intervalConjugateKernelOperator t g z) x =
        unitIntervalCosineHeatValue r
          (cosineCoeffs (fun z => intervalConjugateKernelOperator t g z)) x :=
      intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        hr hB_cont hB_coeff_bound hx
    _ = unitIntervalCosineHeatValue r
          (fun n => Real.exp (-t * unitIntervalCosineEigenvalue n) * b n) x := by
      unfold unitIntervalCosineHeatValue
      apply tsum_congr
      intro n
      rw [hB_coeff n]
    _ = unitIntervalCosineHeatValue (r + t) b x :=
      unitIntervalCosineHeatValue_exp_damped r t b x
    _ = intervalConjugateKernelOperator (r + t) g x := hBout.symm

private theorem intervalConjugateKernelOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (g : ℝ → ℝ) (x : ℝ) :
    intervalConjugateKernelOperator t g x = 0 := by
  rw [intervalConjugateKernelOperator_eq_neg_derivSeries_integral]
  have hfun :
      (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernelDerivSeries
        t y x * g y) = fun _ : ℝ => 0 := by
    funext y
    rw [intervalNeumannFullKernelDerivSeries_eq_zero_of_nonpos ht y x]
    simp
  rw [hfun, integral_zero, neg_zero]

set_option maxHeartbeats 2000000 in
/-- Pull a fixed full semigroup through the head of a conjugate-kernel Duhamel
integral.  This is the B-head needed to restart a B-form mild solution while
requiring only bounded measurability/integrability of the pre-restart flux. -/
theorem intervalFullSemigroupOperator_conjugateDuhamel_head
    {a τ : ℝ} (ha : 0 < a) (haτ : a < τ)
    {q : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_bound : ∀ s y, |q s y| ≤ Cq)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator (τ - a)
        (fun y => ∫ s in (0 : ℝ)..a,
          intervalConjugateKernelOperator (a - s) (q s) y) x =
      ∫ s in (0 : ℝ)..a,
        intervalConjugateKernelOperator (τ - s) (q s) x := by
  let μ := intervalMeasure 1
  let ν := volume.restrict (Set.Ioc (0 : ℝ) a)
  let G : ℝ × ℝ → ℝ := fun p =>
    intervalConjugateKernelOperator (a - p.2) (q p.2) p.1
  let F : ℝ × ℝ → ℝ := fun p =>
    intervalNeumannFullKernel (τ - a) x p.1 * G p
  let Cg := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  let m : ℝ → ℝ := fun s =>
    (Cg * Cq) * (a - s) ^ (-(1 / 2) : ℝ)
  have houter : 0 < τ - a := sub_pos.mpr haτ
  have hCg : 0 ≤ Cg :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hG_meas : Measurable G := by
    have hbase := intervalConjugateKernelOperator_s_param_joint_measurable hq_meas
    have hmap : Measurable (fun p : ℝ × ℝ => ((a, p.1), p.2)) :=
      (measurable_const.prodMk measurable_fst).prodMk measurable_snd
    simpa [G] using hbase.comp hmap
  have hK_ae : AEStronglyMeasurable
      (fun p : ℝ × ℝ => intervalNeumannFullKernel (τ - a) x p.1)
      (μ.prod ν) := by
    have hy : AEStronglyMeasurable
        (fun y => intervalNeumannFullKernel (τ - a) x y) μ := by
      simpa [μ, ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet] using
        (ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd
          houter x).aestronglyMeasurable measurableSet_Icc
    exact hy.comp_fst
  have hF_meas : AEStronglyMeasurable F (μ.prod ν) :=
    hK_ae.mul hG_meas.aestronglyMeasurable
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hm_int : Integrable m ν := by
    have hII :=
      (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half a).const_mul
        (Cg * Cq)
    rw [intervalIntegrable_iff, Set.uIoc_of_le ha.le] at hII
    simpa [m, ν] using hII
  have hmajorant : Integrable
      (fun p : ℝ × ℝ => intervalNeumannFullKernel (τ - a) x p.1 * m p.2)
      (μ.prod ν) :=
    Integrable.mul_prod (intervalNeumannFullKernel_integrable houter x) hm_int
  have hmemν : ∀ᵐ s : ℝ ∂ν, s ∈ Set.Ioc (0 : ℝ) a := by
    simpa [ν] using
      (ae_restrict_mem measurableSet_Ioc :
        ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) a)),
          s ∈ Set.Ioc (0 : ℝ) a)
  have hne_vol : ∀ᵐ s : ℝ ∂volume, s ≠ a := by
    rw [ae_iff]
    simp only [not_not, Set.setOf_eq_eq_singleton]
    exact Real.volume_singleton
  have hneν : ∀ᵐ s : ℝ ∂ν, s ≠ a :=
    ae_mono Measure.restrict_le_self hne_vol
  have hmem_prod : ∀ᵐ p : ℝ × ℝ ∂(μ.prod ν),
      p.2 ∈ Set.Ioc (0 : ℝ) a := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (measurableSet_Ioc.preimage measurable_snd)]
    exact Filter.Eventually.of_forall (fun _y => hmemν)
  have hne_prod : ∀ᵐ p : ℝ × ℝ ∂(μ.prod ν), p.2 ≠ a := by
    have hne_meas : MeasurableSet {p : ℝ × ℝ | p.2 ≠ a} := by
      have hsnd : Measurable (fun p : ℝ × ℝ => p.2) := measurable_snd
      have hconst : Measurable (fun _p : ℝ × ℝ => a) := measurable_const
      have h := (measurableSet_lt hsnd hconst).union
        (measurableSet_lt hconst hsnd)
      have heq : {p : ℝ × ℝ | p.2 ≠ a} =
          {p : ℝ × ℝ | p.2 < a} ∪ {p : ℝ × ℝ | a < p.2} := by
        ext p
        exact ne_iff_lt_or_gt
      rw [heq]
      exact h
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (p := fun p : ℝ × ℝ => p.2 ≠ a)
      hne_meas).2 ?_
    exact Filter.Eventually.of_forall (fun _y => hneν)
  have hF_int : Integrable F (μ.prod ν) := by
    refine Integrable.mono hmajorant hF_meas ?_
    filter_upwards [hmem_prod, hne_prod] with p hp hpa
    have hlag : 0 < a - p.2 := sub_pos.mpr (lt_of_le_of_ne hp.2 hpa)
    have hB := ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_abs_le
      hlag (hq_int p.2) (hq_bound p.2) p.1
    have hBm : |G p| ≤ m p.2 := by
      simpa [G, m, Cg, mul_assoc, mul_left_comm, mul_comm] using hB
    simp only [F, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (intervalNeumannFullKernel_nonneg houter x p.1),
      abs_of_nonneg (mul_nonneg (mul_nonneg hCg hCq)
        (Real.rpow_nonneg (sub_nonneg.mpr hp.2) _))]
    exact mul_le_mul_of_nonneg_left hBm
      (intervalNeumannFullKernel_nonneg houter x p.1)
  have hswap := MeasureTheory.integral_integral_swap
    (μ := μ) (ν := ν) (f := fun y s => F (y, s)) hF_int
  have hhead :
      (fun y => ∫ s in (0 : ℝ)..a,
          intervalConjugateKernelOperator (a - s) (q s) y) =
        fun y => ∫ s, G (y, s) ∂ν := by
    funext y
    rw [intervalIntegral.integral_of_le ha.le]
  rw [hhead, intervalIntegral.integral_of_le ha.le]
  change (∫ y, intervalNeumannFullKernel (τ - a) x y *
      (∫ s, G (y, s) ∂ν) ∂μ) =
    ∫ s, intervalConjugateKernelOperator (τ - s) (q s) x ∂ν
  calc
    (∫ y, intervalNeumannFullKernel (τ - a) x y *
        (∫ s, G (y, s) ∂ν) ∂μ) =
        ∫ y, ∫ s, F (y, s) ∂ν ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => ?_)
      change intervalNeumannFullKernel (τ - a) x y *
          (∫ s, G (y, s) ∂ν) = ∫ s, F (y, s) ∂ν
      rw [← integral_const_mul]
    _ = ∫ s, ∫ y, F (y, s) ∂μ ∂ν := hswap
    _ = ∫ s, intervalFullSemigroupOperator (τ - a) (fun y => G (y, s)) x ∂ν := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun s => ?_)
      rfl
    _ = ∫ s, intervalConjugateKernelOperator (τ - s) (q s) x ∂ν := by
      apply integral_congr_ae
      filter_upwards [hmemν, hneν] with s hs hsa
      have hslt : s < a := lt_of_le_of_ne hs.2 hsa
      have hcomp := intervalFullSemigroupOperator_comp_conjugate_of_bounded
        houter (sub_pos.mpr hslt) (hq_int s) hCq (hq_bound s) hx
      simpa [G, show (τ - a) + (a - s) = τ - s by ring] using hcomp

/-! The preceding head identity plus additivity of interval integrals gives the
public conjugate-Duhamel restart API used by the truncated B-form bootstrap. -/

/-- Restart a conjugate-kernel Duhamel integral at a positive intermediate
time.  Only joint measurability, slice integrability, and a uniform spatial
bound on the source are required. -/
theorem intervalConjugateDuhamel_restart
    {a τ : ℝ} (ha : 0 < a) (haτ : a < τ)
    {q : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_bound : ∀ s y, |q s y| ≤ Cq)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..τ,
        intervalConjugateKernelOperator (τ - s) (q s) x) =
      intervalFullSemigroupOperator (τ - a)
          (fun y => ∫ s in (0 : ℝ)..a,
            intervalConjugateKernelOperator (a - s) (q s) y) x +
        ∫ s in a..τ,
          intervalConjugateKernelOperator (τ - s) (q s) x := by
  have h0τ : 0 < τ := lt_trans ha haτ
  have hI : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (τ - s) (q s) x)
      volume (0 : ℝ) τ :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
        h0τ hCq hq_meas hq_int hq_bound
  have hsub0a : Set.uIcc (0 : ℝ) a ⊆ Set.uIcc (0 : ℝ) τ := by
    rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le h0τ.le]
    exact Set.Icc_subset_Icc le_rfl haτ.le
  have hsubaτ : Set.uIcc a τ ⊆ Set.uIcc (0 : ℝ) τ := by
    rw [Set.uIcc_of_le haτ.le, Set.uIcc_of_le h0τ.le]
    exact Set.Icc_subset_Icc ha.le le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hI.mono_set hsub0a) (hI.mono_set hsubaτ)
  rw [intervalFullSemigroupOperator_conjugateDuhamel_head
    ha haτ hq_meas hq_int hCq hq_bound hx]
  exact hsplit.symm

private theorem intervalFullSemigroupOperator_add_of_kernel_integrable
    {t x : ℝ} {f g : ℝ → ℝ}
    (hf : Integrable
      (fun y => intervalNeumannFullKernel t x y * f y) (intervalMeasure 1))
    (hg : Integrable
      (fun y => intervalNeumannFullKernel t x y * g y) (intervalMeasure 1)) :
    intervalFullSemigroupOperator t (fun y => f y + g y) x =
      intervalFullSemigroupOperator t f x + intervalFullSemigroupOperator t g x := by
  change (∫ y, intervalNeumannFullKernel t x y * (f y + g y)
      ∂ intervalMeasure 1) =
    (∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1) +
      ∫ y, intervalNeumannFullKernel t x y * g y ∂ intervalMeasure 1
  have hfun :
      (fun y => intervalNeumannFullKernel t x y * (f y + g y)) =
        fun y => intervalNeumannFullKernel t x y * f y +
          intervalNeumannFullKernel t x y * g y := by
    funext y
    ring
  rw [hfun, integral_add hf hg]

private theorem intervalFullSemigroupOperator_const_mul
    (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t (fun y => c * f y) x =
      c * intervalFullSemigroupOperator t f x := by
  change (∫ y, intervalNeumannFullKernel t x y * (c * f y)
      ∂ intervalMeasure 1) =
    c * ∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1
  calc
    (∫ y, intervalNeumannFullKernel t x y * (c * f y)
        ∂ intervalMeasure 1) =
        ∫ y, c * (intervalNeumannFullKernel t x y * f y)
          ∂ intervalMeasure 1 := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun y => by ring)
    _ = c * ∫ y, intervalNeumannFullKernel t x y * f y
          ∂ intervalMeasure 1 := integral_const_mul _ _

set_option maxHeartbeats 3000000 in
/-- Restart identity in the exact three-leg shape of a B-form mild map:
homogeneous full semigroup, a scalar multiple of a conjugate-kernel Duhamel
leg, and a full-kernel Duhamel leg. -/
theorem intervalBFormDuhamel_restart
    {a τ : ℝ} (ha : 0 < a) (haτ : a < τ)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_int : Integrable f (intervalMeasure 1))
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    {q ell : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hell_meas : Measurable (Function.uncurry ell))
    (hell_int : ∀ s, Integrable (ell s) (intervalMeasure 1))
    {Cell : ℝ} (hCell : 0 ≤ Cell) (hell_bound : ∀ s y, |ell s y| ≤ Cell)
    (c : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x +
          c * (∫ s in (0 : ℝ)..τ,
            intervalConjugateKernelOperator (τ - s) (q s) x) +
          ∫ s in (0 : ℝ)..τ,
            intervalFullSemigroupOperator (τ - s) (ell s) x =
      intervalFullSemigroupOperator (τ - a)
          (fun y => intervalFullSemigroupOperator a f y +
            c * (∫ s in (0 : ℝ)..a,
              intervalConjugateKernelOperator (a - s) (q s) y) +
            ∫ s in (0 : ℝ)..a,
              intervalFullSemigroupOperator (a - s) (ell s) y) x +
        c * (∫ s in a..τ,
          intervalConjugateKernelOperator (τ - s) (q s) x) +
        ∫ s in a..τ,
          intervalFullSemigroupOperator (τ - s) (ell s) x := by
  let μ := intervalMeasure 1
  let Sf : ℝ → ℝ := fun y => intervalFullSemigroupOperator a f y
  let HB : ℝ → ℝ := fun y =>
    ∫ s in (0 : ℝ)..a, intervalConjugateKernelOperator (a - s) (q s) y
  let HL : ℝ → ℝ := fun y =>
    ∫ s in (0 : ℝ)..a, intervalFullSemigroupOperator (a - s) (ell s) y
  let Cg := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  let CB := Cg * (2 * Real.sqrt a) * Cq
  have houter : 0 < τ - a := sub_pos.mpr haτ
  have hCg : 0 ≤ Cg :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hCB : 0 ≤ CB :=
    mul_nonneg (mul_nonneg hCg (mul_nonneg (by norm_num) (Real.sqrt_nonneg a))) hCq
  have hSf_cont : Continuous Sf := by
    exact ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ha hCf hf_bound hf_meas
  have hSf_bound : ∀ y, |Sf y| ≤ Cf := fun y =>
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      ha hCf hf_bound y
  have hSf_int : Integrable Sf μ :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hSf_cont.measurable.aestronglyMeasurable hSf_bound
  have hBbase := intervalConjugateKernelOperator_s_param_joint_measurable hq_meas
  have hHB_meas : Measurable HB := by
    have hv :=
      ShenWork.IntervalMildPicardThreshold.variable_interval_integral_measurable' hBbase
    simpa [HB] using hv.comp (measurable_const.prodMk measurable_id)
  have hBII : ∀ y, IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (a - s) (q s) y)
      volume (0 : ℝ) a := fun y =>
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
        ha hCq hq_meas hq_int hq_bound
  have hHB_bound : ∀ y, |HB y| ≤ CB := by
    intro y
    exact ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
      ha le_rfl (fun s _hs _hsa => hq_int s) hCq
      (fun s _hs _hsa => hq_bound s) y (hBII y)
  have hHB_int : Integrable HB μ :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hHB_meas.aestronglyMeasurable hHB_bound
  have hLbase :=
    ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
      hell_meas
  have hHL_meas : Measurable HL := by
    have hv :=
      ShenWork.IntervalMildPicardThreshold.variable_interval_integral_measurable' hLbase
    simpa [HL] using hv.comp (measurable_const.prodMk measurable_id)
  have hHL_bound : ∀ y, |HL y| ≤ a * Cell := by
    intro y
    exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      ha le_rfl hCell hell_bound y
  have haCell : 0 ≤ a * Cell := mul_nonneg ha.le hCell
  have hHL_int : Integrable HL μ :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hHL_meas.aestronglyMeasurable hHL_bound
  let cHB : ℝ → ℝ := fun y => c * HB y
  have hcHB_int : Integrable cHB μ := by
    simpa [cHB] using hHB_int.const_mul c
  have hcHB_bound : ∀ y, |cHB y| ≤ |c| * CB := by
    intro y
    change |c * HB y| ≤ |c| * CB
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hHB_bound y) (abs_nonneg c)
  have hcCB : 0 ≤ |c| * CB := mul_nonneg (abs_nonneg c) hCB
  have hKSf : Integrable (fun y => intervalNeumannFullKernel (τ - a) x y * Sf y) μ :=
    ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
      houter x hSf_int hCf hSf_bound
  have hKcHB : Integrable
      (fun y => intervalNeumannFullKernel (τ - a) x y * cHB y) μ :=
    ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
      houter x hcHB_int hcCB hcHB_bound
  have hKHL : Integrable (fun y => intervalNeumannFullKernel (τ - a) x y * HL y) μ :=
    ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
      houter x hHL_int haCell hHL_bound
  have hKsum : Integrable
      (fun y => intervalNeumannFullKernel (τ - a) x y * (Sf y + cHB y)) μ := by
    have hfun :
        (fun y => intervalNeumannFullKernel (τ - a) x y * (Sf y + cHB y)) =
          fun y => intervalNeumannFullKernel (τ - a) x y * Sf y +
            intervalNeumannFullKernel (τ - a) x y * cHB y := by
      funext y
      ring
    rw [hfun]
    exact hKSf.add hKcHB
  have houter_add :
      intervalFullSemigroupOperator (τ - a)
          (fun y => Sf y + cHB y + HL y) x =
        intervalFullSemigroupOperator (τ - a) Sf x +
          c * intervalFullSemigroupOperator (τ - a) HB x +
          intervalFullSemigroupOperator (τ - a) HL x := by
    rw [intervalFullSemigroupOperator_add_of_kernel_integrable hKsum hKHL,
      intervalFullSemigroupOperator_add_of_kernel_integrable hKSf hKcHB]
    change intervalFullSemigroupOperator (τ - a) Sf x +
        intervalFullSemigroupOperator (τ - a) (fun y => c * HB y) x +
        intervalFullSemigroupOperator (τ - a) HL x =
      intervalFullSemigroupOperator (τ - a) Sf x +
        c * intervalFullSemigroupOperator (τ - a) HB x +
        intervalFullSemigroupOperator (τ - a) HL x
    rw [intervalFullSemigroupOperator_const_mul]
  have hcomp_f : intervalFullSemigroupOperator (τ - a) Sf x =
      intervalFullSemigroupOperator τ f x := by
    have h := intervalFullSemigroupOperator_comp_of_bounded
      houter ha hf_meas hf_int hCf hf_bound hx
    simpa [Sf, show (τ - a) + a = τ by ring] using h
  have hheadB : intervalFullSemigroupOperator (τ - a) HB x =
      ∫ s in (0 : ℝ)..a, intervalConjugateKernelOperator (τ - s) (q s) x := by
    simpa [HB] using intervalFullSemigroupOperator_conjugateDuhamel_head
      ha haτ hq_meas hq_int hCq hq_bound hx
  have hheadL : intervalFullSemigroupOperator (τ - a) HL x =
      ∫ s in (0 : ℝ)..a, intervalFullSemigroupOperator (τ - s) (ell s) x := by
    simpa [HL] using intervalFullSemigroupOperator_duhamel_head
      ha haτ hell_meas hell_int hCell hell_bound hx
  have hBI0τ : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (τ - s) (q s) x)
      volume (0 : ℝ) τ :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
        (lt_trans ha haτ) hCq hq_meas hq_int hq_bound
  have hLI0τ : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (τ - s) (ell s) x)
      volume (0 : ℝ) τ :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      (lt_trans ha haτ) hell_meas hCell hell_bound x
  have hsub0a : Set.uIcc (0 : ℝ) a ⊆ Set.uIcc (0 : ℝ) τ := by
    rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le (lt_trans ha haτ).le]
    exact Set.Icc_subset_Icc le_rfl haτ.le
  have hsubaτ : Set.uIcc a τ ⊆ Set.uIcc (0 : ℝ) τ := by
    rw [Set.uIcc_of_le haτ.le, Set.uIcc_of_le (lt_trans ha haτ).le]
    exact Set.Icc_subset_Icc ha.le le_rfl
  have hBsplit := intervalIntegral.integral_add_adjacent_intervals
    (hBI0τ.mono_set hsub0a) (hBI0τ.mono_set hsubaτ)
  have hLsplit := intervalIntegral.integral_add_adjacent_intervals
    (hLI0τ.mono_set hsub0a) (hLI0τ.mono_set hsubaτ)
  change intervalFullSemigroupOperator τ f x +
        c * (∫ s in (0 : ℝ)..τ,
          intervalConjugateKernelOperator (τ - s) (q s) x) +
        ∫ s in (0 : ℝ)..τ,
          intervalFullSemigroupOperator (τ - s) (ell s) x =
    intervalFullSemigroupOperator (τ - a)
        (fun y => Sf y + cHB y + HL y) x +
      c * (∫ s in a..τ,
        intervalConjugateKernelOperator (τ - s) (q s) x) +
      ∫ s in a..τ,
        intervalFullSemigroupOperator (τ - s) (ell s) x
  rw [houter_add, hcomp_f, hheadB, hheadL, ← hBsplit, ← hLsplit]
  ring

/-! ## Tail integration by parts after a B-form restart -/

/-- At one positive lag, combine a conjugate-kernel flux leg with a
full-kernel source leg after spatial integration by parts. -/
theorem intervalBFormSlice_eq_fullSource_of_regularity
    {t x chi : ℝ} (ht : 0 < t) {Q ell : ℝ → ℝ}
    (H : ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity Q)
    (hQ0 : Q 0 = 0) (hQ1 : Q 1 = 0)
    (hell_int : Integrable ell (intervalMeasure 1))
    {Cell : ℝ} (hCell : 0 ≤ Cell) (hell_bound : ∀ y, |ell y| ≤ Cell) :
    (-chi) * intervalConjugateKernelOperator t Q x +
        intervalFullSemigroupOperator t ell x =
      intervalFullSemigroupOperator t
        (fun y => ell y - chi * deriv Q y) x := by
  have hibp :=
    ShenWork.Paper2.IntervalConjugateKernelIBP.intervalConjugateKernelOperator_eq_semigroup_deriv_of_regularity
      (x := x) ht H hQ0 hQ1
  rcases H with ⟨_, _, _, _, hQii⟩
  have hD_on : IntegrableOn (deriv Q) (Set.Icc (0 : ℝ) 1) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    have h := intervalIntegrable_iff.mp hQii
    simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using h
  have hD_int : Integrable (deriv Q) (intervalMeasure 1) := by
    simpa [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet] using hD_on
  have hKell : Integrable
      (fun y => intervalNeumannFullKernel t x y * ell y)
      (intervalMeasure 1) :=
    ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
      ht x hell_int hCell hell_bound
  have hKcont :=
    ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd ht x
  obtain ⟨CK, hCK⟩ := isCompact_Icc.exists_bound_of_continuousOn hKcont
  have hKmeas : AEStronglyMeasurable
      (fun y => intervalNeumannFullKernel t x y) (intervalMeasure 1) := by
    simpa [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet] using
      hKcont.aestronglyMeasurable measurableSet_Icc
  have hKbound : ∀ᵐ y ∂(intervalMeasure 1),
      ‖intervalNeumannFullKernel t x y‖ ≤ CK := by
    simp only [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet]
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with y hy
    exact hCK y hy
  have hDK : Integrable
      (fun y => deriv Q y * intervalNeumannFullKernel t x y)
      (intervalMeasure 1) :=
    hD_int.mul_bdd hKmeas hKbound
  have hKD : Integrable
      (fun y => intervalNeumannFullKernel t x y * deriv Q y)
      (intervalMeasure 1) := by
    simpa only [mul_comm] using hDK
  have hKchiD : Integrable
      (fun y => intervalNeumannFullKernel t x y * (chi * deriv Q y))
      (intervalMeasure 1) := by
    have h := hKD.const_mul chi
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hsub :=
    ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_sub
      hKell hKchiD
  have hscale :=
    intervalFullSemigroupOperator_const_mul t chi (deriv Q) x
  calc
    (-chi) * intervalConjugateKernelOperator t Q x +
          intervalFullSemigroupOperator t ell x =
        (-chi) * intervalFullSemigroupOperator t (deriv Q) x +
          intervalFullSemigroupOperator t ell x := by rw [hibp]
    _ = intervalFullSemigroupOperator t ell x -
          chi * intervalFullSemigroupOperator t (deriv Q) x := by ring
    _ = intervalFullSemigroupOperator t ell x -
          intervalFullSemigroupOperator t (fun y => chi * deriv Q y) x := by
      rw [hscale]
    _ = intervalFullSemigroupOperator t
          (fun y => ell y - chi * deriv Q y) x := hsub.symm

/-- Convert the complete post-restart B-form tail to a full-semigroup tail.
The terminal slice `s = τ`, where the lag vanishes, is removed as a null set. -/
theorem intervalBFormTail_eq_fullSource_of_regularity
    {a τ chi : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (haτ : a < τ)
    {q ell r : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hell_meas : Measurable (Function.uncurry ell))
    (hell_int : ∀ s, Integrable (ell s) (intervalMeasure 1))
    {Cell : ℝ} (hCell : 0 ≤ Cell) (hell_bound : ∀ s y, |ell s y| ≤ Cell)
    (hreg : ∀ s, a ≤ s → s ≤ τ →
      ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity (q s))
    (hq0 : ∀ s, q s 0 = 0) (hq1 : ∀ s, q s 1 = 0)
    (hrepr : ∀ s, a ≤ s → s ≤ τ → ∀ y,
      r s y = ell s y - chi * deriv (q s) y)
    (x : ℝ) :
    (-chi) * (∫ s in a..τ,
        intervalConjugateKernelOperator (τ - s) (q s) x) +
      ∫ s in a..τ,
        intervalFullSemigroupOperator (τ - s) (ell s) x =
    ∫ s in a..τ,
      intervalFullSemigroupOperator (τ - s) (r s) x := by
  have hBI0τ : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (τ - s) (q s) x)
      volume (0 : ℝ) τ :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hτ hCq hq_meas hq_int hq_bound
  have hLI0τ : IntervalIntegrable
      (fun s => intervalFullSemigroupOperator (τ - s) (ell s) x)
      volume (0 : ℝ) τ :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      hτ hell_meas hCell hell_bound x
  have hsub : Set.uIcc a τ ⊆ Set.uIcc (0 : ℝ) τ := by
    rw [Set.uIcc_of_le haτ.le, Set.uIcc_of_le hτ.le]
    exact Set.Icc_subset_Icc ha le_rfl
  have hBII := hBI0τ.mono_set hsub
  have hLII := hLI0τ.mono_set hsub
  calc
    (-chi) * (∫ s in a..τ,
          intervalConjugateKernelOperator (τ - s) (q s) x) +
        ∫ s in a..τ,
          intervalFullSemigroupOperator (τ - s) (ell s) x =
      ∫ s in a..τ,
        ((-chi) * intervalConjugateKernelOperator (τ - s) (q s) x +
          intervalFullSemigroupOperator (τ - s) (ell s) x) := by
      rw [intervalIntegral.integral_add (hBII.const_mul _) hLII,
        intervalIntegral.integral_const_mul]
    _ = ∫ s in a..τ,
        intervalFullSemigroupOperator (τ - s) (r s) x := by
      apply intervalIntegral.integral_congr_ae
      have hae_ne : ∀ᵐ s ∂volume, s ≠ τ := by
        rw [ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton]
        exact Real.volume_singleton
      filter_upwards [hae_ne] with s hsne hs
      have hsIoc : s ∈ Set.Ioc a τ := by
        simpa [Set.uIoc_of_le haτ.le] using hs
      have hslt : s < τ := lt_of_le_of_ne hsIoc.2 hsne
      have hslic := intervalBFormSlice_eq_fullSource_of_regularity
        (x := x) (chi := chi) (sub_pos.mpr hslt)
        (hreg s hsIoc.1.le hsIoc.2) (hq0 s) (hq1 s)
        (hell_int s) hCell (hell_bound s)
      have hrfun : r s = fun y => ell s y - chi * deriv (q s) y := by
        funext y
        exact hrepr s hsIoc.1.le hsIoc.2 y
      rw [hrfun]
      exact hslic

set_option linter.unusedVariables false in
set_option maxHeartbeats 3000000 in
/-- Full B-form restart followed by spatial integration by parts on the tail.
The head remains in conjugate-kernel form inside the restarted state, while
the post-restart flux and source are merged into one full-semigroup source. -/
theorem intervalBFormDuhamel_restart_ibp_tail
    {a τ : ℝ} (ha : 0 < a) (haτ : a < τ)
    {f : ℝ → ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_int : Integrable f (intervalMeasure 1))
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hf_bound : ∀ y, |f y| ≤ Cf)
    {q ell : ℝ → ℝ → ℝ}
    (hq_meas : Measurable (Function.uncurry q))
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_bound : ∀ s y, |q s y| ≤ Cq)
    (hell_meas : Measurable (Function.uncurry ell))
    (hell_int : ∀ s, Integrable (ell s) (intervalMeasure 1))
    {Cell : ℝ} (hCell : 0 ≤ Cell) (hell_bound : ∀ s y, |ell s y| ≤ Cell)
    (c : ℝ)
    (hreg : ∀ s, a ≤ s → s ≤ τ →
      ShenWork.Paper2.IntervalConjugateKernelIBP.IntervalIBPRegularity (q s))
    (hq0 : ∀ s, q s 0 = 0) (hq1 : ∀ s, q s 1 = 0)
    {r : ℝ → ℝ → ℝ}
    (hr_meas : Measurable (Function.uncurry r))
    (hr_int : ∀ s, Integrable (r s) (intervalMeasure 1))
    {Cr : ℝ} (hCr : 0 ≤ Cr) (hr_bound : ∀ s y, |r s y| ≤ Cr)
    (hr_eq : ∀ s, a ≤ s → s ≤ τ → ∀ y,
      r s y = ell s y + c * deriv (q s) y)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x +
          c * (∫ s in (0 : ℝ)..τ,
            intervalConjugateKernelOperator (τ - s) (q s) x) +
          ∫ s in (0 : ℝ)..τ,
            intervalFullSemigroupOperator (τ - s) (ell s) x =
      intervalFullSemigroupOperator (τ - a)
          (fun y => intervalFullSemigroupOperator a f y +
            c * (∫ s in (0 : ℝ)..a,
              intervalConjugateKernelOperator (a - s) (q s) y) +
            ∫ s in (0 : ℝ)..a,
              intervalFullSemigroupOperator (a - s) (ell s) y) x +
        ∫ s in a..τ,
          intervalFullSemigroupOperator (τ - s) (r s) x := by
  have hrestart := intervalBFormDuhamel_restart
    ha haτ hf_meas hf_int hCf hf_bound
    hq_meas hq_int hCq hq_bound
    hell_meas hell_int hCell hell_bound c hx
  have hrepr : ∀ s, a ≤ s → s ≤ τ → ∀ y,
      r s y = ell s y - (-c) * deriv (q s) y := by
    intro s hsa hsτ y
    rw [hr_eq s hsa hsτ y]
    ring
  have htail := intervalBFormTail_eq_fullSource_of_regularity
    (chi := -c) ha.le (lt_trans ha haτ) haτ
    hq_meas hq_int hCq hq_bound
    hell_meas hell_int hCell hell_bound
    hreg hq0 hq1 hrepr x
  calc
    intervalFullSemigroupOperator τ f x +
          c * (∫ s in (0 : ℝ)..τ,
            intervalConjugateKernelOperator (τ - s) (q s) x) +
          ∫ s in (0 : ℝ)..τ,
            intervalFullSemigroupOperator (τ - s) (ell s) x =
        intervalFullSemigroupOperator (τ - a)
            (fun y => intervalFullSemigroupOperator a f y +
              c * (∫ s in (0 : ℝ)..a,
                intervalConjugateKernelOperator (a - s) (q s) y) +
              ∫ s in (0 : ℝ)..a,
                intervalFullSemigroupOperator (a - s) (ell s) y) x +
          c * (∫ s in a..τ,
            intervalConjugateKernelOperator (τ - s) (q s) x) +
          ∫ s in a..τ,
            intervalFullSemigroupOperator (τ - s) (ell s) x := hrestart
    _ = intervalFullSemigroupOperator (τ - a)
            (fun y => intervalFullSemigroupOperator a f y +
              c * (∫ s in (0 : ℝ)..a,
                intervalConjugateKernelOperator (a - s) (q s) y) +
              ∫ s in (0 : ℝ)..a,
                intervalFullSemigroupOperator (a - s) (ell s) y) x +
          (c * (∫ s in a..τ,
            intervalConjugateKernelOperator (τ - s) (q s) x) +
          ∫ s in a..τ,
            intervalFullSemigroupOperator (τ - s) (ell s) x) := by ring
    _ = intervalFullSemigroupOperator (τ - a)
            (fun y => intervalFullSemigroupOperator a f y +
              c * (∫ s in (0 : ℝ)..a,
                intervalConjugateKernelOperator (a - s) (q s) y) +
              ∫ s in (0 : ℝ)..a,
                intervalFullSemigroupOperator (a - s) (ell s) y) x +
          ∫ s in a..τ,
            intervalFullSemigroupOperator (τ - s) (r s) x := by
      simpa only [neg_neg] using congrArg
        (fun z => intervalFullSemigroupOperator (τ - a)
          (fun y => intervalFullSemigroupOperator a f y +
            c * (∫ s in (0 : ℝ)..a,
              intervalConjugateKernelOperator (a - s) (q s) y) +
            ∫ s in (0 : ℝ)..a,
              intervalFullSemigroupOperator (a - s) (ell s) y) x + z)
        htail

end ShenWork.Paper2.IntervalFullDuhamelRestart
