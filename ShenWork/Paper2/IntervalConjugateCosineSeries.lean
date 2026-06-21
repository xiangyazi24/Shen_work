/-
  Spectral cosine-series assembly for the interval conjugate-kernel map.

  This file is additive: it introduces new lemmas only.  The kernel calculation
  uses the cosine-kernel form of `intervalNeumannFullKernel` and differentiates
  `cos(nπy)` in the second variable.  Positive modes carry the Neumann factor
  `2`, so the sine pairing below is normalized with the same positive-mode
  factor as `cosineCoeffs`.

  Proof-health print commands appear near the end of this file.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.PDE.IntervalSemigroupComposition
import ShenWork.PDE.IntervalSemigroupUniform
import ShenWork.PDE.IntervalSpectralSubtypeAdapter

open MeasureTheory Filter Topology

noncomputable section

namespace ShenWork.IntervalConjugateCosineSeries

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateDuhamelMap IntervalConjugateMildSolution)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalFullKernelSpectralClean
  (intervalNeumannFullKernel_eq_cosineKernel_clean
   intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)
open ShenWork.IntervalSpectralSubtypeAdapter
  (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff duhamelSpectral_eq_cosineSeries)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs
   coupledChemDivSourceLift coupledLogisticSourceLift)
open ShenWork.CosineSpectrum (cosineMode)

/-- Neumann cosine-series normalization: the zero mode has weight `1`, positive
integer modes have weight `2`. -/
def neumannCosineWeight (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2

/-- Normalized sine pairing matching the Neumann positive-mode normalization.
For `n > 0`, this is `2∫₀¹ sin(nπy) g(y) dy`; for `n = 0` it is zero. -/
def intervalSineInner (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    2 * ∫ y in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * y) * g y

private theorem intervalSineInner_abs_le_of_bound
    {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ y ∈ Set.Icc (0 : ℝ) 1, |g y| ≤ C) :
    ∀ n : ℕ, |intervalSineInner g n| ≤ 2 * C := by
  intro n
  unfold intervalSineInner
  by_cases hn : n = 0
  · simp [hn, hC]
  · simp only [hn, if_false]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hint :
        ‖∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y‖ ≤ C := by
      have hbound : ∀ y ∈ Set.uIoc (0 : ℝ) 1,
          ‖Real.sin ((n : ℝ) * Real.pi * y) * g y‖ ≤ C := by
        intro y hy
        have hyUcc : y ∈ Set.uIcc (0 : ℝ) 1 :=
          Set.uIoc_subset_uIcc hy
        have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hyUcc
        rw [Real.norm_eq_abs, abs_mul]
        calc |Real.sin ((n : ℝ) * Real.pi * y)| * |g y|
            ≤ 1 * C :=
              mul_le_mul (Real.abs_sin_le_one _)
                (hg y hyIcc) (abs_nonneg _) (by norm_num)
          _ = C := by ring
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := C) hbound
    calc
      2 * |∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y|
          = 2 * ‖∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y‖ := by
              rw [Real.norm_eq_abs]
      _ ≤ 2 * C := mul_le_mul_of_nonneg_left hint (by norm_num)

private theorem intervalSineInner_abs_le_of_continuous
    {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |intervalSineInner g n| ≤ C := by
  obtain ⟨C, hCbd⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (hg.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hC_nonneg : 0 ≤ C :=
    le_trans (norm_nonneg (g 0)) (hCbd 0 ⟨le_refl 0, by norm_num⟩)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC_nonneg, ?_⟩
  exact intervalSineInner_abs_le_of_bound hC_nonneg
    (fun y hy => by simpa [Real.norm_eq_abs] using hCbd y hy)

private theorem intervalSineInner_abs_le_of_continuousOn
    {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |intervalSineInner g n| ≤ C := by
  obtain ⟨C, hCbd⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hg
  have hC_nonneg : 0 ≤ C :=
    le_trans (norm_nonneg (g 0)) (hCbd 0 ⟨le_refl 0, by norm_num⟩)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC_nonneg, ?_⟩
  exact intervalSineInner_abs_le_of_bound hC_nonneg
    (fun y hy => by simpa [Real.norm_eq_abs] using hCbd y hy)

/-- First-order sine/cosine coefficient bridge.  If a flux `g` vanishes at both
endpoints and has derivative `g'` on `[0,1]`, then the positive-mode B-kernel
coefficient `(nπ) · ⟪g,sin nπ·⟫` is exactly the Neumann cosine coefficient of
`g'`; the zero mode is zero by the fundamental theorem of calculus. -/
theorem freq_mul_intervalSineInner_eq_cosineCoeffs_deriv
    {g g' : ℝ → ℝ}
    (hg_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' y) y)
    (hg'_int : IntervalIntegrable g' volume (0 : ℝ) 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) :
    ∀ n : ℕ,
      ((n : ℝ) * Real.pi) * intervalSineInner g n =
        cosineCoeffs g' n := by
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [intervalSineInner, if_pos rfl,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
      if_pos rfl]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
    have hFTC :
        ∫ y in (0 : ℝ)..1, g' y = g 1 - g 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hg_deriv hg'_int
    rw [hFTC, hg0, hg1]
    ring
  · have hcos_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun z : ℝ => Real.cos ((n : ℝ) * Real.pi * z))
          (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * y)) y := by
      intro y _hy
      have hlin : HasDerivAt (fun z : ℝ => ((n : ℝ) * Real.pi) * z)
          ((n : ℝ) * Real.pi) y := by
        simpa using (hasDerivAt_id y).const_mul ((n : ℝ) * Real.pi)
      convert hlin.cos using 1
      ring
    have hcos'_int :
        IntervalIntegrable
          (fun y : ℝ =>
            -((n : ℝ) * Real.pi) *
              Real.sin ((n : ℝ) * Real.pi * y))
          volume (0 : ℝ) 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hIBP :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul
        hcos_deriv hg_deriv hcos'_int hg'_int
    have hcos_int :
        (∫ y in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * y) * g' y) =
        ((n : ℝ) * Real.pi) *
          ∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y := by
      rw [hIBP, hg0, hg1]
      ring_nf
      rw [neg_eq_iff_eq_neg]
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      ring_nf
    rw [intervalSineInner, if_neg hn,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
      if_neg hn]
    rw [hcos_int]
    ring

/-- Open-interior version of
`freq_mul_intervalSineInner_eq_cosineCoeffs_deriv`.  The endpoint values of the
flux are still used to kill the boundary term, but differentiability is required
only on `(0,1)`. -/
theorem freq_mul_intervalSineInner_eq_cosineCoeffs_deriv_open
    {g g' : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Set.uIcc (0 : ℝ) 1))
    (hg_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt g (g' y) y)
    (hg'_int : IntervalIntegrable g' volume (0 : ℝ) 1)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) :
    ∀ n : ℕ,
      ((n : ℝ) * Real.pi) * intervalSineInner g n =
        cosineCoeffs g' n := by
  intro n
  have hg_cont_Icc : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hg_cont
  by_cases hn : n = 0
  · subst hn
    rw [intervalSineInner, if_pos rfl,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
      if_pos rfl]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, one_mul]
    have hFTC :
        ∫ y in (0 : ℝ)..1, g' y = g 1 - g 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (a := (0 : ℝ)) (b := 1) (f := g) (f' := g')
        (by norm_num : (0 : ℝ) ≤ 1) hg_cont_Icc hg_deriv hg'_int
    rw [hFTC, hg0, hg1]
    ring
  · have hcos_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun z : ℝ => Real.cos ((n : ℝ) * Real.pi * z))
          (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * y)) y := by
      intro y _hy
      have hlin : HasDerivAt (fun z : ℝ => ((n : ℝ) * Real.pi) * z)
          ((n : ℝ) * Real.pi) y := by
        simpa using (hasDerivAt_id y).const_mul ((n : ℝ) * Real.pi)
      convert hlin.cos using 1
      ring
    have hcos_cont : ContinuousOn
        (fun y : ℝ => Real.cos ((n : ℝ) * Real.pi * y))
        (Set.uIcc (0 : ℝ) 1) := by
      exact (Real.continuous_cos.comp (by fun_prop)).continuousOn
    have hcos'_int :
        IntervalIntegrable
          (fun y : ℝ =>
            -((n : ℝ) * Real.pi) *
              Real.sin ((n : ℝ) * Real.pi * y))
          volume (0 : ℝ) 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hcos_io : ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1),
        HasDerivAt (fun z : ℝ => Real.cos ((n : ℝ) * Real.pi * z))
          (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * y)) y := by
      simpa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hcos_deriv
    have hg_io : ∀ y ∈ Set.Ioo (min (0 : ℝ) 1) (max 0 1),
        HasDerivAt g (g' y) y := by
      simpa [min_eq_left (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] using hg_deriv
    have hIBP :=
      intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
        hcos_cont hg_cont hcos_io hg_io hcos'_int hg'_int
    have hcos_int :
        (∫ y in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * y) * g' y) =
        ((n : ℝ) * Real.pi) *
          ∫ y in (0 : ℝ)..1,
            Real.sin ((n : ℝ) * Real.pi * y) * g y := by
      rw [hIBP, hg0, hg1]
      ring_nf
      rw [neg_eq_iff_eq_neg]
      rw [← intervalIntegral.integral_const_mul]
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro y _hy
      ring_nf
    rw [intervalSineInner, if_neg hn,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
      if_neg hn]
    rw [hcos_int]
    ring

private theorem neumannCosineWeight_abs_le_two (n : ℕ) :
    |neumannCosineWeight n| ≤ (2 : ℝ) := by
  unfold neumannCosineWeight
  by_cases hn : n = 0 <;> simp [hn]

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
  calc ((n : ℝ) * Real.pi) * Real.exp (-t * unitIntervalCosineEigenvalue n)
      = Real.pi * ((n : ℝ) ^ 1 *
          Real.exp (-(t * Real.pi ^ 2) * (n : ℝ) ^ 2)) := by
          simp only [unitIntervalCosineEigenvalue]
          ring_nf
    _ ≤ Real.pi * ((n : ℝ) ^ 1 *
          Real.exp (-(t * Real.pi ^ 2) * (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp_of_le
          nlinarith

private theorem kernelNatCoeff_grad_summable {t x : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ =>
      |neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineMode n x| * ((n : ℝ) * Real.pi)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((eigen_linear_exp_summable ht).mul_left 2)
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  have hcos : |cosineMode n x| ≤ 1 := by
    simp only [cosineMode]
    exact Real.abs_cos_le_one _
  have hweight : |neumannCosineWeight n| ≤ 2 :=
    neumannCosineWeight_abs_le_two n
  have hE_nonneg : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    Real.exp_nonneg _
  have hnπ_nonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
  have hweightE :
      |neumannCosineWeight n| * Real.exp (-t * unitIntervalCosineEigenvalue n)
        ≤ 2 * Real.exp (-t * unitIntervalCosineEigenvalue n) :=
    mul_le_mul_of_nonneg_right hweight hE_nonneg
  have hweightEcos :
      |neumannCosineWeight n| * Real.exp (-t * unitIntervalCosineEigenvalue n)
          * |cosineMode n x|
        ≤ 2 * (Real.exp (-t * unitIntervalCosineEigenvalue n) * 1) := by
    calc |neumannCosineWeight n| * Real.exp (-t * unitIntervalCosineEigenvalue n)
            * |cosineMode n x|
        ≤ 2 * Real.exp (-t * unitIntervalCosineEigenvalue n) * 1 :=
            mul_le_mul hweightE hcos (abs_nonneg _)
              (mul_nonneg (by norm_num) hE_nonneg)
      _ = 2 * (Real.exp (-t * unitIntervalCosineEigenvalue n) * 1) := by ring
  calc |neumannCosineWeight n| *
        Real.exp (-t * unitIntervalCosineEigenvalue n) * |cosineMode n x|
        * ((n : ℝ) * Real.pi)
      ≤ 2 * (Real.exp (-t * unitIntervalCosineEigenvalue n) * 1)
        * ((n : ℝ) * Real.pi) := by
          exact mul_le_mul_of_nonneg_right hweightEcos hnπ_nonneg
    _ = 2 * (((n : ℝ) * Real.pi) *
        Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring

/-- The integer cosine kernel folded to the Neumann-normalized natural-mode
cosine kernel. -/
theorem intervalNeumannFullKernel_eq_cosineKernel_nat
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalNeumannFullKernel t x y =
      ∑' n : ℕ,
        (neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineMode n x) * cosineMode n y := by
  classical
  set φ : ℤ → ℝ := fun m =>
    Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
      (Real.cos ((m : ℝ) * Real.pi * x) *
        Real.cos ((m : ℝ) * Real.pi * y)) with hφ
  have hφsumm : Summable φ := by
    apply Summable.of_norm_bounded
      (g := fun m : ℤ => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2))
      (ShenWork.IntervalFullKernelSpectralClean.expWeightSummable t ht)
    intro m
    rw [hφ, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hcosx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hcosy : |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
    calc Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
          |Real.cos ((m : ℝ) * Real.pi * x) *
            Real.cos ((m : ℝ) * Real.pi * y)|
        = Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
            (|Real.cos ((m : ℝ) * Real.pi * x)| *
              |Real.cos ((m : ℝ) * Real.pi * y)|) := by rw [abs_mul]
      _ ≤ Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) * 1 := by
          have hprod :
              |Real.cos ((m : ℝ) * Real.pi * x)| *
                  |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := by
            calc |Real.cos ((m : ℝ) * Real.pi * x)| *
                  |Real.cos ((m : ℝ) * Real.pi * y)|
                ≤ 1 * 1 := mul_le_mul hcosx hcosy (abs_nonneg _) (by norm_num)
              _ = 1 := by ring
          exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
      _ = Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) := by ring
  have hφeven : Function.Even φ := by
    intro m
    rw [hφ]
    simp only
    congr 1
    · push_cast; ring
    · rw [show (((-m : ℤ) : ℝ) * Real.pi * x) =
          -((m : ℝ) * Real.pi * x) by push_cast; ring, Real.cos_neg]
      rw [show (((-m : ℤ) : ℝ) * Real.pi * y) =
          -((m : ℝ) * Real.pi * y) by push_cast; ring, Real.cos_neg]
  have hfold := tsum_int_eq_zero_add_two_mul_tsum_pnat hφeven hφsumm
  set ψ : ℕ → ℝ := fun n =>
    (neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
      cosineMode n x) * cosineMode n y with hψ
  have hψ0 : ψ 0 = φ 0 := by
    simp [hψ, hφ, neumannCosineWeight, unitIntervalCosineEigenvalue, cosineMode]
  have hψsucc : ∀ n : ℕ, ψ (n + 1) = 2 * φ ((n + 1 : ℕ) : ℤ) := by
    intro n
    simp only [hψ, hφ, neumannCosineWeight, Nat.succ_ne_zero, if_false]
    simp only [unitIntervalCosineEigenvalue, cosineMode]
    push_cast
    ring
  have hψsumm : Summable ψ := by
    have hφnat : Summable (fun n : ℕ => φ (n : ℤ)) :=
      (summable_int_iff_summable_nat_and_neg.mp hφsumm).1
    apply (summable_nat_add_iff 1).mp
    have : (fun n : ℕ => ψ (n + 1)) =
        fun n : ℕ => 2 * φ ((n + 1 : ℕ) : ℤ) := by
      funext n; exact hψsucc n
    rw [this]
    exact ((summable_nat_add_iff 1).mpr hφnat).mul_left 2
  have hψtsum : (∑' n : ℕ, ψ n) =
      φ 0 + ∑' n : ℕ, (2 : ℝ) * φ ((n + 1 : ℕ) : ℤ) := by
    rw [hψsumm.tsum_eq_zero_add, hψ0]
    congr 1
    exact tsum_congr hψsucc
  have hpnat : (∑' n : ℕ+, φ (n : ℤ)) =
      ∑' n : ℕ, φ ((n + 1 : ℕ) : ℤ) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => φ (n : ℤ))]
  rw [intervalNeumannFullKernel_eq_cosineKernel_clean t ht x y]
  rw [show (∑' m : ℤ, Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) *
        (Real.cos ((m : ℝ) * Real.pi * x) *
          Real.cos ((m : ℝ) * Real.pi * y))) = ∑' m : ℤ, φ m from rfl]
  rw [hfold]
  rw [show (∑' n : ℕ,
        (neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineMode n x) * cosineMode n y) = ∑' n : ℕ, ψ n from rfl]
  rw [hψtsum]
  rw [show (∑' n : ℕ, (2 : ℝ) * φ ((n + 1 : ℕ) : ℤ))
        = 2 * ∑' n : ℕ, φ ((n + 1 : ℕ) : ℤ) from by rw [tsum_mul_left]]
  rw [← hpnat, two_nsmul]
  ring

/-- Second-variable derivative of the full Neumann kernel in folded cosine
spectral form. -/
theorem deriv_intervalNeumannFullKernel_eq_cosineKernel_snd
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y =
      ∑' n : ℕ,
        (neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineMode n x) *
          (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) := by
  set c : ℕ → ℝ := fun n =>
    neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
      cosineMode n x with hc
  have hgrad : Summable (fun n : ℕ => |c n| * ((n : ℝ) * Real.pi)) := by
    simpa [c, hc] using kernelNatCoeff_grad_summable (t := t) (x := x) ht
  have hderiv :=
    ShenWork.IntervalResolverGradientBridge.cosineSeries_hasDerivAt_of_gradSummable
      (c := c) hgrad y
  have hfun : (fun y' : ℝ => intervalNeumannFullKernel t x y') =
      fun y' : ℝ => ∑' n : ℕ, c n * Real.cos ((n : ℝ) * Real.pi * y') := by
    funext y'
    rw [intervalNeumannFullKernel_eq_cosineKernel_nat ht x y']
    refine tsum_congr (fun n => ?_)
    simp only [hc, cosineMode]
  rw [hfun]
  simpa [c, hc, cosineMode] using hderiv.deriv

private theorem intervalMeasure_integral_eq_intervalIntegral
    (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0:ℝ) 1, f y ∂volume) = ∫ y in (0:ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **B-kernel cosine series.**  With the normalized sine pairing
`intervalSineInner`, the conjugate-kernel operator sends a flux `g` to cosine
modes with coefficients
`e^{-tλ_n} · (nπ · intervalSineInner g n)`. -/
theorem intervalConjugateKernelOperator_cosineSeries
    {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (x : ℝ) :
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
  obtain ⟨Cg, hCg⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hg
  have hCg_nonneg : 0 ≤ Cg :=
    le_trans (norm_nonneg (g 0)) (hCg 0 ⟨le_refl 0, by norm_num⟩)
  set F : ℕ → ℝ → ℝ := fun n y => D n y * g y with hF
  have hFint : ∀ n, Integrable (F n) (intervalMeasure 1) := by
    intro n
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    have hcont : ContinuousOn (F n) (Set.Icc (0 : ℝ) 1) := by
      rw [hF, hD]
      have hlin : Continuous (fun y : ℝ => ((n : ℝ) * Real.pi) * y) :=
        continuous_const.mul continuous_id
      have hsin : Continuous (fun y : ℝ =>
          Real.sin ((n : ℝ) * Real.pi * y)) := by
        simpa [mul_assoc] using Real.continuous_sin.comp hlin
      have hDcont : Continuous (D n) := by
        rw [hD]
        exact continuous_const.mul (continuous_const.mul hsin)
      exact hDcont.continuousOn.mul hg
    simpa [IntegrableOn] using
      hcont.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hFbound : ∀ n y, y ∈ Set.Icc (0 : ℝ) 1 →
      ‖F n y‖ ≤
        (2 * Cg) *
          (((n : ℝ) * Real.pi) *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
    intro n y hy
    rw [hF, hD, Real.norm_eq_abs, abs_mul, abs_mul]
    have hweight := neumannCosineWeight_abs_le_two n
    have hE_nonneg : 0 ≤ Real.exp (-t * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    have hcos : |cosineMode n x| ≤ 1 := by
      simp only [cosineMode]
      exact Real.abs_cos_le_one _
    have hnπ_nonneg : 0 ≤ (n : ℝ) * Real.pi := by positivity
    have hA :
        |neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineMode n x|
          ≤ 2 * Real.exp (-t * unitIntervalCosineEigenvalue n) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hE_nonneg]
      have hweightE :
          |neumannCosineWeight n| * Real.exp (-t * unitIntervalCosineEigenvalue n)
            ≤ 2 * Real.exp (-t * unitIntervalCosineEigenvalue n) :=
        mul_le_mul_of_nonneg_right hweight hE_nonneg
      calc |neumannCosineWeight n| *
            Real.exp (-t * unitIntervalCosineEigenvalue n) * |cosineMode n x|
          ≤ 2 * Real.exp (-t * unitIntervalCosineEigenvalue n) * 1 :=
              mul_le_mul hweightE hcos (abs_nonneg _)
                (mul_nonneg (by norm_num) hE_nonneg)
        _ = 2 * Real.exp (-t * unitIntervalCosineEigenvalue n) := by ring
    have hB :
        |-(↑n * Real.pi) * Real.sin (↑n * Real.pi * y)| ≤ (n : ℝ) * Real.pi := by
      rw [abs_mul, abs_neg, abs_of_nonneg hnπ_nonneg]
      calc (n : ℝ) * Real.pi * |Real.sin ((n : ℝ) * Real.pi * y)|
          ≤ (n : ℝ) * Real.pi * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hnπ_nonneg
        _ = (n : ℝ) * Real.pi := by ring
    have hg' : |g y| ≤ Cg := by simpa [Real.norm_eq_abs] using hCg y hy
    have hAB :
        |neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineMode n x| *
          |-(↑n * Real.pi) * Real.sin (↑n * Real.pi * y)|
          ≤ (2 * Real.exp (-t * unitIntervalCosineEigenvalue n)) *
              ((n : ℝ) * Real.pi) :=
      mul_le_mul hA hB (abs_nonneg _)
        (mul_nonneg (by norm_num) hE_nonneg)
    calc |neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
            cosineMode n x| *
          |-(↑n * Real.pi) * Real.sin (↑n * Real.pi * y)| * |g y|
        ≤ ((2 * Real.exp (-t * unitIntervalCosineEigenvalue n)) *
              ((n : ℝ) * Real.pi)) * Cg :=
            mul_le_mul hAB hg' (abs_nonneg _)
              (mul_nonneg (mul_nonneg (by norm_num) hE_nonneg) hnπ_nonneg)
      _ = (2 * Cg) *
          (((n : ℝ) * Real.pi) *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) := by ring
  have hFsum : Summable (fun n : ℕ => ∫ y, ‖F n y‖ ∂ intervalMeasure 1) := by
    have hμ_meas : (intervalMeasure 1).real Set.univ = 1 := by
      rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
        measureReal_restrict_apply_univ, measureReal_def, Real.volume_Icc]
      simp
    have hle : ∀ n, ∫ y, ‖F n y‖ ∂ intervalMeasure 1 ≤
        (2 * Cg) * (((n : ℝ) * Real.pi) *
          Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
      intro n
      have hbound_ae : ∀ᵐ y ∂ intervalMeasure 1,
          ‖F n y‖ ≤ (2 * Cg) * (((n : ℝ) * Real.pi) *
            Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
        rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
        rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
        exact Filter.Eventually.of_forall (fun y hy => hFbound n y hy)
      calc ∫ y, ‖F n y‖ ∂ intervalMeasure 1
          ≤ ∫ _y, (2 * Cg) * (((n : ℝ) * Real.pi) *
              Real.exp (-t * unitIntervalCosineEigenvalue n)) ∂ intervalMeasure 1 :=
            MeasureTheory.integral_mono_ae ((hFint n).norm)
              (MeasureTheory.integrable_const _) hbound_ae
        _ = (2 * Cg) * (((n : ℝ) * Real.pi) *
              Real.exp (-t * unitIntervalCosineEigenvalue n)) := by
            rw [MeasureTheory.integral_const, hμ_meas]; simp
    refine Summable.of_nonneg_of_le
      (fun n => MeasureTheory.integral_nonneg (fun y => norm_nonneg _)) hle ?_
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
  rw [hswap]
  rw [← tsum_neg]
  refine tsum_congr (fun n => ?_)
  rw [hF, hD]
  rw [intervalMeasure_integral_eq_intervalIntegral]
  simp only
  set A : ℝ :=
    neumannCosineWeight n * Real.exp (-t * unitIntervalCosineEigenvalue n) *
      cosineMode n x with hAdef
  rw [show (fun y : ℝ =>
      A * (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * y)) * g y)
      = fun y : ℝ =>
        A * (-((n : ℝ) * Real.pi) *
          (Real.sin ((n : ℝ) * Real.pi * y) * g y)) from by
        funext y; ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_const_mul]
  by_cases hn : n = 0
  · subst hn
    simp [A, intervalSineInner, neumannCosineWeight, unitIntervalCosineEigenvalue, cosineMode]
  · simp only [intervalSineInner, hn, if_false]
    rw [hAdef]
    rw [show neumannCosineWeight n = 2 by simp [neumannCosineWeight, hn]]
    ring

/-- Spectral identification of the B-kernel with the full Neumann semigroup
applied to a derivative.  The only coefficient input is the first-order
sine/cosine bridge; endpoint and regularity hypotheses are packaged in
`freq_mul_intervalSineInner_eq_cosineCoeffs_deriv`. -/
theorem intervalConjugateKernelOperator_eq_fullSemigroup_deriv_of_coeff
    {t x M : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    {g g' : ℝ → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hM : ∀ n : ℕ, |cosineCoeffs g' n| ≤ M)
    (hcoeff : ∀ n : ℕ,
      ((n : ℝ) * Real.pi) * intervalSineInner g n =
        cosineCoeffs g' n) :
    intervalConjugateKernelOperator t g x =
      intervalFullSemigroupOperator t g' x := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  rw [intervalConjugateKernelOperator_cosineSeries ht
    (hg.continuousOn (s := Set.Icc (0 : ℝ) 1)) x]
  rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hg' hM hxIcc]
  unfold unitIntervalCosineHeatValue
  refine tsum_congr (fun n => ?_)
  rw [hcoeff n]
  simp [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode, cosineMode]
  ring

/-- Endpoint-zero `C¹` version of
`intervalConjugateKernelOperator_eq_fullSemigroup_deriv_of_coeff`. -/
theorem intervalConjugateKernelOperator_eq_fullSemigroup_deriv_of_endpoint_zero
    {t x M : ℝ} (ht : 0 < t) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    {g g' : ℝ → ℝ} (hg : Continuous g) (hg' : Continuous g')
    (hg_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' y) y)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    (hM : ∀ n : ℕ, |cosineCoeffs g' n| ≤ M) :
    intervalConjugateKernelOperator t g x =
      intervalFullSemigroupOperator t g' x := by
  have hg'_int : IntervalIntegrable g' volume (0 : ℝ) 1 :=
    hg'.intervalIntegrable 0 1
  exact intervalConjugateKernelOperator_eq_fullSemigroup_deriv_of_coeff
    ht hx hg hg' hM
    (freq_mul_intervalSineInner_eq_cosineCoeffs_deriv
      hg_deriv hg'_int hg0 hg1)

/-- Linear F3 trace: if `g` is endpoint-zero `C¹` on `[0,1]` with continuous
derivative `g'`, then `B_N(r)g` tends uniformly on every interior set `K` to
`deriv g` as `r ↓ 0`.  The proof is the spectral identity
`B_N(r)g = S_N(r)g'` plus the full-kernel uniform approximate identity. -/
theorem intervalConjugateKernelOperator_tendstoUniformlyOn_deriv_of_endpoint_zero
    {K : Set ℝ} {M : ℝ} {g g' : ℝ → ℝ}
    (hKsub : K ⊆ Set.Ioo (0 : ℝ) 1)
    (hg : Continuous g) (hg' : Continuous g')
    (hg_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt g (g' y) y)
    (hg0 : g 0 = 0) (hg1 : g 1 = 0)
    (hM : ∀ n : ℕ, |cosineCoeffs g' n| ≤ M) :
    TendstoUniformlyOn
      (fun r x => intervalConjugateKernelOperator r g x)
      (fun x => deriv g x) (𝓝[>] (0 : ℝ)) K := by
  have hS_Icc :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
      g' hg'
  have hS_K :
      TendstoUniformlyOn
        (fun r x => intervalFullSemigroupOperator r g' x)
        g' (𝓝[>] (0 : ℝ)) K :=
    hS_Icc.mono (fun x hx => Set.Ioo_subset_Icc_self (hKsub hx))
  have hcongr :
      ∀ᶠ r in 𝓝[>] (0 : ℝ),
        Set.EqOn
          (fun x => intervalFullSemigroupOperator r g' x)
          (fun x => intervalConjugateKernelOperator r g x) K := by
    filter_upwards [self_mem_nhdsWithin] with r hr x hx
    exact (intervalConjugateKernelOperator_eq_fullSemigroup_deriv_of_endpoint_zero
      (t := r) (x := x) (M := M) hr (hKsub hx)
      hg hg' hg_deriv hg0 hg1 hM).symm
  have htarget : Set.EqOn g' (fun x => deriv g x) K := by
    intro x hx
    have hxIcc : x ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Set.Ioo_subset_Icc_self (hKsub hx)
    exact (hg_deriv x hxIcc).deriv.symm
  exact (hS_K.congr hcongr).congr_right htarget

theorem unitIntervalCosineHeatValue_linear_sub
    (t x c : ℝ) (a b : ℕ → ℝ)
    (ha : Summable (fun n : ℕ => unitIntervalCosineHeatPointWeight t x n * a n))
    (hb : Summable (fun n : ℕ => unitIntervalCosineHeatPointWeight t x n * b n)) :
    unitIntervalCosineHeatValue t (fun n => a n - c * b n) x =
      unitIntervalCosineHeatValue t a x -
        c * unitIntervalCosineHeatValue t b x := by
  unfold unitIntervalCosineHeatValue
  have hterm :
      (fun n : ℕ => unitIntervalCosineHeatPointWeight t x n * (a n - c * b n)) =
        fun n : ℕ =>
          unitIntervalCosineHeatPointWeight t x n * a n +
            (-c) * (unitIntervalCosineHeatPointWeight t x n * b n) := by
    funext n
    ring
  rw [hterm, Summable.tsum_add ha (hb.mul_left (-c)), tsum_mul_left]
  ring

private theorem heatValue_logisticCoeff_summable
    {τ x M : ℝ} (hτ : 0 < τ) {p : CM2Params}
    {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hM : ∀ n : ℕ, |coupledLogisticSourceCoeffs p u s n| ≤ M) :
    Summable (fun n : ℕ =>
      unitIntervalCosineHeatPointWeight τ x n *
        coupledLogisticSourceCoeffs p u s n) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => M * Real.exp (-τ * unitIntervalCosineEigenvalue n))
    ((ShenWork.IntervalSemigroupComposition.expEigSummable hτ).mul_left M) ?_
  intro n
  have hE : 0 ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
    Real.exp_nonneg _
  have hcos : |unitIntervalCosineMode n x| ≤ 1 := by
    unfold unitIntervalCosineMode
    exact Real.abs_cos_le_one _
  rw [Real.norm_eq_abs, unitIntervalCosineHeatPointWeight, abs_mul, abs_mul,
    abs_of_nonneg hE]
  calc
    Real.exp (-τ * unitIntervalCosineEigenvalue n) *
        |unitIntervalCosineMode n x| *
        |coupledLogisticSourceCoeffs p u s n|
        ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) * 1 *
            |coupledLogisticSourceCoeffs p u s n| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcos hE) (abs_nonneg _)
    _ ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) * 1 * M := by
          exact mul_le_mul_of_nonneg_left (hM n)
            (mul_nonneg hE (by norm_num))
    _ = M * Real.exp (-τ * unitIntervalCosineEigenvalue n) := by ring

private theorem heatValue_chemCoeff_summable_of_sine_bound
    {τ x M : ℝ} (hτ : 0 < τ) {p : CM2Params}
    {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hM : ∀ n : ℕ,
      |intervalSineInner (chemFluxLifted p (u s)) n| ≤ M)
    (hcoeff : ∀ n : ℕ,
      coupledChemDivSourceCoeffs p u s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner (chemFluxLifted p (u s)) n) :
    Summable (fun n : ℕ =>
      unitIntervalCosineHeatPointWeight τ x n *
        coupledChemDivSourceCoeffs p u s n) := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  refine Summable.of_norm_bounded
    (g := fun n : ℕ =>
      M * (((n : ℝ) * Real.pi) *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)))
    ((eigen_linear_exp_summable hτ).mul_left M) ?_
  intro n
  have hE : 0 ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
    Real.exp_nonneg _
  have hfreq : 0 ≤ (n : ℝ) * Real.pi := by positivity
  have hcos : |unitIntervalCosineMode n x| ≤ 1 := by
    unfold unitIntervalCosineMode
    exact Real.abs_cos_le_one _
  rw [Real.norm_eq_abs, unitIntervalCosineHeatPointWeight, hcoeff n, abs_mul]
  have hEcos_abs :
      |Real.exp (-τ * unitIntervalCosineEigenvalue n) *
          unitIntervalCosineMode n x|
        ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) := by
    rw [abs_mul, abs_of_nonneg hE]
    exact mul_le_of_le_one_right hE hcos
  have hfreq_sine_le :
      |(n : ℝ) * Real.pi *
          intervalSineInner (chemFluxLifted p (u s)) n|
        ≤ (n : ℝ) * Real.pi * M := by
    rw [abs_mul, abs_of_nonneg hfreq]
    exact mul_le_mul_of_nonneg_left (hM n) hfreq
  calc
    |Real.exp (-τ * unitIntervalCosineEigenvalue n) *
        unitIntervalCosineMode n x| *
        |(n : ℝ) * Real.pi *
          intervalSineInner (chemFluxLifted p (u s)) n|
        ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) *
            ((n : ℝ) * Real.pi * M) := by
          exact mul_le_mul hEcos_abs hfreq_sine_le
            (abs_nonneg _) hE
    _ = M * (((n : ℝ) * Real.pi) *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring

theorem bForm_source_bridge_from_sine_coefficients
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t s x Mlog Msin : ℝ}
    (hts : 0 < t - s) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hflux_cont : ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
    (hlog_cont : Continuous (logisticLifted p (u s)))
    (hlog_bound : ∀ n : ℕ, |coupledLogisticSourceCoeffs p u s n| ≤ Mlog)
    (hsine_bound : ∀ n : ℕ,
      |intervalSineInner (chemFluxLifted p (u s)) n| ≤ Msin)
    (hchem_coeff : ∀ n : ℕ,
      coupledChemDivSourceCoeffs p u s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner (chemFluxLifted p (u s)) n) :
    (-p.χ₀) * intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x
      + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x := by
  have hlog_bound' :
      ∀ n : ℕ, |cosineCoeffs (logisticLifted p (u s)) n| ≤ Mlog := by
    intro n
    simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
      logisticLifted] using hlog_bound n
  have hlog :
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x =
        unitIntervalCosineHeatValue (t - s)
          (coupledLogisticSourceCoeffs p u s) x := by
    simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
      logisticLifted] using
      (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
        hts hlog_cont hlog_bound' hx)
  have hchem :
      intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x =
        unitIntervalCosineHeatValue (t - s)
          (coupledChemDivSourceCoeffs p u s) x := by
    rw [intervalConjugateKernelOperator_cosineSeries hts hflux_cont x]
    rw [ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
    refine tsum_congr (fun n => ?_)
    rw [hchem_coeff n]
  have hsum_log :
      Summable (fun n : ℕ =>
        unitIntervalCosineHeatPointWeight (t - s) x n *
          coupledLogisticSourceCoeffs p u s n) :=
    heatValue_logisticCoeff_summable hts hlog_bound
  have hsum_chem :
      Summable (fun n : ℕ =>
        unitIntervalCosineHeatPointWeight (t - s) x n *
          coupledChemDivSourceCoeffs p u s n) :=
    heatValue_chemCoeff_summable_of_sine_bound hts hsine_bound hchem_coeff
  have hsrc :
      unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x =
        unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p u s) x -
          p.χ₀ * unitIntervalCosineHeatValue (t - s)
            (coupledChemDivSourceCoeffs p u s) x := by
    simpa [bFormSourceCoeffs] using
      unitIntervalCosineHeatValue_linear_sub (t - s) x p.χ₀
        (coupledLogisticSourceCoeffs p u s)
        (coupledChemDivSourceCoeffs p u s)
        hsum_log hsum_chem
  rw [hlog, hchem, hsrc]
  ring

/-- Coefficient-level chem-div/flux bridge from the source definition and the
first-order sine/cosine integration-by-parts identity.  This is the analytic
payload behind the B-form source bridge: once the lifted chemotaxis-divergence
source is the derivative of the lifted flux on `[0,1]`, its cosine coefficients
are exactly `(nπ)` times the normalized sine coefficients of the flux. -/
theorem coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hsource_cont : Continuous (coupledChemDivSourceLift p u s))
    (hflux_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) y) :
    ∀ n : ℕ,
      coupledChemDivSourceCoeffs p u s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner (chemFluxLifted p (u s)) n := by
  have hsource_int :
      IntervalIntegrable (coupledChemDivSourceLift p u s) volume (0 : ℝ) 1 :=
    hsource_cont.intervalIntegrable 0 1
  have hflux0 : chemFluxLifted p (u s) 0 = 0 := by
    unfold chemFluxLifted
    rw [ShenWork.Paper2.resolverGradReal_zero]
    simp
  have hflux1 : chemFluxLifted p (u s) 1 = 0 := by
    unfold chemFluxLifted
    rw [ShenWork.Paper2.resolverGradReal_one]
    simp
  have hcoeff :=
    freq_mul_intervalSineInner_eq_cosineCoeffs_deriv
      (g := chemFluxLifted p (u s))
      (g' := coupledChemDivSourceLift p u s)
      hflux_deriv hsource_int hflux0 hflux1
  intro n
  rw [coupledChemDivSourceCoeffs]
  exact (hcoeff n).symm

/-- Open-interior version of
`coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv`.  This
is the form used when the flux is only known to be differentiable on `(0,1)`;
the endpoint contribution is still killed by the genuine resolver-gradient trace
of `chemFluxLifted`. -/
theorem coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv_open
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s : ℝ}
    (hflux_cont : ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
    (hsource_int : IntervalIntegrable (coupledChemDivSourceLift p u s)
      volume (0 : ℝ) 1)
    (hflux_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) y) :
    ∀ n : ℕ,
      coupledChemDivSourceCoeffs p u s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner (chemFluxLifted p (u s)) n := by
  have hflux0 : chemFluxLifted p (u s) 0 = 0 := by
    unfold chemFluxLifted
    rw [ShenWork.Paper2.resolverGradReal_zero]
    simp
  have hflux1 : chemFluxLifted p (u s) 1 = 0 := by
    unfold chemFluxLifted
    rw [ShenWork.Paper2.resolverGradReal_one]
    simp
  have hcoeff :=
    freq_mul_intervalSineInner_eq_cosineCoeffs_deriv_open
      (g := chemFluxLifted p (u s))
      (g' := coupledChemDivSourceLift p u s)
      (by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hflux_cont)
      hflux_deriv hsource_int hflux0 hflux1
  intro n
  rw [coupledChemDivSourceCoeffs]
  exact (hcoeff n).symm

/-- Pointwise source bridge from the actual derivative relation between the
chemotaxis flux and chem-div source.  The cosine coefficient identity is proved
inside this theorem, rather than supplied as a free `hsource_bridge` datum. -/
theorem bForm_source_bridge_from_flux_deriv
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t s x Mlog : ℝ}
    (hts : 0 < t - s) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hflux_cont : Continuous (chemFluxLifted p (u s)))
    (hsource_cont : Continuous (coupledChemDivSourceLift p u s))
    (hflux_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) y)
    (hlog_cont : Continuous (logisticLifted p (u s)))
    (hlog_bound : ∀ n : ℕ, |coupledLogisticSourceCoeffs p u s n| ≤ Mlog) :
    (-p.χ₀) * intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x
      + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x := by
  obtain ⟨Msin, _hMsin_nonneg, hsine_bound⟩ :=
    intervalSineInner_abs_le_of_continuousOn
      (hflux_cont.continuousOn (s := Set.Icc (0 : ℝ) 1))
  exact bForm_source_bridge_from_sine_coefficients
    (p := p) (u := u) (t := t) (s := s) (x := x)
    (Mlog := Mlog) (Msin := Msin)
    hts hx (hflux_cont.continuousOn (s := Set.Icc (0 : ℝ) 1))
    hlog_cont hlog_bound hsine_bound
    (coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv
      (p := p) (u := u) (s := s) hsource_cont hflux_deriv)

/-- Subtype-continuity variant of `bForm_source_bridge_from_flux_deriv`.  This
is the paper-faithful form for the logistic leg: the lifted zero-extension need
not be globally continuous when the source is nonzero at the boundary. -/
theorem bForm_source_bridge_from_flux_deriv_subtypeCont
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t s x Mlog : ℝ}
    (hts : 0 < t - s) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hflux_cont : Continuous (chemFluxLifted p (u s)))
    (hsource_cont : Continuous (coupledChemDivSourceLift p u s))
    (hflux_deriv : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) y)
    (hlog_cont : Continuous (intervalLogisticSource p (u s)))
    (hlog_bound : ∀ n : ℕ, |coupledLogisticSourceCoeffs p u s n| ≤ Mlog) :
    (-p.χ₀) * intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x
      + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x := by
  obtain ⟨Msin, _hMsin_nonneg, hsine_bound⟩ :=
    intervalSineInner_abs_le_of_continuousOn
      (hflux_cont.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hchem_coeff : ∀ n : ℕ,
      coupledChemDivSourceCoeffs p u s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner (chemFluxLifted p (u s)) n :=
    coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv
      (p := p) (u := u) (s := s) hsource_cont hflux_deriv
  have hlog_bound' :
      ∀ n : ℕ, |cosineCoeffs (intervalDomainLift (intervalLogisticSource p (u s))) n|
        ≤ Mlog := by
    intro n
    simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
      logisticLifted] using hlog_bound n
  have hlog :
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x =
        unitIntervalCosineHeatValue (t - s)
          (coupledLogisticSourceCoeffs p u s) x := by
    show intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalLogisticSource p (u s))) x =
      unitIntervalCosineHeatValue (t - s)
        (coupledLogisticSourceCoeffs p u s) x
    simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
      logisticLifted] using
      (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        hts hlog_cont hlog_bound' hx)
  have hchem :
      intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x =
        unitIntervalCosineHeatValue (t - s)
          (coupledChemDivSourceCoeffs p u s) x := by
    rw [intervalConjugateKernelOperator_cosineSeries hts
      (hflux_cont.continuousOn (s := Set.Icc (0 : ℝ) 1)) x]
    rw [ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
    refine tsum_congr (fun n => ?_)
    rw [hchem_coeff n]
  have hsum_log :
      Summable (fun n : ℕ =>
        unitIntervalCosineHeatPointWeight (t - s) x n *
          coupledLogisticSourceCoeffs p u s n) :=
    heatValue_logisticCoeff_summable hts hlog_bound
  have hsum_chem :
      Summable (fun n : ℕ =>
        unitIntervalCosineHeatPointWeight (t - s) x n *
          coupledChemDivSourceCoeffs p u s n) :=
    heatValue_chemCoeff_summable_of_sine_bound hts hsine_bound hchem_coeff
  have hsrc :
      unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x =
        unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p u s) x -
          p.χ₀ * unitIntervalCosineHeatValue (t - s)
            (coupledChemDivSourceCoeffs p u s) x := by
    simpa [bFormSourceCoeffs] using
      unitIntervalCosineHeatValue_linear_sub (t - s) x p.χ₀
        (coupledLogisticSourceCoeffs p u s)
        (coupledChemDivSourceCoeffs p u s)
        hsum_log hsum_chem
  rw [hlog, hchem, hsrc]
  ring

/-- Open-interior derivative variant of
`bForm_source_bridge_from_flux_deriv_subtypeCont`.  The flux leg only needs
closed-interval continuity plus an interior derivative identity. -/
theorem bForm_source_bridge_from_flux_deriv_subtypeCont_open
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t s x Mlog : ℝ}
    (hts : 0 < t - s) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hflux_cont : ContinuousOn (chemFluxLifted p (u s)) (Set.Icc (0 : ℝ) 1))
    (hsource_int : IntervalIntegrable (coupledChemDivSourceLift p u s)
      volume (0 : ℝ) 1)
    (hflux_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (chemFluxLifted p (u s))
        (coupledChemDivSourceLift p u s y) y)
    (hlog_cont : Continuous (intervalLogisticSource p (u s)))
    (hlog_bound : ∀ n : ℕ, |coupledLogisticSourceCoeffs p u s n| ≤ Mlog) :
    (-p.χ₀) * intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x
      + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x := by
  obtain ⟨Msin, _hMsin_nonneg, hsine_bound⟩ :=
    intervalSineInner_abs_le_of_continuousOn hflux_cont
  have hchem_coeff : ∀ n : ℕ,
      coupledChemDivSourceCoeffs p u s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner (chemFluxLifted p (u s)) n :=
    coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv_open
      (p := p) (u := u) (s := s) hflux_cont hsource_int hflux_deriv
  have hlog_bound' :
      ∀ n : ℕ, |cosineCoeffs (intervalDomainLift (intervalLogisticSource p (u s))) n|
        ≤ Mlog := by
    intro n
    simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
      logisticLifted] using hlog_bound n
  have hlog :
      intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x =
        unitIntervalCosineHeatValue (t - s)
          (coupledLogisticSourceCoeffs p u s) x := by
    show intervalFullSemigroupOperator (t - s)
        (intervalDomainLift (intervalLogisticSource p (u s))) x =
      unitIntervalCosineHeatValue (t - s)
        (coupledLogisticSourceCoeffs p u s) x
    simpa [coupledLogisticSourceCoeffs, coupledLogisticSourceLift,
      logisticLifted] using
      (intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
        hts hlog_cont hlog_bound' hx)
  have hchem :
      intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x =
        unitIntervalCosineHeatValue (t - s)
          (coupledChemDivSourceCoeffs p u s) x := by
    rw [intervalConjugateKernelOperator_cosineSeries hts hflux_cont x]
    rw [ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries]
    refine tsum_congr (fun n => ?_)
    rw [hchem_coeff n]
  have hsum_log :
      Summable (fun n : ℕ =>
        unitIntervalCosineHeatPointWeight (t - s) x n *
          coupledLogisticSourceCoeffs p u s n) :=
    heatValue_logisticCoeff_summable hts hlog_bound
  have hsum_chem :
      Summable (fun n : ℕ =>
        unitIntervalCosineHeatPointWeight (t - s) x n *
          coupledChemDivSourceCoeffs p u s n) :=
    heatValue_chemCoeff_summable_of_sine_bound hts hsine_bound hchem_coeff
  have hsrc :
      unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p u s) x =
        unitIntervalCosineHeatValue (t - s)
            (coupledLogisticSourceCoeffs p u s) x -
          p.χ₀ * unitIntervalCosineHeatValue (t - s)
            (coupledChemDivSourceCoeffs p u s) x := by
    simpa [bFormSourceCoeffs] using
      unitIntervalCosineHeatValue_linear_sub (t - s) x p.χ₀
        (coupledLogisticSourceCoeffs p u s)
        (coupledChemDivSourceCoeffs p u s)
        hsum_log hsum_chem
  rw [hlog, hchem, hsrc]
  ring

/-!
The following two theorems assemble the spectral form once the physical
chemotaxis flux/divergence bridge is supplied.  They do not assume the final
cosine identity itself; the explicit bridge is the missing analytic statement
needed to identify the B-kernel flux leg with the `coupledChemDivSourceCoeffs`
family.
-/

/-- Spectral form of the full B-form Duhamel map, given the pointwise source
bridge from the B-kernel/logistic integrand to the B-form coefficient family. -/
theorem intervalConjugateDuhamelMap_cosineSeries
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {t x M₀ : ℝ}
    (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p u))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x := by
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x =
      ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc ht hu₀_cont hu₀_bound hx]
    simpa using congrFun
      (ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
        t (cosineCoeffs (intervalDomainLift u₀))) x
  have hsource_eq : (-p.χ₀) *
        (∫ s in (0:ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = ∫ s in (0:ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add (hB_int.const_mul (-p.χ₀)) hlog_int]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t → s ∈ Set.Ioo (0 : ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hst
      exact ⟨hst.1, lt_of_le_of_ne hst.2 (fun heq => hs (by simp [heq]))⟩
    filter_upwards [hmem] with s hs hsIoc
    exact hsource_bridge s (hs hsIoc)
  rw [intervalConjugateDuhamelMap]
  change (intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      + (-p.χ₀) *
          (∫ s in (0:ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      = ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
  rw [hhom]
  rw [add_assoc]
  rw [hsource_eq, duhamelSpectral_eq_cosineSeries hsrcB ht]
  have hsum_hom : Summable (fun n : ℕ =>
      (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x) := by
    have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
    refine Summable.of_norm_bounded
      (g := fun n : ℕ =>
        |Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n|) ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hu₀_bound n) (Real.exp_pos _).le
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * |cosineMode n x|
          ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| := by ring
  have hsum_duh : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (bFormSourceCoeffs p u) t n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|)
      ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        (hsrcB.henv_summable.mul_left t)
      exact ShenWork.IntervalPicardIterateRestart.abs_duhamelSpectralCoeff_le
        hsrcB ht n
    · rw [Real.norm_eq_abs, abs_mul]
      calc |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * |cosineMode n x|
          ≤ |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| := by ring
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun n => ?_)
  unfold localRestartCoeff
  ring

/-- Subtype-continuity variant of
`intervalConjugateDuhamelMap_cosineSeries`.  The homogeneous initial-data leg is
routed through the constant-extension adapter, so this theorem consumes
`Continuous u₀` on the closed interval subtype rather than global continuity of
the zero extension. -/
theorem intervalConjugateDuhamelMap_cosineSeries_of_subtypeCont
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {t x M₀ : ℝ}
    (ht : 0 < t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1 (bFormSourceCoeffs p u))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p (u s)) x) volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (u s)) x) volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (u s)) x
        + intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
        = unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x) :
    intervalConjugateDuhamelMap p u₀ u t ⟨x, hx⟩ =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x := by
  have hhom : intervalFullSemigroupOperator t (intervalDomainLift u₀) x =
      ∑' n : ℕ,
        (Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x := by
    rw [intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      ht hu₀_cont hu₀_bound hx]
    simpa using congrFun
      (ShenWork.IntervalSemigroupNeumann.unitIntervalCosineHeatValue_eq_cosineCoeffSeries
        t (cosineCoeffs (intervalDomainLift u₀))) x
  have hsource_eq : (-p.χ₀) *
        (∫ s in (0:ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x
      = ∫ s in (0:ℝ)..t,
          unitIntervalCosineHeatValue (t - s) (bFormSourceCoeffs p u s) x := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add (hB_int.const_mul (-p.χ₀)) hlog_int]
    refine intervalIntegral.integral_congr_ae ?_
    rw [Set.uIoc_of_le ht.le]
    have hmem : ∀ᵐ s ∂volume, s ∈ Set.Ioc (0 : ℝ) t → s ∈ Set.Ioo (0 : ℝ) t := by
      have hnull : volume ({t} : Set ℝ) = 0 := by simp
      filter_upwards [(MeasureTheory.compl_mem_ae_iff.mpr hnull)] with s hs hst
      exact ⟨hst.1, lt_of_le_of_ne hst.2 (fun heq => hs (by simp [heq]))⟩
    filter_upwards [hmem] with s hs hsIoc
    exact hsource_bridge s (hs hsIoc)
  rw [intervalConjugateDuhamelMap]
  change (intervalFullSemigroupOperator t (intervalDomainLift u₀) x
      + (-p.χ₀) *
          (∫ s in (0:ℝ)..t,
            intervalConjugateKernelOperator (t - s) (chemFluxLifted p (u s)) x)
      + ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x)
      = ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p u) t n * cosineMode n x
  rw [hhom]
  rw [add_assoc]
  rw [hsource_eq, duhamelSpectral_eq_cosineSeries hsrcB ht]
  have hsum_hom : Summable (fun n : ℕ =>
      (Real.exp (-t * unitIntervalCosineEigenvalue n) *
        cosineCoeffs (intervalDomainLift u₀) n) * cosineMode n x) := by
    have hM₀nn : 0 ≤ M₀ := le_trans (abs_nonneg _) (hu₀_bound 0)
    refine Summable.of_norm_bounded
      (g := fun n : ℕ =>
        |Real.exp (-t * unitIntervalCosineEigenvalue n) *
          cosineCoeffs (intervalDomainLift u₀) n|) ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        ((ShenWork.IntervalSemigroupComposition.expEigSummable ht).mul_right M₀)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hu₀_bound n) (Real.exp_pos _).le
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * |cosineMode n x|
          ≤ |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |Real.exp (-t * unitIntervalCosineEigenvalue n) *
              cosineCoeffs (intervalDomainLift u₀) n| := by ring
  have hsum_duh : Summable (fun n : ℕ =>
      duhamelSpectralCoeff (bFormSourceCoeffs p u) t n * cosineMode n x) := by
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n|)
      ?_ (fun n => ?_)
    · refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
        (hsrcB.henv_summable.mul_left t)
      exact ShenWork.IntervalPicardIterateRestart.abs_duhamelSpectralCoeff_le
        hsrcB ht n
    · rw [Real.norm_eq_abs, abs_mul]
      calc |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * |cosineMode n x|
          ≤ |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| * 1 := by
              gcongr
              simpa [cosineMode] using
                Real.abs_cos_le_one ((n : ℝ) * Real.pi * x)
        _ = |duhamelSpectralCoeff (bFormSourceCoeffs p u) t n| := by ring
  rw [← Summable.tsum_add hsum_hom hsum_duh]
  refine tsum_congr (fun n => ?_)
  unfold localRestartCoeff
  ring

/-- Cosine-series form of the conjugate Picard limit from the B-form fixed point
and the explicit source bridge used by `intervalConjugateDuhamelMap_cosineSeries`.
The initial coefficient family is definitionally `cosineCoeffs (lift u₀)`. -/
theorem conjugatePicardLimit_cosineSeries
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hsource_bridge : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      (-p.χ₀) * intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        + intervalFullSemigroupOperator (t - s)
          (logisticLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x
        = unitIntervalCosineHeatValue (t - s)
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s) x) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  have hpoint :=
    hfix t ht htT ⟨x, hx⟩
  rw [show intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t ⟨x, hx⟩ by
      simp [intervalDomainLift, hx]]
  rw [hpoint]
  exact intervalConjugateDuhamelMap_cosineSeries
    (p := p) (u₀ := u₀)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (t := t) (x := x) (M₀ := M₀)
    ht hx hu₀_cont hu₀_bound hsrcB hB_int hlog_int hsource_bridge

theorem conjugatePicardLimit_cosineSeries_from_sine_coefficients
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (Mlog Msin : ℝ → ℝ)
    (hflux_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (chemFluxLifted p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (logisticLifted p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      |coupledLogisticSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n|
        ≤ Mlog s)
    (hsine_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      |intervalSineInner
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) n|
        ≤ Msin s)
    (hchem_coeff : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      coupledChemDivSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n =
        ((n : ℝ) * Real.pi) *
          intervalSineInner
            (chemFluxLifted p
              ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) n) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  refine conjugatePicardLimit_cosineSeries
    (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
    hfix ht htT hx hu₀_cont hu₀_bound hsrcB hB_int hlog_int ?_
  intro s hs
  exact bForm_source_bridge_from_sine_coefficients
    (p := p)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (t := t) (s := s) (x := x) (Mlog := Mlog s) (Msin := Msin s)
    (sub_pos.mpr hs.2) hx
    ((hflux_cont s hs).continuousOn (s := Set.Icc (0 : ℝ) 1)) (hlog_cont s hs)
    (hlog_bound s hs) (hsine_bound s hs) (hchem_coeff s hs)

/-- Cosine-series form of the conjugate Picard limit where the B-form source
bridge is discharged from the source/flux derivative identity. -/
theorem conjugatePicardLimit_cosineSeries_from_flux_deriv
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous (intervalDomainLift u₀))
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (Mlog : ℝ → ℝ)
    (hflux_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (chemFluxLifted p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hsource_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (coupledChemDivSourceLift p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
    (hflux_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
          (coupledChemDivSourceLift p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s y)
          y)
    (hlog_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (logisticLifted p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      |coupledLogisticSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n|
        ≤ Mlog s) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  refine conjugatePicardLimit_cosineSeries
    (p := p) (u₀ := u₀) (T := T) (t := t) (x := x) (M₀ := M₀)
    hfix ht htT hx hu₀_cont hu₀_bound hsrcB hB_int hlog_int ?_
  intro s hs
  exact bForm_source_bridge_from_flux_deriv
    (p := p)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (t := t) (s := s) (x := x) (Mlog := Mlog s)
    (sub_pos.mpr hs.2) hx
    (hflux_cont s hs) (hsource_cont s hs) (hflux_deriv s hs)
    (hlog_cont s hs) (hlog_bound s hs)

/-- Subtype-continuity version of
`conjugatePicardLimit_cosineSeries_from_flux_deriv`.  This is the paper-faithful
F6-style reconstruction wrapper for positive initial data and logistic source
slices. -/
theorem conjugatePicardLimit_cosineSeries_from_flux_deriv_subtypeCont
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (Mlog : ℝ → ℝ)
    (hflux_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (chemFluxLifted p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hsource_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (coupledChemDivSourceLift p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
    (hflux_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ y ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
          (coupledChemDivSourceLift p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s y)
          y)
    (hlog_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (intervalLogisticSource p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      |coupledLogisticSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n|
        ≤ Mlog s) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  have hpoint :=
    hfix t ht htT ⟨x, hx⟩
  rw [show intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t ⟨x, hx⟩ by
      simp [intervalDomainLift, hx]]
  rw [hpoint]
  exact intervalConjugateDuhamelMap_cosineSeries_of_subtypeCont
    (p := p) (u₀ := u₀)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (t := t) (x := x) (M₀ := M₀)
    ht hx hu₀_cont hu₀_bound hsrcB hB_int hlog_int
    (by
      intro s hs
      exact bForm_source_bridge_from_flux_deriv_subtypeCont
        (p := p)
        (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
        (t := t) (s := s) (x := x) (Mlog := Mlog s)
        (sub_pos.mpr hs.2) hx
        (hflux_cont s hs) (hsource_cont s hs) (hflux_deriv s hs)
        (hlog_cont s hs) (hlog_bound s hs))

/-- Open-interior derivative version of
`conjugatePicardLimit_cosineSeries_from_flux_deriv_subtypeCont`.  The flux leg
uses closed-interval continuity, spatial integrability of the chem-div source,
and the interior derivative identity. -/
theorem conjugatePicardLimit_cosineSeries_from_flux_deriv_subtypeCont_open
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t x M₀ : ℝ}
    (hfix : IntervalConjugateMildSolution p T u₀
      (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
    (ht : 0 < t) (htT : t ≤ T) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ n, |cosineCoeffs (intervalDomainLift u₀) n| ≤ M₀)
    (hsrcB : DuhamelSourceTimeC1
      (bFormSourceCoeffs p
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)))
    (hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s)
        (chemFluxLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (hlog_int : IntervalIntegrable
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p
          ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)) x)
      volume 0 t)
    (Mlog : ℝ → ℝ)
    (hflux_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ContinuousOn (chemFluxLifted p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
        (Set.Icc (0 : ℝ) 1))
    (hsource_int : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      IntervalIntegrable
        (coupledChemDivSourceLift p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)
        volume (0 : ℝ) 1)
    (hflux_deriv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt
          (chemFluxLifted p
            ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s))
          (coupledChemDivSourceLift p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s y)
          y)
    (hlog_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous (intervalLogisticSource p
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s)))
    (hlog_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      |coupledLogisticSourceCoeffs p
          (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) s n|
        ≤ Mlog s) :
    intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
      ∑' n : ℕ,
        localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
          (bFormSourceCoeffs p
            (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T))
          t n * cosineMode n x := by
  have hpoint :=
    hfix t ht htT ⟨x, hx⟩
  rw [show intervalDomainLift
        ((ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t) x =
        (ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T) t ⟨x, hx⟩ by
      simp [intervalDomainLift, hx]]
  rw [hpoint]
  exact intervalConjugateDuhamelMap_cosineSeries_of_subtypeCont
    (p := p) (u₀ := u₀)
    (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
    (t := t) (x := x) (M₀ := M₀)
    ht hx hu₀_cont hu₀_bound hsrcB hB_int hlog_int
    (by
      intro s hs
      exact bForm_source_bridge_from_flux_deriv_subtypeCont_open
        (p := p)
        (u := ShenWork.IntervalConjugatePicard.conjugatePicardLimit p u₀ T)
        (t := t) (s := s) (x := x) (Mlog := Mlog s)
        (sub_pos.mpr hs.2) hx
        (hflux_cont s hs) (hsource_int s hs) (hflux_deriv s hs)
        (hlog_cont s hs) (hlog_bound s hs))

#print axioms intervalConjugateKernelOperator_cosineSeries
#print axioms freq_mul_intervalSineInner_eq_cosineCoeffs_deriv
#print axioms intervalConjugateKernelOperator_tendstoUniformlyOn_deriv_of_endpoint_zero
#print axioms bForm_source_bridge_from_sine_coefficients
#print axioms coupledChemDivSourceCoeffs_eq_freq_mul_intervalSineInner_of_flux_deriv
#print axioms bForm_source_bridge_from_flux_deriv
#print axioms bForm_source_bridge_from_flux_deriv_subtypeCont
#print axioms intervalConjugateDuhamelMap_cosineSeries
#print axioms intervalConjugateDuhamelMap_cosineSeries_of_subtypeCont
#print axioms conjugatePicardLimit_cosineSeries
#print axioms conjugatePicardLimit_cosineSeries_from_sine_coefficients
#print axioms conjugatePicardLimit_cosineSeries_from_flux_deriv
#print axioms conjugatePicardLimit_cosineSeries_from_flux_deriv_subtypeCont

end ShenWork.IntervalConjugateCosineSeries
