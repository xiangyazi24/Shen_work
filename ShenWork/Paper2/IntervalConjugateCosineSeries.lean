/-
  Spectral cosine-series assembly for the interval conjugate-kernel map.

  This file is additive: it introduces new lemmas only.  The kernel calculation
  uses the cosine-kernel form of `intervalNeumannFullKernel` and differentiates
  `cos(nπy)` in the second variable.  Positive modes carry the Neumann factor
  `2`, so the sine pairing below is normalized with the same positive-mode
  factor as `cosineCoeffs`.

  No `sorry`, no `admit`, no custom axioms.
-/
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalPicardIterateRestart
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.PDE.IntervalSemigroupComposition

open MeasureTheory Filter Topology

noncomputable section

namespace ShenWork.IntervalConjugateCosineSeries

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator intervalConjugateDuhamelMap IntervalConjugateMildSolution)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalFullKernelSpectralClean
  (intervalNeumannFullKernel_eq_cosineKernel_clean
   intervalFullSemigroupOperator_eq_cosineHeatValue_Icc)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1 duhamelSpectralCoeff duhamelSpectral_eq_cosineSeries)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs)
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
    {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
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
      (hg.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hCg_nonneg : 0 ≤ Cg :=
    le_trans (norm_nonneg (g 0)) (hCg 0 ⟨le_refl 0, by norm_num⟩)
  set F : ℕ → ℝ → ℝ := fun n y => D n y * g y with hF
  have hFint : ∀ n, Integrable (F n) (intervalMeasure 1) := by
    intro n
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    have hcont : Continuous (F n) := by
      rw [hF, hD]
      fun_prop
    simpa [IntegrableOn] using
      hcont.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
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

#print axioms intervalConjugateKernelOperator_cosineSeries
#print axioms intervalConjugateDuhamelMap_cosineSeries
#print axioms conjugatePicardLimit_cosineSeries

end ShenWork.IntervalConjugateCosineSeries