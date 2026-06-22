import ShenWork.Paper2.IntervalBFormCron2SemigroupWeakDuhamel
import ShenWork.PDE.IntervalFullKernelInterchange
import ShenWork.PDE.IntervalFullKernelSpectralClean

open MeasureTheory

noncomputable section

namespace ShenWork.IntervalNHGBricks

open scoped Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.HeatKernelGradientEstimates
open ShenWork.IntervalFullKernelInterchange
open ShenWork.IntervalFullKernelSpectralClean

/-- L¹-dominated interchange: `FullKernelIntegralInterchange` for integrable input. -/
theorem fullKernelIntegralInterchange_holds_of_integrable
    (t : ℝ) (ht : 0 < t) (f : ℝ → ℝ) (hf : Integrable f (intervalMeasure 1)) (x : ℝ) :
    FullKernelIntegralInterchange t f x := by
  classical
  set μ : Measure ℝ := intervalMeasure 1 with hμ
  set E : ℤ → ℝ := fun m => Real.exp (-t * ((m : ℝ) * Real.pi) ^ 2) with hE
  have hE_pos : ∀ m : ℤ, 0 < E m := fun m => Real.exp_pos _
  have hsummE : Summable E := summable_gaussianWeight t ht
  set Cf : ℝ := ∫ y, ‖f y‖ ∂μ with hCf
  have hCf_nonneg : 0 ≤ Cf := integral_nonneg (fun y => norm_nonneg _)
  set F : ℤ → ℝ → ℝ :=
    fun m y => E m * Real.cos ((m : ℝ) * Real.pi * x) *
      (Real.cos ((m : ℝ) * Real.pi * y) * f y) with hF
  -- per-m integrability: bounded continuous multiplier × integrable f
  have hFint : ∀ m : ℤ, Integrable (F m) μ := by
    intro m
    have hcont : Continuous (fun y => E m * Real.cos ((m : ℝ) * Real.pi * x) *
        Real.cos ((m : ℝ) * Real.pi * y)) := by fun_prop
    have hbound : ∀ᵐ y ∂μ, ‖E m * Real.cos ((m : ℝ) * Real.pi * x) *
        Real.cos ((m : ℝ) * Real.pi * y)‖ ≤ |E m * Real.cos ((m : ℝ) * Real.pi * x)| := by
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul]
      calc |E m * Real.cos ((m : ℝ) * Real.pi * x)| * |Real.cos ((m : ℝ) * Real.pi * y)|
          ≤ |E m * Real.cos ((m : ℝ) * Real.pi * x)| * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
        _ = |E m * Real.cos ((m : ℝ) * Real.pi * x)| := by ring
    have hmul := hf.bdd_mul hcont.aestronglyMeasurable hbound
    refine hmul.congr ?_
    filter_upwards with y; rw [hF]; ring
  -- pointwise norm bound ‖F m y‖ ≤ E m * ‖f y‖
  have hFbound : ∀ m : ℤ, ∀ y, ‖F m y‖ ≤ E m * ‖f y‖ := by
    intro m y
    rw [hF, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (hE_pos m), Real.norm_eq_abs]
    have hcx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hcy : |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
    have hEm : (0:ℝ) ≤ E m := (hE_pos m).le
    calc E m * |Real.cos ((m : ℝ) * Real.pi * x)|
          * (|Real.cos ((m : ℝ) * Real.pi * y)| * |f y|)
        ≤ E m * 1 * (1 * |f y|) := by gcongr
      _ = E m * |f y| := by ring
  -- ∫‖F m‖ ≤ E m * Cf
  have hFnorm_int_le : ∀ m : ℤ, ∫ y, ‖F m y‖ ∂μ ≤ E m * Cf := by
    intro m
    calc ∫ y, ‖F m y‖ ∂μ
        ≤ ∫ y, E m * ‖f y‖ ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _))
            ((hf.norm).const_mul (E m))
            (Filter.Eventually.of_forall (hFbound m))
      _ = E m * Cf := by rw [integral_const_mul, hCf]
  have hFsum : Summable (fun m : ℤ => ∫ y, ‖F m y‖ ∂μ) := by
    apply Summable.of_nonneg_of_le
      (fun m => integral_nonneg (fun y => norm_nonneg _)) hFnorm_int_le
    exact hsummE.mul_right Cf
  have hsummand : ∀ y : ℝ,
      Summable (fun m : ℤ => E m *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) := by
    intro y
    apply Summable.of_norm_bounded (g := E) hsummE
    intro m
    have hcx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hcy : |Real.cos ((m : ℝ) * Real.pi * y)| ≤ 1 := Real.abs_cos_le_one _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hE_pos m), abs_mul]
    calc E m * (|Real.cos ((m : ℝ) * Real.pi * x)| * |Real.cos ((m : ℝ) * Real.pi * y)|)
        ≤ E m * (1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hcx hcy (abs_nonneg _) (by norm_num)) (hE_pos m).le
      _ = E m := by ring
  have hintegrand : ∀ y : ℝ,
      (∑' m : ℤ, E m *
        (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y
        = ∑' m : ℤ, F m y := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr (fun m => ?_); rw [hF]; ring
  have hswap :
      (∫ y, (∑' m : ℤ, F m y) ∂μ) = ∑' m : ℤ, ∫ y, F m y ∂μ :=
    (integral_tsum_of_summable_integral_norm hFint hFsum).symm
  set Iint : ℤ → ℝ :=
    (fun m => ∫ y in (0 : ℝ)..1, Real.cos ((m : ℝ) * Real.pi * y) * f y) with hIint
  have hterm : ∀ m : ℤ, (∫ y, F m y ∂μ) =
      E m * Real.cos ((m : ℝ) * Real.pi * x) * Iint m := by
    intro m
    rw [hF, hIint]
    rw [show (fun y => E m * Real.cos ((m : ℝ) * Real.pi * x) *
          (Real.cos ((m : ℝ) * Real.pi * y) * f y))
        = (fun y => (E m * Real.cos ((m : ℝ) * Real.pi * x)) *
          (Real.cos ((m : ℝ) * Real.pi * y) * f y)) from by funext y; ring]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [hμ, intervalMeasure, intervalSet]
    change (∫ y in Set.Icc (0:ℝ) 1, Real.cos ((m : ℝ) * Real.pi * y) * f y ∂volume)
        = ∫ y in (0:ℝ)..1, Real.cos ((m : ℝ) * Real.pi * y) * f y
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hLHS :
      (∫ y, (∑' m : ℤ, E m *
          (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y ∂μ)
        = ∑' m : ℤ, E m * Real.cos ((m : ℝ) * Real.pi * x) * Iint m := by
    rw [show (fun y => (∑' m : ℤ, E m *
            (Real.cos ((m : ℝ) * Real.pi * x) * Real.cos ((m : ℝ) * Real.pi * y))) * f y)
          = (fun y => ∑' m : ℤ, F m y) from by funext y; rw [hintegrand y]]
    rw [hswap]; exact tsum_congr hterm
  set φ : ℤ → ℝ := fun m => E m * Real.cos ((m : ℝ) * Real.pi * x) * Iint m with hφ
  have hEeven : ∀ m : ℤ, E (-m) = E m := by
    intro m; simp only [hE]; congr 2; push_cast; ring
  have hcosxeven : ∀ m : ℤ,
      Real.cos (((-m : ℤ) : ℝ) * Real.pi * x) = Real.cos ((m : ℝ) * Real.pi * x) := by
    intro m
    rw [show (((-m : ℤ) : ℝ) * Real.pi * x) = -((m : ℝ) * Real.pi * x) by push_cast; ring,
      Real.cos_neg]
  have hIinteven : ∀ m : ℤ, Iint (-m) = Iint m := by
    intro m; rw [hIint]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    rw [show (((-m : ℤ) : ℝ) * Real.pi * y) = -((m : ℝ) * Real.pi * y) by push_cast; ring,
      Real.cos_neg]
  have hφeven : Function.Even φ := by
    intro m; rw [hφ]; simp only; rw [hEeven m, hcosxeven m, hIinteven m]
  have hφsumm : Summable φ := by
    apply Summable.of_norm_bounded (g := fun m => E m * Cf)
    · exact hsummE.mul_right Cf
    intro m
    rw [hφ]
    have hcosx : |Real.cos ((m : ℝ) * Real.pi * x)| ≤ 1 := Real.abs_cos_le_one _
    have hIabs : |Iint m| ≤ Cf := by
      have hfIcc : Integrable f (volume.restrict (Set.Icc (0:ℝ) 1)) := by
        rw [hμ, intervalMeasure, intervalSet] at hf; exact hf
      have hfnorm_Ioc : IntegrableOn (fun y => ‖f y‖) (Set.Ioc (0:ℝ) 1) volume := by
        have : IntegrableOn (fun y => ‖f y‖) (Set.Icc (0:ℝ) 1) volume := hfIcc.norm
        exact this.mono_set Set.Ioc_subset_Icc_self
      have hcosf_Ioc : IntegrableOn (fun y => Real.cos ((m:ℝ)*Real.pi*y) * f y)
          (Set.Ioc (0:ℝ) 1) volume := by
        have : IntegrableOn (fun y => Real.cos ((m:ℝ)*Real.pi*y) * f y)
            (Set.Icc (0:ℝ) 1) volume := by
          refine (Integrable.bdd_mul (c := 1) hfIcc ?_ ?_)
          · exact (Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable
          · filter_upwards with y; simpa using Real.abs_cos_le_one ((m:ℝ)*Real.pi*y)
        exact this.mono_set Set.Ioc_subset_Icc_self
      simp only [hIint]
      rw [hCf, hμ, intervalMeasure, intervalSet,
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      calc |∫ y in Set.Ioc (0:ℝ) 1, Real.cos ((m : ℝ) * Real.pi * y) * f y|
          = ‖∫ y in Set.Ioc (0:ℝ) 1, Real.cos ((m : ℝ) * Real.pi * y) * f y‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∫ y in Set.Ioc (0:ℝ) 1, ‖Real.cos ((m : ℝ) * Real.pi * y) * f y‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y in Set.Ioc (0:ℝ) 1, ‖f y‖ := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _))
              hfnorm_Ioc (Filter.Eventually.of_forall (fun y => ?_))
            show ‖Real.cos ((m:ℝ)*Real.pi*y) * f y‖ ≤ ‖f y‖
            rw [norm_mul]
            calc ‖Real.cos ((m:ℝ)*Real.pi*y)‖ * ‖f y‖
                ≤ 1 * ‖f y‖ := mul_le_mul_of_nonneg_right
                  (by simpa using Real.abs_cos_le_one _) (norm_nonneg _)
              _ = ‖f y‖ := one_mul _
        _ = ∫ y in Set.Icc (0:ℝ) 1, ‖f y‖ := (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hE_pos m)]
    calc E m * |Real.cos ((m : ℝ) * Real.pi * x)| * |Iint m|
        ≤ E m * 1 * Cf := by
          apply mul_le_mul _ hIabs (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hcosx (hE_pos m).le
      _ = E m * Cf := by ring
  have hfold := tsum_int_eq_zero_add_two_mul_tsum_pnat hφeven hφsumm
  have hraw_re : ∀ n : ℕ,
      (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x => (f x : ℂ)) n).re = Iint (n : ℤ) := by
    intro n
    rw [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff, hIint]
    rw [show (fun y => (Real.cos ((n : ℝ) * Real.pi * y) : ℂ) * (f y : ℂ))
          = (fun y => (((Real.cos ((n : ℝ) * Real.pi * y) * f y) : ℝ) : ℂ)) from by
        funext y; push_cast; ring]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
    simp only [Int.cast_natCast]
  have hcoeff : ∀ n : ℕ, cosineCoeffs f n =
      (if n = 0 then (1 : ℝ) else 2) * Iint (n : ℤ) := by
    intro n
    rw [cosineCoeffs, ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff]
    by_cases hn : n = 0
    · subst hn; simp [hraw_re 0]
    · simp only [hn, if_false]; rw [hraw_re n]
  have hweight_pt : ∀ n : ℕ,
      unitIntervalCosineHeatPointWeight t x n
        = E (n : ℤ) * Real.cos ((n : ℝ) * Real.pi * x) := by
    intro n
    rw [unitIntervalCosineHeatPointWeight, unitIntervalCosineMode,
      unitIntervalCosineEigenvalue, hE]
    push_cast; ring
  set ψ : ℕ → ℝ := fun n =>
    unitIntervalCosineHeatPointWeight t x n * cosineCoeffs f n with hψ
  have hψ0 : ψ 0 = φ 0 := by
    simp only [hψ, hφ]; rw [hweight_pt 0, hcoeff 0]; simp
  have hψsucc : ∀ n : ℕ, ψ (n + 1) = 2 * φ ((n + 1 : ℕ) : ℤ) := by
    intro n
    simp only [hψ, hφ]
    rw [hweight_pt (n + 1), hcoeff (n + 1)]
    simp only [Nat.succ_ne_zero, if_false]; push_cast; ring
  have hψsumm : Summable ψ := by
    have hφnat : Summable (fun n : ℕ => φ (n : ℤ)) :=
      (summable_int_iff_summable_nat_and_neg.mp hφsumm).1
    apply (summable_nat_add_iff 1).mp
    have : (fun n : ℕ => ψ (n + 1)) = (fun n : ℕ => 2 * φ ((n + 1 : ℕ) : ℤ)) := by
      funext n; exact hψsucc n
    rw [this]
    exact ((summable_nat_add_iff 1).mpr hφnat).mul_left 2
  have hψtsum : (∑' n : ℕ, ψ n) = φ 0 + ∑' n : ℕ, (2 : ℝ) * φ ((n + 1 : ℕ) : ℤ) := by
    rw [hψsumm.tsum_eq_zero_add, hψ0]; congr 1; exact tsum_congr hψsucc
  have hpnat : (∑' n : ℕ+, φ (n : ℤ)) = ∑' n : ℕ, φ ((n + 1 : ℕ) : ℤ) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => φ (n : ℤ))]
  have hRHS : unitIntervalCosineHeatValue t (cosineCoeffs f) x = ∑' m : ℤ, φ m := by
    rw [unitIntervalCosineHeatValue]
    change (∑' n : ℕ, ψ n) = _
    rw [hψtsum, hfold]
    rw [show (∑' n : ℕ, (2 : ℝ) * φ ((n + 1 : ℕ) : ℤ))
          = 2 * ∑' n : ℕ, φ ((n + 1 : ℕ) : ℤ) from by rw [tsum_mul_left]]
    rw [← hpnat, two_nsmul]; ring
  rw [FullKernelIntegralInterchange, ← hμ]
  rw [hLHS, hRHS]

/-- Operator → cosine model for integrable input on `Ioo 0 1`. -/
theorem operator_eq_cosineModel_of_integrable
    {τ : ℝ} (hτ : 0 < τ) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    intervalFullSemigroupOperator τ f x
      = unitIntervalCosineHeatValue τ (cosineCoeffs f) x :=
  intervalFullSemigroupOperator_eq_cosineHeatValue τ hτ f x hx
    (fun y => intervalNeumannFullKernel_eq_cosineKernel_clean τ hτ x y)
    (fullKernelIntegralInterchange_holds_of_integrable τ hτ f hf x)

end ShenWork.IntervalNHGBricks
