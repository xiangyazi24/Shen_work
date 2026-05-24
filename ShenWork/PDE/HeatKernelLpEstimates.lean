/-
  ShenWork/PDE/HeatKernelLpEstimates.lean

  Whole-line L^p estimates for the one-dimensional heat kernel.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.IntervalDomain
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open MeasureTheory Filter Topology Real
open scoped ENNReal

noncomputable section

/-! ## Heat-kernel `L^p` norms -/

/-- Closed-form expression for the finite `L^p` norm of the heat kernel on `ℝ`. -/
def heatKernelLpNormClosedForm (t p : ℝ) : ℝ :=
  (((1 / Real.sqrt (4 * Real.pi * t)) ^ p) *
      Real.sqrt (Real.pi / (p / (4 * t)))) ^ (1 / p)

/-- Power-integral form of the heat-kernel `L^p` norm. -/
theorem heatKernel_Lp_power_integral_eq {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    ∫ x : ℝ, |heatKernel t x| ^ p =
      (1 / Real.sqrt (4 * Real.pi * t)) ^ p *
        Real.sqrt (Real.pi / (p / (4 * t))) := by
  have hcoeff_nonneg : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
    positivity
  have hb : 0 < p / (4 * t) := by
    positivity
  unfold heatKernel
  rw [show
      (fun x : ℝ =>
          |1 / Real.sqrt (4 * Real.pi * t) *
              Real.exp (-x ^ 2 / (4 * t))| ^ p) =
        fun x : ℝ =>
          (1 / Real.sqrt (4 * Real.pi * t)) ^ p *
            Real.exp (-(p / (4 * t)) * x ^ 2) by
      ext x
      rw [abs_mul, abs_of_nonneg hcoeff_nonneg,
        abs_of_nonneg (Real.exp_nonneg _)]
      rw [Real.mul_rpow hcoeff_nonneg (Real.exp_nonneg _)]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp [ne_of_gt ht]]
  rw [MeasureTheory.integral_const_mul, integral_gaussian (p / (4 * t))]

/-- Closed-form finite `L^p` norm of the heat kernel on `ℝ`. -/
theorem heatKernel_Lp_norm_eq {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    (∫ x : ℝ, |heatKernel t x| ^ p) ^ (1 / p) =
      heatKernelLpNormClosedForm t p := by
  rw [heatKernel_Lp_power_integral_eq ht hp]
  rfl

lemma heatKernel_norm_rpow_integrable {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    MeasureTheory.Integrable (fun x : ℝ => ‖heatKernel t x‖ ^ p) := by
  have hcoeff_nonneg : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
    positivity
  have hb : 0 < p / (4 * t) := by
    positivity
  unfold heatKernel
  rw [show
      (fun x : ℝ =>
          ‖1 / Real.sqrt (4 * Real.pi * t) *
              Real.exp (-x ^ 2 / (4 * t))‖ ^ p) =
        fun x : ℝ =>
          (1 / Real.sqrt (4 * Real.pi * t)) ^ p *
            Real.exp (-(p / (4 * t)) * x ^ 2) by
      ext x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff_nonneg,
        abs_of_nonneg (Real.exp_nonneg _)]
      rw [Real.mul_rpow hcoeff_nonneg (Real.exp_nonneg _)]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      field_simp [ne_of_gt ht]]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

/-- The heat kernel belongs to every finite `L^p`, `0 < p < ∞`. -/
lemma heatKernel_memLp {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    MeasureTheory.MemLp (fun x : ℝ => heatKernel t x)
      (ENNReal.ofReal p) MeasureTheory.volume := by
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hp
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hpow :
      MeasureTheory.Integrable
        (fun x : ℝ => ‖heatKernel t x‖ ^ (ENNReal.ofReal p).toReal) := by
    simpa [ENNReal.toReal_ofReal (le_of_lt hp)] using
      heatKernel_norm_rpow_integrable ht hp
  exact (MeasureTheory.integrable_norm_rpow_iff
    (heatKernel_integrable ht).aestronglyMeasurable hp_ne_zero hp_ne_top).mp hpow

theorem heatKernel_Lp_norm_eq_norm {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    (∫ x : ℝ, ‖heatKernel t x‖ ^ p) ^ (1 / p) =
      heatKernelLpNormClosedForm t p := by
  simpa [Real.norm_eq_abs] using heatKernel_Lp_norm_eq ht hp

lemma heatKernel_translated_norm_rpow_integrable {t p : ℝ} (ht : 0 < t)
    (hp : 0 < p) (x : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ => ‖heatKernel t (x - y)‖ ^ p) := by
  have hkey :
      (fun y : ℝ => ‖heatKernel t (x - y)‖ ^ p) =
        fun y : ℝ => (fun z : ℝ => ‖heatKernel t z‖ ^ p) (y + (-x)) := by
    ext y
    rw [show x - y = -(y + (-x)) by ring, heatKernel_neg]
  rw [hkey]
  exact (heatKernel_norm_rpow_integrable ht hp).comp_add_right (-x)

lemma heatKernel_translated_memLp {t p : ℝ} (ht : 0 < t) (hp : 0 < p)
    (x : ℝ) :
    MeasureTheory.MemLp (fun y : ℝ => heatKernel t (x - y))
      (ENNReal.ofReal p) MeasureTheory.volume := by
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hp
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hpow :
      MeasureTheory.Integrable
        (fun y : ℝ => ‖heatKernel t (x - y)‖ ^ (ENNReal.ofReal p).toReal) := by
    simpa [ENNReal.toReal_ofReal (le_of_lt hp)] using
      heatKernel_translated_norm_rpow_integrable ht hp x
  exact (MeasureTheory.integrable_norm_rpow_iff
    (heatKernel_translated_integrable ht x).aestronglyMeasurable
      hp_ne_zero hp_ne_top).mp hpow

theorem heatKernel_translated_Lp_norm_eq {t p : ℝ} (ht : 0 < t)
    (hp : 0 < p) (x : ℝ) :
    (∫ y : ℝ, ‖heatKernel t (x - y)‖ ^ p) ^ (1 / p) =
      heatKernelLpNormClosedForm t p := by
  have hkey :
      (fun y : ℝ => ‖heatKernel t (x - y)‖ ^ p) =
        fun y : ℝ => (fun z : ℝ => ‖heatKernel t z‖ ^ p) (y + (-x)) := by
    ext y
    rw [show x - y = -(y + (-x)) by ring, heatKernel_neg]
  rw [hkey]
  have hshift :
      ∫ y : ℝ, (fun z : ℝ => ‖heatKernel t z‖ ^ p) (y + (-x)) =
        ∫ z : ℝ, ‖heatKernel t z‖ ^ p := by
    simpa using
      (integral_add_right_eq_self
        (fun z : ℝ => ‖heatKernel t z‖ ^ p) (-x))
  rw [hshift]
  exact heatKernel_Lp_norm_eq_norm ht hp

/-! ## Heat-semigroup smoothing constants -/

/-- Young exponent for the one-dimensional heat semigroup `L^p → L^q` estimate. -/
def heatSemigroupYoungExponent (p q : ℝ) : ℝ :=
  (1 + 1 / q - 1 / p)⁻¹

/-- The kernel-norm constant in the whole-line heat-semigroup `L^p → L^q` estimate. -/
def heatSemigroupLpLqSmoothingConstant (t p q : ℝ) : ℝ :=
  heatKernelLpNormClosedForm t (heatSemigroupYoungExponent p q)

theorem heatSemigroup_Lp_Lq_smoothing_constant {t p q r : ℝ}
    (hr : r = heatSemigroupYoungExponent p q) :
    heatKernelLpNormClosedForm t r =
      heatSemigroupLpLqSmoothingConstant t p q := by
  simp [heatSemigroupLpLqSmoothingConstant, hr]

/-! ## Interval Neumann helper smoothing -/

open ShenWork.IntervalDomain

set_option maxHeartbeats 0 in
-- `fun_prop` expands the concrete heat-kernel expression under a product measure.
/-- The concrete interval heat helper is a.e.-strongly measurable whenever
the input is. -/
lemma intervalSemigroupOperator_aestronglyMeasurable
    {L t : ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (intervalMeasure L)) :
    AEStronglyMeasurable (fun x => intervalSemigroupOperator L t f x)
      (intervalMeasure L) := by
  unfold intervalSemigroupOperator
  let F : ℝ × ℝ → ℝ :=
    fun z => normalizedZerothReflectionKernel L t z.1 z.2 * f z.2
  change AEStronglyMeasurable (fun x => ∫ y, F (x, y) ∂ intervalMeasure L)
    (intervalMeasure L)
  apply MeasureTheory.AEStronglyMeasurable.integral_prod_right' (f := F)
  dsimp [F]
  have hk_cont :
      Continuous
        (fun z : ℝ × ℝ => normalizedZerothReflectionKernel L t z.1 z.2) := by
    unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection heatKernel
    fun_prop
  exact hk_cont.aestronglyMeasurable.mul hf.comp_snd

set_option maxHeartbeats 0 in
-- The `LpSeminorm` simplifications expand `intervalSemigroupOperator` and `lpNorm`.
/-- Interval Neumann heat-helper endpoint smoothing in `LpSeminorm` notation:
`L¹([0,L]) → L∞([0,L])`.  This is the `p = 1`, `q = ∞` endpoint of
the interval heat-semigroup smoothing chain. -/
theorem intervalHeatSemigroup_Lp_Lq_bound
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) :
    lpNorm (fun x => intervalSemigroupOperator L t f x) ∞ (intervalMeasure L) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure L) := by
  let C : ℝ :=
    (1 / Real.sqrt (4 * Real.pi * t)) *
      lpNorm f (1 : ℝ≥0∞) (intervalMeasure L)
  have hT_meas :
      AEStronglyMeasurable (fun x => intervalSemigroupOperator L t f x)
        (intervalMeasure L) :=
    intervalSemigroupOperator_aestronglyMeasurable hf_int.aestronglyMeasurable
  have hpoint : ∀ x, ‖intervalSemigroupOperator L t f x‖ ≤ C := by
    intro x
    have h := intervalSemigroupOperator_L1_Linfty
      (L := L) (t := t) ht hf_int x
    simpa [C, lpNorm_one_eq_integral_norm hf_int.aestronglyMeasurable] using h
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) lpNorm_nonneg
  have hess :
      eLpNormEssSup (fun x => intervalSemigroupOperator L t f x)
          (intervalMeasure L) ≤
        ENNReal.ofReal C :=
    eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hpoint)
  calc
    lpNorm (fun x => intervalSemigroupOperator L t f x) ∞ (intervalMeasure L)
        = (eLpNorm (fun x => intervalSemigroupOperator L t f x) ∞
            (intervalMeasure L)).toReal := by
          exact (toReal_eLpNorm hT_meas).symm
    _ = (eLpNormEssSup (fun x => intervalSemigroupOperator L t f x)
          (intervalMeasure L)).toReal := by
          rw [eLpNorm_exponent_top]
    _ ≤ (ENNReal.ofReal C).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = C := ENNReal.toReal_ofReal hC_nonneg
    _ = (1 / Real.sqrt (4 * Real.pi * t)) *
        lpNorm f (1 : ℝ≥0∞) (intervalMeasure L) := rfl

/-- Hölder endpoint of the heat-semigroup smoothing estimate. -/
theorem heatSemigroup_Lp_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t p r : ℝ} (ht : 0 < t)
    (hrp : r.HolderConjugate p) (x : ℝ)
    (hf_mem : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume) :
    |heatSemigroup t f x| ≤
      heatKernelLpNormClosedForm t r *
        (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) := by
  have hkernel_mem :
      MeasureTheory.MemLp (fun y : ℝ => heatKernel t (x - y))
        (ENNReal.ofReal r) MeasureTheory.volume :=
    heatKernel_translated_memLp ht hrp.pos x
  have hholder :
      ∫ y : ℝ, ‖heatKernel t (x - y)‖ * ‖f y‖ ≤
        (∫ y : ℝ, ‖heatKernel t (x - y)‖ ^ r) ^ (1 / r) *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := MeasureTheory.volume)
      (f := fun y : ℝ => heatKernel t (x - y)) (g := f)
      hrp hkernel_mem hf_mem
  unfold heatSemigroup
  calc
    |∫ y : ℝ, heatKernel t (x - y) * f y|
        = ‖∫ y : ℝ, heatKernel t (x - y) * f y‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ, ‖heatKernel t (x - y) * f y‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ y : ℝ, ‖heatKernel t (x - y)‖ * ‖f y‖ := by
        congr 1
        ext y
        rw [norm_mul]
    _ ≤ (∫ y : ℝ, ‖heatKernel t (x - y)‖ ^ r) ^ (1 / r) *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) :=
        hholder
    _ = heatKernelLpNormClosedForm t r *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p) := by
        rw [heatKernel_translated_Lp_norm_eq ht hrp.pos x]

/-- Hölder endpoint of the modified heat-semigroup smoothing estimate. -/
theorem modifiedSemigroup_Lp_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t p r : ℝ} (ht : 0 < t)
    (hrp : r.HolderConjugate p) (x : ℝ)
    (hf_mem : MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume) :
    |modifiedSemigroup t f x| ≤
      Real.exp (-t) *
        (heatKernelLpNormClosedForm t r *
          (∫ y : ℝ, ‖f y‖ ^ p) ^ (1 / p)) := by
  unfold modifiedSemigroup
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (heatSemigroup_Lp_Linfty_smoothing_abs ht hrp x hf_mem)
    (Real.exp_nonneg _)

/-! ## Gradient smoothing -/

/-- Pointwise kernel-derivative constant for the `L¹ → L∞` gradient estimate. -/
def heatSemigroupGradientL1LinftyConstant (t : ℝ) : ℝ :=
  ((1 / (2 * t)) * (1 / Real.sqrt (4 * Real.pi * t))) *
    (Real.sqrt (1 / (4 * t)))⁻¹

theorem heatSemigroup_gradient_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |deriv (fun z : ℝ => heatSemigroup t f z) x| ≤
      heatSemigroupGradientL1LinftyConstant t * ∫ y : ℝ, |f y| := by
  simpa [heatSemigroupGradientL1LinftyConstant] using
    deriv_heatSemigroup_L1_Linfty_smoothing_abs ht x hf_int

theorem modifiedSemigroup_gradient_L1_Linfty_smoothing_abs
    {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f) :
    |deriv (fun z : ℝ => modifiedSemigroup t f z) x| ≤
      Real.exp (-t) *
        (heatSemigroupGradientL1LinftyConstant t * ∫ y : ℝ, |f y|) := by
  simpa [heatSemigroupGradientL1LinftyConstant] using
    deriv_modifiedSemigroup_L1_Linfty_smoothing_abs ht x hf_int

theorem heatSemigroup_gradient_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |deriv (fun z : ℝ => heatSemigroup t f z) x -
        deriv (fun z : ℝ => heatSemigroup t g z) x| ≤
      heatSemigroupGradientL1LinftyConstant t *
        ∫ y : ℝ, |f y - g y| := by
  simpa [heatSemigroupGradientL1LinftyConstant] using
    deriv_heatSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int

theorem modifiedSemigroup_gradient_diff_L1_Linfty_smoothing_abs
    {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ)
    (hf_int : MeasureTheory.Integrable f)
    (hg_int : MeasureTheory.Integrable g) :
    |deriv (fun z : ℝ => modifiedSemigroup t f z) x -
        deriv (fun z : ℝ => modifiedSemigroup t g z) x| ≤
      Real.exp (-t) *
        (heatSemigroupGradientL1LinftyConstant t *
          ∫ y : ℝ, |f y - g y|) := by
  simpa [heatSemigroupGradientL1LinftyConstant] using
    deriv_modifiedSemigroup_diff_L1_Linfty_smoothing_abs ht x hf_int hg_int

end
