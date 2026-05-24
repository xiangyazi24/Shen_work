/-
  ShenWork/PDE/HeatKernelLpEstimates.lean

  Whole-line L^p estimates for the one-dimensional heat kernel.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.CosineSpectrum
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.Prod

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

/-- Symmetry of the normalized zeroth-reflection interval helper kernel. -/
lemma normalizedZerothReflectionKernel_symm (L t x y : ℝ) :
    normalizedZerothReflectionKernel L t x y =
      normalizedZerothReflectionKernel L t y x := by
  unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection
  rw [heatKernel_sub_comm t x y]
  congr 1
  ring_nf

/-- The restricted interval mass is also at most one when integrating in the
first spatial variable. -/
lemma normalizedZerothReflectionKernel_intervalIntegral_left_le_one
    {t : ℝ} (ht : 0 < t) (L y : ℝ) :
    ∫ x, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤ 1 := by
  have h :=
    normalizedZerothReflectionKernel_intervalIntegral_le_one
      (L := L) (t := t) ht y
  simpa [normalizedZerothReflectionKernel_symm] using h

/-- `L¹` contraction for the restricted interval heat helper. -/
lemma intervalSemigroupOperator_L1_contraction
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) :
    ∫ x, ‖intervalSemigroupOperator L t f x‖ ∂ intervalMeasure L ≤
      ∫ y, ‖f y‖ ∂ intervalMeasure L := by
  let μ := intervalMeasure L
  let K : ℝ → ℝ → ℝ := fun x y =>
    normalizedZerothReflectionKernel L t x y
  let F : ℝ × ℝ → ℝ := fun z => K z.1 z.2 * ‖f z.2‖
  have hK_cont : Continuous (fun z : ℝ × ℝ => K z.1 z.2) := by
    dsimp [K]
    unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection heatKernel
    fun_prop
  have hF_int : Integrable F (μ.prod μ) := by
    have hf_prod : Integrable (fun z : ℝ × ℝ => ‖f z.2‖) (μ.prod μ) := by
      exact hf_int.norm.comp_snd μ
    have hK_bound :
        ∀ z : ℝ × ℝ, ‖K z.1 z.2‖ ≤
          1 / Real.sqrt (4 * Real.pi * t) := by
      intro z
      dsimp [K]
      rw [abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L z.1 z.2)]
      exact normalizedZerothReflectionKernel_pointwise_bound ht L z.1 z.2
    simpa [F, mul_comm] using
      hf_prod.mul_bdd hK_cont.aestronglyMeasurable
        (Filter.Eventually.of_forall hK_bound)
  have hright_int :
      Integrable (fun x => ∫ y, F (x, y) ∂ μ) μ :=
    hF_int.integral_prod_left
  have hfirst :
      ∫ x, ‖intervalSemigroupOperator L t f x‖ ∂ μ ≤
        ∫ x, ∫ y, F (x, y) ∂ μ ∂ μ := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · exact hright_int
    · exact Filter.Eventually.of_forall fun x => by
        dsimp [F, K]
        simpa [Real.norm_eq_abs] using
          intervalSemigroupOperator_abs_le_integral_abs
            (L := L) (t := t) ht f x
  have hswap :
      ∫ x, ∫ y, F (x, y) ∂ μ ∂ μ =
        ∫ y, ∫ x, F (x, y) ∂ μ ∂ μ :=
    MeasureTheory.integral_integral_swap (μ := μ) (ν := μ)
      (f := fun x y => F (x, y)) hF_int
  have hsecond :
      ∫ y, ∫ x, F (x, y) ∂ μ ∂ μ ≤
        ∫ y, ‖f y‖ ∂ μ := by
    have hleft_int :
        Integrable (fun y => ∫ x, F (x, y) ∂ μ) μ :=
      hF_int.integral_prod_right
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun y =>
        integral_nonneg fun x => by
          exact mul_nonneg
            (normalizedZerothReflectionKernel_nonneg ht L x y)
            (norm_nonneg _)
    · exact hf_int.norm
    · exact Filter.Eventually.of_forall fun y => by
        have hmass :=
          normalizedZerothReflectionKernel_intervalIntegral_left_le_one
            (L := L) (t := t) ht y
        calc
          ∫ x, F (x, y) ∂ μ
              = ‖f y‖ * ∫ x, K x y ∂ μ := by
                dsimp [F, K]
                rw [MeasureTheory.integral_mul_const]
                ring
          _ ≤ ‖f y‖ * 1 :=
                mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
          _ = ‖f y‖ := by ring
  exact hfirst.trans (hswap.trans_le hsecond)

/-- Nonnegative `L¹` contraction, without absolute values in the displayed
integrals. -/
lemma intervalSemigroupOperator_L1_contraction_nonneg
    {L t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure L)) (hf_nonneg : ∀ y, 0 ≤ f y) :
    ∫ x, intervalSemigroupOperator L t f x ∂ intervalMeasure L ≤
      ∫ y, f y ∂ intervalMeasure L := by
  have hleft :
      (∫ x, ‖intervalSemigroupOperator L t f x‖ ∂ intervalMeasure L) =
        ∫ x, intervalSemigroupOperator L t f x ∂ intervalMeasure L := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [Real.norm_eq_abs,
        abs_of_nonneg (intervalSemigroupOperator_nonneg ht hf_nonneg x)]
  have hright :
      (∫ y, ‖f y‖ ∂ intervalMeasure L) =
        ∫ y, f y ∂ intervalMeasure L := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg y)]
  have h :=
    intervalSemigroupOperator_L1_contraction
      (L := L) (t := t) ht hf_int
  rw [hleft, hright] at h
  exact h

set_option maxHeartbeats 0 in
-- Pointwise Hölder expands several concrete real-power kernel factors.
/-- Pointwise Jensen-type estimate for the interval helper:
`|T f|^p ≤ T(|f|^p)` for `1 < p < ∞`. -/
lemma intervalSemigroupOperator_norm_rpow_le_operator_norm_rpow
    {L t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure L))
    (x : ℝ) :
    ‖intervalSemigroupOperator L t f x‖ ^ p ≤
      intervalSemigroupOperator L t (fun y => ‖f y‖ ^ p) x := by
  let μ := intervalMeasure L
  let K : ℝ → ℝ := fun y => normalizedZerothReflectionKernel L t x y
  let a : ℝ → ℝ := fun y => (K y) ^ (1 / r)
  let b : ℝ → ℝ := fun y => (K y) ^ (1 / p) * ‖f y‖
  let B : ℝ := ∫ y, K y * ‖f y‖ ^ p ∂ μ
  have hK_nonneg : ∀ y, 0 ≤ K y := by
    intro y
    exact normalizedZerothReflectionKernel_nonneg ht L x y
  have hK_pos : ∀ y, K y ≠ 0 := by
    intro y
    exact (normalizedZerothReflectionKernel_pos ht L x y).ne'
  have hK_bound : ∀ y, K y ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
    intro y
    exact normalizedZerothReflectionKernel_pointwise_bound ht L x y
  have hA_nonneg : 0 ≤ 1 / Real.sqrt (4 * Real.pi * t) := by
    positivity
  have hK_cont : Continuous K := by
    dsimp [K]
    unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection heatKernel
    fun_prop
  have ha_meas : AEStronglyMeasurable a μ :=
    (hK_cont.rpow_const (p := 1 / r)
      (fun y => Or.inl (hK_pos y))).aestronglyMeasurable
  have hb_meas : AEStronglyMeasurable b μ := by
    have hKp_meas :
        AEStronglyMeasurable (fun y => (K y) ^ (1 / p)) μ :=
      (hK_cont.rpow_const (p := 1 / p)
        (fun y => Or.inl (hK_pos y))).aestronglyMeasurable
    exact hKp_meas.mul hf_mem.aestronglyMeasurable.norm
  have ha_mem : MemLp a (ENNReal.ofReal r) μ := by
    apply MemLp.of_bound ha_meas
      ((1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / r))
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a]
      rw [abs_of_nonneg (Real.rpow_nonneg (hK_nonneg y) (1 / r))]
      exact Real.rpow_le_rpow (hK_nonneg y) (hK_bound y) hrp.one_div_nonneg
  have hb_mem : MemLp b (ENNReal.ofReal p) μ := by
    apply MemLp.of_le_mul (g := f)
      (c := (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p)) hf_mem hb_meas
    exact Filter.Eventually.of_forall fun y => by
      dsimp [b]
      rw [abs_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (hK_nonneg y) (1 / p)) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hK_nonneg y) (hK_bound y)
          hrp.symm.one_div_nonneg)
        (abs_nonneg _)
  have ha_nonneg : 0 ≤ᵐ[μ] a :=
    Filter.Eventually.of_forall fun y =>
      Real.rpow_nonneg (hK_nonneg y) (1 / r)
  have hb_nonneg : 0 ≤ᵐ[μ] b :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg (hK_nonneg y) (1 / p)) (norm_nonneg _)
  have hholder :
      ∫ y, a y * b y ∂ μ ≤
        (∫ y, a y ^ r ∂ μ) ^ (1 / r) *
          (∫ y, b y ^ p ∂ μ) ^ (1 / p) :=
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := μ) (p := r) (q := p) hrp ha_nonneg hb_nonneg ha_mem hb_mem
  have hsum : 1 / r + 1 / p = 1 := by
    simpa [one_div] using hrp.inv_add_inv_eq_one
  have hab_integral :
      (∫ y, a y * b y ∂ μ) =
        ∫ y, K y * ‖f y‖ ∂ μ := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a, b]
      calc
        K y ^ (1 / r) * (K y ^ (1 / p) * ‖f y‖)
            = (K y ^ (1 / r) * K y ^ (1 / p)) * ‖f y‖ := by ring
        _ = K y ^ (1 / r + 1 / p) * ‖f y‖ := by
            rw [Real.rpow_add_of_nonneg (hK_nonneg y)
              hrp.one_div_nonneg hrp.symm.one_div_nonneg]
        _ = K y * ‖f y‖ := by rw [hsum, Real.rpow_one]
  have ha_pow_integral :
      (∫ y, a y ^ r ∂ μ) = ∫ y, K y ∂ μ := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a]
      rw [one_div, Real.rpow_inv_rpow (hK_nonneg y) hrp.ne_zero]
  have hb_pow_integral :
      (∫ y, b y ^ p ∂ μ) = B := by
    dsimp [B]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [b]
      rw [Real.mul_rpow
        (Real.rpow_nonneg (hK_nonneg y) (1 / p)) (abs_nonneg (f y))]
      rw [one_div, Real.rpow_inv_rpow (hK_nonneg y) hrp.symm.ne_zero]
  rw [hab_integral, ha_pow_integral, hb_pow_integral] at hholder
  have hmass_nonneg : 0 ≤ ∫ y, K y ∂ μ :=
    normalizedZerothReflectionKernel_intervalIntegral_nonneg ht L x
  have hmass_le : ∫ y, K y ∂ μ ≤ 1 :=
    normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x
  have hmass_root_le : (∫ y, K y ∂ μ) ^ (1 / r) ≤ 1 := by
    calc
      (∫ y, K y ∂ μ) ^ (1 / r)
          ≤ (1 : ℝ) ^ (1 / r) :=
            Real.rpow_le_rpow hmass_nonneg hmass_le hrp.one_div_nonneg
      _ = 1 := Real.one_rpow _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg fun y =>
      mul_nonneg (hK_nonneg y) (Real.rpow_nonneg (abs_nonneg (f y)) p)
  have hkernel_norm_le :
      ∫ y, K y * ‖f y‖ ∂ μ ≤ B ^ (1 / p) := by
    calc
      ∫ y, K y * ‖f y‖ ∂ μ
          ≤ (∫ y, K y ∂ μ) ^ (1 / r) * B ^ (1 / p) := hholder
      _ ≤ 1 * B ^ (1 / p) :=
            mul_le_mul_of_nonneg_right hmass_root_le
              (Real.rpow_nonneg hB_nonneg (1 / p))
      _ = B ^ (1 / p) := by ring
  have hkernel_norm_nonneg :
      0 ≤ ∫ y, K y * ‖f y‖ ∂ μ := by
    exact integral_nonneg fun y =>
      mul_nonneg (hK_nonneg y) (norm_nonneg _)
  have hTf_le :
      ‖intervalSemigroupOperator L t f x‖ ≤
        ∫ y, K y * ‖f y‖ ∂ μ := by
    simpa [K, μ, Real.norm_eq_abs] using
      intervalSemigroupOperator_abs_le_integral_abs
        (L := L) (t := t) ht f x
  calc
    ‖intervalSemigroupOperator L t f x‖ ^ p
        ≤ (∫ y, K y * ‖f y‖ ∂ μ) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) hTf_le hrp.symm.nonneg
    _ ≤ (B ^ (1 / p)) ^ p :=
          Real.rpow_le_rpow hkernel_norm_nonneg hkernel_norm_le
            hrp.symm.nonneg
    _ = B := by
          rw [one_div, Real.rpow_inv_rpow hB_nonneg hrp.symm.ne_zero]
    _ = intervalSemigroupOperator L t (fun y => ‖f y‖ ^ p) x := by
          rfl

/-- Integral `L^p` contraction for the restricted interval heat helper. -/
lemma intervalSemigroupOperator_Lp_contraction_integral
    {L t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure L)) :
    ∫ x, ‖intervalSemigroupOperator L t f x‖ ^ p ∂ intervalMeasure L ≤
      ∫ y, ‖f y‖ ^ p ∂ intervalMeasure L := by
  let g : ℝ → ℝ := fun y => ‖f y‖ ^ p
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hg_int : Integrable g (intervalMeasure L) := by
    simpa [g, ENNReal.toReal_ofReal hrp.symm.nonneg] using
      hf_mem.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hg_nonneg : ∀ y, 0 ≤ g y := by
    intro y
    exact Real.rpow_nonneg (norm_nonneg _) p
  have hTg_int :
      Integrable (fun x => intervalSemigroupOperator L t g x)
        (intervalMeasure L) := by
    have hTg_meas :
        AEStronglyMeasurable (fun x => intervalSemigroupOperator L t g x)
          (intervalMeasure L) :=
      intervalSemigroupOperator_aestronglyMeasurable hg_int.aestronglyMeasurable
    have hbound : ∀ x, ‖intervalSemigroupOperator L t g x‖ ≤
        (1 / Real.sqrt (4 * Real.pi * t)) *
          ∫ y, ‖g y‖ ∂ intervalMeasure L := by
      intro x
      exact intervalSemigroupOperator_L1_Linfty ht hg_int x
    exact Integrable.of_bound hTg_meas
      ((1 / Real.sqrt (4 * Real.pi * t)) *
        ∫ y, ‖g y‖ ∂ intervalMeasure L)
      (Filter.Eventually.of_forall hbound)
  have hpoint : ∀ x,
      ‖intervalSemigroupOperator L t f x‖ ^ p ≤
        intervalSemigroupOperator L t g x := by
    intro x
    simpa [g] using
      intervalSemigroupOperator_norm_rpow_le_operator_norm_rpow
        (L := L) (t := t) (p := p) (r := r) ht hrp hf_mem x
  have hfirst :
      ∫ x, ‖intervalSemigroupOperator L t f x‖ ^ p ∂ intervalMeasure L ≤
        ∫ x, intervalSemigroupOperator L t g x ∂ intervalMeasure L := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (norm_nonneg _) p
    · exact hTg_int
    · exact Filter.Eventually.of_forall hpoint
  have hcontract :=
    intervalSemigroupOperator_L1_contraction_nonneg
      (L := L) (t := t) ht hg_int hg_nonneg
  calc
    ∫ x, ‖intervalSemigroupOperator L t f x‖ ^ p ∂ intervalMeasure L
        ≤ ∫ x, intervalSemigroupOperator L t g x ∂ intervalMeasure L := hfirst
    _ ≤ ∫ y, g y ∂ intervalMeasure L := hcontract
    _ = ∫ y, ‖f y‖ ^ p ∂ intervalMeasure L := rfl

/-- `L^p` contraction for the restricted interval heat helper, in
`LpSeminorm` notation. -/
lemma intervalHeatSemigroup_Lp_contraction
    {L t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure L)) :
    lpNorm (fun x => intervalSemigroupOperator L t f x)
        (ENNReal.ofReal p) (intervalMeasure L) ≤
      lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := by
  have hT_meas :
      AEStronglyMeasurable (fun x => intervalSemigroupOperator L t f x)
        (intervalMeasure L) :=
    intervalSemigroupOperator_aestronglyMeasurable hf_mem.aestronglyMeasurable
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  rw [lpNorm_eq_integral_norm_rpow_toReal hp_ne_zero hp_ne_top hT_meas]
  rw [lpNorm_eq_integral_norm_rpow_toReal
    hp_ne_zero hp_ne_top hf_mem.aestronglyMeasurable]
  rw [ENNReal.toReal_ofReal hrp.symm.nonneg]
  exact Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p)
    (intervalSemigroupOperator_Lp_contraction_integral
      (L := L) (t := t) (p := p) (r := r) ht hrp hf_mem)
    hrp.symm.inv_nonneg

/-- Uniform `L^r` bound for the restricted reflected interval heat kernel.
If `r` is Hölder-conjugate to `p`, the bound has the expected
`t^{-1/(2p)}` singularity. -/
lemma intervalHeatKernel_Lr_norm_bound
    {L t r p : ℝ} (ht : 0 < t)
    (hrp : r.HolderConjugate p) (x : ℝ) :
    (∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L) ^
        (1 / r) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) := by
  let A : ℝ := 1 / Real.sqrt (4 * Real.pi * t)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hkernel_nonneg :
      ∀ y, 0 ≤ normalizedZerothReflectionKernel L t x y := by
    intro y
    exact normalizedZerothReflectionKernel_nonneg ht L x y
  have hkernel_bound :
      ∀ y, normalizedZerothReflectionKernel L t x y ≤ A := by
    intro y
    simpa [A] using normalizedZerothReflectionKernel_pointwise_bound ht L x y
  have hkernel_int :
      Integrable (fun y => normalizedZerothReflectionKernel L t x y)
        (intervalMeasure L) :=
    normalizedZerothReflectionKernel_interval_integrable ht L x
  have hright_int :
      Integrable
        (fun y => A ^ (r - 1) * normalizedZerothReflectionKernel L t x y)
        (intervalMeasure L) :=
    hkernel_int.const_mul (A ^ (r - 1))
  have hpow_le :
      ∀ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ≤
        A ^ (r - 1) * normalizedZerothReflectionKernel L t x y := by
    intro y
    let k := normalizedZerothReflectionKernel L t x y
    have hk_nonneg : 0 ≤ k := hkernel_nonneg y
    have hk_bound : k ≤ A := hkernel_bound y
    have hr_minus_nonneg : 0 ≤ r - 1 := le_of_lt hrp.sub_one_pos
    have hkpow : k ^ r = k ^ (r - 1) * k := by
      calc
        k ^ r = k ^ ((r - 1) + 1) := by ring_nf
        _ = k ^ (r - 1) * k ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hk_nonneg hr_minus_nonneg zero_le_one
        _ = k ^ (r - 1) * k := by rw [Real.rpow_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hk_nonneg, hkpow]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hk_nonneg hk_bound hr_minus_nonneg) hk_nonneg
  have hintegral_le :
      ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L ≤
        A ^ (r - 1) *
          ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
    calc
      ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L
          ≤ ∫ y, A ^ (r - 1) *
              normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun y =>
                Real.rpow_nonneg (norm_nonneg _) r
            · exact hright_int
            · exact Filter.Eventually.of_forall hpow_le
      _ = A ^ (r - 1) *
            ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L := by
            rw [MeasureTheory.integral_const_mul]
  have hmass := normalizedZerothReflectionKernel_intervalIntegral_le_one ht L x
  have hscale :
      A ^ (r - 1) *
          ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L ≤
        A ^ (r - 1) * 1 := by
    exact mul_le_mul_of_nonneg_left hmass
      (Real.rpow_nonneg hA_nonneg (r - 1))
  have htotal :
      ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L ≤
        A ^ (r - 1) := by
    calc
      ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L
          ≤ A ^ (r - 1) *
              ∫ y, normalizedZerothReflectionKernel L t x y ∂ intervalMeasure L :=
            hintegral_le
      _ ≤ A ^ (r - 1) * 1 := hscale
      _ = A ^ (r - 1) := by ring
  have hleft_nonneg :
      0 ≤ ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L := by
    exact integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) r
  have hroot := Real.rpow_le_rpow hleft_nonneg htotal
    (le_of_lt hrp.one_div_pos)
  have hexp : (r - 1) * (1 / r) = 1 / p := by
    have h := hrp.inv_add_inv_eq_one
    field_simp [hrp.ne_zero, hrp.symm.ne_zero] at h ⊢
    linarith
  calc
    (∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r ∂ intervalMeasure L) ^
        (1 / r)
        ≤ (A ^ (r - 1)) ^ (1 / r) := hroot
    _ = A ^ (1 / p) := by
      rw [← Real.rpow_mul hA_nonneg]
      rw [hexp]
    _ = (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) := rfl

set_option maxHeartbeats 0 in
-- The `LpSeminorm` simplifications expand `intervalSemigroupOperator` and `lpNorm`.
/-- Interval Neumann heat-helper endpoint smoothing in `LpSeminorm` notation:
`L¹([0,L]) → L∞([0,L])`.  This is the `p = 1`, `q = ∞` endpoint of
the interval heat-semigroup smoothing chain. -/
theorem intervalHeatSemigroup_L1_Linfty_bound
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

set_option maxHeartbeats 0 in
-- Pointwise Hölder plus the interval-kernel `L^r` bound.
/-- Pointwise interval Neumann heat-helper smoothing from `L^p([0,L])` to
`L∞([0,L])`. -/
lemma intervalSemigroupOperator_Lp_Linfty_pointwise
    {L t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure L))
    (x : ℝ) :
    ‖intervalSemigroupOperator L t f x‖ ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := by
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hlp_eq :
      lpNorm f (ENNReal.ofReal p) (intervalMeasure L) =
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      hp_ne_zero hp_ne_top hf_mem.aestronglyMeasurable]
    rw [ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  have hkernel_meas :
      AEStronglyMeasurable
        (fun y => normalizedZerothReflectionKernel L t x y)
        (intervalMeasure L) := by
    have hk_cont :
        Continuous (fun y : ℝ => normalizedZerothReflectionKernel L t x y) := by
      unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection heatKernel
      fun_prop
    exact hk_cont.aestronglyMeasurable
  have hkernel_mem :
      MemLp (fun y => normalizedZerothReflectionKernel L t x y)
        (ENNReal.ofReal r) (intervalMeasure L) := by
    apply MemLp.of_bound hkernel_meas (1 / Real.sqrt (4 * Real.pi * t))
    exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y)]
      exact normalizedZerothReflectionKernel_pointwise_bound ht L x y
  have hholder :
      ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ * ‖f y‖
          ∂ intervalMeasure L ≤
        (∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r
            ∂ intervalMeasure L) ^ (1 / r) *
          (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) :=
    MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := intervalMeasure L)
      (f := fun y : ℝ => normalizedZerothReflectionKernel L t x y)
      (g := f) hrp hkernel_mem hf_mem
  have hkernel_norm :=
    intervalHeatKernel_Lr_norm_bound
      (L := L) (t := t) (r := r) (p := p) ht hrp x
  unfold intervalSemigroupOperator
  calc
    ‖∫ y, normalizedZerothReflectionKernel L t x y * f y
        ∂ intervalMeasure L‖
        ≤ ∫ y, ‖normalizedZerothReflectionKernel L t x y * f y‖
            ∂ intervalMeasure L :=
          norm_integral_le_integral_norm _
    _ = ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ * ‖f y‖
            ∂ intervalMeasure L := by
          congr 1
          ext y
          rw [norm_mul]
    _ ≤ (∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r
            ∂ intervalMeasure L) ^ (1 / r) *
          (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) :=
          hholder
    _ ≤ (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
          (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) := by
          exact mul_le_mul_of_nonneg_right hkernel_norm
            (Real.rpow_nonneg
              (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) p)
              (1 / p))
    _ = (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
          lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := by
          rw [hlp_eq]

set_option maxHeartbeats 0 in
-- This proof combines Hölder, the interval-kernel `L^r` bound, and `LpSeminorm`.
/-- Interval Neumann heat-helper smoothing from `L^p([0,L])` to `L∞([0,L])`.
Here `r` is the Hölder conjugate of `p`, so the coefficient has the standard
one-dimensional heat singularity `t^{-1/(2p)}`. -/
theorem intervalHeatSemigroup_Lp_Linfty_bound
    {L t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure L)) :
    lpNorm (fun x => intervalSemigroupOperator L t f x) ∞ (intervalMeasure L) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := by
  let C : ℝ :=
    (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
      lpNorm f (ENNReal.ofReal p) (intervalMeasure L)
  have hT_meas :
      AEStronglyMeasurable (fun x => intervalSemigroupOperator L t f x)
        (intervalMeasure L) :=
    intervalSemigroupOperator_aestronglyMeasurable hf_mem.aestronglyMeasurable
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hlp_eq :
      lpNorm f (ENNReal.ofReal p) (intervalMeasure L) =
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      hp_ne_zero hp_ne_top hf_mem.aestronglyMeasurable]
    rw [ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  have hpoint : ∀ x, ‖intervalSemigroupOperator L t f x‖ ≤ C := by
    intro x
    have hkernel_meas :
        AEStronglyMeasurable
          (fun y => normalizedZerothReflectionKernel L t x y)
          (intervalMeasure L) := by
      have hk_cont :
          Continuous (fun y : ℝ => normalizedZerothReflectionKernel L t x y) := by
        unfold normalizedZerothReflectionKernel neumannHeatKernel_zerothReflection heatKernel
        fun_prop
      exact hk_cont.aestronglyMeasurable
    have hkernel_mem :
        MemLp (fun y => normalizedZerothReflectionKernel L t x y)
          (ENNReal.ofReal r) (intervalMeasure L) := by
      apply MemLp.of_bound hkernel_meas (1 / Real.sqrt (4 * Real.pi * t))
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (normalizedZerothReflectionKernel_nonneg ht L x y)]
        exact normalizedZerothReflectionKernel_pointwise_bound ht L x y
    have hholder :
        ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ * ‖f y‖
            ∂ intervalMeasure L ≤
          (∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r
              ∂ intervalMeasure L) ^ (1 / r) *
            (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := intervalMeasure L)
        (f := fun y : ℝ => normalizedZerothReflectionKernel L t x y)
        (g := f) hrp hkernel_mem hf_mem
    have hkernel_norm :=
      intervalHeatKernel_Lr_norm_bound
        (L := L) (t := t) (r := r) (p := p) ht hrp x
    unfold intervalSemigroupOperator
    calc
      ‖∫ y, normalizedZerothReflectionKernel L t x y * f y
          ∂ intervalMeasure L‖
          ≤ ∫ y, ‖normalizedZerothReflectionKernel L t x y * f y‖
              ∂ intervalMeasure L :=
            norm_integral_le_integral_norm _
      _ = ∫ y, ‖normalizedZerothReflectionKernel L t x y‖ * ‖f y‖
              ∂ intervalMeasure L := by
            congr 1
            ext y
            rw [norm_mul]
      _ ≤ (∫ y, ‖normalizedZerothReflectionKernel L t x y‖ ^ r
              ∂ intervalMeasure L) ^ (1 / r) *
            (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) :=
            hholder
      _ ≤ (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
            (∫ y, ‖f y‖ ^ p ∂ intervalMeasure L) ^ (1 / p) := by
            exact mul_le_mul_of_nonneg_right hkernel_norm
              (Real.rpow_nonneg
                (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) p)
                (1 / p))
      _ = C := by
            dsimp [C]
            rw [hlp_eq]
            simp [Real.norm_eq_abs]
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) (1 / p)) lpNorm_nonneg
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
    _ = (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := rfl

set_option maxHeartbeats 0 in
-- Interpolate the `L^p` contraction with the pointwise `L^p → L∞` bound.
/-- Interval Neumann heat-helper smoothing from `L^p([0,L])` to finite
`L^q([0,L])`, for `1 < p ≤ q < ∞`.  The exponent is the one-dimensional
heat singularity `t^{-1/2(1/p-1/q)}`. -/
theorem intervalHeatSemigroup_Lp_Lq_bound
    {L t p q r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    (hpq : p ≤ q)
    {f : ℝ → ℝ} (hf_mem : MemLp f (ENNReal.ofReal p) (intervalMeasure L)) :
    lpNorm (fun x => intervalSemigroupOperator L t f x)
        (ENNReal.ofReal q) (intervalMeasure L) ≤
      (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p - 1 / q) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := by
  let μ := intervalMeasure L
  let T : ℝ → ℝ := fun x => intervalSemigroupOperator L t f x
  let A : ℝ := 1 / Real.sqrt (4 * Real.pi * t)
  let Fp : ℝ := lpNorm f (ENNReal.ofReal p) μ
  let M : ℝ := A ^ (1 / p) * Fp
  have hp_pos : 0 < p := hrp.symm.pos
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have hq_ne_zero : q ≠ 0 := hq_pos.ne'
  have hq_minus_nonneg : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hp_div_q_le_one : p / q ≤ 1 := by
    rw [div_le_one hq_pos]
    exact hpq
  have htheta_nonneg : 0 ≤ 1 - p / q := sub_nonneg.mpr hp_div_q_le_one
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hFp_nonneg : 0 ≤ Fp := by
    dsimp [Fp]
    exact lpNorm_nonneg
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.rpow_nonneg hA_nonneg (1 / p)) hFp_nonneg
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hp_pos
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hq_ne_zero_enn : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hq_pos
  have hq_ne_top : ENNReal.ofReal q ≠ ⊤ := by
    simp
  have hT_meas : AEStronglyMeasurable T μ := by
    dsimp [T, μ]
    exact intervalSemigroupOperator_aestronglyMeasurable hf_mem.aestronglyMeasurable
  have hpoint : ∀ x, ‖T x‖ ≤ M := by
    intro x
    dsimp [T, M, A, Fp, μ]
    exact intervalSemigroupOperator_Lp_Linfty_pointwise
      (L := L) (t := t) (p := p) (r := r) ht hrp hf_mem x
  have hT_mem_p : MemLp T (ENNReal.ofReal p) μ := by
    exact MemLp.of_bound hT_meas M (Filter.Eventually.of_forall hpoint)
  have hTp_int :
      Integrable (fun x => ‖T x‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hrp.symm.nonneg] using
      hT_mem_p.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hright_int :
      Integrable (fun x => M ^ (q - p) * ‖T x‖ ^ p) μ :=
    hTp_int.const_mul (M ^ (q - p))
  have hpow_point : ∀ x, ‖T x‖ ^ q ≤ M ^ (q - p) * ‖T x‖ ^ p := by
    intro x
    have hx_nonneg : 0 ≤ ‖T x‖ := norm_nonneg _
    have hsplit : ‖T x‖ ^ q = ‖T x‖ ^ (q - p) * ‖T x‖ ^ p := by
      calc
        ‖T x‖ ^ q = ‖T x‖ ^ ((q - p) + p) := by ring_nf
        _ = ‖T x‖ ^ (q - p) * ‖T x‖ ^ p :=
          Real.rpow_add_of_nonneg hx_nonneg hq_minus_nonneg hrp.symm.nonneg
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx_nonneg (hpoint x) hq_minus_nonneg)
      (Real.rpow_nonneg hx_nonneg p)
  have hq_integral_le :
      ∫ x, ‖T x‖ ^ q ∂ μ ≤
        M ^ (q - p) * ∫ x, ‖f x‖ ^ p ∂ μ := by
    calc
      ∫ x, ‖T x‖ ^ q ∂ μ
          ≤ ∫ x, M ^ (q - p) * ‖T x‖ ^ p ∂ μ := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun x =>
                Real.rpow_nonneg (norm_nonneg _) q
            · exact hright_int
            · exact Filter.Eventually.of_forall hpow_point
      _ = M ^ (q - p) * ∫ x, ‖T x‖ ^ p ∂ μ := by
            rw [MeasureTheory.integral_const_mul]
      _ ≤ M ^ (q - p) * ∫ x, ‖f x‖ ^ p ∂ μ := by
            exact mul_le_mul_of_nonneg_left
              (intervalSemigroupOperator_Lp_contraction_integral
                (L := L) (t := t) (p := p) (r := r) ht hrp hf_mem)
              (Real.rpow_nonneg hM_nonneg (q - p))
  let If : ℝ := ∫ x, ‖f x‖ ^ p ∂ μ
  have hIf_nonneg : 0 ≤ If := by
    dsimp [If]
    exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg (f x)) p
  have hFp_eq : Fp = If ^ (1 / p) := by
    dsimp [Fp, If, μ]
    rw [lpNorm_eq_integral_norm_rpow_toReal
      hp_ne_zero hp_ne_top hf_mem.aestronglyMeasurable]
    rw [ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  have hFp_pow : Fp ^ p = If := by
    rw [hFp_eq]
    rw [one_div, Real.rpow_inv_rpow hIf_nonneg hrp.symm.ne_zero]
  have hq_integral_le' :
      ∫ x, ‖T x‖ ^ q ∂ μ ≤ M ^ (q - p) * If := by
    simpa [If] using hq_integral_le
  have hroot_le :
      (∫ x, ‖T x‖ ^ q ∂ μ) ^ (1 / q) ≤
        (M ^ (q - p) * If) ^ (1 / q) := by
    exact Real.rpow_le_rpow
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) q)
      hq_integral_le' (le_of_lt (one_div_pos.mpr hq_pos))
  have hFp_add : Fp ^ (q - p) * Fp ^ p = Fp ^ q := by
    calc
      Fp ^ (q - p) * Fp ^ p = Fp ^ ((q - p) + p) := by
        rw [Real.rpow_add_of_nonneg hFp_nonneg hq_minus_nonneg hrp.symm.nonneg]
      _ = Fp ^ q := by ring_nf
  have hA_exp :
      (1 / p) * (q - p) * (1 / q) = 1 / p - 1 / q := by
    field_simp [hrp.symm.ne_zero, hq_ne_zero]
  have hroot_eq :
      (M ^ (q - p) * If) ^ (1 / q) =
        A ^ (1 / p - 1 / q) * Fp := by
    calc
      (M ^ (q - p) * If) ^ (1 / q)
          = ((A ^ (1 / p) * Fp) ^ (q - p) * Fp ^ p) ^ (1 / q) := by
              rw [hFp_pow]
      _ = ((A ^ (1 / p)) ^ (q - p) * Fp ^ (q - p) * Fp ^ p) ^
            (1 / q) := by
              rw [Real.mul_rpow
                (Real.rpow_nonneg hA_nonneg (1 / p)) hFp_nonneg]
      _ = ((A ^ (1 / p)) ^ (q - p) * Fp ^ q) ^ (1 / q) := by
              rw [← hFp_add]
              ring_nf
      _ = ((A ^ (1 / p)) ^ (q - p)) ^ (1 / q) *
            (Fp ^ q) ^ (1 / q) := by
              rw [Real.mul_rpow
                (Real.rpow_nonneg
                  (Real.rpow_nonneg hA_nonneg (1 / p)) (q - p))
                (Real.rpow_nonneg hFp_nonneg q)]
      _ = A ^ ((1 / p) * (q - p) * (1 / q)) * Fp := by
              rw [← Real.rpow_mul hA_nonneg (1 / p) (q - p)]
              rw [← Real.rpow_mul hA_nonneg ((1 / p) * (q - p)) (1 / q)]
              rw [show (Fp ^ q) ^ (1 / q) = Fp by
                rw [one_div]
                rw [← Real.rpow_mul hFp_nonneg q q⁻¹]
                rw [mul_inv_cancel₀ hq_ne_zero, Real.rpow_one]]
      _ = A ^ (1 / p - 1 / q) * Fp := by
              rw [hA_exp]
  calc
    lpNorm T (ENNReal.ofReal q) μ
        = (∫ x, ‖T x‖ ^ q ∂ μ) ^ (1 / q) := by
          rw [lpNorm_eq_integral_norm_rpow_toReal hq_ne_zero_enn hq_ne_top hT_meas]
          rw [ENNReal.toReal_ofReal hq_pos.le]
          simp [one_div]
    _ ≤ (M ^ (q - p) * If) ^ (1 / q) := hroot_le
    _ = A ^ (1 / p - 1 / q) * Fp := hroot_eq
    _ = (1 / Real.sqrt (4 * Real.pi * t)) ^ (1 / p - 1 / q) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure L) := rfl

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

/-! ## Cosine-series gradient model -/

/-- The `unitIntervalCosineMode` used by the heat semigroup is the same
cosine mode as the spectral API in `CosineSpectrum`. -/
theorem unitIntervalCosineMode_eq_cosineMode (n : ℕ) (x : ℝ) :
    unitIntervalCosineMode n x =
      ShenWork.CosineSpectrum.cosineMode n x := by
  rfl

/-- Derivative of the unit-interval cosine mode, imported from the spectral API. -/
theorem unitIntervalCosineMode_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (unitIntervalCosineMode n)
      (-((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x)) x := by
  simpa [unitIntervalCosineMode_eq_cosineMode] using
    ShenWork.CosineSpectrum.cosineMode_hasDerivAt n x

/-- Pointwise derivative formula for the unit-interval cosine mode. -/
theorem unitIntervalCosineMode_deriv (n : ℕ) (x : ℝ) :
    deriv (unitIntervalCosineMode n) x =
      -((n : ℝ) * Real.pi) *
        Real.sin ((n : ℝ) * Real.pi * x) :=
  (unitIntervalCosineMode_hasDerivAt n x).deriv

/-- Pointwise coefficient multiplying the `n`-th cosine coefficient in the
spatial derivative of the interval heat flow. -/
def unitIntervalCosineHeatGradientPointWeight (t x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * unitIntervalCosineEigenvalue n) *
    (-((n : ℝ) * Real.pi) * Real.sin ((n : ℝ) * Real.pi * x))

/-- Cosine-coefficient model for the spatial derivative of the interval heat
semigroup value at `x`. -/
def unitIntervalCosineHeatGradientValue (t : ℝ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatGradientPointWeight t x n * a n

/-- Derivative of a single heat-weighted cosine mode. -/
theorem unitIntervalCosineHeatPointWeight_hasDerivAt
    (t : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => unitIntervalCosineHeatPointWeight t y n)
      (unitIntervalCosineHeatGradientPointWeight t x n) x := by
  have hmode := unitIntervalCosineMode_hasDerivAt n x
  simpa [unitIntervalCosineHeatPointWeight,
    unitIntervalCosineHeatGradientPointWeight, mul_assoc] using
    hmode.const_mul (Real.exp (-t * unitIntervalCosineEigenvalue n))

/-- Derivative formula for one heat-weighted cosine coefficient. -/
theorem unitIntervalCosineHeatPointWeight_deriv
    (t : ℝ) (n : ℕ) (x : ℝ) :
    deriv (fun y : ℝ => unitIntervalCosineHeatPointWeight t y n) x =
      unitIntervalCosineHeatGradientPointWeight t x n :=
  (unitIntervalCosineHeatPointWeight_hasDerivAt t n x).deriv

/-- Derivative of one heat-weighted cosine term with a fixed coefficient. -/
theorem unitIntervalCosineHeatTerm_hasDerivAt
    (t : ℝ) (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => unitIntervalCosineHeatPointWeight t y n * a n)
      (unitIntervalCosineHeatGradientPointWeight t x n * a n) x := by
  simpa [mul_assoc] using
    (unitIntervalCosineHeatPointWeight_hasDerivAt t n x).mul_const (a n)

/-- Term-by-term differentiation of the cosine heat series, stated with an
explicit summable majorant for the derivative series.  This is the analytic
bridge needed before turning the spectral gradient estimate into an interval
`LpSeminorm` estimate. -/
theorem unitIntervalCosineHeatValue_hasDerivAt_of_summable_bound
    {t x x₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hbound :
      ∀ n y,
        ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t x₀ n * a n) :
    HasDerivAt (fun z : ℝ => unitIntervalCosineHeatValue t a z)
      (unitIntervalCosineHeatGradientValue t a x) x := by
  simpa [unitIntervalCosineHeatValue, unitIntervalCosineHeatGradientValue] using
    (hasDerivAt_tsum
      (𝕜 := ℝ) (F := ℝ)
      (u := u)
      (g := fun n z =>
        unitIntervalCosineHeatPointWeight t z n * a n)
      (g' := fun n z =>
        unitIntervalCosineHeatGradientPointWeight t z n * a n)
      hu
      (fun n y => by
        simpa using unitIntervalCosineHeatTerm_hasDerivAt t a n y)
      (fun n y => by
        simpa using hbound n y)
      (by simpa using h₀)
      x)

/-- Derivative form of `unitIntervalCosineHeatValue_hasDerivAt_of_summable_bound`. -/
theorem unitIntervalCosineHeatValue_deriv_of_summable_bound
    {t x x₀ : ℝ} {a : ℕ → ℝ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hbound :
      ∀ n y,
        ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤ u n)
    (h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t x₀ n * a n) :
    deriv (fun z : ℝ => unitIntervalCosineHeatValue t a z) x =
      unitIntervalCosineHeatGradientValue t a x :=
  (unitIntervalCosineHeatValue_hasDerivAt_of_summable_bound
    (t := t) (x := x) (x₀ := x₀) hu hbound h₀).deriv

/-- Existing spectral coefficient `L² → L²` gradient smoothing, exposed from
`HeatKernelLpEstimates` for the interval heat-kernel layer. -/
theorem intervalCosineHeatGradient_L2_L2_coeff_bound
    {t : ℝ} (ht : 0 < t) {a : ℕ → ℝ}
    (ha : Summable fun n => (a n) ^ 2) :
    unitIntervalCosineHeatGradientTsumL2Norm t a ≤
      (1 / Real.sqrt t) * unitIntervalCosineL2TsumNorm a :=
  unitIntervalCosineHeatGradientTsumL2Norm_le_inv_sqrt ht ha

/-- Pointwise energy of the derivative evaluation functional. -/
def unitIntervalCosineHeatGradientPointEnergy (t x : ℝ) : ℝ :=
  ∑' n, (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2

/-- Heat-gradient trace for the unit-interval cosine model. -/
def unitIntervalCosineHeatGradientTrace (t : ℝ) : ℝ :=
  ∑' n, unitIntervalCosineHeatGradientMultiplier t n

/-- The squared pointwise derivative weight is bounded by the spectral
gradient multiplier. -/
lemma unitIntervalCosineHeatGradientPointWeight_sq_le_multiplier
    (t x : ℝ) (n : ℕ) :
    (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2 ≤
      unitIntervalCosineHeatGradientMultiplier t n := by
  let lambda := unitIntervalCosineEigenvalue n
  let s := Real.sin ((n : ℝ) * Real.pi * x)
  have hsin : s ^ 2 ≤ 1 := by
    dsimp [s]
    rw [sq_le_one_iff_abs_le_one]
    exact abs_sin_le_one _
  have hcoeff_nonneg : 0 ≤ (Real.exp (-t * lambda)) ^ 2 * lambda := by
    dsimp [lambda, unitIntervalCosineEigenvalue]
    positivity
  calc
    (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2
        = (Real.exp (-t * lambda)) ^ 2 * lambda * s ^ 2 := by
          dsimp [unitIntervalCosineHeatGradientPointWeight, lambda,
            unitIntervalCosineEigenvalue, s]
          ring
    _ ≤ (Real.exp (-t * lambda)) ^ 2 * lambda * 1 := by
          exact mul_le_mul_of_nonneg_left hsin hcoeff_nonneg
    _ = unitIntervalCosineHeatGradientMultiplier t n := by
          dsimp [unitIntervalCosineHeatGradientMultiplier, lambda]
          rw [mul_one, sq, ← Real.exp_add]
          ring

/-- Pointwise derivative evaluation energy is bounded by the heat-gradient trace. -/
lemma unitIntervalCosineHeatGradientPointEnergy_le_trace {t x : ℝ}
    (htrace : Summable fun n => unitIntervalCosineHeatGradientMultiplier t n) :
    unitIntervalCosineHeatGradientPointEnergy t x ≤
      unitIntervalCosineHeatGradientTrace t := by
  have hpoint :
      Summable fun n =>
        (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatGradientPointWeight_sq_le_multiplier t x n)
      htrace
  calc
    unitIntervalCosineHeatGradientPointEnergy t x
        = ∑' n, (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2 := rfl
    _ ≤ ∑' n, unitIntervalCosineHeatGradientMultiplier t n :=
        hpoint.tsum_le_tsum
          (fun n =>
            unitIntervalCosineHeatGradientPointWeight_sq_le_multiplier t x n)
          htrace
    _ = unitIntervalCosineHeatGradientTrace t := rfl

/-- The nonzero spectral multiplier is controlled by the reciprocal spectrum. -/
lemma unitIntervalCosineHeatGradientMultiplier_le_reciprocal
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : n ≠ 0) :
    unitIntervalCosineHeatGradientMultiplier t n ≤
      (1 / t ^ 2) * (1 / unitIntervalCosineEigenvalue n) := by
  let lambda := unitIntervalCosineEigenvalue n
  have hnpos_real : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda, unitIntervalCosineEigenvalue]
    exact sq_pos_of_pos (mul_pos hnpos_real Real.pi_pos)
  let z := (t * lambda) * Real.exp (-(t * lambda))
  have hz_nonneg : 0 ≤ z := by
    dsimp [z]
    positivity
  have hz_le_one : z ≤ 1 := by
    dsimp [z]
    exact real_mul_exp_neg_le_one (by positivity)
  have hz_sq : z ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    rw [abs_of_nonneg hz_nonneg]
    exact hz_le_one
  have hscale_nonneg : 0 ≤ 1 / (t ^ 2 * lambda) := by
    positivity
  calc
    unitIntervalCosineHeatGradientMultiplier t n
        = (1 / (t ^ 2 * lambda)) * z ^ 2 := by
          dsimp [unitIntervalCosineHeatGradientMultiplier, z, lambda]
          have hexp_sq :
              (Real.exp (-(t * unitIntervalCosineEigenvalue n))) ^ 2 =
                Real.exp (-2 * t * unitIntervalCosineEigenvalue n) := by
            rw [sq, ← Real.exp_add]
            congr 1
            ring
          rw [show
              (t * unitIntervalCosineEigenvalue n *
                  Real.exp (-(t * unitIntervalCosineEigenvalue n))) ^ 2 =
                t ^ 2 * (unitIntervalCosineEigenvalue n) ^ 2 *
                  Real.exp (-2 * t * unitIntervalCosineEigenvalue n) by
            rw [mul_pow, mul_pow, hexp_sq]]
          field_simp [ne_of_gt ht, ne_of_gt hlambda_pos]
    _ ≤ (1 / (t ^ 2 * lambda)) * 1 := by
          exact mul_le_mul_of_nonneg_left hz_sq hscale_nonneg
    _ = (1 / t ^ 2) * (1 / unitIntervalCosineEigenvalue n) := by
          dsimp [lambda]
          field_simp [ne_of_gt ht, ne_of_gt hlambda_pos]

/-- A summable majorant for the heat-gradient trace. -/
def unitIntervalCosineHeatGradientTraceMajorant (t : ℝ) (n : ℕ) : ℝ :=
  (1 / t ^ 2) * unitIntervalCosineReciprocalEigenvalueTerm n

/-- Each heat-gradient trace summand is controlled by the reciprocal-spectrum
majorant. -/
lemma unitIntervalCosineHeatGradientMultiplier_le_majorant
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    unitIntervalCosineHeatGradientMultiplier t n ≤
      unitIntervalCosineHeatGradientTraceMajorant t n := by
  by_cases hn : n = 0
  · subst n
    simp [unitIntervalCosineHeatGradientTraceMajorant,
      unitIntervalCosineHeatGradientMultiplier,
      unitIntervalCosineReciprocalEigenvalueTerm, unitIntervalCosineEigenvalue]
  · have hrecip :=
      unitIntervalCosineHeatGradientMultiplier_le_reciprocal
        (t := t) ht (n := n) hn
    simpa [unitIntervalCosineHeatGradientTraceMajorant,
      unitIntervalCosineReciprocalEigenvalueTerm, hn] using hrecip

/-- The heat-gradient trace is summable when the nonzero reciprocal spectrum
is summable. -/
lemma unitIntervalCosineHeatGradientTrace_summable
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm) :
    Summable fun n => unitIntervalCosineHeatGradientMultiplier t n := by
  have hnonneg :
      ∀ n, 0 ≤ unitIntervalCosineHeatGradientMultiplier t n := by
    intro n
    dsimp [unitIntervalCosineHeatGradientMultiplier,
      unitIntervalCosineEigenvalue]
    positivity
  have hdom :
      ∀ n,
        unitIntervalCosineHeatGradientMultiplier t n ≤
          unitIntervalCosineHeatGradientTraceMajorant t n :=
    unitIntervalCosineHeatGradientMultiplier_le_majorant ht
  exact Summable.of_nonneg_of_le hnonneg hdom
    (by
      simpa [unitIntervalCosineHeatGradientTraceMajorant] using
        hrecip.mul_left (1 / t ^ 2))

/-- Heat-gradient trace bound by the reciprocal-spectrum trace. -/
lemma unitIntervalCosineHeatGradientTrace_le_reciprocalTrace
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm) :
    unitIntervalCosineHeatGradientTrace t ≤
      (1 / t ^ 2) * unitIntervalCosineReciprocalEigenvalueTrace := by
  have htrace := unitIntervalCosineHeatGradientTrace_summable ht hrecip
  have hdom :
      ∀ n,
        unitIntervalCosineHeatGradientMultiplier t n ≤
          unitIntervalCosineHeatGradientTraceMajorant t n :=
    unitIntervalCosineHeatGradientMultiplier_le_majorant ht
  calc
    unitIntervalCosineHeatGradientTrace t
        = ∑' n, unitIntervalCosineHeatGradientMultiplier t n := rfl
    _ ≤ ∑' n, unitIntervalCosineHeatGradientTraceMajorant t n :=
        htrace.tsum_le_tsum hdom
          (by
            simpa [unitIntervalCosineHeatGradientTraceMajorant] using
              hrecip.mul_left (1 / t ^ 2))
    _ = (1 / t ^ 2) * unitIntervalCosineReciprocalEigenvalueTrace := by
        dsimp [unitIntervalCosineHeatGradientTraceMajorant,
          unitIntervalCosineReciprocalEigenvalueTrace]
        exact Summable.tsum_mul_left (1 / t ^ 2) hrecip

/-- Short-time-independent constant for coefficient `L² → L∞` heat-gradient
smoothing. -/
def unitIntervalCosineHeatGradientL2LinftyConstant : ℝ :=
  Real.sqrt unitIntervalCosineReciprocalEigenvalueTrace

/-- Square-root form of the heat-gradient trace bound. -/
lemma unitIntervalCosineHeatGradientTrace_sqrt_le_inv
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm) :
    Real.sqrt (unitIntervalCosineHeatGradientTrace t) ≤
      unitIntervalCosineHeatGradientL2LinftyConstant / t := by
  have hrecip_nonneg :
      ∀ n, 0 ≤ unitIntervalCosineReciprocalEigenvalueTerm n := by
    intro n
    by_cases hn : n = 0
    · simp [unitIntervalCosineReciprocalEigenvalueTerm, hn]
    · have hnpos_real : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hlambda_pos : 0 < unitIntervalCosineEigenvalue n := by
        dsimp [unitIntervalCosineEigenvalue]
        exact sq_pos_of_pos (mul_pos hnpos_real Real.pi_pos)
      rw [unitIntervalCosineReciprocalEigenvalueTerm, if_neg hn]
      exact div_nonneg zero_le_one hlambda_pos.le
  have htrace :=
    unitIntervalCosineHeatGradientTrace_le_reciprocalTrace ht hrecip
  have hfactor_nonneg : 0 ≤ 1 / t ^ 2 := by
    positivity
  have hsqrt_factor : Real.sqrt (1 / t ^ 2) = 1 / t := by
    have hsq : 1 / t ^ 2 = (1 / t) ^ 2 := by
      field_simp [ne_of_gt ht]
    rw [hsq, Real.sqrt_sq (by positivity)]
  calc
    Real.sqrt (unitIntervalCosineHeatGradientTrace t)
        ≤ Real.sqrt
            ((1 / t ^ 2) * unitIntervalCosineReciprocalEigenvalueTrace) :=
          Real.sqrt_le_sqrt htrace
    _ = Real.sqrt (1 / t ^ 2) *
          Real.sqrt unitIntervalCosineReciprocalEigenvalueTrace := by
          rw [Real.sqrt_mul hfactor_nonneg]
    _ = unitIntervalCosineHeatGradientL2LinftyConstant / t := by
          rw [hsqrt_factor]
          dsimp [unitIntervalCosineHeatGradientL2LinftyConstant]
          ring

/-- Pointwise derivative series controlled by derivative-evaluation energy
and the coefficient `L²` norm. -/
lemma unitIntervalCosineHeatGradientValue_abs_le_pointEnergy
    {t x : ℝ} {a : ℕ → ℝ}
    (hpoint :
      Summable fun n =>
        (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2)
    (ha : Summable fun n => (a n) ^ 2) :
    |unitIntervalCosineHeatGradientValue t a x| ≤
      Real.sqrt (unitIntervalCosineHeatGradientPointEnergy t x) *
        unitIntervalCosineL2TsumNorm a := by
  simpa [unitIntervalCosineHeatGradientValue,
    unitIntervalCosineHeatGradientPointEnergy, unitIntervalCosineL2TsumNorm]
    using
      real_abs_tsum_mul_le_sqrt_tsum_sq_mul_sqrt_tsum_sq
        (u := fun n => unitIntervalCosineHeatGradientPointWeight t x n)
        (v := a) hpoint ha

/-- Pointwise derivative series controlled by the heat-gradient trace and
the coefficient `L²` norm. -/
lemma unitIntervalCosineHeatGradientValue_abs_le_trace
    {t x : ℝ} {a : ℕ → ℝ}
    (htrace : Summable fun n => unitIntervalCosineHeatGradientMultiplier t n)
    (ha : Summable fun n => (a n) ^ 2) :
    |unitIntervalCosineHeatGradientValue t a x| ≤
      Real.sqrt (unitIntervalCosineHeatGradientTrace t) *
        unitIntervalCosineL2TsumNorm a := by
  have hpoint :
      Summable fun n =>
        (unitIntervalCosineHeatGradientPointWeight t x n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatGradientPointWeight_sq_le_multiplier t x n)
      htrace
  have hbase :=
    unitIntervalCosineHeatGradientValue_abs_le_pointEnergy
      (t := t) (x := x) (a := a) hpoint ha
  have henergy :=
    unitIntervalCosineHeatGradientPointEnergy_le_trace
      (t := t) (x := x) htrace
  exact hbase.trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt henergy) (Real.sqrt_nonneg _))

/-- Coefficient-space pointwise `L² → L∞` smoothing for the spatial
derivative of the interval cosine heat model. -/
theorem unitIntervalCosineHeatGradientValue_L2_Linfty_smoothing
    {t : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    ∀ x : ℝ,
      |unitIntervalCosineHeatGradientValue t a x| ≤
        (unitIntervalCosineHeatGradientL2LinftyConstant / t) *
          unitIntervalCosineL2TsumNorm a := by
  intro x
  have htrace := unitIntervalCosineHeatGradientTrace_summable ht hrecip
  have hbase :=
    unitIntervalCosineHeatGradientValue_abs_le_trace
      (t := t) (x := x) (a := a) htrace ha
  have hsqrt := unitIntervalCosineHeatGradientTrace_sqrt_le_inv ht hrecip
  exact hbase.trans
    (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))

/-- Absolute summability of products from square summability, the summability
part of the real Cauchy-Schwarz estimate. -/
lemma real_summable_abs_mul_of_summable_sq
    {u v : ℕ → ℝ} (hu : Summable fun n => (u n) ^ 2)
    (hv : Summable fun n => (v n) ^ 2) :
    Summable fun n => |u n * v n| := by
  have hdom :
      ∀ n, |u n * v n| ≤
        (1 / 2) * (u n) ^ 2 + (1 / 2) * (v n) ^ 2 := by
    intro n
    rw [abs_mul]
    have hsq := sq_nonneg (|u n| - |v n|)
    nlinarith [sq_abs (u n), sq_abs (v n), hsq]
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _)
    hdom ((hu.mul_left (1 / 2)).add (hv.mul_left (1 / 2)))

/-- Summability of products from square summability. -/
lemma real_summable_mul_of_summable_sq
    {u v : ℕ → ℝ} (hu : Summable fun n => (u n) ^ 2)
    (hv : Summable fun n => (v n) ^ 2) :
    Summable fun n => u n * v n :=
  Summable.of_abs (real_summable_abs_mul_of_summable_sq hu hv)

/-- Term-by-term differentiation of the cosine heat series for `L²`
coefficient data.  The derivative majorant is discharged from the
heat-gradient trace and the coefficient `L²` norm. -/
theorem unitIntervalCosineHeatValue_hasDerivAt_of_l2
    {t x : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    HasDerivAt (fun z : ℝ => unitIntervalCosineHeatValue t a z)
      (unitIntervalCosineHeatGradientValue t a x) x := by
  let m : ℕ → ℝ := fun n => unitIntervalCosineHeatGradientMultiplier t n
  let u : ℕ → ℝ := fun n => Real.sqrt (m n) * |a n|
  have hm_nonneg : ∀ n, 0 ≤ m n := by
    intro n
    dsimp [m, unitIntervalCosineHeatGradientMultiplier,
      unitIntervalCosineEigenvalue]
    positivity
  have hm : Summable m := by
    simpa [m] using unitIntervalCosineHeatGradientTrace_summable ht hrecip
  have hsqrt_sq : Summable fun n => (Real.sqrt (m n)) ^ 2 := by
    refine hm.congr ?_
    intro n
    exact (Real.sq_sqrt (hm_nonneg n)).symm
  have hu_abs :
      Summable fun n => |Real.sqrt (m n) * a n| :=
    real_summable_abs_mul_of_summable_sq hsqrt_sq ha
  have hu : Summable u := by
    simpa [u, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hu_abs
  have hbound :
      ∀ n y,
        ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖ ≤ u n := by
    intro n y
    have hsq :=
      unitIntervalCosineHeatGradientPointWeight_sq_le_multiplier t y n
    have hw_abs :
        |unitIntervalCosineHeatGradientPointWeight t y n| ≤
          Real.sqrt (m n) := by
      simpa [m] using Real.abs_le_sqrt hsq
    calc
      ‖unitIntervalCosineHeatGradientPointWeight t y n * a n‖
          = |unitIntervalCosineHeatGradientPointWeight t y n| * |a n| := by
            rw [Real.norm_eq_abs, abs_mul]
      _ ≤ Real.sqrt (m n) * |a n| :=
            mul_le_mul_of_nonneg_right hw_abs (abs_nonneg _)
      _ = u n := rfl
  have htrace :=
    unitIntervalCosineHeatTrace_summable ht hrecip
  have hpoint₀ :
      Summable fun n => (unitIntervalCosineHeatPointWeight t 0 n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => unitIntervalCosineHeatPointWeight_sq_le_traceTerm t 0 n)
      htrace
  have h₀ :
      Summable fun n => unitIntervalCosineHeatPointWeight t 0 n * a n :=
    real_summable_mul_of_summable_sq hpoint₀ ha
  exact unitIntervalCosineHeatValue_hasDerivAt_of_summable_bound
    (t := t) (x := x) (x₀ := 0) hu hbound h₀

/-- Derivative identity for the cosine heat series with `L²` coefficient data. -/
theorem unitIntervalCosineHeatValue_deriv_of_l2
    {t x : ℝ} (ht : 0 < t)
    (hrecip : Summable unitIntervalCosineReciprocalEigenvalueTerm)
    {a : ℕ → ℝ} (ha : Summable fun n => (a n) ^ 2) :
    deriv (fun z : ℝ => unitIntervalCosineHeatValue t a z) x =
      unitIntervalCosineHeatGradientValue t a x :=
  (unitIntervalCosineHeatValue_hasDerivAt_of_l2
    (t := t) (x := x) ht hrecip ha).deriv

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
