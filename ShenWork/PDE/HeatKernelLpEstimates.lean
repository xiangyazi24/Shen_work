/-
  ShenWork/PDE/HeatKernelLpEstimates.lean

  Whole-line L^p estimates for the one-dimensional heat kernel.
-/
import ShenWork.PDE.HeatSemigroup
import ShenWork.PDE.IntervalDomain
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
-- This proof combines Hölder, the interval-kernel `L^r` bound, and `LpSeminorm`.
/-- Interval Neumann heat-helper smoothing from `L^p([0,L])` to `L∞([0,L])`.
Here `r` is the Hölder conjugate of `p`, so the coefficient has the standard
one-dimensional heat singularity `t^{-1/(2p)}`. -/
theorem intervalHeatSemigroup_Lp_Lq_bound
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
