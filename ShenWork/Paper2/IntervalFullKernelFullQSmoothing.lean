import ShenWork.Paper2.IntervalFullKernelLpContraction
import ShenWork.Paper2.IntervalDomainRestartedLpLinf

/-!
# Full-exponent estimates for the genuine Neumann heat kernel on `[0,1]`

This file upgrades the bounded-input Markov contraction to arbitrary finite
`L^p` inputs, `1 < p < infinity`, and combines it with the explicit
periodised-Gaussian row bound.  The resulting finite `L^p -> L^q` estimate is
for the genuine full Neumann kernel, not the zeroth-reflection helper.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace ShenWork.Paper2.IntervalFullKernelFullQSmoothing

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2.IntervalNegativePartWeakEnergy
open ShenWork.Paper2.IntervalDomainRestartedLpLinf

/-! ## Measurability and integrability of the full operator -/

/-- Joint measurability of a positive-time full Neumann kernel slice. -/
theorem intervalNeumannFullKernel_joint_measurable
    {t : ℝ} (ht : 0 < t) :
    Measurable (fun z : ℝ × ℝ => intervalNeumannFullKernel t z.1 z.2) := by
  let g : ℤ → ℝ × ℝ → ℝ := fun k z =>
    heatKernel t (z.1 - z.2 + 2 * (k : ℝ)) +
      heatKernel t (z.1 + z.2 + 2 * (k : ℝ))
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    dsimp [g]
    unfold heatKernel
    fun_prop
  have hg_sum : ∀ z, Summable (fun k : ℤ => g k z) := by
    intro z
    exact (latticeGaussianSummable ht (z.1 - z.2)).add
      (latticeGaussianSummable ht (z.1 + z.2))
  have hmeas := measurable_tsum_int_of_summable hg_meas hg_sum
  simpa [intervalNeumannFullKernel, g] using hmeas

/-- The full Neumann heat operator is a.e.-strongly measurable on the unit
interval for every a.e.-strongly measurable input. -/
theorem intervalFullSemigroupOperator_aestronglyMeasurable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (intervalMeasure 1)) :
    AEStronglyMeasurable (intervalFullSemigroupOperator t f)
      (intervalMeasure 1) := by
  let F : ℝ × ℝ → ℝ := fun z =>
    intervalNeumannFullKernel t z.1 z.2 * f z.2
  have hF : AEStronglyMeasurable F
      ((intervalMeasure 1).prod (intervalMeasure 1)) :=
    (intervalNeumannFullKernel_joint_measurable ht).aestronglyMeasurable.mul
      hf.comp_snd
  have hI := hF.integral_prod_right'
  simpa [F, intervalFullSemigroupOperator] using hI

/-- An integrable input is sent to an integrable output by the full Neumann
heat operator.  This is the absolute-integrability part of the Markov/Fubini
argument, exposed separately for reuse below. -/
theorem intervalFullSemigroupOperator_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) :
    Integrable (intervalFullSemigroupOperator t f) (intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let F : ℝ × ℝ → ℝ := fun z =>
    intervalNeumannFullKernel t z.1 z.2 * f z.2
  have hF_meas : AEStronglyMeasurable F (μ.prod μ) := by
    exact (intervalNeumannFullKernel_joint_measurable ht).aestronglyMeasurable.mul
      hf.aestronglyMeasurable.comp_snd
  have hF_int : Integrable F (μ.prod μ) := by
    refine (MeasureTheory.integrable_prod_iff' hF_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun y => ?_
      have hK : Integrable (fun x => intervalNeumannFullKernel t x y) μ := by
        have hrow := intervalNeumannFullKernel_integrable ht y
        exact hrow.congr (Eventually.of_forall fun x =>
          intervalNeumannFullKernel_symm ht y x)
      exact hK.mul_const (f y)
    · have hinner :
          (fun y => ∫ x, ‖F (x, y)‖ ∂μ) = fun y => |f y| := by
        funext y
        calc
          (∫ x, ‖F (x, y)‖ ∂μ) =
              (∫ x, intervalNeumannFullKernel t x y ∂μ) * |f y| := by
            rw [← integral_mul_const]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              simp only [F, Real.norm_eq_abs, abs_mul]
              rw [abs_of_nonneg (intervalNeumannFullKernel_nonneg ht x y)]
          _ = 1 * |f y| := by
            rw [show (∫ x, intervalNeumannFullKernel t x y ∂μ) = 1 by
              calc
                (∫ x, intervalNeumannFullKernel t x y ∂μ) =
                    ∫ x, intervalNeumannFullKernel t y x ∂μ := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun x =>
                    intervalNeumannFullKernel_symm ht x y
                _ = 1 :=
                  intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht y]
          _ = |f y| := one_mul _
      rw [hinner]
      exact hf.norm
  simpa [F, μ, intervalFullSemigroupOperator] using hF_int.integral_prod_left

/-! ## Endpoint and finite-exponent Markov contraction -/

/-- `L^1` contraction of the genuine full Neumann heat operator. -/
theorem intervalFullSemigroupOperator_L1_contraction
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf : Integrable f (intervalMeasure 1)) :
    ∫ x, ‖intervalFullSemigroupOperator t f x‖ ∂(intervalMeasure 1) ≤
      ∫ y, ‖f y‖ ∂(intervalMeasure 1) := by
  let g : ℝ → ℝ := fun y => ‖f y‖
  have hg : Integrable g (intervalMeasure 1) := hf.norm
  have hSg : Integrable (intervalFullSemigroupOperator t g)
      (intervalMeasure 1) := intervalFullSemigroupOperator_integrable ht hg
  have hpoint : ∀ x,
      ‖intervalFullSemigroupOperator t f x‖ ≤
        intervalFullSemigroupOperator t g x := by
    intro x
    unfold intervalFullSemigroupOperator
    calc
      ‖∫ y, intervalNeumannFullKernel t x y * f y ∂(intervalMeasure 1)‖ ≤
          ∫ y, ‖intervalNeumannFullKernel t x y * f y‖
            ∂(intervalMeasure 1) := norm_integral_le_integral_norm _
      _ = ∫ y, intervalNeumannFullKernel t x y * ‖f y‖
            ∂(intervalMeasure 1) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change ‖intervalNeumannFullKernel t x y * f y‖ =
            intervalNeumannFullKernel t x y * ‖f y‖
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (intervalNeumannFullKernel_nonneg ht x y)]
      _ = ∫ y, intervalNeumannFullKernel t x y * g y
            ∂(intervalMeasure 1) := rfl
  calc
    ∫ x, ‖intervalFullSemigroupOperator t f x‖ ∂(intervalMeasure 1) ≤
        ∫ x, intervalFullSemigroupOperator t g x
          ∂(intervalMeasure 1) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
      · exact hSg
      · exact Filter.Eventually.of_forall hpoint
    _ = ∫ y, g y ∂(intervalMeasure 1) :=
      intervalFullSemigroupOperator_integral_eq ht
        hg.aestronglyMeasurable hg
    _ = ∫ y, ‖f y‖ ∂(intervalMeasure 1) := rfl

/-- Pointwise Jensen/Hölder estimate for an arbitrary finite `L^p` input.
Unlike the earlier bounded-input version, no pointwise bound on `f` is used. -/
theorem intervalFullSemigroupOperator_norm_rpow_le
    {t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) (x : ℝ) :
    ‖intervalFullSemigroupOperator t f x‖ ^ p ≤
      intervalFullSemigroupOperator t (fun y => ‖f y‖ ^ p) x := by
  let μ := intervalMeasure 1
  let K : ℝ → ℝ := fun y => intervalNeumannFullKernel t x y
  let a : ℝ → ℝ := fun y => K y ^ (1 / r)
  let b : ℝ → ℝ := fun y => K y ^ (1 / p) * ‖f y‖
  let B : ℝ := ∫ y, K y * ‖f y‖ ^ p ∂μ
  have hK_nonneg : ∀ y, 0 ≤ K y := fun y =>
    intervalNeumannFullKernel_nonneg ht x y
  have hK_cont : ContinuousOn K (Icc (0 : ℝ) 1) := by
    exact continuousOn_intervalNeumannFullKernel_snd ht x
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hK_cont
  have hM_nonneg : 0 ≤ M :=
    (norm_nonneg (K 0)).trans (hM 0 (by norm_num))
  have ha_meas : AEStronglyMeasurable a μ := by
    exact (hK_cont.rpow_const
      (fun _ _ => Or.inr hrp.one_div_nonneg)).aestronglyMeasurable
        measurableSet_Icc
  have hb_meas : AEStronglyMeasurable b μ := by
    have hKp : AEStronglyMeasurable (fun y => K y ^ (1 / p)) μ :=
      (hK_cont.rpow_const
        (fun _ _ => Or.inr hrp.symm.one_div_nonneg)).aestronglyMeasurable
          measurableSet_Icc
    exact hKp.mul hf.aestronglyMeasurable.norm
  have ha_mem : MemLp a (ENNReal.ofReal r) μ := by
    apply MemLp.of_bound ha_meas (M ^ (1 / r))
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    exact Filter.Eventually.of_forall fun y hy => by
      dsimp [a]
      rw [abs_of_nonneg (Real.rpow_nonneg (hK_nonneg y) _)]
      exact Real.rpow_le_rpow (hK_nonneg y)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg (hK_nonneg y)] using
          hM y hy) hrp.one_div_nonneg
  have hb_mem : MemLp b (ENNReal.ofReal p) μ := by
    apply MemLp.of_le_mul (g := f) (c := M ^ (1 / p)) hf hb_meas
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    exact Filter.Eventually.of_forall fun y hy => by
      dsimp [b]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hK_nonneg y) _),
        abs_abs]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hK_nonneg y)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (hK_nonneg y)] using
            hM y hy) hrp.symm.one_div_nonneg)
        (abs_nonneg _)
  have ha_nonneg : 0 ≤ᵐ[μ] a :=
    Filter.Eventually.of_forall fun y => Real.rpow_nonneg (hK_nonneg y) _
  have hb_nonneg : 0 ≤ᵐ[μ] b :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg (hK_nonneg y) _) (norm_nonneg _)
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := r) (q := p) hrp
      ha_nonneg hb_nonneg ha_mem hb_mem
  have hsum : 1 / r + 1 / p = 1 := by
    simpa [one_div] using hrp.inv_add_inv_eq_one
  have hab : (∫ y, a y * b y ∂μ) = ∫ y, K y * ‖f y‖ ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a, b]
      calc
        K y ^ (1 / r) * (K y ^ (1 / p) * ‖f y‖) =
            (K y ^ (1 / r) * K y ^ (1 / p)) * ‖f y‖ := by ring
        _ = K y ^ (1 / r + 1 / p) * ‖f y‖ := by
          rw [Real.rpow_add_of_nonneg (hK_nonneg y)
            hrp.one_div_nonneg hrp.symm.one_div_nonneg]
        _ = K y * ‖f y‖ := by rw [hsum, Real.rpow_one]
  have hapow : (∫ y, a y ^ r ∂μ) = ∫ y, K y ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a]
      rw [one_div, Real.rpow_inv_rpow (hK_nonneg y) hrp.ne_zero]
  have hbpow : (∫ y, b y ^ p ∂μ) = B := by
    dsimp [B]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [b]
      rw [Real.mul_rpow (Real.rpow_nonneg (hK_nonneg y) _)
        (abs_nonneg (f y)), one_div,
        Real.rpow_inv_rpow (hK_nonneg y) hrp.symm.ne_zero]
  rw [hab, hapow, hbpow] at hholder
  have hmass : (∫ y, K y ∂μ) = 1 := by
    exact intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  have hB_nonneg : 0 ≤ B := integral_nonneg fun y =>
    mul_nonneg (hK_nonneg y) (Real.rpow_nonneg (norm_nonneg _) p)
  have hkernel : ∫ y, K y * ‖f y‖ ∂μ ≤ B ^ (1 / p) := by
    calc
      ∫ y, K y * ‖f y‖ ∂μ ≤
          (∫ y, K y ∂μ) ^ (1 / r) * B ^ (1 / p) := hholder
      _ = B ^ (1 / p) := by rw [hmass, Real.one_rpow, one_mul]
  have hkernel_nonneg : 0 ≤ ∫ y, K y * ‖f y‖ ∂μ :=
    integral_nonneg fun y => mul_nonneg (hK_nonneg y) (norm_nonneg _)
  have hoperator : ‖intervalFullSemigroupOperator t f x‖ ≤
      ∫ y, K y * ‖f y‖ ∂μ := by
    unfold intervalFullSemigroupOperator
    calc
      ‖∫ y, intervalNeumannFullKernel t x y * f y ∂μ‖ ≤
          ∫ y, ‖intervalNeumannFullKernel t x y * f y‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ y, K y * ‖f y‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change ‖intervalNeumannFullKernel t x y * f y‖ =
            K y * ‖f y‖
          rw [norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (hK_nonneg y)]
  have hraised := Real.rpow_le_rpow (norm_nonneg _)
    (hoperator.trans hkernel) hrp.symm.nonneg
  calc
    ‖intervalFullSemigroupOperator t f x‖ ^ p ≤
        (B ^ (1 / p)) ^ p := hraised
    _ = B := by
      rw [one_div, Real.rpow_inv_rpow hB_nonneg hrp.symm.ne_zero]
    _ = intervalFullSemigroupOperator t (fun y => ‖f y‖ ^ p) x := rfl

/-- Integral `L^p` contraction for every finite exponent `1 < p < infinity`. -/
theorem intervalFullSemigroupOperator_Lp_contraction_integral
    {t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    ∫ x, ‖intervalFullSemigroupOperator t f x‖ ^ p
        ∂(intervalMeasure 1) ≤
      ∫ y, ‖f y‖ ^ p ∂(intervalMeasure 1) := by
  let g : ℝ → ℝ := fun y => ‖f y‖ ^ p
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hg_int : Integrable g (intervalMeasure 1) := by
    simpa [g, ENNReal.toReal_ofReal hrp.symm.nonneg] using
      hf.integrable_norm_rpow hp_zero hp_top
  have hSg_int : Integrable (intervalFullSemigroupOperator t g)
      (intervalMeasure 1) := intervalFullSemigroupOperator_integrable ht hg_int
  calc
    ∫ x, ‖intervalFullSemigroupOperator t f x‖ ^ p
        ∂(intervalMeasure 1) ≤
        ∫ x, intervalFullSemigroupOperator t g x
          ∂(intervalMeasure 1) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (norm_nonneg _) p
      · exact hSg_int
      · exact Filter.Eventually.of_forall fun x =>
          intervalFullSemigroupOperator_norm_rpow_le ht hrp hf x
    _ = ∫ y, g y ∂(intervalMeasure 1) :=
      intervalFullSemigroupOperator_integral_eq ht
        hg_int.aestronglyMeasurable hg_int
    _ = ∫ y, ‖f y‖ ^ p ∂(intervalMeasure 1) := rfl

/-- Real-valued `lpNorm` contraction for arbitrary finite `L^p` input. -/
theorem intervalFullSemigroupOperator_lpNorm_le
    {t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm (intervalFullSemigroupOperator t f) (ENNReal.ofReal p)
        (intervalMeasure 1) ≤
      lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hS_meas := intervalFullSemigroupOperator_aestronglyMeasurable
    ht hf.aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top hS_meas,
    lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top
      hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hrp.symm.nonneg]
  exact Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p)
    (intervalFullSemigroupOperator_Lp_contraction_integral ht hrp hf)
    (by simpa [one_div] using hrp.symm.one_div_nonneg)

/-! ## Explicit short-time `L^p -> L^q` smoothing -/

/-- Pointwise `L^p -> L^infinity` estimate obtained from the explicit
periodised-Gaussian row bound. -/
theorem intervalFullSemigroupOperator_Lp_Linfty_pointwise_short
    {t p r : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) (x : ℝ) :
    ‖intervalFullSemigroupOperator t f x‖ ≤
      (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hlp :
      lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) =
        (∫ y, ‖f y‖ ^ p ∂(intervalMeasure 1)) ^ (1 / p) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  rw [hlp]
  simpa [Real.norm_eq_abs] using
    intervalFullSemigroupOperator_abs_le_Lp_short
      ht ht1 hrp hf x

/-- Real `lpNorm` form of the short-time `L^p -> L^infinity` estimate. -/
theorem intervalFullSemigroupOperator_Lp_Linfty_short
    {t p r : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm (intervalFullSemigroupOperator t f) ∞ (intervalMeasure 1) ≤
      (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  let C : ℝ :=
    (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
      lpNorm f (ENNReal.ofReal p) (intervalMeasure 1)
  have hS_meas := intervalFullSemigroupOperator_aestronglyMeasurable
    ht hf.aestronglyMeasurable
  have hpoint : ∀ x, ‖intervalFullSemigroupOperator t f x‖ ≤ C := by
    intro x
    exact intervalFullSemigroupOperator_Lp_Linfty_pointwise_short
      ht ht1 hrp hf x
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (Real.rpow_nonneg
        (mul_nonneg fullHeatShortConstant_nonneg
          (Real.rpow_nonneg ht.le _)) _)
      lpNorm_nonneg
  have hess :
      eLpNormEssSup (intervalFullSemigroupOperator t f) (intervalMeasure 1) ≤
        ENNReal.ofReal C :=
    eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hpoint)
  calc
    lpNorm (intervalFullSemigroupOperator t f) ∞ (intervalMeasure 1) =
        (eLpNorm (intervalFullSemigroupOperator t f) ∞
          (intervalMeasure 1)).toReal := (toReal_eLpNorm hS_meas).symm
    _ = (eLpNormEssSup (intervalFullSemigroupOperator t f)
          (intervalMeasure 1)).toReal := by rw [eLpNorm_exponent_top]
    _ ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = C := ENNReal.toReal_ofReal hC
    _ = (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := rfl

set_option maxHeartbeats 0 in
/-- Full-kernel finite `L^p -> L^q` smoothing for `1 < p ≤ q < infinity`.
The exponent of the explicit kernel factor is exactly `1/p - 1/q`. -/
theorem intervalFullSemigroupOperator_Lp_Lq_short
    {t p q r : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p) (hpq : p ≤ q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm (intervalFullSemigroupOperator t f) (ENNReal.ofReal q)
        (intervalMeasure 1) ≤
      (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^
          (1 / p - 1 / q) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let T : ℝ → ℝ := intervalFullSemigroupOperator t f
  let A : ℝ := fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))
  let Fp : ℝ := lpNorm f (ENNReal.ofReal p) μ
  let M : ℝ := A ^ (1 / p) * Fp
  have hp_pos : 0 < p := hrp.symm.pos
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  have hq_ne_zero : q ≠ 0 := hq_pos.ne'
  have hq_minus_nonneg : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hp_div_q_le_one : p / q ≤ 1 := by
    rw [div_le_one hq_pos]
    exact hpq
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg fullHeatShortConstant_nonneg
      (Real.rpow_nonneg ht.le _)
  have hFp_nonneg : 0 ≤ Fp := by
    dsimp [Fp]
    exact lpNorm_nonneg
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.rpow_nonneg hA_nonneg _) hFp_nonneg
  have hp_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hp_pos
  have hp_top : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hq_zero : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hq_pos
  have hq_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hT_meas : AEStronglyMeasurable T μ := by
    exact intervalFullSemigroupOperator_aestronglyMeasurable
      ht hf.aestronglyMeasurable
  have hpoint : ∀ x, ‖T x‖ ≤ M := by
    intro x
    exact intervalFullSemigroupOperator_Lp_Linfty_pointwise_short
      ht ht1 hrp hf x
  have hT_mem_p : MemLp T (ENNReal.ofReal p) μ :=
    MemLp.of_bound hT_meas M (Filter.Eventually.of_forall hpoint)
  have hTp_int : Integrable (fun x => ‖T x‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hrp.symm.nonneg] using
      hT_mem_p.integrable_norm_rpow hp_zero hp_top
  have hright_int : Integrable (fun x => M ^ (q - p) * ‖T x‖ ^ p) μ :=
    hTp_int.const_mul (M ^ (q - p))
  have hpow_point : ∀ x, ‖T x‖ ^ q ≤ M ^ (q - p) * ‖T x‖ ^ p := by
    intro x
    have hx : 0 ≤ ‖T x‖ := norm_nonneg _
    have hsplit : ‖T x‖ ^ q = ‖T x‖ ^ (q - p) * ‖T x‖ ^ p := by
      calc
        ‖T x‖ ^ q = ‖T x‖ ^ ((q - p) + p) := by ring_nf
        _ = ‖T x‖ ^ (q - p) * ‖T x‖ ^ p :=
          Real.rpow_add_of_nonneg hx hq_minus_nonneg hrp.symm.nonneg
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx (hpoint x) hq_minus_nonneg)
      (Real.rpow_nonneg hx p)
  have hq_integral_le :
      ∫ x, ‖T x‖ ^ q ∂μ ≤
        M ^ (q - p) * ∫ x, ‖f x‖ ^ p ∂μ := by
    calc
      ∫ x, ‖T x‖ ^ q ∂μ ≤
          ∫ x, M ^ (q - p) * ‖T x‖ ^ p ∂μ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (norm_nonneg _) q
        · exact hright_int
        · exact Filter.Eventually.of_forall hpow_point
      _ = M ^ (q - p) * ∫ x, ‖T x‖ ^ p ∂μ := by
        rw [integral_const_mul]
      _ ≤ M ^ (q - p) * ∫ x, ‖f x‖ ^ p ∂μ := by
        exact mul_le_mul_of_nonneg_left
          (intervalFullSemigroupOperator_Lp_contraction_integral ht hrp hf)
          (Real.rpow_nonneg hM_nonneg _)
  let If : ℝ := ∫ x, ‖f x‖ ^ p ∂μ
  have hIf_nonneg : 0 ≤ If := by
    exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) p
  have hFp_eq : Fp = If ^ (1 / p) := by
    dsimp [Fp, If, μ]
    rw [lpNorm_eq_integral_norm_rpow_toReal hp_zero hp_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hrp.symm.nonneg]
    simp [one_div]
  have hFp_pow : Fp ^ p = If := by
    rw [hFp_eq, one_div,
      Real.rpow_inv_rpow hIf_nonneg hrp.symm.ne_zero]
  have hroot_le :
      (∫ x, ‖T x‖ ^ q ∂μ) ^ (1 / q) ≤
        (M ^ (q - p) * If) ^ (1 / q) := by
    apply Real.rpow_le_rpow
    · exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) q
    · simpa [If] using hq_integral_le
    · exact one_div_nonneg.mpr hq_pos.le
  have hFp_add : Fp ^ (q - p) * Fp ^ p = Fp ^ q := by
    calc
      Fp ^ (q - p) * Fp ^ p = Fp ^ ((q - p) + p) := by
        rw [Real.rpow_add_of_nonneg hFp_nonneg hq_minus_nonneg
          hrp.symm.nonneg]
      _ = Fp ^ q := by ring_nf
  have hA_exp : (1 / p) * (q - p) * (1 / q) = 1 / p - 1 / q := by
    field_simp [hrp.symm.ne_zero, hq_ne_zero]
  have hroot_eq :
      (M ^ (q - p) * If) ^ (1 / q) =
        A ^ (1 / p - 1 / q) * Fp := by
    calc
      (M ^ (q - p) * If) ^ (1 / q) =
          ((A ^ (1 / p) * Fp) ^ (q - p) * Fp ^ p) ^ (1 / q) := by
        rw [hFp_pow]
      _ = ((A ^ (1 / p)) ^ (q - p) * Fp ^ (q - p) * Fp ^ p) ^
          (1 / q) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA_nonneg _) hFp_nonneg]
      _ = ((A ^ (1 / p)) ^ (q - p) * Fp ^ q) ^ (1 / q) := by
        rw [← hFp_add]
        ring_nf
      _ = ((A ^ (1 / p)) ^ (q - p)) ^ (1 / q) *
          (Fp ^ q) ^ (1 / q) := by
        rw [Real.mul_rpow
          (Real.rpow_nonneg (Real.rpow_nonneg hA_nonneg _) _)
          (Real.rpow_nonneg hFp_nonneg q)]
      _ = A ^ ((1 / p) * (q - p) * (1 / q)) * Fp := by
        rw [← Real.rpow_mul hA_nonneg (1 / p) (q - p),
          ← Real.rpow_mul hA_nonneg ((1 / p) * (q - p)) (1 / q)]
        rw [show (Fp ^ q) ^ (1 / q) = Fp by
          rw [one_div, ← Real.rpow_mul hFp_nonneg q q⁻¹,
            mul_inv_cancel₀ hq_ne_zero, Real.rpow_one]]
      _ = A ^ (1 / p - 1 / q) * Fp := by rw [hA_exp]
  calc
    lpNorm T (ENNReal.ofReal q) μ =
        (∫ x, ‖T x‖ ^ q ∂μ) ^ (1 / q) := by
      rw [lpNorm_eq_integral_norm_rpow_toReal hq_zero hq_top hT_meas,
        ENNReal.toReal_ofReal hq_pos.le]
      simp [one_div]
    _ ≤ (M ^ (q - p) * If) ^ (1 / q) := hroot_le
    _ = A ^ (1 / p - 1 / q) * Fp := hroot_eq
    _ = (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^
          (1 / p - 1 / q) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := rfl

/-! ## Positive spectral shift -/

/-- The physical full Neumann heat operator with a positive scalar shift. -/
def intervalShiftedFullHeatOperator
    (omega t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(omega * t)) * intervalFullSemigroupOperator t f x

/-- Exact scalar-factor identity for shifted full heat flow. -/
theorem intervalShiftedFullHeatOperator_lpNorm
    (omega t p : ℝ) (f : ℝ → ℝ) :
    lpNorm (intervalShiftedFullHeatOperator omega t f)
        (ENNReal.ofReal p) (intervalMeasure 1) =
      Real.exp (-(omega * t)) *
        lpNorm (intervalFullSemigroupOperator t f)
          (ENNReal.ofReal p) (intervalMeasure 1) := by
  have h := lpNorm_const_smul (p := ENNReal.ofReal p)
    (Real.exp (-(omega * t))) (intervalFullSemigroupOperator t f)
      (intervalMeasure 1)
  simpa [intervalShiftedFullHeatOperator, Pi.smul_apply, smul_eq_mul,
    Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h

/-- Shifted full-kernel short-time `L^p -> L^q` smoothing. -/
theorem intervalShiftedFullHeatOperator_Lp_Lq_short
    {omega t p q r : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p) (hpq : p ≤ q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm (intervalShiftedFullHeatOperator omega t f)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^
          (1 / p - 1 / q) * Real.exp (-(omega * t)) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  rw [intervalShiftedFullHeatOperator_lpNorm]
  have hsmooth := intervalFullSemigroupOperator_Lp_Lq_short
    ht ht1 hrp hpq hf
  calc
    Real.exp (-(omega * t)) *
        lpNorm (intervalFullSemigroupOperator t f) (ENNReal.ofReal q)
          (intervalMeasure 1) ≤
      Real.exp (-(omega * t)) *
        ((fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^
            (1 / p - 1 / q) *
          lpNorm f (ENNReal.ofReal p) (intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_left hsmooth (Real.exp_nonneg _)
    _ = (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^
          (1 / p - 1 / q) * Real.exp (-(omega * t)) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by ring

/-- Shifted same-exponent contraction with its exact spectral-gap factor. -/
theorem intervalShiftedFullHeatOperator_lpNorm_le
    {omega t p r : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    lpNorm (intervalShiftedFullHeatOperator omega t f)
        (ENNReal.ofReal p) (intervalMeasure 1) ≤
      Real.exp (-(omega * t)) *
        lpNorm f (ENNReal.ofReal p) (intervalMeasure 1) := by
  rw [intervalShiftedFullHeatOperator_lpNorm]
  exact mul_le_mul_of_nonneg_left
    (intervalFullSemigroupOperator_lpNorm_le ht hrp hf)
    (Real.exp_nonneg _)

/-- Full-`q` `sigma = 0` branch of Paper 2 Lemma 2.1 for the honest physical
shifted Neumann semigroup.  The domain hypothesis is explicit, and the
constant is uniform in `q`. -/
theorem Lemma_2_1_interval_full_q_sigma_zero
    {omega delta : ℝ} (_hdelta : 0 < delta) (hdeltaomega : delta < omega) :
    ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ f : ℝ → ℝ,
      MemLp f (ENNReal.ofReal q) (intervalMeasure 1) →
        lpNorm (intervalShiftedFullHeatOperator omega t f)
            (ENNReal.ofReal q) (intervalMeasure 1) ≤
          C * t ^ (-(0 : ℝ)) * Real.exp (-(delta * t)) *
            lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro q hq t ht f hf
  let r := Real.conjExponent q
  have hrq : r.HolderConjugate q :=
    (Real.HolderConjugate.conjExponent hq).symm
  have hbase := intervalShiftedFullHeatOperator_lpNorm_le
    (omega := omega) ht hrq hf
  have hexp : Real.exp (-(omega * t)) ≤ Real.exp (-(delta * t)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right hdeltaomega.le ht.le)
  calc
    lpNorm (intervalShiftedFullHeatOperator omega t f)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      Real.exp (-(omega * t)) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := hbase
    _ ≤ Real.exp (-(delta * t)) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) :=
      mul_le_mul_of_nonneg_right hexp lpNorm_nonneg
    _ = (1 : ℝ) * t ^ (-(0 : ℝ)) * Real.exp (-(delta * t)) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by simp

#print axioms intervalNeumannFullKernel_joint_measurable
#print axioms intervalFullSemigroupOperator_aestronglyMeasurable
#print axioms intervalFullSemigroupOperator_integrable
#print axioms intervalFullSemigroupOperator_L1_contraction
#print axioms intervalFullSemigroupOperator_norm_rpow_le
#print axioms intervalFullSemigroupOperator_Lp_contraction_integral
#print axioms intervalFullSemigroupOperator_lpNorm_le
#print axioms intervalFullSemigroupOperator_Lp_Linfty_pointwise_short
#print axioms intervalFullSemigroupOperator_Lp_Linfty_short
#print axioms intervalFullSemigroupOperator_Lp_Lq_short
#print axioms intervalShiftedFullHeatOperator_lpNorm
#print axioms intervalShiftedFullHeatOperator_Lp_Lq_short
#print axioms intervalShiftedFullHeatOperator_lpNorm_le
#print axioms Lemma_2_1_interval_full_q_sigma_zero

end ShenWork.Paper2.IntervalFullKernelFullQSmoothing
