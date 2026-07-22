import ShenWork.Paper2.IntervalFullKernelFullQSmoothing
import ShenWork.Paper2.IntervalConjugateKernelCtheta
import ShenWork.Paper2.ChemMildInterchange

/-!
# Same-exponent generator bound for the full Neumann heat kernel

This file supplies the integer-order input used by fractional subordination.
The kernel is the negative second spatial derivative of the full Neumann heat
kernel, so it represents `(-Delta_N) exp(t Delta_N)`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace ShenWork.Paper2.IntervalFullKernelFullQGenerator

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2.IntervalNegativePartWeakEnergy
open ShenWork.Paper2.IntervalDomainRestartedLpLinf

/-- Kernel of `(-Delta_N) exp(t Delta_N)`. -/
def intervalFullGeneratorKernel (t x y : ℝ) : ℝ :=
  -deriv (fun z : ℝ => deriv
    (fun w : ℝ => intervalNeumannFullKernel t w y) z) x

/-- Physical integral operator associated with `(-Delta_N) exp(t Delta_N)`. -/
def intervalFullGeneratorHeatOperator
    (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, intervalFullGeneratorKernel t x y * f y ∂(intervalMeasure 1)

/-- The whole-line heat Hessian is even. -/
theorem secondDeriv_heatKernel_neg {t : ℝ} (ht : 0 < t) (z : ℝ) :
    deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) (-z) =
      deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u) z := by
  rw [deriv_deriv_heatKernel ht, deriv_deriv_heatKernel ht,
    heatKernel_neg]
  ring_nf

/-- Symmetry of the pure Neumann Hessian. -/
theorem secondDeriv_intervalNeumannFullKernel_symm
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    deriv (fun z : ℝ => deriv
        (fun w : ℝ => intervalNeumannFullKernel t w y) z) x =
      deriv (fun z : ℝ => deriv
        (fun w : ℝ => intervalNeumannFullKernel t w x) z) y := by
  rw [secondDeriv_intervalNeumannFullKernel_eq_components ht,
    secondDeriv_intervalNeumannFullKernel_eq_components ht]
  have hdirect : intervalDirectHeatHessComponent t x y =
      intervalDirectHeatHessComponent t y x := by
    unfold intervalDirectHeatHessComponent
    rw [← (Equiv.neg ℤ).tsum_eq
      (fun k : ℤ =>
        deriv (fun u : ℝ => deriv (fun z : ℝ => heatKernel t z) u)
          (y - x + 2 * (k : ℝ)))]
    refine tsum_congr (fun k => ?_)
    rw [← secondDeriv_heatKernel_neg ht
      (y - x + 2 * ((Equiv.neg ℤ k : ℤ) : ℝ))]
    congr 1
    simp only [Equiv.neg_apply]
    push_cast
    ring
  have hreflected : intervalReflectedHeatHessComponent t x y =
      intervalReflectedHeatHessComponent t y x := by
    unfold intervalReflectedHeatHessComponent
    refine tsum_congr (fun k => ?_)
    congr 1
    ring
  rw [hdirect, hreflected]

theorem intervalFullGeneratorKernel_symm
    {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    intervalFullGeneratorKernel t x y =
      intervalFullGeneratorKernel t y x := by
  simp only [intervalFullGeneratorKernel]
  rw [secondDeriv_intervalNeumannFullKernel_symm ht]

/-- Joint measurability of the fixed-time generator kernel. -/
theorem intervalFullGeneratorKernel_joint_measurable
    (t : ℝ) :
    Measurable (fun z : ℝ × ℝ => intervalFullGeneratorKernel t z.1 z.2) := by
  let g₁ : ℤ → ℝ × ℝ → ℝ := fun k z =>
    deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
      (z.1 - z.2 + 2 * (k : ℝ))
  let g₂ : ℤ → ℝ × ℝ → ℝ := fun k z =>
    deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
      (z.1 + z.2 + 2 * (k : ℝ))
  have hg₁ : ∀ k, Measurable (g₁ k) := by
    intro k
    dsimp [g₁]
    rw [show (fun z : ℝ × ℝ =>
      deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
        (z.1 - z.2 + 2 * (k : ℝ))) = fun z =>
      (1 / (2 * t)) *
        ((z.1 - z.2 + 2 * (k : ℝ)) ^ 2 / (2 * t) - 1) *
          heatKernel t (z.1 - z.2 + 2 * (k : ℝ)) by
            funext z
            exact ShenWork.Paper2.deriv_deriv_heatKernel_global _ _]
    unfold heatKernel
    fun_prop
  have hg₂ : ∀ k, Measurable (g₂ k) := by
    intro k
    dsimp [g₂]
    rw [show (fun z : ℝ × ℝ =>
      deriv (fun u : ℝ => deriv (fun w : ℝ => heatKernel t w) u)
        (z.1 + z.2 + 2 * (k : ℝ))) = fun z =>
      (1 / (2 * t)) *
        ((z.1 + z.2 + 2 * (k : ℝ)) ^ 2 / (2 * t) - 1) *
          heatKernel t (z.1 + z.2 + 2 * (k : ℝ)) by
            funext z
            exact ShenWork.Paper2.deriv_deriv_heatKernel_global _ _]
    unfold heatKernel
    fun_prop
  have hsum₁ : ∀ z, Summable (fun k : ℤ => g₁ k z) := by
    intro z
    by_cases ht : 0 < t
    · simpa [g₁] using latticeGaussianHessSummable ht (z.1 - z.2)
    · have hz : ∀ k, g₁ k z = 0 := by
        intro k
        dsimp [g₁]
        rw [ShenWork.Paper2.deriv_deriv_heatKernel_global,
          heatKernel_of_nonpos (le_of_not_gt ht)]
        simp
      simpa only [hz] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
  have hsum₂ : ∀ z, Summable (fun k : ℤ => g₂ k z) := by
    intro z
    by_cases ht : 0 < t
    · simpa [g₂] using latticeGaussianHessSummable ht (z.1 + z.2)
    · have hz : ∀ k, g₂ k z = 0 := by
        intro k
        dsimp [g₂]
        rw [ShenWork.Paper2.deriv_deriv_heatKernel_global,
          heatKernel_of_nonpos (le_of_not_gt ht)]
        simp
      simpa only [hz] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
  have hsum : Measurable (fun z : ℝ × ℝ =>
      (∑' k : ℤ, g₁ k z) + ∑' k : ℤ, g₂ k z) :=
    (measurable_tsum_int_of_summable hg₁ hsum₁).add
      (measurable_tsum_int_of_summable hg₂ hsum₂)
  have heq : (fun z : ℝ × ℝ => intervalFullGeneratorKernel t z.1 z.2) =
      fun z => -((∑' k : ℤ, g₁ k z) + ∑' k : ℤ, g₂ k z) := by
    funext z
    unfold intervalFullGeneratorKernel
    by_cases ht : 0 < t
    · rw [(hasDerivAt_deriv_intervalNeumannFullKernel_fst ht z.1 z.2).deriv]
    · have hzero : (fun w : ℝ => intervalNeumannFullKernel t w z.2) =
          fun _ : ℝ => (0 : ℝ) := by
        funext w
        unfold intervalNeumannFullKernel
        simp only [heatKernel_of_nonpos (le_of_not_gt ht), add_zero, tsum_zero]
      have hleft : deriv (fun u : ℝ => deriv
          (fun w : ℝ => intervalNeumannFullKernel t w z.2) u) z.1 = 0 := by
        rw [hzero]
        simp
      rw [hleft, neg_zero]
      have hgzero : ∀ k, g₁ k z = 0 ∧ g₂ k z = 0 := by
        intro k
        dsimp [g₁, g₂]
        rw [ShenWork.Paper2.deriv_deriv_heatKernel_global,
          ShenWork.Paper2.deriv_deriv_heatKernel_global,
          heatKernel_of_nonpos (le_of_not_gt ht),
          heatKernel_of_nonpos (le_of_not_gt ht)]
        simp
      have hg₁zero : ∀ k, g₁ k z = 0 := fun k => (hgzero k).1
      have hg₂zero : ∀ k, g₂ k z = 0 := fun k => (hgzero k).2
      simp only [hg₁zero, hg₂zero, tsum_zero, add_zero, neg_zero]
  rw [heq]
  exact hsum.neg

/-- A.e.-strong measurability of the generator heat output. -/
theorem intervalFullGeneratorHeatOperator_aestronglyMeasurable
    {t : ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (intervalMeasure 1)) :
    AEStronglyMeasurable (intervalFullGeneratorHeatOperator t f)
      (intervalMeasure 1) := by
  let F : ℝ × ℝ → ℝ := fun z =>
    intervalFullGeneratorKernel t z.1 z.2 * f z.2
  have hF : AEStronglyMeasurable F
      ((intervalMeasure 1).prod (intervalMeasure 1)) :=
    (intervalFullGeneratorKernel_joint_measurable t).aestronglyMeasurable.mul
      hf.comp_snd
  have hI := hF.integral_prod_right'
  simpa [F, intervalFullGeneratorHeatOperator] using hI

/-- Explicit constant in the full-kernel generator Schur estimate. -/
def fullGeneratorKernelConstant : ℝ := 5 * Real.sqrt 2 / 2

theorem fullGeneratorKernelConstant_pos : 0 < fullGeneratorKernelConstant := by
  unfold fullGeneratorKernelConstant
  positivity

/-- Row `L¹` mass of the generator kernel. -/
theorem intervalFullGeneratorKernel_abs_integral_le
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (∫ y, |intervalFullGeneratorKernel t x y| ∂(intervalMeasure 1)) ≤
      fullGeneratorKernelConstant * t ^ (-(1 : ℝ)) := by
  have hcv :
      (∫ y, |intervalFullGeneratorKernel t x y| ∂(intervalMeasure 1)) =
        ∫ y in (0 : ℝ)..1,
          |deriv (fun z : ℝ => deriv
            (fun w : ℝ => intervalNeumannFullKernel t w y) z) x| := by
    simp only [intervalFullGeneratorKernel, abs_neg, intervalMeasure, intervalSet]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [hcv]
  simpa [fullGeneratorKernelConstant] using
    intervalNeumannFullKernel_secondDeriv_abs_interval_integral_le ht x

/-- Column `L¹` mass, obtained from Hessian symmetry. -/
theorem intervalFullGeneratorKernel_abs_integral_le_swap
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (∫ x, |intervalFullGeneratorKernel t x y| ∂(intervalMeasure 1)) ≤
      fullGeneratorKernelConstant * t ^ (-(1 : ℝ)) := by
  have heq : (fun x => |intervalFullGeneratorKernel t x y|) =
      fun x => |intervalFullGeneratorKernel t y x| := by
    funext x
    rw [intervalFullGeneratorKernel_symm ht]
  rw [heq]
  exact intervalFullGeneratorKernel_abs_integral_le ht y

/-- Row continuity on the physical interval. -/
theorem intervalFullGeneratorKernel_abs_continuousOn
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ContinuousOn (fun y => |intervalFullGeneratorKernel t x y|)
      (Set.Icc (0 : ℝ) 1) := by
  simpa [intervalFullGeneratorKernel] using
    (continuousOn_secondDeriv_intervalNeumannFullKernel_fst ht x).abs

/-- Column continuity on the physical interval. -/
theorem intervalFullGeneratorKernel_abs_continuousOn_swap
    {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ContinuousOn (fun x => |intervalFullGeneratorKernel t x y|)
      (Set.Icc (0 : ℝ) 1) := by
  have heq : (fun x => |intervalFullGeneratorKernel t x y|) =
      fun x => |intervalFullGeneratorKernel t y x| := by
    funext x
    rw [intervalFullGeneratorKernel_symm ht]
  rw [heq]
  exact intervalFullGeneratorKernel_abs_continuousOn ht y

/-- Pointwise weighted-Holder estimate used in the Schur argument. -/
theorem intervalFullGeneratorHeatOperator_abs_rpow_le
    {t r q : ℝ} (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) (x : ℝ) :
    |intervalFullGeneratorHeatOperator t f x| ^ q ≤
      (fullGeneratorKernelConstant * t ^ (-(1 : ℝ))) ^ (q / r) *
      ∫ y, |intervalFullGeneratorKernel t x y| * ‖f y‖ ^ q
        ∂(intervalMeasure 1) := by
  let mu := intervalMeasure 1
  let K : ℝ → ℝ := fun y => |intervalFullGeneratorKernel t x y|
  let a : ℝ → ℝ := fun y => K y ^ (1 / r)
  let b : ℝ → ℝ := fun y => K y ^ (1 / q) * ‖f y‖
  let B : ℝ := ∫ y, K y * ‖f y‖ ^ q ∂mu
  let A : ℝ := fullGeneratorKernelConstant * t ^ (-(1 : ℝ))
  have hA : 0 ≤ A :=
    mul_nonneg fullGeneratorKernelConstant_pos.le (Real.rpow_nonneg ht.le _)
  have hApos : 0 < A := by
    dsimp [A, fullGeneratorKernelConstant]
    positivity
  have hKnonneg : ∀ y, 0 ≤ K y := fun y => abs_nonneg _
  have hKcont : ContinuousOn K (Icc (0 : ℝ) 1) := by
    dsimp [K]
    exact intervalFullGeneratorKernel_abs_continuousOn ht x
  obtain ⟨MK, hMK⟩ := isCompact_Icc.exists_bound_of_continuousOn hKcont
  have hMK0 : 0 ≤ MK :=
    (norm_nonneg (K 0)).trans (hMK 0 (by norm_num))
  have ha_meas : AEStronglyMeasurable a mu := by
    apply ((hKcont.rpow_const (fun _ _ => Or.inr hrq.one_div_nonneg)).aestronglyMeasurable
      measurableSet_Icc)
  have hb_meas : AEStronglyMeasurable b mu := by
    have hkq : AEStronglyMeasurable (fun y => K y ^ (1 / q)) mu :=
      (hKcont.rpow_const (fun _ _ => Or.inr hrq.symm.one_div_nonneg)).aestronglyMeasurable
        measurableSet_Icc
    exact hkq.mul hf.aestronglyMeasurable.norm
  have ha_mem : MemLp a (ENNReal.ofReal r) mu := by
    apply MemLp.of_bound ha_meas (MK ^ (1 / r))
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    exact Filter.Eventually.of_forall fun y hy => by
      dsimp [a]
      rw [abs_of_nonneg (Real.rpow_nonneg (hKnonneg y) _)]
      exact Real.rpow_le_rpow (hKnonneg y)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)] using hMK y hy)
        hrq.one_div_nonneg
  have hb_mem : MemLp b (ENNReal.ofReal q) mu := by
    apply MemLp.of_le_mul (g := f) (c := MK ^ (1 / q)) hf hb_meas
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    exact Filter.Eventually.of_forall fun y hy => by
      dsimp [b]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hKnonneg y) _), abs_abs]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hKnonneg y)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)] using hMK y hy)
          hrq.symm.one_div_nonneg)
        (abs_nonneg _)
  have ha_nonneg : 0 ≤ᵐ[mu] a :=
    Filter.Eventually.of_forall fun y => Real.rpow_nonneg (hKnonneg y) _
  have hb_nonneg : 0 ≤ᵐ[mu] b :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg (hKnonneg y) _) (norm_nonneg _)
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) (p := r) (q := q) hrq
    ha_nonneg hb_nonneg ha_mem hb_mem
  have hsum : 1 / r + 1 / q = 1 := by
    simpa [one_div] using hrq.inv_add_inv_eq_one
  have hab : (∫ y, a y * b y ∂mu) = ∫ y, K y * ‖f y‖ ∂mu := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a, b]
      calc
        K y ^ (1 / r) * (K y ^ (1 / q) * ‖f y‖) =
            (K y ^ (1 / r) * K y ^ (1 / q)) * ‖f y‖ := by ring
        _ = K y ^ (1 / r + 1 / q) * ‖f y‖ := by
          rw [Real.rpow_add_of_nonneg (hKnonneg y)
            hrq.one_div_nonneg hrq.symm.one_div_nonneg]
        _ = K y * ‖f y‖ := by rw [hsum, Real.rpow_one]
  have hapow : (∫ y, a y ^ r ∂mu) = ∫ y, K y ∂mu := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a]
      rw [one_div, Real.rpow_inv_rpow (hKnonneg y) hrq.ne_zero]
  have hbpow : (∫ y, b y ^ q ∂mu) = B := by
    dsimp [B]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [b]
      rw [Real.mul_rpow (Real.rpow_nonneg (hKnonneg y) _) (abs_nonneg (f y)),
        one_div, Real.rpow_inv_rpow (hKnonneg y) hrq.symm.ne_zero]
  rw [hab, hapow, hbpow] at hholder
  have hmass : (∫ y, K y ∂mu) ≤ A := by
    dsimp [K, A, mu]
    exact intervalFullGeneratorKernel_abs_integral_le ht x
  have hmass0 : 0 ≤ ∫ y, K y ∂mu := integral_nonneg fun y => hKnonneg y
  have hmassroot : (∫ y, K y ∂mu) ^ (1 / r) ≤ A ^ (1 / r) :=
    Real.rpow_le_rpow hmass0 hmass hrq.one_div_nonneg
  have hB0 : 0 ≤ B := integral_nonneg fun y =>
    mul_nonneg (hKnonneg y) (Real.rpow_nonneg (norm_nonneg _) q)
  have hkernel : ∫ y, K y * ‖f y‖ ∂mu ≤
      A ^ (1 / r) * B ^ (1 / q) := by
    exact hholder.trans (mul_le_mul_of_nonneg_right hmassroot
      (Real.rpow_nonneg hB0 _))
  have hkernel0 : 0 ≤ ∫ y, K y * ‖f y‖ ∂mu :=
    integral_nonneg fun y => mul_nonneg (hKnonneg y) (norm_nonneg _)
  have hoperator : |intervalFullGeneratorHeatOperator t f x| ≤
      ∫ y, K y * ‖f y‖ ∂mu := by
    unfold intervalFullGeneratorHeatOperator
    calc
      |∫ y, intervalFullGeneratorKernel t x y * f y ∂mu| ≤
          ∫ y, ‖intervalFullGeneratorKernel t x y * f y‖ ∂mu := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
      _ = ∫ y, K y * ‖f y‖ ∂mu := by
        congr 1
        ext y
        dsimp [K]
        rw [abs_mul]
  have hraised := Real.rpow_le_rpow (abs_nonneg _) (hoperator.trans hkernel)
    hrq.symm.nonneg
  calc
    |intervalFullGeneratorHeatOperator t f x| ^ q ≤
        (A ^ (1 / r) * B ^ (1 / q)) ^ q := hraised
    _ = A ^ (q / r) * B := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB0 _),
        ← Real.rpow_mul hA, ← Real.rpow_mul hB0]
      have hBexp : (1 / q) * q = 1 := by
        field_simp [hrq.symm.ne_zero]
      have hAexp : (1 / r) * q = q / r := by
        field_simp [hrq.ne_zero]
      rw [hBexp, hAexp, Real.rpow_one]
    _ = (fullGeneratorKernelConstant * t ^ (-(1 : ℝ))) ^ (q / r) *
        ∫ y, |intervalFullGeneratorKernel t x y| * ‖f y‖ ^ q
          ∂ intervalMeasure 1 := rfl

/-- Same-exponent Schur bound at the integral-power level. -/
theorem intervalFullGeneratorHeatOperator_Lp_integral_le
    {t r q : ℝ} (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    (∫ x, |intervalFullGeneratorHeatOperator t f x| ^ q
        ∂(intervalMeasure 1)) ≤
      (fullGeneratorKernelConstant * t ^ (-(1 : ℝ))) ^ q *
      ∫ y, ‖f y‖ ^ q ∂(intervalMeasure 1) := by
  let mu := intervalMeasure 1
  let K : ℝ × ℝ → ℝ := fun z => |intervalFullGeneratorKernel t z.1 z.2|
  let F : ℝ × ℝ → ℝ := fun z => K z * ‖f z.2‖ ^ q
  let A : ℝ := fullGeneratorKernelConstant * t ^ (-(1 : ℝ))
  have hA : 0 ≤ A :=
    mul_nonneg fullGeneratorKernelConstant_pos.le (Real.rpow_nonneg ht.le _)
  have hApos : 0 < A := by
    dsimp [A, fullGeneratorKernelConstant]
    positivity
  have hq_ne_zero : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrq.symm.pos
  have hq_ne_top : ENNReal.ofReal q ≠ ⊤ := by simp
  have hfq_int : Integrable (fun y => ‖f y‖ ^ q) mu := by
    simpa [mu, ENNReal.toReal_ofReal hrq.symm.nonneg] using
      hf.integrable_norm_rpow hq_ne_zero hq_ne_top
  have hK_meas : Measurable K := by
    dsimp [K]
    simpa [Real.norm_eq_abs] using
      (intervalFullGeneratorKernel_joint_measurable t).norm
  have hF_meas : AEStronglyMeasurable F (mu.prod mu) := by
    dsimp [F]
    exact hK_meas.aestronglyMeasurable.mul
      hfq_int.aestronglyMeasurable.comp_snd
  have hF_int : Integrable F (mu.prod mu) := by
    refine (MeasureTheory.integrable_prod_iff' hF_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun y => ?_
      have hKsec : Integrable (fun x => K (x, y)) mu := by
        have hcont : ContinuousOn (fun x => K (x, y)) (Icc (0 : ℝ) 1) := by
          simpa [K] using intervalFullGeneratorKernel_abs_continuousOn_swap ht y
        simpa [mu, intervalMeasure, intervalSet] using hcont.integrableOn_Icc
      exact hKsec.mul_const (‖f y‖ ^ q)
    · have hinner_meas : AEStronglyMeasurable
          (fun y => ∫ x, ‖F (x, y)‖ ∂mu) mu := by
        simpa only [Prod.swap_prod_mk] using
          hF_meas.norm.prod_swap.integral_prod_right'
      apply (hfq_int.const_mul A).mono hinner_meas
      refine Filter.Eventually.of_forall fun y => ?_
      have hKmass : (∫ x, K (x, y) ∂mu) ≤ A := by
        dsimp [K, A, mu]
        exact intervalFullGeneratorKernel_abs_integral_le_swap ht y
      have hKnonneg : ∀ x, 0 ≤ K (x, y) := fun x => abs_nonneg _
      calc
        ‖∫ x, ‖F (x, y)‖ ∂mu‖ =
            (∫ x, K (x, y) ∂mu) * ‖f y‖ ^ q := by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
            ← MeasureTheory.integral_mul_const]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp [F]
            rw [abs_of_nonneg]
            exact mul_nonneg (hKnonneg x)
              (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ A * ‖f y‖ ^ q :=
          mul_le_mul_of_nonneg_right hKmass
            (Real.rpow_nonneg (norm_nonneg _) _)
        _ = ‖A * ‖f y‖ ^ q‖ := by
          rw [Real.norm_of_nonneg
            (mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _))]
  have hright_int : Integrable
      (fun x => A ^ (q / r) * ∫ y, F (x, y) ∂mu) mu :=
    hF_int.integral_prod_left.const_mul (A ^ (q / r))
  have hfirst :
      (∫ x, |intervalFullGeneratorHeatOperator t f x| ^ q ∂mu) ≤
        A ^ (q / r) * ∫ x, ∫ y, F (x, y) ∂mu ∂mu := by
    calc
      (∫ x, |intervalFullGeneratorHeatOperator t f x| ^ q ∂mu) ≤
          ∫ x, A ^ (q / r) * ∫ y, F (x, y) ∂mu ∂mu := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (abs_nonneg _) q
        · exact hright_int
        · exact Filter.Eventually.of_forall fun x => by
            have hx := intervalFullGeneratorHeatOperator_abs_rpow_le
              ht hrq hf x
            have hrewrite :
                (∫ y, |intervalFullGeneratorKernel t x y| *
                    ‖f y‖ ^ q ∂mu) = ∫ y, F (x, y) ∂mu := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun y => by
                dsimp [F, K]
            rw [hrewrite] at hx
            simpa [A, mu] using hx
      _ = A ^ (q / r) * ∫ x, ∫ y, F (x, y) ∂mu ∂mu := by
        rw [MeasureTheory.integral_const_mul]
  have hswap :
      (∫ x, ∫ y, F (x, y) ∂mu ∂mu) =
        ∫ y, ∫ x, F (x, y) ∂mu ∂mu :=
    MeasureTheory.integral_integral_swap (μ := mu) (ν := mu)
      (f := fun x y => F (x, y)) hF_int
  have hsecond :
      (∫ y, ∫ x, F (x, y) ∂mu ∂mu) ≤
        A * ∫ y, ‖f y‖ ^ q ∂mu := by
    calc
      (∫ y, ∫ x, F (x, y) ∂mu ∂mu) ≤
          ∫ y, A * ‖f y‖ ^ q ∂mu := by
        apply MeasureTheory.integral_mono hF_int.integral_prod_right
          (hfq_int.const_mul A)
        intro y
        have hKmass : (∫ x, K (x, y) ∂mu) ≤ A := by
          dsimp [K, A, mu]
          exact intervalFullGeneratorKernel_abs_integral_le_swap ht y
        calc
          (∫ x, F (x, y) ∂mu) =
              (∫ x, K (x, y) ∂mu) * ‖f y‖ ^ q := by
            dsimp [F]
            rw [MeasureTheory.integral_mul_const]
          _ ≤ A * ‖f y‖ ^ q :=
            mul_le_mul_of_nonneg_right hKmass
              (Real.rpow_nonneg (norm_nonneg _) _)
      _ = A * ∫ y, ‖f y‖ ^ q ∂mu := by
        rw [MeasureTheory.integral_const_mul]
  have hexp : q / r + 1 = q := by
    have hsum := hrq.inv_add_inv_eq_one
    field_simp [hrq.ne_zero, hrq.symm.ne_zero] at hsum ⊢
    linarith
  calc
    (∫ x, |intervalFullGeneratorHeatOperator t f x| ^ q ∂mu) ≤
        A ^ (q / r) * ∫ x, ∫ y, F (x, y) ∂mu ∂mu := hfirst
    _ = A ^ (q / r) * ∫ y, ∫ x, F (x, y) ∂mu ∂mu := by rw [hswap]
    _ ≤ A ^ (q / r) * (A * ∫ y, ‖f y‖ ^ q ∂mu) :=
      mul_le_mul_of_nonneg_left hsecond (Real.rpow_nonneg hA _)
    _ = A ^ q * ∫ y, ‖f y‖ ^ q ∂mu := by
      calc
        A ^ (q / r) * (A * ∫ y, ‖f y‖ ^ q ∂mu) =
            (A ^ (q / r) * A) * ∫ y, ‖f y‖ ^ q ∂mu := by ring
        _ = A ^ (q / r + 1) * ∫ y, ‖f y‖ ^ q ∂mu := by
          congr 1
          calc
            A ^ (q / r) * A = A ^ (q / r) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = A ^ (q / r + 1) := (Real.rpow_add hApos _ _).symm
        _ = A ^ q * ∫ y, ‖f y‖ ^ q ∂mu := by rw [hexp]
    _ = (fullGeneratorKernelConstant * t ^ (-(1 : ℝ))) ^ q *
        ∫ y, ‖f y‖ ^ q ∂ intervalMeasure 1 := rfl

/-- Same-exponent generator estimate for every finite `1 < q < infinity`,
in the physical `lpNorm` interface. -/
theorem intervalFullGeneratorHeatOperator_lpNorm_le
    {t q r : ℝ} (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    lpNorm (intervalFullGeneratorHeatOperator t f) (ENNReal.ofReal q)
        (intervalMeasure 1) ≤
      (fullGeneratorKernelConstant * t ^ (-(1 : ℝ))) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let B : ℝ → ℝ := intervalFullGeneratorHeatOperator t f
  let A : ℝ := fullGeneratorKernelConstant * t ^ (-(1 : ℝ))
  let If : ℝ := ∫ y, ‖f y‖ ^ q ∂μ
  have hq_pos : 0 < q := hrq.symm.pos
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq_zero : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hq_pos
  have hq_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hA : 0 ≤ A := by
    exact mul_nonneg fullGeneratorKernelConstant_pos.le
      (Real.rpow_nonneg ht.le _)
  have hIf : 0 ≤ If := by
    exact integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) q
  have hB_meas : AEStronglyMeasurable B μ :=
    intervalFullGeneratorHeatOperator_aestronglyMeasurable
      hf.aestronglyMeasurable
  have hraw :
      ∫ x, |B x| ^ q ∂μ ≤ A ^ q * If := by
    simpa [B, A, If, μ] using
      intervalFullGeneratorHeatOperator_Lp_integral_le ht hrq hf
  have hroot :
      (∫ x, ‖B x‖ ^ q ∂μ) ^ (1 / q) ≤
        (A ^ q * If) ^ (1 / q) := by
    apply Real.rpow_le_rpow
    · exact integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) q
    · simpa [Real.norm_eq_abs] using hraw
    · exact one_div_nonneg.mpr hq_pos.le
  have hfactor : (A ^ q * If) ^ (1 / q) = A * If ^ (1 / q) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA q) hIf]
    congr 1
    rw [one_div, ← Real.rpow_mul hA q q⁻¹,
      mul_inv_cancel₀ hq_ne, Real.rpow_one]
  have hf_lp :
      lpNorm f (ENNReal.ofReal q) μ = If ^ (1 / q) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hq_zero hq_top
      hf.aestronglyMeasurable, ENNReal.toReal_ofReal hq_pos.le]
    simp [If, μ, one_div]
  calc
    lpNorm B (ENNReal.ofReal q) μ =
        (∫ x, ‖B x‖ ^ q ∂μ) ^ (1 / q) := by
      rw [lpNorm_eq_integral_norm_rpow_toReal hq_zero hq_top hB_meas,
        ENNReal.toReal_ofReal hq_pos.le]
      simp [one_div]
    _ ≤ (A ^ q * If) ^ (1 / q) := hroot
    _ = A * If ^ (1 / q) := hfactor
    _ = A * lpNorm f (ENNReal.ofReal q) μ := by rw [hf_lp]
    _ = (fullGeneratorKernelConstant * t ^ (-(1 : ℝ))) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := rfl

#print axioms intervalFullGeneratorHeatOperator_abs_rpow_le
#print axioms intervalFullGeneratorHeatOperator_Lp_integral_le
#print axioms intervalFullGeneratorHeatOperator_lpNorm_le

end ShenWork.Paper2.IntervalFullKernelFullQGenerator
