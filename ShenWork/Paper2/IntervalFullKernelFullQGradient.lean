import ShenWork.Paper2.IntervalDomainRestartedLpLinf
import ShenWork.Paper2.IntervalConjugateKernelJointMeas

/-!
# Full-exponent gradient estimates for the Neumann heat kernel

The full kernel has uniform `L^1` row and column bounds for its spatial
derivative.  The weighted Holder/Fubini argument already available at the
integral level therefore gives an `L^q -> L^q` estimate for every
`1 < q < infinity`.  This file converts that estimate to the physical
`lpNorm` interface and adds the positive spectral shift used in Paper 2.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace ShenWork.Paper2.IntervalFullKernelFullQGradient

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalConjugateKernelJointMeas
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper2.IntervalDomainRestartedLpLinf

/-- A.e.-strong measurability of the full Neumann conjugate-kernel operator
for an arbitrary a.e.-strongly measurable source. -/
theorem intervalConjugateKernelOperator_aestronglyMeasurable
    {t : ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (intervalMeasure 1)) :
    AEStronglyMeasurable (intervalConjugateKernelOperator t f)
      (intervalMeasure 1) := by
  let F : ℝ × ℝ → ℝ := fun z =>
    intervalNeumannFullKernelDerivSeries t z.2 z.1 * f z.2
  have hK : Measurable (fun z : ℝ × ℝ =>
      intervalNeumannFullKernelDerivSeries t z.2 z.1) :=
    intervalNeumannFullKernelDerivSeries_joint_measurable.comp
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hF : AEStronglyMeasurable F
      ((intervalMeasure 1).prod (intervalMeasure 1)) :=
    hK.aestronglyMeasurable.mul hf.comp_snd
  have hI := hF.integral_prod_right'
  have heq : intervalConjugateKernelOperator t f =
      fun x => -∫ y, F (x, y) ∂(intervalMeasure 1) := by
    funext x
    rw [intervalConjugateKernelOperator_eq_neg_derivSeries_integral]
  rw [heq]
  exact hI.neg

/-- Physical same-exponent gradient estimate for every finite
`1 < q < infinity`. -/
theorem intervalConjugateKernelOperator_lpNorm_le
    {t q r : ℝ} (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    lpNorm (intervalConjugateKernelOperator t f) (ENNReal.ofReal q)
        (intervalMeasure 1) ≤
      (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  let μ := intervalMeasure 1
  let B : ℝ → ℝ := intervalConjugateKernelOperator t f
  let A : ℝ := heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))
  let If : ℝ := ∫ y, ‖f y‖ ^ q ∂μ
  have hq_pos : 0 < q := hrq.symm.pos
  have hq_ne : q ≠ 0 := hq_pos.ne'
  have hq_zero : ENNReal.ofReal q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hq_pos
  have hq_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hA : 0 ≤ A := by
    exact mul_nonneg heatGradientLinftyLinftyConstant_nonneg
      (Real.rpow_nonneg ht.le _)
  have hIf : 0 ≤ If := by
    exact integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) q
  have hB_meas : AEStronglyMeasurable B μ :=
    intervalConjugateKernelOperator_aestronglyMeasurable
      hf.aestronglyMeasurable
  have hraw :
      ∫ x, |B x| ^ q ∂μ ≤ A ^ q * If := by
    simpa [B, A, If, μ] using
      intervalConjugateKernelOperator_Lp_integral_le ht hrq hf
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
    _ = (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := rfl

/-- The positively shifted physical divergence/gradient heat operator. -/
def intervalShiftedFullDivergenceOperator
    (omega t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(omega * t)) * intervalConjugateKernelOperator t f x

/-- Exact scalar-factor identity for the shifted divergence operator. -/
theorem intervalShiftedFullDivergenceOperator_lpNorm
    (omega t q : ℝ) (f : ℝ → ℝ) :
    lpNorm (intervalShiftedFullDivergenceOperator omega t f)
        (ENNReal.ofReal q) (intervalMeasure 1) =
      Real.exp (-(omega * t)) *
        lpNorm (intervalConjugateKernelOperator t f)
          (ENNReal.ofReal q) (intervalMeasure 1) := by
  have h := lpNorm_const_smul (p := ENNReal.ofReal q)
    (Real.exp (-(omega * t)))
    (intervalConjugateKernelOperator t f) (intervalMeasure 1)
  simpa [intervalShiftedFullDivergenceOperator, Pi.smul_apply,
    smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h

/-- Shifted same-exponent gradient estimate, valid for every finite
`1 < q < infinity`. -/
theorem intervalShiftedFullDivergenceOperator_lpNorm_le
    {omega t q r : ℝ} (ht : 0 < t) (hrq : r.HolderConjugate q)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal q) (intervalMeasure 1)) :
    lpNorm (intervalShiftedFullDivergenceOperator omega t f)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(omega * t)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  rw [intervalShiftedFullDivergenceOperator_lpNorm]
  have hgrad := intervalConjugateKernelOperator_lpNorm_le ht hrq hf
  have hexp : 0 ≤ Real.exp (-(omega * t)) := Real.exp_nonneg _
  calc
    Real.exp (-(omega * t)) *
        lpNorm (intervalConjugateKernelOperator t f)
          (ENNReal.ofReal q) (intervalMeasure 1) ≤
      Real.exp (-(omega * t)) *
        ((heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1)) :=
        mul_le_mul_of_nonneg_left hgrad hexp
    _ = heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(omega * t)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by ring

/-- Full-`q` physical form of Paper 2 Lemma 2.3, with the honest `MemLp`
hypothesis missing from the raw statement-layer record.  The constant is
independent of `q`. -/
theorem Lemma_2_3_interval_full_q
    (omega : ℝ) :
    ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ f : ℝ → ℝ,
      MemLp f (ENNReal.ofReal q) (intervalMeasure 1) →
        lpNorm (intervalShiftedFullDivergenceOperator omega t f)
            (ENNReal.ofReal q) (intervalMeasure 1) ≤
          C * (1 + t ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(omega * t)) *
              lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  let C := heatGradientLinftyLinftyConstant
  have hC : 0 < C := by
    dsimp [C, heatGradientLinftyLinftyConstant]
    positivity
  refine ⟨C, hC, ?_⟩
  intro q hq t ht f hf
  let r := Real.conjExponent q
  have hrq : r.HolderConjugate q :=
    (Real.HolderConjugate.conjExponent hq).symm
  have hbase := intervalShiftedFullDivergenceOperator_lpNorm_le
    (omega := omega) ht hrq hf
  have hpow : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  have hcore : C * t ^ (-(1 / 2 : ℝ)) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hC.le
  have htail : 0 ≤
      Real.exp (-(omega * t)) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) :=
    mul_nonneg (Real.exp_nonneg _) lpNorm_nonneg
  calc
    lpNorm (intervalShiftedFullDivergenceOperator omega t f)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      C * t ^ (-(1 / 2 : ℝ)) * Real.exp (-(omega * t)) *
        lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := hbase
    _ = (C * t ^ (-(1 / 2 : ℝ))) *
        (Real.exp (-(omega * t)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1)) := by ring
    _ ≤ (C * (1 + t ^ (-(1 / 2 : ℝ)))) *
        (Real.exp (-(omega * t)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1)) :=
      mul_le_mul_of_nonneg_right hcore htail
    _ = C * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(omega * t)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by ring

/-- The full-`q` zero-fractional-order base of Paper 2 Lemma 2.4.  It has
the requested `omega / 2` decay and leaves only the positive fractional
Neumann power to be constructed. -/
theorem Lemma_2_4_interval_full_q_sigma_zero
    {omega : ℝ} (homega : 0 < omega) :
    ∃ C > 0, ∀ q > 1, ∀ t > 0, ∀ f : ℝ → ℝ,
      MemLp f (ENNReal.ofReal q) (intervalMeasure 1) →
        lpNorm (intervalShiftedFullDivergenceOperator omega t f)
            (ENNReal.ofReal q) (intervalMeasure 1) ≤
          C * (1 + t ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(omega / 2) * t) *
              lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  rcases Lemma_2_3_interval_full_q omega with ⟨C, hC, hbase⟩
  refine ⟨C, hC, ?_⟩
  intro q hq t ht f hf
  have h := hbase q hq t ht f hf
  have hexp : Real.exp (-(omega * t)) ≤
      Real.exp (-(omega / 2) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  have hleft : 0 ≤ C * (1 + t ^ (-(1 / 2 : ℝ))) :=
    mul_nonneg hC.le (by linarith)
  calc
    lpNorm (intervalShiftedFullDivergenceOperator omega t f)
        (ENNReal.ofReal q) (intervalMeasure 1) ≤
      C * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(omega * t)) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := h
    _ ≤ C * (1 + t ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(omega / 2) * t) *
          lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp hleft) lpNorm_nonneg

#print axioms intervalConjugateKernelOperator_aestronglyMeasurable
#print axioms intervalConjugateKernelOperator_lpNorm_le
#print axioms intervalShiftedFullDivergenceOperator_lpNorm
#print axioms intervalShiftedFullDivergenceOperator_lpNorm_le
#print axioms Lemma_2_3_interval_full_q
#print axioms Lemma_2_4_interval_full_q_sigma_zero

end ShenWork.Paper2.IntervalFullKernelFullQGradient
