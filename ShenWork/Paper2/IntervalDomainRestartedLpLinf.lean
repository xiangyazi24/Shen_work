/-
Sharp short-time full-Neumann heat and B-form smoothing used by the
finite-Lp restarted endpoint in Paper 2.  The B-form estimate is obtained
without differentiating its source: first prove the Lp contraction from the
two kernel-derivative mass bounds, then factor B(t) as S(t/2) B(t/2).
-/
import ShenWork.PDE.IntervalFullKernelSpectralClean
import ShenWork.PDE.IntervalFullKernelSupBound
import ShenWork.PDE.IntervalFullKernelGradientLinfty
import ShenWork.PDE.HeatKernelLpEstimates
import ShenWork.Paper2.IntervalConjugateKernelJointMeas
import ShenWork.Paper2.IntervalFullDuhamelRestart
import ShenWork.Paper2.IntervalConjugateSemigroupComposition

open MeasureTheory Set Filter
open scoped Topology Interval ENNReal

noncomputable section

namespace ShenWork.Paper2.IntervalDomainRestartedLpLinf

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalFullKernelSpectralClean
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.Paper2
open ShenWork.HeatKernelGradientEstimates

noncomputable def thetaOne : ℝ :=
  ∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2)

theorem summable_exp_neg_int_sq :
    Summable (fun n : ℤ => Real.exp (-(n : ℝ) ^ 2)) := by
  have hpi2 : 0 < (1 / Real.pi ^ 2 : ℝ) := by positivity
  convert expWeightSummable (1 / Real.pi ^ 2) hpi2 using 1
  ext n
  congr 1
  field_simp [Real.pi_ne_zero]

theorem thetaOne_nonneg : 0 ≤ thetaOne := by
  exact tsum_nonneg fun _ => Real.exp_nonneg _

theorem expWeightTrace_le_short
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∑' n : ℤ, Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2)) ≤
      (thetaOne / Real.sqrt Real.pi) * t ^ (-(1 / 2 : ℝ)) := by
  have hpit : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have hpoisson := Real.tsum_exp_neg_mul_int_sq hpit
  have hleft :
      (∑' n : ℤ, Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2)) =
        ∑' n : ℤ, Real.exp (-Real.pi * (Real.pi * t) * (n : ℝ) ^ 2) := by
    apply tsum_congr
    intro n
    congr 1
    ring
  have hone_inv : (1 : ℝ) ≤ 1 / t := by
    exact (le_div_iff₀ ht).2 (by simpa using ht1)
  have hdual_term : ∀ n : ℤ,
      Real.exp (-Real.pi / (Real.pi * t) * (n : ℝ) ^ 2) ≤
        Real.exp (-(n : ℝ) ^ 2) := by
    intro n
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    have hcoef : -Real.pi / (Real.pi * t) = -(1 / t) := by
      field_simp [Real.pi_ne_zero, ne_of_gt ht]
    rw [hcoef]
    nlinarith
  have hdual_sum :
      (∑' n : ℤ, Real.exp (-Real.pi / (Real.pi * t) * (n : ℝ) ^ 2)) ≤
        thetaOne := by
    dsimp [thetaOne]
    exact Summable.tsum_le_tsum hdual_term
      ((summable_exp_neg_int_sq).of_nonneg_of_le
        (fun _ => Real.exp_nonneg _) hdual_term)
      summable_exp_neg_int_sq
  rw [hleft, hpoisson]
  have hfactor : 0 ≤ (1 : ℝ) / (Real.pi * t) ^ (1 / 2 : ℝ) := by positivity
  calc
    1 / (Real.pi * t) ^ (1 / 2 : ℝ) *
          (∑' n : ℤ, Real.exp (-Real.pi / (Real.pi * t) * (n : ℝ) ^ 2))
        ≤ 1 / (Real.pi * t) ^ (1 / 2 : ℝ) * thetaOne :=
      mul_le_mul_of_nonneg_left hdual_sum hfactor
    _ = (thetaOne / Real.sqrt Real.pi) * t ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le]
      have hsqrtpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
      have hsqrtt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
      rw [Real.rpow_neg (by positivity : 0 ≤ t), ← Real.sqrt_eq_rpow]
      field_simp

noncomputable def fullHeatShortConstant : ℝ :=
  thetaOne / Real.sqrt Real.pi

theorem fullHeatShortConstant_nonneg : 0 ≤ fullHeatShortConstant := by
  exact div_nonneg thetaOne_nonneg (Real.sqrt_nonneg _)

theorem intervalNeumannFullKernel_abs_le_short
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x y : ℝ) :
    |intervalNeumannFullKernel t x y| ≤
      fullHeatShortConstant * t ^ (-(1 / 2 : ℝ)) := by
  let a : ℤ → ℝ := fun n =>
    Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2) *
      (Real.cos ((n : ℝ) * Real.pi * x) *
        Real.cos ((n : ℝ) * Real.pi * y))
  let b : ℤ → ℝ := fun n =>
    Real.exp (-t * ((n : ℝ) * Real.pi) ^ 2)
  have hb : Summable b := by
    simpa [b] using expWeightSummable t ht
  have hab : ∀ n, ‖a n‖ ≤ b n := by
    intro n
    dsimp [a, b]
    rw [abs_mul,
      abs_of_pos (Real.exp_pos _), abs_mul]
    have hcos : |Real.cos ((n : ℝ) * Real.pi * x)| *
        |Real.cos ((n : ℝ) * Real.pi * y)| ≤ 1 := by
      nlinarith [Real.abs_cos_le_one ((n : ℝ) * Real.pi * x),
        Real.abs_cos_le_one ((n : ℝ) * Real.pi * y),
        abs_nonneg (Real.cos ((n : ℝ) * Real.pi * x)),
        abs_nonneg (Real.cos ((n : ℝ) * Real.pi * y))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le hcos
  have ha_norm : Summable (fun n => ‖a n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hab hb
  rw [intervalNeumannFullKernel_eq_cosineKernel_clean t ht x y]
  change |∑' n, a n| ≤ _
  calc
    |∑' n, a n| = ‖∑' n, a n‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∑' n, ‖a n‖ := norm_tsum_le_tsum_norm ha_norm
    _ ≤ ∑' n, b n := ha_norm.tsum_le_tsum hab hb
    _ ≤ fullHeatShortConstant * t ^ (-(1 / 2 : ℝ)) := by
      simpa [b, fullHeatShortConstant] using expWeightTrace_le_short ht ht1

theorem intervalNeumannFullKernel_Lr_norm_le_short
    {t r p : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p) (x : ℝ) :
    (∫ y, ‖intervalNeumannFullKernel t x y‖ ^ r ∂ intervalMeasure 1) ^
        (1 / r) ≤
      (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) := by
  let A : ℝ := fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))
  have hA : 0 ≤ A := mul_nonneg fullHeatShortConstant_nonneg
    (Real.rpow_nonneg ht.le _)
  have hKnonneg : ∀ y, 0 ≤ intervalNeumannFullKernel t x y :=
    fun y => intervalNeumannFullKernel_nonneg ht x y
  have hKbound : ∀ y, intervalNeumannFullKernel t x y ≤ A := by
    intro y
    simpa [A, abs_of_nonneg (hKnonneg y)] using
      intervalNeumannFullKernel_abs_le_short ht ht1 x y
  have hKint : Integrable (fun y => intervalNeumannFullKernel t x y)
      (intervalMeasure 1) :=
    intervalNeumannFullKernel_integrable ht x
  have hright : Integrable
      (fun y => A ^ (r - 1) * intervalNeumannFullKernel t x y)
      (intervalMeasure 1) := hKint.const_mul (A ^ (r - 1))
  have hpow : ∀ y,
      ‖intervalNeumannFullKernel t x y‖ ^ r ≤
        A ^ (r - 1) * intervalNeumannFullKernel t x y := by
    intro y
    let k := intervalNeumannFullKernel t x y
    have hk : 0 ≤ k := hKnonneg y
    have hkle : k ≤ A := hKbound y
    have hr1 : 0 ≤ r - 1 := hrp.sub_one_pos.le
    have hkpow : k ^ r = k ^ (r - 1) * k := by
      calc
        k ^ r = k ^ ((r - 1) + 1) := by ring_nf
        _ = k ^ (r - 1) * k ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg hk hr1 zero_le_one
        _ = k ^ (r - 1) * k := by rw [Real.rpow_one]
    rw [Real.norm_eq_abs, abs_of_nonneg hk, hkpow]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hk hkle hr1) hk
  have hintle :
      ∫ y, ‖intervalNeumannFullKernel t x y‖ ^ r ∂ intervalMeasure 1 ≤
        A ^ (r - 1) := by
    calc
      ∫ y, ‖intervalNeumannFullKernel t x y‖ ^ r ∂ intervalMeasure 1 ≤
          ∫ y, A ^ (r - 1) * intervalNeumannFullKernel t x y
            ∂ intervalMeasure 1 := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun y =>
            Real.rpow_nonneg (norm_nonneg _) r
        · exact hright
        · exact Filter.Eventually.of_forall hpow
      _ = A ^ (r - 1) *
          ∫ y, intervalNeumannFullKernel t x y ∂ intervalMeasure 1 := by
        rw [MeasureTheory.integral_const_mul]
      _ = A ^ (r - 1) := by
        rw [intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x,
          mul_one]
  have hleft : 0 ≤
      ∫ y, ‖intervalNeumannFullKernel t x y‖ ^ r ∂ intervalMeasure 1 :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) r
  have hroot := Real.rpow_le_rpow hleft hintle hrp.one_div_pos.le
  have hexp : (r - 1) * (1 / r) = 1 / p := by
    have h := hrp.inv_add_inv_eq_one
    field_simp [hrp.ne_zero, hrp.symm.ne_zero] at h ⊢
    linarith
  calc
    (∫ y, ‖intervalNeumannFullKernel t x y‖ ^ r ∂ intervalMeasure 1) ^
          (1 / r) ≤ (A ^ (r - 1)) ^ (1 / r) := hroot
    _ = A ^ (1 / p) := by
      rw [← Real.rpow_mul hA, hexp]
    _ = (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) := rfl

theorem intervalFullSemigroupOperator_abs_le_Lp_short
    {t r p : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) (x : ℝ) :
    |intervalFullSemigroupOperator t f x| ≤
      (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
  let A : ℝ := fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))
  have hA : 0 ≤ A := mul_nonneg fullHeatShortConstant_nonneg
    (Real.rpow_nonneg ht.le _)
  have hKmeas : AEStronglyMeasurable
      (fun y => intervalNeumannFullKernel t x y) (intervalMeasure 1) :=
    (continuousOn_intervalNeumannFullKernel_snd ht x).aestronglyMeasurable
      measurableSet_Icc
  have hKmem : MemLp (fun y => intervalNeumannFullKernel t x y)
      (ENNReal.ofReal r) (intervalMeasure 1) := by
    apply MemLp.of_bound hKmeas A
    exact Filter.Eventually.of_forall fun y => by
      simpa [A, Real.norm_eq_abs] using
        intervalNeumannFullKernel_abs_le_short ht ht1 x y
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := intervalMeasure 1)
    (f := fun y => intervalNeumannFullKernel t x y)
    (g := f) hrp hKmem hf
  unfold intervalFullSemigroupOperator
  calc
    |∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1| =
        ‖∫ y, intervalNeumannFullKernel t x y * f y ∂ intervalMeasure 1‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∫ y, ‖intervalNeumannFullKernel t x y * f y‖ ∂ intervalMeasure 1 :=
      norm_integral_le_integral_norm _
    _ = ∫ y, ‖intervalNeumannFullKernel t x y‖ * ‖f y‖
          ∂ intervalMeasure 1 := by
      congr 1
      ext y
      rw [norm_mul]
    _ ≤ (∫ y, ‖intervalNeumannFullKernel t x y‖ ^ r ∂ intervalMeasure 1) ^
          (1 / r) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := hholder
    _ ≤ A ^ (1 / p) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
      exact mul_le_mul_of_nonneg_right
        (intervalNeumannFullKernel_Lr_norm_le_short ht ht1 hrp x)
        (Real.rpow_nonneg (integral_nonneg fun y =>
          Real.rpow_nonneg (norm_nonneg _) p) _)
    _ = (fullHeatShortConstant * t ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := rfl

theorem intervalConjugateKernelOperator_abs_rpow_le
    {t r p : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) (x : ℝ) :
    |intervalConjugateKernelOperator t f x| ^ p ≤
      (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) ^ (p / r) *
        ∫ y,
          |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| *
            ‖f y‖ ^ p ∂ intervalMeasure 1 := by
  let mu := intervalMeasure 1
  let K : ℝ → ℝ := fun y =>
    |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y|
  let a : ℝ → ℝ := fun y => K y ^ (1 / r)
  let b : ℝ → ℝ := fun y => K y ^ (1 / p) * ‖f y‖
  let B : ℝ := ∫ y, K y * ‖f y‖ ^ p ∂mu
  let A : ℝ := heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))
  have hA : 0 ≤ A := mul_nonneg heatGradientLinftyLinftyConstant_nonneg
    (Real.rpow_nonneg ht.le _)
  have hApos : 0 < A := by
    dsimp [A, heatGradientLinftyLinftyConstant]
    positivity
  have hKnonneg : ∀ y, 0 ≤ K y := fun y => abs_nonneg _
  have hKcont : ContinuousOn K (Icc (0 : ℝ) 1) := by
    dsimp [K]
    exact (continuousOn_deriv_intervalNeumannFullKernel_snd ht x).abs
  obtain ⟨MK, hMK⟩ := isCompact_Icc.exists_bound_of_continuousOn hKcont
  have hMK0 : 0 ≤ MK :=
    (norm_nonneg (K 0)).trans (hMK 0 (by norm_num))
  have ha_meas : AEStronglyMeasurable a mu := by
    apply ((hKcont.rpow_const (fun _ _ => Or.inr hrp.one_div_nonneg)).aestronglyMeasurable
      measurableSet_Icc)
  have hb_meas : AEStronglyMeasurable b mu := by
    have hkp : AEStronglyMeasurable (fun y => K y ^ (1 / p)) mu :=
      (hKcont.rpow_const (fun _ _ => Or.inr hrp.symm.one_div_nonneg)).aestronglyMeasurable
        measurableSet_Icc
    exact hkp.mul hf.aestronglyMeasurable.norm
  have ha_mem : MemLp a (ENNReal.ofReal r) mu := by
    apply MemLp.of_bound ha_meas (MK ^ (1 / r))
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    exact Filter.Eventually.of_forall fun y hy => by
      dsimp [a]
      rw [abs_of_nonneg (Real.rpow_nonneg (hKnonneg y) _)]
      exact Real.rpow_le_rpow (hKnonneg y)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)] using hMK y hy)
        hrp.one_div_nonneg
  have hb_mem : MemLp b (ENNReal.ofReal p) mu := by
    apply MemLp.of_le_mul (g := f) (c := MK ^ (1 / p)) hf hb_meas
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    exact Filter.Eventually.of_forall fun y hy => by
      dsimp [b]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (hKnonneg y) _), abs_abs]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hKnonneg y)
          (by simpa [Real.norm_eq_abs, abs_of_nonneg (hKnonneg y)] using hMK y hy)
          hrp.symm.one_div_nonneg)
        (abs_nonneg _)
  have ha_nonneg : 0 ≤ᵐ[mu] a :=
    Filter.Eventually.of_forall fun y => Real.rpow_nonneg (hKnonneg y) _
  have hb_nonneg : 0 ≤ᵐ[mu] b :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg (hKnonneg y) _) (norm_nonneg _)
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) (p := r) (q := p) hrp
    ha_nonneg hb_nonneg ha_mem hb_mem
  have hsum : 1 / r + 1 / p = 1 := by
    simpa [one_div] using hrp.inv_add_inv_eq_one
  have hab : (∫ y, a y * b y ∂mu) = ∫ y, K y * ‖f y‖ ∂mu := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a, b]
      calc
        K y ^ (1 / r) * (K y ^ (1 / p) * ‖f y‖) =
            (K y ^ (1 / r) * K y ^ (1 / p)) * ‖f y‖ := by ring
        _ = K y ^ (1 / r + 1 / p) * ‖f y‖ := by
          rw [Real.rpow_add_of_nonneg (hKnonneg y)
            hrp.one_div_nonneg hrp.symm.one_div_nonneg]
        _ = K y * ‖f y‖ := by rw [hsum, Real.rpow_one]
  have hapow : (∫ y, a y ^ r ∂mu) = ∫ y, K y ∂mu := by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [a]
      rw [one_div, Real.rpow_inv_rpow (hKnonneg y) hrp.ne_zero]
  have hbpow : (∫ y, b y ^ p ∂mu) = B := by
    dsimp [B]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp [b]
      rw [Real.mul_rpow (Real.rpow_nonneg (hKnonneg y) _) (abs_nonneg (f y)),
        one_div, Real.rpow_inv_rpow (hKnonneg y) hrp.symm.ne_zero]
  rw [hab, hapow, hbpow] at hholder
  have hmass : (∫ y, K y ∂mu) ≤ A := by
    dsimp [K, mu, A]
    have hcv :
        (∫ y,
          |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y|
            ∂ intervalMeasure 1) =
          ∫ y in (0 : ℝ)..1,
            |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| := by
      simp only [intervalMeasure, intervalSet]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [hcv]
    exact intervalNeumannFullKernel_deriv_snd_abs_interval_integral_le ht x
  have hmass0 : 0 ≤ ∫ y, K y ∂mu := integral_nonneg fun y => hKnonneg y
  have hmassroot : (∫ y, K y ∂mu) ^ (1 / r) ≤ A ^ (1 / r) :=
    Real.rpow_le_rpow hmass0 hmass hrp.one_div_nonneg
  have hB0 : 0 ≤ B := integral_nonneg fun y =>
    mul_nonneg (hKnonneg y) (Real.rpow_nonneg (norm_nonneg _) p)
  have hkernel : ∫ y, K y * ‖f y‖ ∂mu ≤
      A ^ (1 / r) * B ^ (1 / p) := by
    exact hholder.trans (mul_le_mul_of_nonneg_right hmassroot
      (Real.rpow_nonneg hB0 _))
  have hkernel0 : 0 ≤ ∫ y, K y * ‖f y‖ ∂mu :=
    integral_nonneg fun y => mul_nonneg (hKnonneg y) (norm_nonneg _)
  have hoperator : |intervalConjugateKernelOperator t f x| ≤
      ∫ y, K y * ‖f y‖ ∂mu := by
    unfold intervalConjugateKernelOperator
    rw [abs_neg]
    calc
      |∫ y, deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * f y ∂mu| ≤
          ∫ y, ‖deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y * f y‖ ∂mu := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_integral_norm _
      _ = ∫ y, K y * ‖f y‖ ∂mu := by
        congr 1
        ext y
        rw [norm_mul, Real.norm_eq_abs]
  have hraised := Real.rpow_le_rpow (abs_nonneg _) (hoperator.trans hkernel)
    hrp.symm.nonneg
  calc
    |intervalConjugateKernelOperator t f x| ^ p ≤
        (A ^ (1 / r) * B ^ (1 / p)) ^ p := hraised
    _ = A ^ (p / r) * B := by
      rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB0 _),
        ← Real.rpow_mul hA, ← Real.rpow_mul hB0]
      have hBexp : (1 / p) * p = 1 := by
        field_simp [hrp.symm.ne_zero]
      have hAexp : (1 / r) * p = p / r := by
        field_simp [hrp.ne_zero]
      rw [hBexp, hAexp, Real.rpow_one]
    _ = (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) ^ (p / r) *
        ∫ y,
          |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| *
            ‖f y‖ ^ p ∂ intervalMeasure 1 := rfl

theorem intervalConjugateKernelOperator_Lp_integral_le
    {t r p : ℝ} (ht : 0 < t) (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1)) :
    (∫ x, |intervalConjugateKernelOperator t f x| ^ p
        ∂ intervalMeasure 1) ≤
      (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) ^ p *
        ∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1 := by
  let mu := intervalMeasure 1
  let K : ℝ × ℝ → ℝ := fun z =>
    |intervalNeumannFullKernelDerivSeries t z.2 z.1|
  let F : ℝ × ℝ → ℝ := fun z => K z * ‖f z.2‖ ^ p
  let A : ℝ := heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))
  have hA : 0 ≤ A := mul_nonneg heatGradientLinftyLinftyConstant_nonneg
    (Real.rpow_nonneg ht.le _)
  have hApos : 0 < A := by
    dsimp [A, heatGradientLinftyLinftyConstant]
    positivity
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le_of_gt hrp.symm.pos
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by simp
  have hfp_int : Integrable (fun y => ‖f y‖ ^ p) mu := by
    simpa [mu, ENNReal.toReal_ofReal hrp.symm.nonneg] using
      hf.integrable_norm_rpow hp_ne_zero hp_ne_top
  have hK_meas : Measurable K := by
    dsimp [K]
    change Measurable (fun z : ℝ × ℝ =>
      ‖intervalNeumannFullKernelDerivSeries t z.2 z.1‖)
    exact (intervalNeumannFullKernelDerivSeries_joint_measurable.comp
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).norm
  have hF_meas : AEStronglyMeasurable F (mu.prod mu) := by
    dsimp [F]
    exact hK_meas.aestronglyMeasurable.mul
      hfp_int.aestronglyMeasurable.comp_snd
  have hF_int : Integrable F (mu.prod mu) := by
    refine (MeasureTheory.integrable_prod_iff' hF_meas).2 ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun y => ?_
      have hKsec : Integrable (fun x => K (x, y)) mu := by
        have hcont : ContinuousOn (fun x => K (x, y)) (Icc (0 : ℝ) 1) := by
          simpa [K, intervalNeumannFullKernelDerivSeries_eq_deriv_fst ht] using
            (continuousOn_deriv_intervalNeumannFullKernel_fst ht y).abs
        simpa [mu, intervalMeasure, intervalSet] using hcont.integrableOn_Icc
      exact hKsec.mul_const (‖f y‖ ^ p)
    · have hinner_meas : AEStronglyMeasurable
          (fun y => ∫ x, ‖F (x, y)‖ ∂mu) mu := by
        simpa only [Prod.swap_prod_mk] using
          hF_meas.norm.prod_swap.integral_prod_right'
      apply (hfp_int.const_mul A).mono hinner_meas
      refine Filter.Eventually.of_forall fun y => ?_
      have hKmass : (∫ x, K (x, y) ∂mu) ≤ A := by
        have hcv : (∫ x, K (x, y) ∂mu) =
            ∫ x in (0 : ℝ)..1,
              |deriv (fun z : ℝ => intervalNeumannFullKernel t z x) y| := by
          dsimp [K, mu]
          simp_rw [intervalNeumannFullKernelDerivSeries_eq_deriv_fst ht]
          simp only [intervalMeasure, intervalSet]
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        rw [hcv]
        exact intervalNeumannFullKernel_deriv_abs_interval_integral_le ht y
      have hKnonneg : ∀ x, 0 ≤ K (x, y) := fun x => abs_nonneg _
      calc
        ‖∫ x, ‖F (x, y)‖ ∂mu‖ =
            (∫ x, K (x, y) ∂mu) * ‖f y‖ ^ p := by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
            ← MeasureTheory.integral_mul_const]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp [F]
            rw [abs_of_nonneg]
            exact mul_nonneg (hKnonneg x)
              (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ A * ‖f y‖ ^ p :=
          mul_le_mul_of_nonneg_right hKmass
            (Real.rpow_nonneg (norm_nonneg _) _)
        _ = ‖A * ‖f y‖ ^ p‖ := by
          rw [Real.norm_of_nonneg
            (mul_nonneg hA (Real.rpow_nonneg (norm_nonneg _) _))]
  have hright_int : Integrable
      (fun x => A ^ (p / r) * ∫ y, F (x, y) ∂mu) mu :=
    hF_int.integral_prod_left.const_mul (A ^ (p / r))
  have hfirst :
      (∫ x, |intervalConjugateKernelOperator t f x| ^ p ∂mu) ≤
        A ^ (p / r) * ∫ x, ∫ y, F (x, y) ∂mu ∂mu := by
    calc
      (∫ x, |intervalConjugateKernelOperator t f x| ^ p ∂mu) ≤
          ∫ x, A ^ (p / r) * ∫ y, F (x, y) ∂mu ∂mu := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun x =>
            Real.rpow_nonneg (abs_nonneg _) p
        · exact hright_int
        · exact Filter.Eventually.of_forall fun x => by
            have hx := intervalConjugateKernelOperator_abs_rpow_le
              ht hrp hf x
            have hrewrite :
                (∫ y,
                    |deriv (fun y' : ℝ => intervalNeumannFullKernel t x y') y| *
                      ‖f y‖ ^ p ∂mu) = ∫ y, F (x, y) ∂mu := by
              apply MeasureTheory.integral_congr_ae
              exact Filter.Eventually.of_forall fun y => by
                dsimp [F, K]
                rw [deriv_intervalNeumannFullKernel_snd_eq_fst_swap ht x y,
                  ← intervalNeumannFullKernelDerivSeries_eq_deriv_fst ht y x]
            rw [hrewrite] at hx
            simpa [A, mu] using hx
      _ = A ^ (p / r) * ∫ x, ∫ y, F (x, y) ∂mu ∂mu := by
        rw [MeasureTheory.integral_const_mul]
  have hswap :
      (∫ x, ∫ y, F (x, y) ∂mu ∂mu) =
        ∫ y, ∫ x, F (x, y) ∂mu ∂mu :=
    MeasureTheory.integral_integral_swap (μ := mu) (ν := mu)
      (f := fun x y => F (x, y)) hF_int
  have hsecond :
      (∫ y, ∫ x, F (x, y) ∂mu ∂mu) ≤
        A * ∫ y, ‖f y‖ ^ p ∂mu := by
    calc
      (∫ y, ∫ x, F (x, y) ∂mu ∂mu) ≤
          ∫ y, A * ‖f y‖ ^ p ∂mu := by
        apply MeasureTheory.integral_mono hF_int.integral_prod_right
          (hfp_int.const_mul A)
        intro y
        have hKmass : (∫ x, K (x, y) ∂mu) ≤ A := by
          have hcv : (∫ x, K (x, y) ∂mu) =
              ∫ x in (0 : ℝ)..1,
                |deriv (fun z : ℝ => intervalNeumannFullKernel t z x) y| := by
            dsimp [K, mu]
            simp_rw [intervalNeumannFullKernelDerivSeries_eq_deriv_fst ht]
            simp only [intervalMeasure, intervalSet]
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
              ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
          rw [hcv]
          exact intervalNeumannFullKernel_deriv_abs_interval_integral_le ht y
        calc
          (∫ x, F (x, y) ∂mu) =
              (∫ x, K (x, y) ∂mu) * ‖f y‖ ^ p := by
            dsimp [F]
            rw [MeasureTheory.integral_mul_const]
          _ ≤ A * ‖f y‖ ^ p :=
            mul_le_mul_of_nonneg_right hKmass
              (Real.rpow_nonneg (norm_nonneg _) _)
      _ = A * ∫ y, ‖f y‖ ^ p ∂mu := by
        rw [MeasureTheory.integral_const_mul]
  have hexp : p / r + 1 = p := by
    have hsum := hrp.inv_add_inv_eq_one
    field_simp [hrp.ne_zero, hrp.symm.ne_zero] at hsum ⊢
    linarith
  calc
    (∫ x, |intervalConjugateKernelOperator t f x| ^ p ∂mu) ≤
        A ^ (p / r) * ∫ x, ∫ y, F (x, y) ∂mu ∂mu := hfirst
    _ = A ^ (p / r) * ∫ y, ∫ x, F (x, y) ∂mu ∂mu := by rw [hswap]
    _ ≤ A ^ (p / r) * (A * ∫ y, ‖f y‖ ^ p ∂mu) :=
      mul_le_mul_of_nonneg_left hsecond (Real.rpow_nonneg hA _)
    _ = A ^ p * ∫ y, ‖f y‖ ^ p ∂mu := by
      calc
        A ^ (p / r) * (A * ∫ y, ‖f y‖ ^ p ∂mu) =
            (A ^ (p / r) * A) * ∫ y, ‖f y‖ ^ p ∂mu := by ring
        _ = A ^ (p / r + 1) * ∫ y, ‖f y‖ ^ p ∂mu := by
          congr 1
          calc
            A ^ (p / r) * A = A ^ (p / r) * A ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = A ^ (p / r + 1) := (Real.rpow_add hApos _ _).symm
        _ = A ^ p * ∫ y, ‖f y‖ ^ p ∂mu := by rw [hexp]
    _ = (heatGradientLinftyLinftyConstant * t ^ (-(1 / 2 : ℝ))) ^ p *
        ∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1 := rfl

theorem intervalConjugateKernelOperator_abs_le_Lp_short_half
    {t r p : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hfint : Integrable f (intervalMeasure 1))
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hfbound : ∀ y, |f y| ≤ Cf)
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |intervalConjugateKernelOperator t f x| ≤
      (fullHeatShortConstant * (t / 2) ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (heatGradientLinftyLinftyConstant *
          (t / 2) ^ (-(1 / 2 : ℝ))) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
  let a : ℝ := t / 2
  let A : ℝ := heatGradientLinftyLinftyConstant * a ^ (-(1 / 2 : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hA : 0 ≤ A := mul_nonneg heatGradientLinftyLinftyConstant_nonneg
    (Real.rpow_nonneg ha.le _)
  have hBcont : Continuous
      (fun y => intervalConjugateKernelOperator a f y) := by
    have hBdiff : Differentiable ℝ
        (fun y => intervalConjugateKernelOperator a f y) := fun y =>
      (intervalConjugateKernelOperator_hasDerivAt ha hfint hfbound y).differentiableAt
    exact hBdiff.continuous
  have hBbound : ∀ y,
      |intervalConjugateKernelOperator a f y| ≤ A * Cf := by
    intro y
    simpa [A] using intervalConjugateKernelOperator_abs_le ha hfint hfbound y
  have hBmem : MemLp (fun y => intervalConjugateKernelOperator a f y)
      (ENNReal.ofReal p) (intervalMeasure 1) := by
    apply MemLp.of_bound hBcont.aestronglyMeasurable (A * Cf)
    exact Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hBbound y
  have hcomp := intervalFullSemigroupOperator_comp_conjugateKernel
    ha ha hfcont hfint hfbound hx
  have hheat := intervalFullSemigroupOperator_abs_le_Lp_short
    ha ha1 hrp hBmem x
  have hI0 : 0 ≤
      ∫ y, ‖intervalConjugateKernelOperator a f y‖ ^ p
        ∂ intervalMeasure 1 :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) p
  have hJ0 : 0 ≤ ∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1 :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) p
  have hLp := intervalConjugateKernelOperator_Lp_integral_le ha hrp hf
  have hroot := Real.rpow_le_rpow hI0 hLp hrp.symm.one_div_nonneg
  have hAp : (A ^ p * ∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) =
      A * (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
    have hApos : 0 < A := by
      dsimp [A, heatGradientLinftyLinftyConstant]
      positivity
    rw [Real.mul_rpow (Real.rpow_nonneg hA p) hJ0,
      ← Real.rpow_mul hA]
    have hexp : p * (1 / p) = 1 := by
      field_simp [hrp.symm.ne_zero]
    rw [hexp, Real.rpow_one]
  have hroot' :
      (∫ y, ‖intervalConjugateKernelOperator a f y‖ ^ p
          ∂ intervalMeasure 1) ^ (1 / p) ≤
        A * (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
    exact hroot.trans_eq hAp
  rw [show a + a = t by dsimp [a]; ring] at hcomp
  rw [← hcomp]
  calc
    |intervalFullSemigroupOperator a
        (fun y => intervalConjugateKernelOperator a f y) x| ≤
      (fullHeatShortConstant * a ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (∫ y, ‖intervalConjugateKernelOperator a f y‖ ^ p
          ∂ intervalMeasure 1) ^ (1 / p) := hheat
    _ ≤ (fullHeatShortConstant * a ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (A * (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p)) :=
      mul_le_mul_of_nonneg_left hroot'
        (Real.rpow_nonneg
          (mul_nonneg fullHeatShortConstant_nonneg
            (Real.rpow_nonneg ha.le _)) _)
    _ = (fullHeatShortConstant * (t / 2) ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (heatGradientLinftyLinftyConstant *
          (t / 2) ^ (-(1 / 2 : ℝ))) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
      dsimp [a, A]
      ring

noncomputable def conjugateLpLinftyTheta (p : ℝ) : ℝ :=
  1 / 2 + 1 / (2 * p)

noncomputable def conjugateLpLinftyConstant (p : ℝ) : ℝ :=
  (fullHeatShortConstant * 2 ^ (1 / 2 : ℝ)) ^ (1 / p) *
    (heatGradientLinftyLinftyConstant * 2 ^ (1 / 2 : ℝ))

theorem conjugateLpLinftyTheta_pos {p : ℝ} (hp : 0 < p) :
    0 < conjugateLpLinftyTheta p := by
  simp only [conjugateLpLinftyTheta]
  have : 0 < 1 / (2 * p) := by positivity
  linarith

theorem conjugateLpLinftyTheta_lt_one {p : ℝ} (hp : 1 < p) :
    conjugateLpLinftyTheta p < 1 := by
  simp only [conjugateLpLinftyTheta]
  have h2p : 2 < 2 * p := by linarith
  have hinv : 1 / (2 * p) < 1 / 2 := by
    exact one_div_lt_one_div_of_lt (by norm_num) h2p
  linarith

theorem intervalIntegrable_sub_rpow_neg_conjugateTheta
    {p r : ℝ} (hp : 1 < p) :
    IntervalIntegrable
      (fun s : ℝ => (r - s) ^ (-conjugateLpLinftyTheta p))
      volume 0 r := by
  have h0 : IntervalIntegrable
      (fun x : ℝ => x ^ (-conjugateLpLinftyTheta p)) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow'
      (by linarith [conjugateLpLinftyTheta_lt_one hp])
  simpa using (h0.comp_sub_left r).symm

theorem integral_sub_rpow_neg_conjugateTheta
    {p r : ℝ} (hp : 1 < p) (hr : 0 ≤ r) :
    (∫ s in (0 : ℝ)..r,
      (r - s) ^ (-conjugateLpLinftyTheta p)) =
      r ^ (1 - conjugateLpLinftyTheta p) /
        (1 - conjugateLpLinftyTheta p) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun x : ℝ => x ^ (-conjugateLpLinftyTheta p)) r]
  simp only [sub_self, sub_zero]
  rw [integral_rpow
    (Or.inl (by linarith [conjugateLpLinftyTheta_lt_one hp]))]
  have hne : 1 - conjugateLpLinftyTheta p ≠ 0 := by
    linarith [conjugateLpLinftyTheta_lt_one hp]
  rw [show -conjugateLpLinftyTheta p + 1 =
      1 - conjugateLpLinftyTheta p by ring,
    Real.zero_rpow hne, sub_zero]

theorem half_rpow_neg_half
    {t : ℝ} (ht : 0 < t) :
    (t / 2) ^ (-(1 / 2 : ℝ)) =
      2 ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.div_rpow ht.le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

theorem conjugateLpLinfty_half_factor_eq
    {t p : ℝ} (ht : 0 < t) (hp : 0 < p) :
    (fullHeatShortConstant * (t / 2) ^ (-(1 / 2 : ℝ))) ^ (1 / p) *
        (heatGradientLinftyLinftyConstant *
          (t / 2) ^ (-(1 / 2 : ℝ))) =
      conjugateLpLinftyConstant p *
        t ^ (-conjugateLpLinftyTheta p) := by
  rw [half_rpow_neg_half ht]
  have hH : 0 ≤ fullHeatShortConstant * 2 ^ (1 / 2 : ℝ) :=
    mul_nonneg fullHeatShortConstant_nonneg
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  have htneg : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  rw [show fullHeatShortConstant *
      (2 ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ))) =
        (fullHeatShortConstant * 2 ^ (1 / 2 : ℝ)) *
          t ^ (-(1 / 2 : ℝ)) by ring,
    Real.mul_rpow hH htneg]
  have htpow :
      (t ^ (-(1 / 2 : ℝ))) ^ (1 / p) =
        t ^ (-(1 / (2 * p) : ℝ)) := by
    rw [← Real.rpow_mul ht.le]
    congr 1
    field_simp [ne_of_gt hp]
  rw [htpow]
  have hexp :
      t ^ (-(1 / (2 * p) : ℝ)) * t ^ (-(1 / 2 : ℝ)) =
        t ^ (-conjugateLpLinftyTheta p) := by
    rw [← Real.rpow_add ht]
    congr 1
    simp only [conjugateLpLinftyTheta]
    ring
  rw [show
    ((fullHeatShortConstant * 2 ^ (1 / 2 : ℝ)) ^ (1 / p) *
        t ^ (-(1 / (2 * p) : ℝ))) *
      (heatGradientLinftyLinftyConstant *
        (2 ^ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)))) =
      ((fullHeatShortConstant * 2 ^ (1 / 2 : ℝ)) ^ (1 / p) *
        (heatGradientLinftyLinftyConstant * 2 ^ (1 / 2 : ℝ))) *
      (t ^ (-(1 / (2 * p) : ℝ)) * t ^ (-(1 / 2 : ℝ))) by ring,
    hexp]
  rfl

theorem intervalConjugateKernelOperator_abs_le_Lp_short
    {t r p : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hrp : r.HolderConjugate p)
    {f : ℝ → ℝ} (hfcont : Continuous f)
    (hfint : Integrable f (intervalMeasure 1))
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hfbound : ∀ y, |f y| ≤ Cf)
    (hf : MemLp f (ENNReal.ofReal p) (intervalMeasure 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |intervalConjugateKernelOperator t f x| ≤
      conjugateLpLinftyConstant p *
        t ^ (-conjugateLpLinftyTheta p) *
        (∫ y, ‖f y‖ ^ p ∂ intervalMeasure 1) ^ (1 / p) := by
  rw [← conjugateLpLinfty_half_factor_eq ht hrp.symm.pos]
  exact intervalConjugateKernelOperator_abs_le_Lp_short_half
    ht ht1 hrp hfcont hfint hCf hfbound hf hx

#print axioms intervalNeumannFullKernel_abs_le_short
#print axioms intervalFullSemigroupOperator_abs_le_Lp_short
#print axioms intervalConjugateKernelOperator_Lp_integral_le
#print axioms intervalConjugateKernelOperator_abs_le_Lp_short_half
#print axioms intervalConjugateKernelOperator_abs_le_Lp_short

end ShenWork.Paper2.IntervalDomainRestartedLpLinf
