import ShenWork.Paper2.IntervalNegativePartWeakEnergy
import ShenWork.Paper2.IntervalDuhamelIntegrability
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# `L^p` contraction of the full Neumann heat kernel

This file proves the Markov-kernel estimate used by Paper 2 Proposition 2.1.
The proof is the direct Jensen argument for the positive, mass-one, symmetric
full Neumann kernel on `[0,1]`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace ShenWork.Paper2.IntervalFullKernelLpContraction

open ShenWork.IntervalDomain (intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2.IntervalNegativePartWeakEnergy

/-- Pointwise Jensen inequality for the full Neumann Markov kernel. -/
theorem intervalFullSemigroupOperator_abs_rpow_le
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q)
    {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalFullSemigroupOperator t f x| ^ q ≤
      intervalFullSemigroupOperator t (fun y => |f y| ^ q) x := by
  let K : ℝ → ℝ := fun y => intervalNeumannFullKernel t x y
  let Kd : ℝ → ENNReal := fun y => ENNReal.ofReal (K y)
  let μK := (intervalMeasure 1).withDensity Kd
  have hK_nn : ∀ y, 0 ≤ K y := fun y => intervalNeumannFullKernel_nonneg ht x y
  have hK_int : Integrable K (intervalMeasure 1) := by
    simpa [K] using intervalNeumannFullKernel_integrable ht x
  have hKd_aem : AEMeasurable Kd (intervalMeasure 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      hK_int.aestronglyMeasurable.aemeasurable
  have hKd_ae_lt : ∀ᵐ y ∂(intervalMeasure 1), Kd y < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hKd_toReal : ∀ y, (Kd y).toReal = K y := by
    intro y
    simp [Kd, ENNReal.toReal_ofReal (hK_nn y)]
  have hmassK : ∫ y, K y ∂(intervalMeasure 1) = 1 := by
    simpa [K] using
      intervalNeumannFullKernel_intervalMeasure_integral_eq_one ht x
  have hμK_mass : μK Set.univ = 1 := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hK_int
        (Filter.Eventually.of_forall hK_nn)]
    simp [hmassK]
  haveI : IsProbabilityMeasure μK := ⟨hμK_mass⟩
  have hM_nonneg : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf_bdd 0)
  have habs_meas : AEStronglyMeasurable (fun y => |f y|)
      (intervalMeasure 1) := hf_meas.norm
  have hrpow_meas : AEStronglyMeasurable (fun y => |f y| ^ q)
      (intervalMeasure 1) :=
    (continuous_abs.rpow_const (fun _ => Or.inr (zero_le_one.trans hq))).comp_aestronglyMeasurable
      hf_meas
  have habs_bdd : ∀ y, ‖|f y|‖ ≤ M := by
    intro y
    rw [Real.norm_eq_abs, abs_abs]
    exact hf_bdd y
  have hrpow_bdd : ∀ y, ‖|f y| ^ q‖ ≤ M ^ q := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hf_bdd y) (zero_le_one.trans hq)
  have hKabs_int : Integrable (fun y => K y * |f y|) (intervalMeasure 1) := by
    have hmul : Integrable (fun y => |f y| * K y) (intervalMeasure 1) :=
      hK_int.bdd_mul habs_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_abs]
          exact hf_bdd y)
    exact hmul.congr (Eventually.of_forall fun y => by ring)
  have hKrpow_int : Integrable (fun y => K y * |f y| ^ q)
      (intervalMeasure 1) := by
    have hmul : Integrable (fun y => |f y| ^ q * K y) (intervalMeasure 1) :=
      hK_int.bdd_mul hrpow_meas
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact hrpow_bdd y)
    exact hmul.congr (Eventually.of_forall fun y => by ring)
  have habs_int_μK : Integrable (fun y => |f y|) μK := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀' hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • |f y|) = fun y => K y * |f y| by
        ext y
        simp [hKd_toReal, smul_eq_mul]]
    exact hKabs_int
  have hrpow_int_μK : Integrable (fun y => |f y| ^ q) μK := by
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integrable_withDensity_iff_integrable_smul₀' hKd_aem hKd_ae_lt,
      show (fun y => (Kd y).toReal • |f y| ^ q) =
          fun y => K y * |f y| ^ q by
        ext y
        simp [hKd_toReal, smul_eq_mul]]
    exact hKrpow_int
  have hint_rel : ∀ g : ℝ → ℝ,
      ∫ y, g y ∂μK = ∫ y, K y * g y ∂(intervalMeasure 1) := by
    intro g
    rw [show μK = (intervalMeasure 1).withDensity Kd from rfl,
      integral_withDensity_eq_integral_toReal_smul₀ hKd_aem hKd_ae_lt]
    congr 1
    ext y
    simp [hKd_toReal, smul_eq_mul]
  have hJ := (convexOn_rpow hq).map_integral_le
    ((continuous_id.rpow_const (fun _ => Or.inr (zero_le_one.trans hq))).continuousOn)
    isClosed_Ici
    (Filter.Eventually.of_forall fun y => abs_nonneg (f y))
    habs_int_μK hrpow_int_μK
  rw [hint_rel (fun y => |f y|), hint_rel (fun y => |f y| ^ q)] at hJ
  have habs_int :
      |∫ y, K y * f y ∂(intervalMeasure 1)| ≤
        ∫ y, K y * |f y| ∂(intervalMeasure 1) := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ y, K y * f y ∂(intervalMeasure 1)‖ ≤
          ∫ y, ‖K y * f y‖ ∂(intervalMeasure 1) :=
        norm_integral_le_integral_norm _
      _ = ∫ y, K y * |f y| ∂(intervalMeasure 1) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          change ‖K y * f y‖ = K y * |f y|
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK_nn y)]
  calc
    |intervalFullSemigroupOperator t f x| ^ q
        ≤ (∫ y, K y * |f y| ∂(intervalMeasure 1)) ^ q :=
      Real.rpow_le_rpow (abs_nonneg _) habs_int (zero_le_one.trans hq)
    _ ≤ ∫ y, K y * |f y| ^ q ∂(intervalMeasure 1) := hJ
    _ = intervalFullSemigroupOperator t (fun y => |f y| ^ q) x := by
      rfl

/-- Integral form of the Markov contraction: the full Neumann heat operator
does not increase the `q`-th absolute moment for `q ≥ 1`. -/
theorem intervalFullSemigroupOperator_integral_abs_rpow_le
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q)
    {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M) :
    (∫ x, |intervalFullSemigroupOperator t f x| ^ q ∂(intervalMeasure 1)) ≤
      ∫ y, |f y| ^ q ∂(intervalMeasure 1) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hM : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf_bdd 0)
  have hsrc_meas : AEStronglyMeasurable (fun y => |f y| ^ q)
      (intervalMeasure 1) :=
    (continuous_abs.rpow_const (fun _ => Or.inr hq0)).comp_aestronglyMeasurable
      hf_meas
  have hMq : 0 ≤ M ^ q := Real.rpow_nonneg hM q
  have hsrc_bdd : ∀ y, ‖|f y| ^ q‖ ≤ M ^ q := by
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hf_bdd y) hq0
  have hsrc_int : Integrable (fun y => |f y| ^ q) (intervalMeasure 1) := by
    exact (integrable_const (M ^ q)).mono' hsrc_meas
      (Filter.Eventually.of_forall hsrc_bdd)
  have hSsrc_cont : Continuous
      (fun x => intervalFullSemigroupOperator t (fun y => |f y| ^ q) x) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ht hMq (fun y => by
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hf_bdd y) hq0)
      hsrc_meas
  have hSsrc_int : Integrable
      (fun x => intervalFullSemigroupOperator t (fun y => |f y| ^ q) x)
      (intervalMeasure 1) := by
    have hi : IntegrableOn
        (fun x => intervalFullSemigroupOperator t (fun y => |f y| ^ q) x)
        (Set.Icc (0 : ℝ) 1) volume :=
      hSsrc_cont.continuousOn.integrableOn_Icc
    simpa [ShenWork.IntervalDomain.intervalMeasure,
      ShenWork.IntervalDomain.intervalSet] using hi
  have hleft_nonneg : 0 ≤ᵐ[intervalMeasure 1]
      (fun x => |intervalFullSemigroupOperator t f x| ^ q) :=
    Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hpoint : (∀ᵐ x ∂(intervalMeasure 1),
      |intervalFullSemigroupOperator t f x| ^ q ≤
        intervalFullSemigroupOperator t (fun y => |f y| ^ q) x) :=
    Filter.Eventually.of_forall fun x =>
      intervalFullSemigroupOperator_abs_rpow_le ht hq hf_meas hf_bdd x
  calc
    (∫ x, |intervalFullSemigroupOperator t f x| ^ q ∂(intervalMeasure 1)) ≤
        ∫ x, intervalFullSemigroupOperator t (fun y => |f y| ^ q) x
          ∂(intervalMeasure 1) :=
      integral_mono_of_nonneg hleft_nonneg hSsrc_int hpoint
    _ = ∫ y, |f y| ^ q ∂(intervalMeasure 1) :=
      intervalFullSemigroupOperator_integral_eq ht hsrc_meas hsrc_int

/-- Real-valued `L^q` contraction for the full Neumann heat operator. -/
theorem intervalFullSemigroupOperator_lpNorm_le
    {t q : ℝ} (ht : 0 < t) (hq : 1 ≤ q)
    {f : ℝ → ℝ} {M : ℝ}
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hf_bdd : ∀ y, |f y| ≤ M) :
    lpNorm (intervalFullSemigroupOperator t f) (ENNReal.ofReal q)
        (intervalMeasure 1) ≤
      lpNorm f (ENNReal.ofReal q) (intervalMeasure 1) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hM : 0 ≤ M := le_trans (abs_nonneg (f 0)) (hf_bdd 0)
  have hSf_cont : Continuous (fun x => intervalFullSemigroupOperator t f x) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      ht hM hf_bdd hf_meas
  have hSf_meas : AEStronglyMeasurable (intervalFullSemigroupOperator t f)
      (intervalMeasure 1) := hSf_cont.aestronglyMeasurable
  have hq_ne_zero : ENNReal.ofReal q ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hqpos)
  have hq_ne_top : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [lpNorm_eq_integral_norm_rpow_toReal hq_ne_zero hq_ne_top hSf_meas,
    lpNorm_eq_integral_norm_rpow_toReal hq_ne_zero hq_ne_top hf_meas,
    ENNReal.toReal_ofReal hq0]
  have hint := intervalFullSemigroupOperator_integral_abs_rpow_le
    ht hq hf_meas hf_bdd
  simpa [Real.norm_eq_abs] using
    Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)
      hint (one_div_nonneg.mpr hq0)

#print axioms intervalFullSemigroupOperator_abs_rpow_le
#print axioms intervalFullSemigroupOperator_integral_abs_rpow_le
#print axioms intervalFullSemigroupOperator_lpNorm_le

end ShenWork.Paper2.IntervalFullKernelLpContraction
