import ShenWork.Paper2.IntervalBFormCron2SemigroupWeakDuhamel

open MeasureTheory

noncomputable section

namespace ShenWork.IntervalNHGBrickB

open scoped Real ENNReal
open ShenWork.IntervalDomain
open ShenWork.CosineParsevalBridge
open ShenWork.HeatKernelGradientEstimates

/-- `|·|` is quasi measure preserving from the doubled interval to the unit interval. -/
theorem abs_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun x : ℝ => |x|)
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  refine ⟨continuous_abs.measurable, Measure.AbsolutelyContinuous.mk (fun s hs hs0 => ?_)⟩
  -- s measurable, (restrict Icc) s = 0; show ((restrict Ioc).map abs) s = 0
  rw [Measure.restrict_apply hs] at hs0
  rw [Measure.map_apply continuous_abs.measurable hs,
    Measure.restrict_apply (continuous_abs.measurable hs)]
  refine measure_mono_null (t := (s ∩ Set.Icc (0:ℝ) 1)
      ∪ (Neg.neg ⁻¹' (s ∩ Set.Icc (0:ℝ) 1))) ?_ ?_
  · intro x hx
    obtain ⟨hxs, hxIoc⟩ := hx
    simp only [Set.mem_preimage] at hxs
    rcases le_or_gt 0 x with hx0 | hx0
    · left; exact ⟨by rwa [abs_of_nonneg hx0] at hxs, hx0, hxIoc.2⟩
    · right
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Icc]
      refine ⟨by rwa [abs_of_neg hx0] at hxs, by linarith, by linarith [hxIoc.1]⟩
  · rw [measure_union_null_iff]
    refine ⟨hs0, ?_⟩
    have hqmp : Measure.QuasiMeasurePreserving (Neg.neg : ℝ → ℝ) volume volume :=
      (Measure.measurePreserving_neg volume).quasiMeasurePreserving
    exact hqmp.preimage_null hs0

/-- The even reflection of an `L²` interval function is `MemLp 2` on the doubled interval. -/
theorem evenReflection_memLp_two_of_memLp
    {f : ℝ → ℝ} (hf : MemLp f 2 (intervalMeasure 1)) :
    MemLp (unitIntervalEvenReflection (fun x => (f x : ℂ))) 2
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) := by
  set fc : ℝ → ℂ := fun x => (f x : ℂ) with hfc
  have hfmem : MemLp f 2 (volume.restrict (Set.Icc (0:ℝ) 1)) := hf
  have hfcmem : MemLp fc 2 (volume.restrict (Set.Icc (0:ℝ) 1)) := hfmem.ofReal
  -- AEStronglyMeasurable of the reflection via the QMP of |·|
  have hAESM : AEStronglyMeasurable (unitIntervalEvenReflection fc)
      (volume.restrict (Set.Ioc (-1:ℝ) 1)) := by
    have hcomp : AEStronglyMeasurable (fc ∘ (fun x => |x|))
        (volume.restrict (Set.Ioc (-1:ℝ) 1)) :=
      hfcmem.1.comp_quasiMeasurePreserving abs_quasiMeasurePreserving
    refine hcomp.congr (Filter.Eventually.of_forall (fun x => ?_))
    rfl
  -- Integrable ‖reflection‖² on Ioc(-1)1 via the value lemma + IntervalIntegrable f²
  have hf_sq_II : IntervalIntegrable (fun x : ℝ => ‖fc x‖ ^ 2) volume 0 1 := by
    have hint : Integrable (fun x => (f x) ^ 2) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      hfmem.integrable_sq
    have : IntegrableOn (fun x => ‖fc x‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume := by
      have h2 : IntegrableOn (fun x => (f x) ^ 2) (Set.Icc (0:ℝ) 1) volume := hint
      refine (h2.mono_set Set.Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
      intro x _; simp [hfc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact this
  -- MemLp via integrable ‖·‖² on the doubled interval
  rw [memLp_two_iff_integrable_sq_norm hAESM]
  -- ‖reflection‖² is integrable on Ioc(-1)1 (mass = 2∫₀¹‖f‖² < ∞)
  have hrefl_II : IntervalIntegrable
      (fun x => ‖unitIntervalEvenReflection fc x‖ ^ 2) volume (-1) 1 := by
    have hII01 : IntervalIntegrable
        (fun x => ‖unitIntervalEvenReflection fc x‖ ^ 2) volume 0 1 := by
      refine hf_sq_II.congr (fun x hx => ?_)
      have hx0 : 0 ≤ x := by
        have : x ∈ Set.Ioc (0:ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
        exact this.1.le
      simp [unitIntervalEvenReflection, abs_of_nonneg hx0]
    have hIIneg : IntervalIntegrable
        (fun x => ‖unitIntervalEvenReflection fc x‖ ^ 2) volume (-1) 0 := by
      have hcomp : IntervalIntegrable
          (fun x => (fun y => ‖unitIntervalEvenReflection fc y‖ ^ 2) (-x)) volume 0 (-1) := by
        simpa only [neg_zero] using
          (IntervalIntegrable.iff_comp_neg
            (f := fun y => ‖unitIntervalEvenReflection fc y‖ ^ 2) (a := 0) (b := 1)).mp hII01
      exact hcomp.symm.congr (fun x _ => by
        simp [unitIntervalEvenReflection_apply_neg])
    exact hIIneg.trans hII01
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hrefl_II
  exact hrefl_II

open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

/-- From `MemLp f 2 (intervalMeasure 1)`, the Neumann cosine coefficients are `ℓ²`
and obey the Bessel bound `√(Σ cₙ²) ≤ 2·√(∫₀¹ f²)`. -/
theorem cosineCoeffs_l2_of_memLp
    {f : ℝ → ℝ} (hf : MemLp f 2 (intervalMeasure 1)) :
    Summable (fun n => (cosineCoeffs f n) ^ 2) ∧
      Real.sqrt (∑' n, (cosineCoeffs f n) ^ 2)
        ≤ 2 * Real.sqrt (∫ x in (0 : ℝ)..1, (f x) ^ 2) := by
  set fc : ℝ → ℂ := fun x => (f x : ℂ) with hfc
  have hfmem : MemLp f 2 (volume.restrict (Set.Icc (0:ℝ) 1)) := hf
  -- IntervalIntegrable fc on [0,1]
  have hfc_II : IntervalIntegrable fc volume 0 1 := by
    have hfL1 : Integrable f (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      memLp_one_iff_integrable.1 (hfmem.mono_exponent (by norm_num))
    have : IntegrableOn fc (Set.Ioc (0:ℝ) 1) volume := by
      have h2 : IntegrableOn f (Set.Icc (0:ℝ) 1) volume := hfL1
      exact (h2.mono_set Set.Ioc_subset_Icc_self).ofReal
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- IntervalIntegrable ‖fc‖² on [0,1]
  have hfc_sq_II : IntervalIntegrable (fun x : ℝ => ‖fc x‖ ^ 2) volume 0 1 := by
    have hint : Integrable (fun x => (f x) ^ 2) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
      hfmem.integrable_sq
    have : IntegrableOn (fun x => ‖fc x‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume := by
      have h2 : IntegrableOn (fun x => (f x) ^ 2) (Set.Icc (0:ℝ) 1) volume := hint
      refine (h2.mono_set Set.Ioc_subset_Icc_self).congr_fun ?_ measurableSet_Ioc
      intro x _; simp [hfc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hL2 := evenReflection_memLp_two_of_memLp hf
  obtain ⟨hsum, hbound⟩ := unitIntervalNeumannCosineCoeff_l2_bound hfc_II hL2 hfc_sq_II
  -- transfer to cosineCoeffs (definitionally unitIntervalNeumannCosineCoeff fc)
  constructor
  · exact hsum
  · -- ‖fc x‖² = (f x)²
    have hnormsq : (∫ x in (0:ℝ)..1, ‖fc x‖ ^ 2) = ∫ x in (0:ℝ)..1, (f x) ^ 2 := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp [hfc, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h2 : Real.sqrt (∑' n, (cosineCoeffs f n) ^ 2)
        = unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff fc) := by
      rw [unitIntervalCosineL2TsumNorm, unitIntervalCosineL2TsumEnergy]
      rfl
    rw [h2]
    calc unitIntervalCosineL2TsumNorm (unitIntervalNeumannCosineCoeff fc)
        ≤ 2 * Real.sqrt (∫ x in (0:ℝ)..1, ‖fc x‖ ^ 2) := hbound
      _ = 2 * Real.sqrt (∫ x in (0:ℝ)..1, (f x) ^ 2) := by rw [hnormsq]

end ShenWork.IntervalNHGBrickB
