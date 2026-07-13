import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalPicardIterateInitialApproach
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory Filter Topology Set
open scoped BigOperators

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugateMildSolutionData conjugateMildSolutionData_of_data
   conjugatePicardLimit)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormInitialTrace

/-- Uniform chemotaxis-flux bound on the ball carried by the B-form Picard data. -/
theorem chemFluxLifted_bound_of_ball
    (p : CM2Params) {M : ℝ} (hM_nonneg : 0 ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hw_bound : ∀ x, |w x| ≤ M)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_cont : Continuous w) :
    ∀ y : ℝ,
      |chemFluxLifted p w y| ≤
        M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * M ^ p.γ))) := by
  intro y
  set C_RG := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)))
  unfold chemFluxLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [this]
      exact hw_cont
    have hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift w x := by
      intro x hx
      simp [intervalDomainLift, hx, hw_nonneg ⟨x, hx⟩]
    have hgrad :
        |ShenWork.Paper2.resolverGradReal p w y| ≤ C_RG := by
      have hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift w x ≤ M := by
        intro x hx
        calc intervalDomainLift w x
            ≤ |intervalDomainLift w x| := le_abs_self _
          _ ≤ M := by
              simpa [intervalDomainLift, hx] using hw_bound ⟨x, hx⟩
      simpa [C_RG] using
        ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
          p hcont_on hlb hub hy
    have hlift : |intervalDomainLift w y| ≤ M := by
      simpa [intervalDomainLift, hy] using hw_bound ⟨y, hy⟩
    have hR_nonneg_pt :
        0 ≤ intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y := by
      have hcont_src : Continuous (fun x : intervalDomainPoint => p.ν * (w x) ^ p.γ) :=
        continuous_const.mul (hw_cont.rpow_const (fun x => Or.inr p.hγ.le))
      set clip : ℝ → intervalDomainPoint := fun x =>
        ⟨max 0 (min x 1), le_max_left 0 _,
          max_le (by norm_num) (min_le_right x 1)⟩
      have hclip_cont : Continuous clip :=
        Continuous.subtype_mk
          (continuous_const.max (continuous_id.min continuous_const)) _
      set f : ℝ → ℝ :=
        (fun x : intervalDomainPoint => p.ν * (w x) ^ p.γ) ∘ clip
      have hf_cont : Continuous f := hcont_src.comp hclip_cont
      have hf_nonneg : ∀ z, 0 ≤ f z := fun z =>
        mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
      have hf_coeff : ∀ k, ShenWork.IntervalNeumannFullKernel.cosineCoeffs f k =
          (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re := by
        intro k
        have hsrc_eq :
            (ShenWork.PDE.intervalNeumannResolverSourceCoeff p w k).re =
            ShenWork.IntervalNeumannFullKernel.cosineCoeffs
              (fun x => p.ν * intervalDomainLift w x ^ p.γ) k := by
          simp [ShenWork.IntervalNeumannFullKernel.cosineCoeffs,
            ShenWork.PDE.intervalNeumannResolverSourceCoeff, Complex.ofReal_re]
        rw [hsrc_eq]
        exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc (fun x hx => by
          simp only [f, Function.comp, clip]
          have hclip_eq : max 0 (min x 1) = x := by
            rw [min_eq_left hx.2, max_eq_right hx.1]
          simp only [hclip_eq, intervalDomainLift,
            dif_pos (Set.mem_Icc.mpr hx)]) k
      have hâ : Summable (fun k =>
          (ShenWork.IntervalNeumannFullKernel.cosineCoeffs f k) ^ 2) := by
        have h :=
          ShenWork.IntervalResolverWeakBounds.resolverSourceCoeff_re_sq_summable_of_continuousOn
            p hcont_on
        simp only [ShenWork.Paper2.intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
        exact h.congr (fun k => by rw [hf_coeff])
      have hR_nonneg_sub :
          0 ≤ ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ :=
        ShenWork.IntervalResolverPositivity.intervalNeumannResolverR_nonneg_of_nonneg_source
          hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
      have hR_lift_eq :
          intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y =
            ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ := by
        simp [intervalDomainLift, hy]
      simpa [hR_lift_eq] using hR_nonneg_sub
    have hR_lift_eq :
        intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y =
          ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ := by
      simp [intervalDomainLift, hy]
    have hden_ge_one :
        1 ≤ (1 + intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β := by
      rw [hR_lift_eq]
      exact Real.one_le_rpow (by linarith [hR_nonneg_pt]) p.hβ
    calc |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y /
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β|
        = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| /
          |(1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β| :=
          abs_div _ _
      _ ≤ |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          rwa [abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos
            (by rw [hR_lift_eq]; linarith [hR_nonneg_pt]) p.β))]
      _ = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| := by
          rw [div_one]
      _ ≤ |intervalDomainLift w y| * |ShenWork.Paper2.resolverGradReal p w y| :=
          le_of_eq (abs_mul _ _)
      _ ≤ M * C_RG :=
          mul_le_mul hlift hgrad (abs_nonneg _) hM_nonneg
  · have hzero :
        intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y /
            (1 + intervalDomainLift
              (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β =
          0 := by
      rw [show intervalDomainLift w y = 0 by simp [intervalDomainLift, hy],
        zero_mul, zero_div]
    rw [hzero, abs_zero]
    exact mul_nonneg hM_nonneg hC_RG_nn

/-- B-form Duhamel `√T` bound with the time integrability discharged by
`integral_undef` when the interval-integrability obligation is absent. -/
theorem conjugateDuhamel_sup_bound_of_integrable_sources
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) {q : ℝ → ℝ → ℝ}
    (hq_int : ∀ s, Integrable (q s) (intervalMeasure 1))
    {Cq : ℝ} (hCq : 0 ≤ Cq) (hq_sup : ∀ s y, |q s y| ≤ Cq) (x : ℝ) :
    |∫ s in (0:ℝ)..t, intervalConjugateKernelOperator (t - s) (q s) x|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * Cq := by
  by_cases hB_int : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x)
      volume 0 t
  · exact ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
      ht htT (fun s _ _ => hq_int s) hCq (fun s _ _ => hq_sup s) x hB_int
  · rw [intervalIntegral.integral_undef hB_int, abs_zero]
    exact mul_nonneg
      (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg T)))
      hCq

/-- B-form Picard map approaches the initial datum as `t → 0+`.  The proof
consumes the homogeneous semigroup initial approach and the two Duhamel
small-time bounds. -/
theorem intervalConjugateDuhamelMap_initialApproach_of_solution_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : ConjugateMildSolutionData p u₀) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀
            (D.u) t x - u₀ x| < ε := by
  intro ε hε
  set M : ℝ := D.M with hMdef
  have hM_pos : 0 < M := by simpa [M] using D.hM
  have hM_nonneg : 0 ≤ M := hM_pos.le
  set C_L : ℝ := M * (p.a + p.b * M ^ p.α) with hCLdef
  have hCL_nonneg : 0 ≤ C_L :=
    mul_nonneg hM_nonneg
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg hM_nonneg _)))
  set C_Q : ℝ := M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ))) with hCQdef
  have hCQ_nonneg : 0 ≤ C_Q := by
    rw [hCQdef]
    exact mul_nonneg hM_nonneg
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _))))
  set A_corr : ℝ := 2 * |p.χ₀| * heatGradientLinftyLinftyConstant * C_Q
    with hAdef
  have hA_nonneg : 0 ≤ A_corr := by
    rw [hAdef]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg p.χ₀))
        heatGradientLinftyLinftyConstant_nonneg)
      hCQ_nonneg
  obtain ⟨δS, hδS, hSclose⟩ :=
    ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
      p hu₀_cont (ε / 2) (by linarith)
  obtain ⟨δD, hδD, hDsmall⟩ :=
    exists_small_contraction_time_target hA_nonneg hCL_nonneg
      (show 0 < ε / 2 by linarith)
  refine ⟨min (min δS δD) D.T, lt_min (lt_min hδS hδD) D.hT, ?_⟩
  intro t ht htδ x
  have htδS : t < δS :=
    lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_left _ _))
  have htδD : t < δD :=
    lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_right _ _))
  have htT_lt : t < D.T := lt_of_lt_of_le htδ (min_le_right _ _)
  have htT : t ≤ D.T := le_of_lt htT_lt
  have hSg_close :
      |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1 - u₀ x| < ε / 2 :=
    hSclose t ht htδS x
  set r_chem : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then
      chemFluxLifted p ((D.u) s) y
    else 0
  have hr_chem_bound : ∀ s y, |r_chem s y| ≤ C_Q := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ D.T
    · have h :=
        chemFluxLifted_bound_of_ball p hM_nonneg
          (by simpa [M] using D.hbound s hs.1 hs.2)
          (by simpa using D.hnonneg s hs.1 hs.2)
          (by simpa using D.hcont s hs.1 hs.2) y
      simpa [r_chem, hs, C_Q, hCQdef, M] using h
    · simp [r_chem, hs, hCQ_nonneg]
  have hr_chem_int : ∀ s, Integrable (r_chem s) (intervalMeasure 1) := by
    intro s
    by_cases hs : 0 < s ∧ s ≤ D.T
    · have h :=
        ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
          p (by simpa [M] using D.hbound s hs.1 hs.2) hM_nonneg
          (by simpa using D.hcont s hs.1 hs.2)
          (by simpa using D.hnonneg s hs.1 hs.2)
      simpa [r_chem, hs] using h
    · simp [r_chem, hs]
  have hchem_eq :
      (∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p ((D.u) s)) x.1)
        =
      ∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s) (r_chem s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le ht.le] at hs
      simp [r_chem, hs.1, hs.2.trans htT]
  have hchem_bound :
      |∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p ((D.u) s)) x.1|
        ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * C_Q := by
    rw [hchem_eq]
    exact conjugateDuhamel_sup_bound_of_integrable_sources
      ht (le_refl t) hr_chem_int hCQ_nonneg hr_chem_bound x.1
  set r_val : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then
      logisticLifted p ((D.u) s) y
    else 0
  have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ D.T
    · have h :=
        ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
          p hM_pos (by simpa [M] using D.hbound s hs.1 hs.2) y
      simpa [r_val, hs, C_L, hCLdef, M] using h
    · simp [r_val, hs, hCL_nonneg]
  have hval_eq :
      (∫ s in (0:ℝ)..t,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
          (logisticLifted p ((D.u) s)) x.1)
        =
      ∫ s in (0:ℝ)..t,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
          (r_val s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    exact Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le ht.le] at hs
      simp [r_val, hs.1, hs.2.trans htT]
  have hval_bound :
      |∫ s in (0:ℝ)..t,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
          (logisticLifted p ((D.u) s)) x.1|
        ≤ t * C_L := by
    rw [hval_eq]
    exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      ht (le_refl t) hCL_nonneg hr_val_bound x.1
  have hcorr_le :
      |(-p.χ₀) *
          (∫ s in (0:ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p ((D.u) s)) x.1)
        + (∫ s in (0:ℝ)..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
              (logisticLifted p ((D.u) s)) x.1)|
        ≤ A_corr * Real.sqrt t + C_L * t := by
    calc
      |(-p.χ₀) *
          (∫ s in (0:ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p ((D.u) s)) x.1)
        + (∫ s in (0:ℝ)..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
              (logisticLifted p ((D.u) s)) x.1)|
          ≤ |(-p.χ₀) *
              (∫ s in (0:ℝ)..t,
                intervalConjugateKernelOperator (t - s)
                  (chemFluxLifted p ((D.u) s)) x.1)|
            + |∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (logisticLifted p ((D.u) s)) x.1| :=
            abs_add_le _ _
      _ = |p.χ₀| *
            |∫ s in (0:ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxLifted p ((D.u) s)) x.1|
            + |∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (logisticLifted p ((D.u) s)) x.1| := by
          rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| *
            (heatGradientLinftyLinftyConstant * (2 * Real.sqrt t) * C_Q)
            + t * C_L := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hchem_bound (abs_nonneg p.χ₀))
            hval_bound
      _ = A_corr * Real.sqrt t + C_L * t := by
          rw [hAdef]
          ring
  have hcorr_small : A_corr * Real.sqrt t + C_L * t < ε / 2 := by
    have hsqrt_le : Real.sqrt t ≤ Real.sqrt δD := Real.sqrt_le_sqrt htδD.le
    have hpart1 : A_corr * Real.sqrt t ≤ A_corr * Real.sqrt δD :=
      mul_le_mul_of_nonneg_left hsqrt_le hA_nonneg
    have hpart2 : C_L * t ≤ C_L * δD :=
      mul_le_mul_of_nonneg_left htδD.le hCL_nonneg
    linarith [hDsmall, hpart1, hpart2]
  unfold intervalConjugateDuhamelMap
  calc
    |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1
        + (-p.χ₀) *
            (∫ s in (0:ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxLifted p ((D.u) s)) x.1)
        + (∫ s in (0:ℝ)..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
              (logisticLifted p ((D.u) s)) x.1)
        - u₀ x|
        = |(ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) x.1 - u₀ x)
          + ((-p.χ₀) *
              (∫ s in (0:ℝ)..t,
                intervalConjugateKernelOperator (t - s)
                  (chemFluxLifted p ((D.u) s)) x.1)
            + (∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (logisticLifted p ((D.u) s)) x.1))| := by
            congr 1
            ring
    _ ≤ |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) x.1 - u₀ x|
          + |(-p.χ₀) *
              (∫ s in (0:ℝ)..t,
                intervalConjugateKernelOperator (t - s)
                  (chemFluxLifted p ((D.u) s)) x.1)
            + (∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (logisticLifted p ((D.u) s)) x.1)| :=
          abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hSg_close (lt_of_le_of_lt hcorr_le hcorr_small)
    _ = ε := by ring

/-- Compatibility wrapper for the original Picard-data interface. -/
theorem intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (DB : ConjugateMildExistenceData p u₀) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀
            (conjugatePicardLimit p u₀ DB.T) t x - u₀ x| < ε := by
  simpa using intervalConjugateDuhamelMap_initialApproach_of_solution_data
    p hu₀_cont (conjugateMildSolutionData_of_data DB)

/-- Initial trace of the B-form Picard fixed point, derived from the B-form
map initial approach and the fixed-point equation. -/
theorem conjugateMildSolutionData_initialTrace
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (D : ConjugateMildSolutionData p u₀) :
    InitialTrace intervalDomain u₀ D.u := by
  intro ε hε
  have hMapApproach :=
    intervalConjugateDuhamelMap_initialApproach_of_solution_data p hu₀_cont D
  obtain ⟨δ₀, hδ₀, hsmall⟩ := hMapApproach (ε / 2) (by linarith)
  refine ⟨min δ₀ D.T, lt_min hδ₀ D.hT, fun t ht htδ ↦ ?_⟩
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htT : t ≤ D.T := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
  change ShenWork.IntervalDomain.intervalDomainSupNorm
    (fun x ↦ D.u t x - u₀ x) < ε
  unfold ShenWork.IntervalDomain.intervalDomainSupNorm
  have hpt : ∀ x : intervalDomainPoint, |D.u t x - u₀ x| < ε / 2 := by
    intro x
    rw [D.hmild t ht htT x]
    exact hsmall t ht htδ₀ x
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  have hle : sSup (Set.range (fun x : intervalDomainPoint ↦ |D.u t x - u₀ x|)) ≤
      ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact le_of_lt (hpt x)
  linarith

/-- Initial trace of the B-form Picard fixed point, derived from the B-form
map initial approach and the fixed-point equation. -/
theorem conjugatePicardLimit_initialTrace_of_conjugate_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (DB : ConjugateMildExistenceData p u₀) :
    InitialTrace intervalDomain u₀ (conjugatePicardLimit p u₀ DB.T) := by
  intro ε hε
  have hMapApproach :=
    intervalConjugateDuhamelMap_initialApproach_of_conjugate_data p hu₀_cont DB
  obtain ⟨δ₀, hδ₀, hsmall⟩ := hMapApproach (ε / 2) (by linarith)
  refine ⟨min δ₀ DB.T, lt_min hδ₀ DB.hT, fun t ht htδ => ?_⟩
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htT : t ≤ DB.T := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
  change ShenWork.IntervalDomain.intervalDomainSupNorm
    (fun x => conjugatePicardLimit p u₀ DB.T t x - u₀ x) < ε
  unfold ShenWork.IntervalDomain.intervalDomainSupNorm
  have hpt :
      ∀ x : intervalDomainPoint,
        |conjugatePicardLimit p u₀ DB.T t x - u₀ x| < ε / 2 := by
    intro x
    change |(conjugateMildSolutionData_of_data DB).u t x - u₀ x| < ε / 2
    rw [(conjugateMildSolutionData_of_data DB).hmild t ht htT x]
    exact hsmall t ht htδ₀ x
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  have hle :
      sSup (Set.range
          (fun x : intervalDomainPoint =>
            |conjugatePicardLimit p u₀ DB.T t x - u₀ x|)) ≤
        ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact le_of_lt (hpt x)
  linarith

#print axioms chemFluxLifted_bound_of_ball
#print axioms conjugateDuhamel_sup_bound_of_integrable_sources
#print axioms intervalConjugateDuhamelMap_initialApproach_of_solution_data
#print axioms intervalConjugateDuhamelMap_initialApproach_of_conjugate_data
#print axioms conjugateMildSolutionData_initialTrace
#print axioms conjugatePicardLimit_initialTrace_of_conjugate_data

end ShenWork.Paper2.BFormInitialTrace
