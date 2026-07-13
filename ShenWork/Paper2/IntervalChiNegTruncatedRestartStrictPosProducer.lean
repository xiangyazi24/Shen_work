import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPos
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.Paper2.IntervalTruncatedChemFluxBound
import ShenWork.Paper2.IntervalChiNegUniformCoreComplete

open Filter Topology Set MeasureTheory
open scoped BigOperators

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData UniformConjugateMildExistenceCore
   conjugatePicardLimit)
open ShenWork.Paper2.BFormPositiveDatumNegPart

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Positive parts preserve slice continuity. -/
theorem positivePartSlice_continuous
    {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    Continuous (positivePartSlice w) := by
  simpa [positivePartSlice, positivePart] using hw.max continuous_const

/-- Uniform bound for the faithful truncated chemotaxis flux. -/
theorem truncatedChemFluxLifted_bound_of_ball
    (p : CM2Params) {M : ℝ} (hM_pos : 0 < M)
    {w : intervalDomainPoint → ℝ}
    (hw_bound : ∀ x, |w x| ≤ M)
    (hw_cont : Continuous w) :
    ∀ y : ℝ,
      |truncatedChemFluxLifted p w y| ≤
        M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * M ^ p.γ))) := fun y =>
  _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedChemFluxLifted_abs_le_of_abs_ball
    p hM_pos hw_cont hw_bound y

/-- Uniform bound for the faithful truncated logistic source. -/
theorem truncatedLogisticLifted_bound_of_ball
    (p : CM2Params) {M : ℝ} (hM_pos : 0 < M)
    {w : intervalDomainPoint → ℝ}
    (hw_bound : ∀ x, |w x| ≤ M) :
    ∀ y : ℝ,
      |truncatedLogisticLifted p w y| ≤
        M * (p.a + p.b * M ^ p.α) := fun y =>
  _root_.ShenWork.Paper2.TruncatedPositiveTimeBootstrap.truncatedLogisticLifted_abs_le_of_abs_ball
    p hM_pos hw_bound y

/-- The faithful truncated B-form Picard map approaches the initial datum as
`t → 0+`, uniformly on the interval. -/
theorem truncatedConjugateDuhamelMap_initialApproach_of_truncated_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |truncatedConjugateDuhamelMap p u₀
            (truncatedConjugatePicardLimit p u₀ DT.T) t x - u₀ x| < ε := by
  intro ε hε
  let D := truncatedConjugateMildSolutionData_of_data DT
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
  set A_corr : ℝ := 2 * |p.χ₀| *
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant * C_Q
    with hAdef
  have hA_nonneg : 0 ≤ A_corr := by
    rw [hAdef]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg p.χ₀))
        ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg)
      hCQ_nonneg
  obtain ⟨δS, hδS, hSclose⟩ :=
    ShenWork.IntervalPicardIterateInitialApproach.semigroup_initialApproach
      p hu₀_cont (ε / 2) (by linarith)
  obtain ⟨δD, hδD, hDsmall⟩ :=
    exists_small_contraction_time_target
      hA_nonneg hCL_nonneg (show 0 < ε / 2 by linarith)
  refine ⟨min (min δS δD) DT.T, lt_min (lt_min hδS hδD) DT.hT, ?_⟩
  intro t ht htδ x
  have htδS : t < δS :=
    lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_left _ _))
  have htδD : t < δD :=
    lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_right _ _))
  have htT_lt : t < DT.T := lt_of_lt_of_le htδ (min_le_right _ _)
  have htT : t ≤ DT.T := le_of_lt htT_lt
  have hSg_close :
      |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1 - u₀ x| < ε / 2 :=
    hSclose t ht htδS x
  set r_chem : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ DT.T then
      truncatedChemFluxLifted p ((truncatedConjugatePicardLimit p u₀ DT.T) s) y
    else 0
  have hr_chem_bound : ∀ s y, |r_chem s y| ≤ C_Q := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ DT.T
    · have h :=
        truncatedChemFluxLifted_bound_of_ball p hM_pos
          (by simpa [D, M] using D.hbound s hs.1 hs.2)
          (by simpa [D] using D.hcont s hs.1 hs.2) y
      simpa [r_chem, hs, C_Q, hCQdef, M] using h
    · simp [r_chem, hs, hCQ_nonneg]
  have hr_chem_int : ∀ s, Integrable (r_chem s) (intervalMeasure 1) := by
    intro s
    by_cases hs : 0 < s ∧ s ≤ DT.T
    · have h :=
        ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
          p
          (w := positivePartSlice ((truncatedConjugatePicardLimit p u₀ DT.T) s))
          (fun x =>
            (abs_positivePart_le_abs
              ((truncatedConjugatePicardLimit p u₀ DT.T) s x)).trans
              (by simpa [D, M] using D.hbound s hs.1 hs.2 x))
          hM_nonneg
          (positivePartSlice_continuous
            (by simpa [D] using D.hcont s hs.1 hs.2))
          (positivePartSlice_nonneg
            ((truncatedConjugatePicardLimit p u₀ DT.T) s))
      have heq :=
        truncatedChemFluxLifted_eq_chemFluxLifted_positivePartSlice p
          ((truncatedConjugatePicardLimit p u₀ DT.T) s)
      simpa [r_chem, hs, heq] using h
    · simp [r_chem, hs]
  have hchem_eq :
      (∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
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
          (truncatedChemFluxLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1|
        ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt t) * C_Q := by
    rw [hchem_eq]
    exact ShenWork.Paper2.BFormInitialTrace.conjugateDuhamel_sup_bound_of_integrable_sources
      ht (le_refl t) hr_chem_int hCQ_nonneg hr_chem_bound x.1
  set r_val : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ DT.T then
      truncatedLogisticLifted p ((truncatedConjugatePicardLimit p u₀ DT.T) s) y
    else 0
  have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L := by
    intro s y
    by_cases hs : 0 < s ∧ s ≤ DT.T
    · have h :=
        truncatedLogisticLifted_bound_of_ball p hM_pos
          (by simpa [D, M] using D.hbound s hs.1 hs.2) y
      simpa [r_val, hs, C_L, hCLdef, M] using h
    · simp [r_val, hs, hCL_nonneg]
  have hval_eq :
      (∫ s in (0:ℝ)..t,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
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
          (truncatedLogisticLifted p
            ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1|
        ≤ t * C_L := by
    rw [hval_eq]
    exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      ht (le_refl t) hCL_nonneg hr_val_bound x.1
  have hcorr_le :
      |(-p.χ₀) *
          (∫ s in (0:ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (truncatedChemFluxLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
        + (∫ s in (0:ℝ)..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)|
        ≤ A_corr * Real.sqrt t + C_L * t := by
    calc
      |(-p.χ₀) *
          (∫ s in (0:ℝ)..t,
            intervalConjugateKernelOperator (t - s)
              (truncatedChemFluxLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
        + (∫ s in (0:ℝ)..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)|
          ≤ |(-p.χ₀) *
              (∫ s in (0:ℝ)..t,
                intervalConjugateKernelOperator (t - s)
                  (truncatedChemFluxLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)|
            + |∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (truncatedLogisticLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1| :=
            abs_add_le _ _
      _ = |p.χ₀| *
            |∫ s in (0:ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p
                  ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1|
            + |∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (truncatedLogisticLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1| := by
          rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              (2 * Real.sqrt t) * C_Q)
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
  unfold truncatedConjugateDuhamelMap
  calc
    |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1
        + (-p.χ₀) *
            (∫ s in (0:ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p
                  ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
        + (∫ s in (0:ℝ)..t,
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
              (truncatedLogisticLifted p
                ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
        - u₀ x|
        = |(ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) x.1 - u₀ x)
          + ((-p.χ₀) *
              (∫ s in (0:ℝ)..t,
                intervalConjugateKernelOperator (t - s)
                  (truncatedChemFluxLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
            + (∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (truncatedLogisticLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1))| := by
            congr 1
            ring
    _ ≤ |ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
            (intervalDomainLift u₀) x.1 - u₀ x|
          + |(-p.χ₀) *
              (∫ s in (0:ℝ)..t,
                intervalConjugateKernelOperator (t - s)
                  (truncatedChemFluxLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)
            + (∫ s in (0:ℝ)..t,
                ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (t - s)
                  (truncatedLogisticLifted p
                    ((truncatedConjugatePicardLimit p u₀ DT.T) s)) x.1)| :=
          abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hSg_close (lt_of_le_of_lt hcorr_le hcorr_small)
    _ = ε := by ring

/-- Initial trace of the faithful truncated B-form Picard fixed point. -/
theorem truncatedConjugatePicardLimit_initialTrace_of_truncated_data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (hu₀_cont : Continuous u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀) :
    InitialTrace intervalDomain u₀
      (truncatedConjugatePicardLimit p u₀ DT.T) := by
  intro ε hε
  have hMapApproach :=
    truncatedConjugateDuhamelMap_initialApproach_of_truncated_data p hu₀_cont DT
  obtain ⟨δ₀, hδ₀, hsmall⟩ := hMapApproach (ε / 2) (by linarith)
  refine ⟨min δ₀ DT.T, lt_min hδ₀ DT.hT, fun t ht htδ => ?_⟩
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htT : t ≤ DT.T := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
  change ShenWork.IntervalDomain.intervalDomainSupNorm
    (fun x => truncatedConjugatePicardLimit p u₀ DT.T t x - u₀ x) < ε
  unfold ShenWork.IntervalDomain.intervalDomainSupNorm
  have hpt :
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardLimit p u₀ DT.T t x - u₀ x| < ε / 2 := by
    intro x
    change |(truncatedConjugateMildSolutionData_of_data DT).u t x - u₀ x| < ε / 2
    rw [(truncatedConjugateMildSolutionData_of_data DT).hmild t ht htT x]
    exact hsmall t ht htδ₀ x
  haveI : Nonempty intervalDomainPoint :=
    ⟨⟨0, by constructor <;> norm_num⟩⟩
  have hle :
      sSup (Set.range
          (fun x : intervalDomainPoint =>
            |truncatedConjugatePicardLimit p u₀ DT.T t x - u₀ x|)) ≤
        ε / 2 := by
    apply csSup_le (Set.range_nonempty _)
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact le_of_lt (hpt x)
  linarith

/-- A bridge on `(0,T]` upgrades to equality of the globally zero-extended
Picard-limit names. -/
theorem truncatedConjugatePicardLimit_eq_conjugatePicardLimit_of_bridge
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (Hbridge : TruncatedConjugateLimitBridge p DB DT) :
    truncatedConjugatePicardLimit p u₀ DT.T =
      conjugatePicardLimit p u₀ DB.T := by
  rcases Hbridge with ⟨hT, hlim⟩
  funext t x
  by_cases ht : 0 < t ∧ t ≤ DB.T
  · exact (hlim t ht.1 ht.2 x).symm
  · have htDT : ¬(0 < t ∧ t ≤ DT.T) := by
      intro h
      exact ht ⟨h.1, by simpa [hT] using h.2⟩
    simp [truncatedConjugatePicardLimit, conjugatePicardLimit, ht, htDT]

/-- If the faithful truncated Picard limit is nonnegative on its active window
and lies in the full Picard ball, it agrees with the old full Picard-limit
name. -/
theorem truncatedConjugatePicardLimit_eq_conjugatePicardLimit_of_nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    {DT : TruncatedConjugateMildExistenceData p u₀}
    (hT : DT.T = DB.T)
    (htrunc_nonneg :
      ∀ t, 0 < t → t ≤ DT.T → ∀ x : intervalDomainPoint,
        0 ≤ truncatedConjugatePicardLimit p u₀ DT.T t x)
    (htrunc_bound :
      ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardLimit p u₀ DT.T t x| ≤ DB.M) :
    truncatedConjugatePicardLimit p u₀ DT.T =
      conjugatePicardLimit p u₀ DB.T :=
  truncatedConjugatePicardLimit_eq_conjugatePicardLimit_of_bridge
    (truncatedConjugateLimitBridge_of_faithful_truncation
      { hT := hT
        truncated_nonneg := htrunc_nonneg
        truncated_bound_in_full_ball := htrunc_bound })

end ShenWork.Paper2.BFormPositiveDatumNegPart

namespace ShenWork.Paper2.IntervalChiNegFinalAssemblyV3

/-- Uniform restart-comparison certificates for the truncated Picard limit. -/
abbrev UniformTruncatedRestartSquareHeatComparisonData
    (p : CM2Params) : Type :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      TruncatedRestartSquareHeatComparisonData C.T
        (truncatedConjugatePicardLimit p u₀ C.T)

/-- Uniform initial trace certificates for the truncated Picard limit. -/
abbrev UniformTruncatedRestartInitialTraceData
    (p : CM2Params) : Prop :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      InitialTrace intervalDomain u₀
        (truncatedConjugatePicardLimit p u₀ C.T)

/-- Uniform certificates that the faithful truncated limit is the old full
Picard-limit name once truncation is inactive. -/
abbrev UniformTruncatedRestartFullPicardAgreementData
    (p : CM2Params) : Prop :=
  ∀ {M : ℝ}, 0 < M → ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ → (∀ x, |u₀ x| ≤ M) →
    ∀ C : UniformConjugateMildExistenceCore p u₀,
      truncatedConjugatePicardLimit p u₀ C.T =
        conjugatePicardLimit p u₀ C.T

/-!
The former V3 Stampacchia producer wrappers
(`UniformTruncatedRestartStampacchiaProducerData`,
`uniformTruncatedRestartInitialTraceData`,
`uniformTruncatedRestartStampacchiaBarrierInputs*`,
`uniformCoreMildSolutionFrontier_of_truncatedRestartProducerData`)
were removed: they targeted the pre-certificate
`uniformTruncatedConjugateMildExistenceCore_of_uniformCore` API and had no
consumers.  The route consumes only the trajectory-level theorems above.
-/

end ShenWork.Paper2.IntervalChiNegFinalAssemblyV3
