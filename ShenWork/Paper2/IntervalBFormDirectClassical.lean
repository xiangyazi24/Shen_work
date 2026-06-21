import ShenWork.Paper2.IntervalBFormPIDUnconditional
import ShenWork.Paper2.IntervalConjugateCosineSeries
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalDomainTheorem11Umbrella
import ShenWork.Paper2.IntervalBFormInitialTrace
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalChemDivOuterCommute
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.Paper2.ChemMildHolderBootstrap

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap
   intervalConjugateKernelOperator
   conjugateKernelDuhamel_intervalIntegrable_of_joint_measurable)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugateMildSolutionData_of_data conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations RestartCosineRepresentation restartDuhamelCoeff)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalSourceCoefficientTimeC1
  (localRestartCoeff)
open ShenWork.IntervalDuhamelClosedC2
  (DuhamelSourceTimeC1)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs coupledChemDivSourceLift
   coupledChemDivFluxLift coupledChemDivSourceLift_eq_deriv_fluxLift_interior
   sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
   coupledChemical_ellipticPDE_of_closedC2_neumann
   coupledChemical_neumannBC_of_closedC2_neumann)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.CosineSpectrum
  (cosineMode)
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierAssembly
open ShenWork.IntervalResolverSpatialC2
  (resolverR_summability)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateCosineSeries
  (conjugatePicardLimit_cosineSeries_from_flux_deriv_subtypeCont_open)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainCosineSlice_contDiffOn_Ioo
   intervalDomainCosineSlice_neumann_limit_left
   intervalDomainCosineSlice_neumann_limit_right
   intervalDomainCosineSlice_conjunct7)
open ShenWork.PDE

noncomputable section

namespace ShenWork.Paper2.BFormDirectClassical

/-- Banked B-form inputs needed for the direct classical assembly.

This is the B-form half of the old end-to-end file, without any gradient-form
solution record or output-derivative bridge. -/
structure BFormBankedInputs
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  huPaper : PaperPositiveInitialDatum intervalDomain u₀
  Hinf : ConjugatePicardInfThresholdData p u₀ DB.T
  hsmall :
    |p.χ₀| * (heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt DB.T) * Hinf.CQ)
      + DB.T * Hinf.CL ≤ paperPositiveFloor huPaper / 2
  MInit : ℝ
  haInit : ∀ n,
    |cosineCoeffs (intervalDomainLift u₀) n| ≤ MInit
  hlogSrc : DuhamelSourceTimeC1
    (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
  hchemSrc : DuhamelSourceTimeC1
    (coupledChemDivSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
  hlogCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p
          ((conjugatePicardLimit p u₀ DB.T) t)))
  hlogFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (ShenWork.IntervalDomainExistence.intervalLogisticSource p
              ((conjugatePicardLimit p u₀ DB.T) t)))) n)
  hchemCont : ∀ t, 0 < t → t < DB.T →
    Continuous
      (intervalDomainConstExtend
        (fun x : intervalDomainPoint =>
          intervalDomainChemotaxisDiv p
            ((conjugatePicardLimit p u₀ DB.T) t)
            (coupledChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t) x))
  hchemFourier : ∀ t, 0 < t → t < DB.T →
    Summable (fun n : ℤ =>
      fourierCoeff
        (ShenWork.IntervalCosineInversion.reflCircle
          (intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              intervalDomainChemotaxisDiv p
                ((conjugatePicardLimit p u₀ DB.T) t)
                (coupledChemicalConcentration p
                  (conjugatePicardLimit p u₀ DB.T) t) x))) n)

def BFormBankedInputs.hsrcB
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    DuhamelSourceTimeC1
      (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)) :=
  bFormSource_duhamelSourceTimeC1 B.hlogSrc B.hchemSrc

private theorem logisticSource_continuous_of_constExtend
    {p : CM2Params} {w : intervalDomainPoint → ℝ}
    (hcont : Continuous
      (intervalDomainConstExtend
        (ShenWork.IntervalDomainExistence.intervalLogisticSource p w))) :
    Continuous (ShenWork.IntervalDomainExistence.intervalLogisticSource p w) := by
  have heq :
      ShenWork.IntervalDomainExistence.intervalLogisticSource p w =
        (intervalDomainConstExtend
          (ShenWork.IntervalDomainExistence.intervalLogisticSource p w)) ∘
            Subtype.val := by
    funext y
    rcases y with ⟨y, hy⟩
    simp only [Function.comp]
    rw [constExtend_eq_lift_on_Icc hy]
    simp only [intervalDomainLift]
    split_ifs with h
    · exact congr_arg _ (Subtype.ext rfl)
    · exact absurd hy h
  rw [heq]
  exact hcont.comp continuous_subtype_val

/-- Direct B-form frontier for one datum.  Every field is map-agnostic: no
gradient mild record and no output-derivative bridge. -/
structure BFormDirectFrontier
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) where
  bank : BFormBankedInputs p DB
  hTimeNhd :
    HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)
  hResolverData :
    HasResolverDirectSpectralData DB.T
      (mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T)) p
  hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t x

private theorem bform_u_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t x, 0 < t → t < DB.T →
      0 < conjugatePicardLimit p u₀ DB.T t x := by
  intro t x ht htT
  exact ShenWork.IntervalConjugatePicard.conjugatePicardLimit_pos_of_PID
    B.huPaper B.Hinf B.hsmall t ht (le_of_lt htT) x

private theorem exists_restartCosineRepresentation_of_timeNhd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T))
    (t : ℝ) (ht : 0 < t) (htT : t < DB.T) :
    Nonempty
      (RestartCosineRepresentation
        ((conjugatePicardLimit p u₀ DB.T) t)) := by
  obtain ⟨a₀, M, _hM, ha₀, a, src, offset, hτ, hagree_nhd⟩ :=
    H.exists_data t ht htT
  refine ⟨?_⟩
  refine
    { τ := t - offset
      hτ := hτ
      M := M
      a₀ := a₀
      a := a
      ha₀ := ha₀
      src := src
      hagree := ?_ }
  intro x hx
  have h := hagree_nhd.self_of_nhds ⟨x, hx⟩
  simpa [intervalDomainLift, hx, restartDuhamelCoeff, localRestartCoeff] using h

private def restartCosineRepresentation_of_timeNhd
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T))
    (t : ℝ) (ht : 0 < t) (htT : t < DB.T) :
    RestartCosineRepresentation
      ((conjugatePicardLimit p u₀ DB.T) t) :=
  Classical.choice
    (exists_restartCosineRepresentation_of_timeNhd H t ht htT)

private theorem bform_u_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t, 0 < t → t < DB.T →
      ContDiffOn ℝ 2
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
          (Set.Icc (0 : ℝ) 1)
        ∧ deriv
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)) 0 = 0
        ∧ deriv
          (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)) 1 = 0 := by
  intro t ht htT
  let R := restartCosineRepresentation_of_timeNhd H t ht htT
  have h0 : intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) 0 ≠ 0 := by
    have hmem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (bform_u_pos B t ⟨0, hmem⟩ ht htT)
  have h1 : intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) 1 ≠ 0 := by
    have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    simp only [intervalDomainLift, hmem, dif_pos]
    exact ne_of_gt (bform_u_pos B t ⟨1, hmem⟩ ht htT)
  exact R.conjunct7 h0 h1

private theorem bform_u_neumann_left
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t, 0 < t → t < DB.T →
      Filter.Tendsto
        (deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro t ht htT
  exact (restartCosineRepresentation_of_timeNhd H t ht htT).neumann_limit_left

private theorem bform_u_neumann_right
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t, 0 < t → t < DB.T →
      Filter.Tendsto
        (deriv (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht htT
  exact (restartCosineRepresentation_of_timeNhd H t ht htT).neumann_limit_right

private theorem lift_resolver_eqOn_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Set.EqOn
      (intervalDomainLift (intervalNeumannResolverR p u))
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hxIcc
  simp only [intervalDomainLift, dif_pos hxIcc,
    ShenWork.IntervalResolverGradientBridge.resolverR_apply_eq, cosineMode]

private theorem resolver_lift_ne_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint)
    (hpos : 0 < intervalNeumannResolverR p u x) :
    intervalDomainLift (intervalNeumannResolverR p u) x.1 ≠ 0 := by
  have heq : intervalDomainLift (intervalNeumannResolverR p u) x.1 =
      intervalNeumannResolverR p u x := by
    unfold intervalDomainLift
    split
    · rfl
    · exact absurd x.2 ‹_›
  rw [heq]
  exact ne_of_gt hpos

private def bform_sourceDecay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T))
    {t : ℝ} (ht : 0 < t) (htT : t < DB.T) :
    SourceCoeffQuadraticDecay p
      (conjugatePicardLimit p u₀ DB.T t) := by
  have hpos_lift :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        0 < intervalDomainLift (conjugatePicardLimit p u₀ DB.T t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact bform_u_pos B t ⟨y, hy⟩ ht htT
  exact sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    (p := p)
    (u := conjugatePicardLimit p u₀ DB.T t)
    (bform_u_closedC2_endpointDerivs B H t ht htT).1
    (bform_u_neumann_left H t ht htT)
    (bform_u_neumann_right H t ht htT)
    hpos_lift

private theorem bform_vSpatialInterior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      ContDiffOn ℝ 2
        (intervalDomainLift
          (mildChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T) t))
        (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  change ContDiffOn ℝ 2
    (intervalDomainLift
      (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t)))
    (Set.Ioo (0 : ℝ) 1)
  exact intervalDomainCosineSlice_contDiffOn_Ioo
    (resolverR_summability (bform_sourceDecay B H ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))

private theorem bform_vNeumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      Filter.Tendsto
          (deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht
  change Filter.Tendsto
          (deriv (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  exact
    ⟨intervalDomainCosineSlice_neumann_limit_left
        (resolverR_summability (bform_sourceDecay B H ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t)),
      intervalDomainCosineSlice_neumann_limit_right
        (resolverR_summability (bform_sourceDecay B H ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))⟩

private theorem bform_vClosedSpatial
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB)
    (H : HasTimeNeighborhoodSpectralAgreement DB.T
      (conjugatePicardLimit p u₀ DB.T))
    (hVpos : ∀ t, 0 < t → t < DB.T → ∀ x : intervalDomainPoint,
      0 < mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t x) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) DB.T →
      ContDiffOn ℝ 2
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)) 0 = 0 ∧
        deriv
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) t)) 1 = 0 := by
  intro t ht
  change ContDiffOn ℝ 2
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t)))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))) 0 = 0 ∧
        deriv
          (intervalDomainLift
            (intervalNeumannResolverR p (conjugatePicardLimit p u₀ DB.T t))) 1 = 0
  have hv0 : 0 < intervalNeumannResolverR p
      (conjugatePicardLimit p u₀ DB.T t) ⟨0, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      hVpos t ht.1 ht.2 ⟨0, by constructor <;> norm_num⟩
  have hv1 : 0 < intervalNeumannResolverR p
      (conjugatePicardLimit p u₀ DB.T t) ⟨1, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      hVpos t ht.1 ht.2 ⟨1, by constructor <;> norm_num⟩
  exact intervalDomainCosineSlice_conjunct7
    (resolverR_summability (bform_sourceDecay B H ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (conjugatePicardLimit p u₀ DB.T t))
    (resolver_lift_ne_zero ⟨0, by constructor <;> norm_num⟩ hv0)
    (resolver_lift_ne_zero ⟨1, by constructor <;> norm_num⟩ hv1)

private theorem bform_logisticDuhamel_intervalIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} :
    ∀ t, 0 < t → t ≤ DB.T →
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable
          (fun s : ℝ =>
            intervalFullSemigroupOperator (t - s)
              (logisticLifted p ((conjugatePicardLimit p u₀ DB.T) s)) x)
          MeasureTheory.volume 0 t := by
  intro t ht htT x _hx
  let D := conjugateMildSolutionData_of_data DB
  set CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α) with hCL
  have hCL_nn : 0 ≤ CL := by
    rw [hCL]
    have hpow : 0 ≤ D.M ^ p.α := Real.rpow_nonneg D.hM.le _
    exact mul_nonneg D.hM.le (add_nonneg p.ha (mul_nonneg p.hb hpow))
  set f : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ DB.T then
      logisticLifted p ((conjugatePicardLimit p u₀ DB.T) s) y
    else 0 with hf
  have hf_bdd : ∀ s y, |f s y| ≤ CL := by
    intro s y
    simp only [hf]
    split_ifs with h
    · exact ShenWork.Paper2.logisticLifted_orderBox_bound
        D.hM D.hbound s h.1 h.2 y
    · simpa using hCL_nn
  have hf_meas : Measurable (Function.uncurry f) := by
    have hbase :=
      ShenWork.Paper2.logisticLifted_uncurry_measurable
        (p := p) (u := conjugatePicardLimit p u₀ DB.T) D.hmeas
    simp only [Function.uncurry] at hbase ⊢
    simp only [hf]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hf_int :=
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
      ht hf_meas hCL_nn hf_bdd x
  refine IntervalIntegrable.congr ?_ hf_int
  intro s hs
  rw [Set.uIoc_of_le ht.le] at hs
  have hmem : 0 < s ∧ s ≤ DB.T := ⟨hs.1, le_trans hs.2 htT⟩
  simp only [hf, if_pos hmem]

private theorem bform_conjugateKernelDuhamel_intervalIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} :
    ∀ t, 0 < t → t ≤ DB.T →
      ∀ x, x ∈ Set.Icc (0 : ℝ) 1 →
        IntervalIntegrable
          (fun s : ℝ =>
            intervalConjugateKernelOperator (t - s)
              (chemFluxLifted p ((conjugatePicardLimit p u₀ DB.T) s)) x)
          MeasureTheory.volume 0 t := by
  intro t ht htT x _hx
  let D := conjugateMildSolutionData_of_data DB
  set CQ : ℝ := D.M * (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ))) with hCQ
  have hCQ_nn : 0 ≤ CQ := by
    rw [hCQ]
    exact mul_nonneg D.hM.le (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  set f : ℝ → ℝ → ℝ :=
    fun s y => if 0 < s ∧ s ≤ DB.T then
      chemFluxLifted p ((conjugatePicardLimit p u₀ DB.T) s) y
    else 0 with hf
  have hf_bdd : ∀ s y, |f s y| ≤ CQ := by
    intro s y
    simp only [hf]
    split_ifs with h
    · exact ShenWork.Paper2.chemFluxLifted_bound_of_ball'
        p D.hM.le (fun z => D.hbound s h.1 h.2 z)
        (fun z => D.hnonneg s h.1 h.2 z) (D.hcont s h.1 h.2) y
    · simpa using hCQ_nn
  have hf_meas : Measurable (Function.uncurry f) := by
    have hbase :=
      ShenWork.Paper2.chemFluxLifted_uncurry_measurable
        (p := p) (u := conjugatePicardLimit p u₀ DB.T) D.hmeas
    simp only [Function.uncurry] at hbase ⊢
    simp only [hf]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hf_int :=
    conjugateKernelDuhamel_intervalIntegrable_of_joint_measurable
      ht hf_meas hCQ_nn hf_bdd x
  refine IntervalIntegrable.congr ?_ hf_int
  intro s hs
  rw [Set.uIoc_of_le ht.le] at hs
  have hmem : 0 < s ∧ s ≤ DB.T := ⟨hs.1, le_trans hs.2 htT⟩
  simp only [hf, if_pos hmem]

private theorem bform_flux_continuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} :
    ∀ t, 0 < t → t ≤ DB.T →
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ContinuousOn
          (chemFluxLifted p ((conjugatePicardLimit p u₀ DB.T) s))
          (Set.Icc (0 : ℝ) 1) := by
  intro t _ht htT s hs
  let D := conjugateMildSolutionData_of_data DB
  have hsT : s ≤ DB.T := le_trans (le_of_lt hs.2) htT
  exact
    ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_continuousOn_Icc_of_continuous
      p (fun z => D.hbound s hs.1 hsT z) D.hM.le
      (D.hcont s hs.1 hsT) (fun z => D.hnonneg s hs.1 hsT z)

private theorem bform_source_intervalIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (B : BFormBankedInputs p DB) :
    ∀ t, 0 < t → t ≤ DB.T →
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        IntervalIntegrable
          (coupledChemDivSourceLift p
            (conjugatePicardLimit p u₀ DB.T) s)
          MeasureTheory.volume 0 1 := by
  intro t _ht htT s hs
  have hsT : s < DB.T := lt_of_lt_of_le hs.2 htT
  let src : intervalDomainPoint → ℝ := fun x =>
    intervalDomainChemotaxisDiv p
      ((conjugatePicardLimit p u₀ DB.T) s)
      (coupledChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) s) x
  have hcont_ext : Continuous (intervalDomainConstExtend src) :=
    B.hchemCont s hs.1 hsT
  have hcont_lift : ContinuousOn (intervalDomainLift src) (Set.Icc (0 : ℝ) 1) := by
    refine hcont_ext.continuousOn.congr ?_
    intro y hy
    exact (constExtend_eq_lift_on_Icc hy).symm
  have hsourceContOn :
      ContinuousOn
        (coupledChemDivSourceLift p
          (conjugatePicardLimit p u₀ DB.T) s)
        (Set.Icc (0 : ℝ) 1) := by
    simpa [coupledChemDivSourceLift, src] using hcont_lift
  have hsourceContOn_u :
      ContinuousOn
        (coupledChemDivSourceLift p
          (conjugatePicardLimit p u₀ DB.T) s)
        (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hsourceContOn
  exact hsourceContOn_u.intervalIntegrable

private theorem resolver_lift_deriv_eq_resolverGrad_eventually
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (intervalNeumannResolverR p u))
      =ᶠ[𝓝 y] ShenWork.Paper2.resolverGradReal p u := by
  filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy] with z hz
  classical
  set S : ℝ → ℝ := fun r =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * r) with hS
  have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
  have hSderiv :
      HasDerivAt S (intervalNeumannResolverRGrad p u ⟨z, hzIcc⟩) z := by
    rw [hS]
    exact solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay hzIcc
  have hEq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      intervalDomainLift (intervalNeumannResolverR p u) r = S r := by
    intro r hr
    have hrIcc : r ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hr
    simp only [intervalDomainLift, hrIcc, dif_pos]
    rw [ShenWork.IntervalResolverGradientBridge.resolverR_apply_eq, hS]
  have hlocS :
      intervalDomainLift (intervalNeumannResolverR p u) =ᶠ[𝓝 z] S := by
    refine Filter.eventuallyEq_of_mem ?_ hEq
    exact IsOpen.mem_nhds isOpen_Ioo hz
  rw [hlocS.deriv_eq, hSderiv.deriv,
    resolverGradReal_eq p u ⟨z, hzIcc⟩]

private theorem bform_coupled_flux_contDiffOn_Ioo
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB)
    {s : ℝ} (hs0 : 0 < s) (hsT : s < DB.T) :
    ContDiffOn ℝ 1
      (coupledChemDivFluxLift p
        (conjugatePicardLimit p u₀ DB.T) s)
      (Set.Ioo (0 : ℝ) 1) := by
  have hCu : ContDiffOn ℝ 2
      (intervalDomainLift (conjugatePicardLimit p u₀ DB.T s))
      (Set.Ioo (0 : ℝ) 1) :=
    (bform_u_closedC2_endpointDerivs F.bank F.hTimeNhd s hs0 hsT).1.mono
      Set.Ioo_subset_Icc_self
  have hCv : ContDiffOn ℝ 2
      (intervalDomainLift
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T) s))
      (Set.Ioo (0 : ℝ) 1) :=
    bform_vSpatialInterior F.bank F.hTimeNhd s ⟨hs0, hsT⟩
  have hu1 : ContDiffOn ℝ 1
      (intervalDomainLift (conjugatePicardLimit p u₀ DB.T s))
      (Set.Ioo (0 : ℝ) 1) :=
    hCu.of_le (by norm_num)
  have hdv1 : ContDiffOn ℝ 1
      (deriv (intervalDomainLift
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T) s)))
      (Set.Ioo (0 : ℝ) 1) := by
    have hderivWithin : ContDiffOn ℝ 1
        (derivWithin
          (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) s))
          (Set.Ioo (0 : ℝ) 1))
        (Set.Ioo (0 : ℝ) 1) :=
      hCv.derivWithin isOpen_Ioo.uniqueDiffOn (by norm_num)
    refine hderivWithin.congr (fun x hx => ?_)
    exact (derivWithin_of_isOpen isOpen_Ioo hx).symm
  have hbase1 : ContDiffOn ℝ 1
      (fun x => 1 + intervalDomainLift
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T) s) x)
      (Set.Ioo (0 : ℝ) 1) :=
    contDiffOn_const.add (hCv.of_le (by norm_num))
  have hpos : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      0 < 1 + intervalDomainLift
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T) s) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
    have hvpos := F.hVpos s hs0 hsT ⟨x, hxIcc⟩
    have hval :
        intervalDomainLift
          (mildChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T) s) x =
          mildChemicalConcentration p
            (conjugatePicardLimit p u₀ DB.T) s ⟨x, hxIcc⟩ := by
      simp [intervalDomainLift, hxIcc]
    rw [hval]
    linarith
  have hq1 : ContDiffOn ℝ 1
      (fun x => (1 + intervalDomainLift
        (mildChemicalConcentration p
          (conjugatePicardLimit p u₀ DB.T) s) x) ^ (-p.β))
      (Set.Ioo (0 : ℝ) 1) :=
    hbase1.rpow_const_of_ne (fun x hx => ne_of_gt (hpos x hx))
  have hprod : ContDiffOn ℝ 1
      (fun x =>
        intervalDomainLift (conjugatePicardLimit p u₀ DB.T s) x *
          deriv (intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) s)) x *
          (1 + intervalDomainLift
            (mildChemicalConcentration p
              (conjugatePicardLimit p u₀ DB.T) s) x) ^ (-p.β))
      (Set.Ioo (0 : ℝ) 1) :=
    (hu1.mul hdv1).mul hq1
  refine hprod.congr (fun x hx => ?_)
  have hbase_pos := hpos x hx
  have hbase_pos' :
      0 < 1 + intervalDomainLift
        (intervalNeumannResolverR p
          (conjugatePicardLimit p u₀ DB.T s)) x := by
    simpa [mildChemicalConcentration] using hbase_pos
  simp [coupledChemDivFluxLift, coupledChemicalConcentration,
    mildChemicalConcentration]
  rw [div_eq_mul_inv, ← Real.rpow_neg hbase_pos'.le]

private theorem bform_flux_deriv_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    ∀ t, 0 < t → t ≤ DB.T →
      ∀ s ∈ Set.Ioo (0 : ℝ) t,
        ∀ y ∈ Set.Ioo (0 : ℝ) 1,
          HasDerivAt
            (chemFluxLifted p ((conjugatePicardLimit p u₀ DB.T) s))
            (coupledChemDivSourceLift p
              (conjugatePicardLimit p u₀ DB.T) s y)
            y := by
  intro t _ht htT s hs y hy
  have hsT : s < DB.T := lt_of_lt_of_le hs.2 htT
  have hfluxC1 := bform_coupled_flux_contDiffOn_Ioo F hs.1 hsT
  have hflux_has :
      HasDerivAt
        (coupledChemDivFluxLift p
          (conjugatePicardLimit p u₀ DB.T) s)
        (deriv (coupledChemDivFluxLift p
          (conjugatePicardLimit p u₀ DB.T) s) y) y :=
    ((hfluxC1.differentiableOn (by norm_num)).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioo hy)).hasDerivAt
  have hdecay :
      SourceCoeffQuadraticDecay p
        (conjugatePicardLimit p u₀ DB.T s) :=
    bform_sourceDecay F.bank F.hTimeNhd hs.1 hsT
  have hresolver :=
    resolver_lift_deriv_eq_resolverGrad_eventually hdecay hy
  have hev :
      chemFluxLifted p ((conjugatePicardLimit p u₀ DB.T) s)
        =ᶠ[𝓝 y]
      coupledChemDivFluxLift p
        (conjugatePicardLimit p u₀ DB.T) s := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo hy, hresolver] with z hz hgrad
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hz
    unfold chemFluxLifted coupledChemDivFluxLift
    simp only [intervalDomainLift, hzIcc, dif_pos, coupledChemicalConcentration]
    rw [hgrad]
  have hsource_eq :=
    coupledChemDivSourceLift_eq_deriv_fluxLift_interior
      (p := p) (u := conjugatePicardLimit p u₀ DB.T) (s := s) (x := y) hy
  rw [hsource_eq]
  exact hflux_has.congr_of_eventuallyEq hev

/-- Global B-form cosine representation produced from the regularity frontier:
the five old banked hypotheses are reconstructed from the Picard order box and
the carried classical regularity data. -/
theorem hB_global_of_flux_deriv_reconstruction
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    ∀ t, 0 < t → t ≤ DB.T →
      Set.EqOn
        (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  intro t ht htT x hx
  have hTfix :
      IntervalConjugateMildSolution p DB.T u₀
        (conjugatePicardLimit p u₀ DB.T) :=
    (conjugateMildSolutionData_of_data DB).hmild
  let Mlog : ℝ → ℝ := fun _ => ∑' k, F.bank.hlogSrc.envelope k
  have hlog_bound : ∀ s ∈ Set.Ioo (0 : ℝ) t, ∀ n : ℕ,
      |coupledLogisticSourceCoeffs p
          (conjugatePicardLimit p u₀ DB.T) s n| ≤ Mlog s := by
    intro s hs n
    have hnn : ∀ k, 0 ≤ F.bank.hlogSrc.envelope k := fun k =>
      le_trans (abs_nonneg _) (F.bank.hlogSrc.henv_bound 0 le_rfl k)
    refine le_trans (F.bank.hlogSrc.henv_bound s (le_of_lt hs.1) n) ?_
    have := F.bank.hlogSrc.henv_summable.sum_le_tsum {n} (fun k _ => hnn k)
    simpa [Mlog] using this
  exact
    conjugatePicardLimit_cosineSeries_from_flux_deriv_subtypeCont_open
      (p := p) (u₀ := u₀) (T := DB.T) (t := t) (x := x)
      (M₀ := F.bank.MInit)
      hTfix ht htT hx
      (PaperPositiveInitialDatum.admissible F.bank.huPaper).2
      F.bank.haInit F.bank.hsrcB
      (bform_conjugateKernelDuhamel_intervalIntegrable
        (p := p) (u₀ := u₀) (DB := DB) t ht htT x hx)
      (bform_logisticDuhamel_intervalIntegrable
        (p := p) (u₀ := u₀) (DB := DB) t ht htT x hx)
      Mlog
      (bform_flux_continuousOn_Icc
        (p := p) (u₀ := u₀) (DB := DB) t ht htT)
      (bform_source_intervalIntegrable F.bank t ht htT)
      (bform_flux_deriv_interior F t ht htT)
      (fun s hs =>
        logisticSource_continuous_of_constExtend
          (F.bank.hlogCont s hs.1 (lt_of_lt_of_le hs.2 htT)))
      hlog_bound

theorem BFormDirectFrontier.hB_global
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    ∀ t, 0 < t → t ≤ DB.T →
      Set.EqOn
        (intervalDomainLift (conjugatePicardLimit p u₀ DB.T t))
        (fun x => ∑' n,
          localRestartCoeff (cosineCoeffs (intervalDomainLift u₀))
            (bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))
            t n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) :=
  hB_global_of_flux_deriv_reconstruction F

theorem hasRestartCosineRepresentations_of_BFormDirectFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    HasRestartCosineRepresentations DB.T
      (conjugatePicardLimit p u₀ DB.T) := by
  intro t ht htT
  refine ⟨?_⟩
  refine
    { τ := t
      hτ := ht
      M := F.bank.MInit
      a₀ := cosineCoeffs (intervalDomainLift u₀)
      a := bFormSourceCoeffs p (conjugatePicardLimit p u₀ DB.T)
      ha₀ := F.bank.haInit
      src := F.bank.hsrcB
      hagree := ?_ }
  intro x hx
  have h := F.hB_global t ht htT.le hx
  simpa [restartDuhamelCoeff, localRestartCoeff] using h

theorem BFormDirectFrontier.hpde_u
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    ∀ t x, 0 < t → t < DB.T → x ∈ intervalDomain.inside →
      intervalDomain.timeDeriv (conjugatePicardLimit p u₀ DB.T) t x =
        intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ DB.T) t) x
          - p.χ₀ * intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ DB.T) t)
              (mildChemicalConcentration p
                (conjugatePicardLimit p u₀ DB.T) t) x
          + (conjugatePicardLimit p u₀ DB.T) t x
            * (p.a - p.b *
              ((conjugatePicardLimit p u₀ DB.T) t x) ^ p.α) :=
  ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_PID_unconditional
      DB F.bank.huPaper F.bank.Hinf F.bank.hsmall
      (cosineCoeffs (intervalDomainLift u₀)) F.bank.haInit
      F.bank.hlogSrc F.bank.hchemSrc F.hB_global
      F.bank.hlogCont F.bank.hlogFourier F.bank.hchemCont F.bank.hchemFourier

theorem intervalConjugatePicardLimit_classicalRegularity_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    intervalDomainClassicalRegularity DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  unfold intervalDomainClassicalRegularity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact
      ⟨(bform_u_closedC2_endpointDerivs F.bank F.hTimeNhd t ht.1 ht.2).1.mono
          Set.Ioo_subset_Icc_self,
        bform_vSpatialInterior F.bank F.hTimeNhd t ht⟩
  · intro x t ht
    have hu := timeSlices_u_of_spectralAgreement F.hTimeNhd x
    have hv := timeSlices_v_of_resolverSpectral F.hResolverData x
    exact ⟨⟨hu.1 t ht, hv.1 t ht⟩, ⟨hu.2, hv.2⟩⟩
  · exact
      ⟨jointTimeDerivInterior_u_of_spectralAgreement F.hTimeNhd,
       jointTimeDerivInterior_v_of_resolverSpectral F.hResolverData⟩
  · intro t ht
    exact
      ⟨⟨bform_u_neumann_left F.hTimeNhd t ht.1 ht.2,
          bform_u_neumann_right F.hTimeNhd t ht.1 ht.2⟩,
        bform_vNeumannLimits F.bank F.hTimeNhd t ht⟩
  · intro t ht
    exact
      ⟨bform_u_closedC2_endpointDerivs F.bank F.hTimeNhd t ht.1 ht.2,
        bform_vClosedSpatial F.bank F.hTimeNhd F.hVpos t ht⟩
  · exact
      ⟨jointTimeDerivClosed_u_of_spectralAgreement F.hTimeNhd,
       jointTimeDerivClosed_v_of_resolverSpectral F.hResolverData⟩
  · exact
      ⟨jointSolutionClosed_u_of_spectralAgreement F.hTimeNhd,
       jointSolutionClosed_v_of_resolverSpectral F.hResolverData⟩

theorem intervalConjugatePicardLimit_initialTrace_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    InitialTrace intervalDomain u₀
      (conjugatePicardLimit p u₀ DB.T) :=
  ShenWork.Paper2.BFormInitialTrace.conjugatePicardLimit_initialTrace_of_conjugate_data
    p (PaperPositiveInitialDatum.admissible F.bank.huPaper).2 DB

theorem intervalConjugatePicardLimit_isClassicalSolution_direct
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    IsPaper2ClassicalSolution intervalDomain p DB.T
      (conjugatePicardLimit p u₀ DB.T)
      (mildChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T)) := by
  refine IsPaper2ClassicalSolution.of_components DB.hT
    (intervalConjugatePicardLimit_classicalRegularity_direct F)
    ?_ ?_ ?_ ?_ ?_
  · exact bform_u_pos F.bank
  · intro t x ht htT
    exact le_of_lt (F.hVpos t ht htT x)
  · exact F.hpde_u
  · have h :=
      coupledChemical_ellipticPDE_of_closedC2_neumann p
        (bform_u_pos F.bank)
        (fun t ht htT => (bform_u_closedC2_endpointDerivs F.bank F.hTimeNhd t ht htT).1)
        (bform_u_neumann_left F.hTimeNhd)
        (bform_u_neumann_right F.hTimeNhd)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h
  · have h :=
      coupledChemical_neumannBC_of_closedC2_neumann p
        (bform_u_pos F.bank)
        (fun t ht htT => (bform_u_closedC2_endpointDerivs F.bank F.hTimeNhd t ht htT).1)
        (bform_u_neumann_left F.hTimeNhd)
        (bform_u_neumann_right F.hTimeNhd)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h

theorem localClassicalSolution_of_BFormDirectFrontier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (F : BFormDirectFrontier p DB) :
    ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
      IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
      InitialTrace intervalDomain u₀ u := by
  refine ⟨DB.T, DB.hT,
    conjugatePicardLimit p u₀ DB.T,
    mildChemicalConcentration p (conjugatePicardLimit p u₀ DB.T), ?_⟩
  exact ⟨intervalConjugatePicardLimit_isClassicalSolution_direct F,
    intervalConjugatePicardLimit_initialTrace_direct F⟩

def BFormPaperLocalFrontier (p : CM2Params) : Prop :=
  ∀ u₀ : intervalDomainPoint → ℝ,
    PaperPositiveInitialDatum intervalDomain u₀ →
      ∃ DB : ConjugateMildExistenceData p u₀,
        Nonempty (BFormDirectFrontier p DB)

theorem paperPositive_localExistence_of_BFormDirect
    {p : CM2Params}
    (hPerDatum : BFormPaperLocalFrontier p) :
    ∀ u₀ : intervalDomainPoint → ℝ,
      PaperPositiveInitialDatum intervalDomain u₀ →
        ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
          IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
          InitialTrace intervalDomain u₀ u := by
  intro u₀ hu₀
  obtain ⟨DB, ⟨F⟩⟩ := hPerDatum u₀ hu₀
  exact localClassicalSolution_of_BFormDirectFrontier F

/-- The actual gamma-`≥ 1` continuation umbrella still asks for local existence
for the weaker `PositiveInitialDatum` interface.  This wrapper records that
requirement explicitly rather than pretending that the B-form PID bank proves
`PositiveInitialDatum → PaperPositiveInitialDatum`. -/
theorem paper2_theorem_1_1_general_chi_bform
    (p : CM2Params) (hχ : p.χ₀ ≤ 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hγ_ge_one : 1 ≤ p.γ)
    (hlocal :
      ∀ u₀ : intervalDomainPoint → ℝ,
        PositiveInitialDatum intervalDomain u₀ →
          ∃ Tmax > 0, ∃ u v : ℝ → intervalDomainPoint → ℝ,
            IsPaper2ClassicalSolution intervalDomain p Tmax u v ∧
            InitialTrace intervalDomain u₀ u)
    (hUniform : IntervalDomainUniformLocalExistence p) :
    Theorem_1_1 intervalDomain p := by
  let hData : IntervalDomainPaper2ContinuationDataGammaGeOne_no_hextend_mge p :=
    { localExistence := hlocal
      uniformLocal := hUniform }
  exact Theorem_1_1_intervalDomain_via_regime_gammaGeOne_no_hextend_mge_bundled
    p hχ ha hb hγ_ge_one hData

#print axioms BFormBankedInputs.hsrcB
#print axioms hB_global_of_flux_deriv_reconstruction
#print axioms BFormDirectFrontier.hB_global
#print axioms hasRestartCosineRepresentations_of_BFormDirectFrontier
#print axioms BFormDirectFrontier.hpde_u
#print axioms intervalConjugatePicardLimit_classicalRegularity_direct
#print axioms intervalConjugatePicardLimit_initialTrace_direct
#print axioms intervalConjugatePicardLimit_isClassicalSolution_direct
#print axioms localClassicalSolution_of_BFormDirectFrontier
#print axioms paperPositive_localExistence_of_BFormDirect
#print axioms paper2_theorem_1_1_general_chi_bform

end ShenWork.Paper2.BFormDirectClassical
