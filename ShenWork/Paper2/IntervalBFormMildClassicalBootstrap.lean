import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalResolverDirectTimeRegularity
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalMildFrontierFromSpectral

open Filter Topology Set
open ShenWork.IntervalDomain ShenWork.IntervalConjugatePicard
open ShenWork.IntervalMildToClassical ShenWork.IntervalSourceCoefficientTimeC1
open ShenWork.IntervalBFormSpectral ShenWork.IntervalMildTimeDerivContinuity
open ShenWork.IntervalResolverDirectTimeRegularity ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverSpatialC2 ShenWork.IntervalCosineSliceRegularity
open ShenWork.CosineSpectrum ShenWork.Paper2 ShenWork.PDE
noncomputable section
namespace ShenWork.Paper2
structure BFormMildSpectralBootstrapData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀) : Prop where
  hPdeAgreement : HasBFormSpectralPdeAgreement p S.T S.u
  hTimeNhd : HasTimeNeighborhoodSpectralAgreement S.T S.u
  hResolverData : HasResolverDirectSpectralData S.T
    (mildChemicalConcentration p S.u) p
  hResolverPos : ∀ t, 0 < t → t < S.T → ∀ x : intervalDomainPoint,
    0 < mildChemicalConcentration p S.u t x
private def midpoint : intervalDomainPoint :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
private theorem midpoint_mem_Ioo :
    (midpoint : intervalDomainPoint).1 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> norm_num [midpoint]
private theorem mild_spectral_slice
    {p : CM2Params} {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (Hpde : HasBFormSpectralPdeAgreement p T u)
    {t : ℝ} (ht : 0 < t) (htT : t < T) :
    ∃ b : ℕ → ℝ,
      Summable (fun n : ℕ => unitIntervalCosineEigenvalue n * |b n|) ∧
      Set.EqOn (intervalDomainLift (u t))
        (fun x : ℝ => ∑' n : ℕ, b n * cosineMode n x)
        (Set.Icc (0 : ℝ) 1) := by
  obtain ⟨a₀, _M, _hM, _ha₀, a, _src, offset, _hoff,
      _hlog, _hchem, hrep, _hsplit, hsum⟩ :=
    Hpde.exists_data t ht htT (x := midpoint) midpoint_mem_Ioo
  refine ⟨fun n => localRestartCoeff a₀ a (t - offset) n, hsum, ?_⟩
  intro x hx
  simp only [intervalDomainLift, hx, dif_pos]
  exact hrep.self_of_nhds ⟨x, hx⟩
private theorem mild_u_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    ∀ t, 0 < t → t < S.T →
      ContDiffOn ℝ 2 (intervalDomainLift (S.u t)) (Set.Icc (0 : ℝ) 1)
        ∧ deriv (intervalDomainLift (S.u t)) 0 = 0
        ∧ deriv (intervalDomainLift (S.u t)) 1 = 0 := by
  intro t ht htT
  obtain ⟨b, hsum, hagree⟩ :=
    mild_spectral_slice H.hPdeAgreement ht htT
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have h0 : intervalDomainLift (S.u t) 0 ≠ 0 := by
    simp only [intervalDomainLift, h0mem, dif_pos]
    exact ne_of_gt (S.hpos t ht (le_of_lt htT) ⟨0, h0mem⟩)
  have h1 : intervalDomainLift (S.u t) 1 ≠ 0 := by
    simp only [intervalDomainLift, h1mem, dif_pos]
    exact ne_of_gt (S.hpos t ht (le_of_lt htT) ⟨1, h1mem⟩)
  exact intervalDomainCosineSlice_conjunct7 hsum hagree h0 h1
private theorem mild_u_neumann_left
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    ∀ t, 0 < t → t < S.T →
      Filter.Tendsto (deriv (intervalDomainLift (S.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro t ht htT
  obtain ⟨b, hsum, hagree⟩ :=
    mild_spectral_slice H.hPdeAgreement ht htT
  exact intervalDomainCosineSlice_neumann_limit_left hsum hagree
private theorem mild_u_neumann_right
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    ∀ t, 0 < t → t < S.T →
      Filter.Tendsto (deriv (intervalDomainLift (S.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht htT
  obtain ⟨b, hsum, hagree⟩ :=
    mild_spectral_slice H.hPdeAgreement ht htT
  exact intervalDomainCosineSlice_neumann_limit_right hsum hagree
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
private def mild_sourceDecay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S)
    {t : ℝ} (ht : 0 < t) (htT : t < S.T) :
    SourceCoeffQuadraticDecay p (S.u t) := by
  have hpos_lift :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (S.u t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact S.hpos t ht (le_of_lt htT) ⟨y, hy⟩
  exact sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    (p := p) (u := S.u t)
    (mild_u_closedC2_endpointDerivs S H t ht htT).1
    (mild_u_neumann_left S H t ht htT)
    (mild_u_neumann_right S H t ht htT)
    hpos_lift
private theorem mild_vSpatialInterior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) S.T →
      ContDiffOn ℝ 2
        (intervalDomainLift (mildChemicalConcentration p S.u t))
        (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  change ContDiffOn ℝ 2
    (intervalDomainLift (intervalNeumannResolverR p (S.u t)))
    (Set.Ioo (0 : ℝ) 1)
  exact intervalDomainCosineSlice_contDiffOn_Ioo
    (resolverR_summability (mild_sourceDecay S H ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (S.u t))
private theorem mild_vNeumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) S.T →
      Filter.Tendsto
          (deriv (intervalDomainLift (mildChemicalConcentration p S.u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift (mildChemicalConcentration p S.u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  intro t ht
  change Filter.Tendsto
          (deriv (intervalDomainLift (intervalNeumannResolverR p (S.u t))))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto
          (deriv (intervalDomainLift (intervalNeumannResolverR p (S.u t))))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  exact
    ⟨intervalDomainCosineSlice_neumann_limit_left
        (resolverR_summability (mild_sourceDecay S H ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (S.u t)),
      intervalDomainCosineSlice_neumann_limit_right
        (resolverR_summability (mild_sourceDecay S H ht.1 ht.2))
        (lift_resolver_eqOn_Icc p (S.u t))⟩
private theorem mild_vClosedSpatial
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) S.T →
      ContDiffOn ℝ 2
          (intervalDomainLift (mildChemicalConcentration p S.u t))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (mildChemicalConcentration p S.u t)) 0 = 0 ∧
        deriv (intervalDomainLift (mildChemicalConcentration p S.u t)) 1 = 0 := by
  intro t ht
  change ContDiffOn ℝ 2
          (intervalDomainLift (intervalNeumannResolverR p (S.u t)))
          (Set.Icc (0 : ℝ) 1) ∧
        deriv (intervalDomainLift (intervalNeumannResolverR p (S.u t))) 0 = 0 ∧
        deriv (intervalDomainLift (intervalNeumannResolverR p (S.u t))) 1 = 0
  have hv0 : 0 < intervalNeumannResolverR p (S.u t)
      ⟨0, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      H.hResolverPos t ht.1 ht.2 ⟨0, by constructor <;> norm_num⟩
  have hv1 : 0 < intervalNeumannResolverR p (S.u t)
      ⟨1, by constructor <;> norm_num⟩ := by
    simpa [mildChemicalConcentration] using
      H.hResolverPos t ht.1 ht.2 ⟨1, by constructor <;> norm_num⟩
  exact intervalDomainCosineSlice_conjunct7
    (resolverR_summability (mild_sourceDecay S H ht.1 ht.2))
    (lift_resolver_eqOn_Icc p (S.u t))
    (resolver_lift_ne_zero ⟨0, by constructor <;> norm_num⟩ hv0)
    (resolver_lift_ne_zero ⟨1, by constructor <;> norm_num⟩ hv1)
theorem classicalRegularity_of_conjugateMild_spectral
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    intervalDomainClassicalRegularity S.T S.u
      (mildChemicalConcentration p S.u) := by
  unfold intervalDomainClassicalRegularity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact
      ⟨(mild_u_closedC2_endpointDerivs S H t ht.1 ht.2).1.mono
          Set.Ioo_subset_Icc_self,
        mild_vSpatialInterior S H t ht⟩
  · intro x t ht
    have huDiff :
        ∀ t ∈ Set.Ioo (0 : ℝ) S.T,
          DifferentiableAt ℝ (fun s => S.u s x) t := by
      intro t ht
      obtain ⟨a₀, M, hM, ha₀, a, src, offset, hτ, hagree⟩ :=
        H.hTimeNhd.exists_data t ht.1 ht.2
      exact (ShenWork.IntervalMildTimeDerivContinuity.mildSolution_hasDerivAt_time
        hM ha₀ src hτ hagree x).differentiableAt
    have huCont :
        ContinuousOn (fun s => deriv (fun r => S.u r x) s)
          (Set.Ioo (0 : ℝ) S.T) :=
      ShenWork.IntervalMildTimeDerivContinuity.mildSolution_timeDeriv_continuousOn_fixed_x
        H.hTimeNhd x
    have hvDiff :
        ∀ t ∈ Set.Ioo (0 : ℝ) S.T,
          DifferentiableAt ℝ
            (fun s => mildChemicalConcentration p S.u s x) t := by
      intro t ht
      exact ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_differentiableAt_time
        H.hResolverData ht.1 ht.2 x
    have hvCont :
        ContinuousOn
          (fun s => deriv (fun r => mildChemicalConcentration p S.u r x) s)
          (Set.Ioo (0 : ℝ) S.T) :=
      ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_timeDeriv_continuousOn
        H.hResolverData x
    exact ⟨⟨huDiff t ht, hvDiff t ht⟩, ⟨huCont, hvCont⟩⟩
  · exact
      ⟨ShenWork.IntervalMildTimeDerivContinuity.mildSolution_timeDeriv_jointContinuousOn
          H.hTimeNhd,
       ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_jointTimeDerivInterior
          H.hResolverData⟩
  · intro t ht
    exact
      ⟨⟨mild_u_neumann_left S H t ht.1 ht.2,
          mild_u_neumann_right S H t ht.1 ht.2⟩,
        mild_vNeumannLimits S H t ht⟩
  · intro t ht
    exact
      ⟨mild_u_closedC2_endpointDerivs S H t ht.1 ht.2,
        mild_vClosedSpatial S H t ht⟩
  · exact
      ⟨ShenWork.IntervalMildFrontierFromSpectral.mildSolution_timeDeriv_jointContinuousOn_closed
          H.hTimeNhd,
       ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_jointTimeDerivClosed
          H.hResolverData⟩
  · exact
      ⟨ShenWork.IntervalMildFrontierFromSpectral.mildSolution_jointContinuousOn_closed
          H.hTimeNhd,
       ShenWork.IntervalResolverDirectTimeRegularity.resolver_direct_jointSolutionClosed
          H.hResolverData⟩
theorem isClassicalSolution_of_conjugateMild_spectral
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S) :
    IsPaper2ClassicalSolution intervalDomain p S.T S.u
      (mildChemicalConcentration p S.u) := by
  refine IsPaper2ClassicalSolution.of_components S.hT
    (classicalRegularity_of_conjugateMild_spectral S H)
    ?_ ?_ ?_ ?_ ?_
  · intro t x ht htT
    exact S.hpos t ht (le_of_lt htT) x
  · intro t x ht htT
    exact le_of_lt (H.hResolverPos t ht htT x)
  · exact intervalConjugateMildSolution_pde_u_of_spectral p S.hmild
      H.hPdeAgreement
  · have h :=
      coupledChemical_ellipticPDE_of_closedC2_neumann p
        (fun t x ht htT => S.hpos t ht (le_of_lt htT) x)
        (fun t ht htT => (mild_u_closedC2_endpointDerivs S H t ht htT).1)
        (mild_u_neumann_left S H)
        (mild_u_neumann_right S H)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h
  · have h :=
      coupledChemical_neumannBC_of_closedC2_neumann p
        (fun t x ht htT => S.hpos t ht (le_of_lt htT) x)
        (fun t ht htT => (mild_u_closedC2_endpointDerivs S H t ht htT).1)
        (mild_u_neumann_left S H)
        (mild_u_neumann_right S H)
    simpa [coupledChemicalConcentration, mildChemicalConcentration] using h
theorem localClassicalSolution_of_conjugateMild_spectral
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (S : ConjugateMildSolutionData p u₀)
    (H : BFormMildSpectralBootstrapData p S)
    (hTrace : InitialTrace intervalDomain u₀ S.u) :
    ∃ u v, IsPaper2ClassicalSolution intervalDomain p S.T u v ∧
      InitialTrace intervalDomain u₀ u := by
  exact ⟨S.u, mildChemicalConcentration p S.u,
    isClassicalSolution_of_conjugateMild_spectral S H, hTrace⟩
#print axioms isClassicalSolution_of_conjugateMild_spectral
#print axioms localClassicalSolution_of_conjugateMild_spectral
end ShenWork.Paper2
