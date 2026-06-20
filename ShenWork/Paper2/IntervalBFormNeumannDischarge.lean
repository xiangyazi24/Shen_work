import ShenWork.Paper2.IntervalBFormSpectralPdeAgreementStandardFacts
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalDomainNormalDeriv)
open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalBFormSpectral
  (bFormChemFluxAt bFormConjugateDuhamelLeg bFormLogisticDuhamelLeg)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)
open ShenWork.IntervalResolverGradientBridge
  (resolverR_apply_eq)
open ShenWork.PDE
  (intervalNeumannResolverR intervalNeumannResolverCoeff
   intervalNeumannResolverRGrad)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- Endpoint vanishing of the actual B-form chemotaxis flux on the current time
window.  This is the compatibility input that removes the boundary layer in the
B-kernel Duhamel leg. -/
def BFormChemFluxBoundaryVanishing
    (p : CM2Params) (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ s, 0 < s → s < T →
    bFormChemFluxAt p u s 0 = 0 ∧ bFormChemFluxAt p u s 1 = 0

/-- The B-form flux vanishes at both endpoints because its numerator contains
`resolverGradReal`, whose sine series is zero at `0` and `1`. -/
theorem bFormChemFluxBoundaryVanishing_of_resolverGradReal_zero
    (p : CM2Params) {T : ℝ}
    (u : ℝ → intervalDomainPoint → ℝ) :
    BFormChemFluxBoundaryVanishing p T u := by
  intro s _hs _hsT
  constructor
  · unfold bFormChemFluxAt chemFluxLifted
    rw [resolverGradReal_zero]
    simp
  · unfold bFormChemFluxAt chemFluxLifted
    rw [resolverGradReal_one]
    simp

/-- Per-slice resolver coefficient decay/termwise-differentiation license for
the actual Picard trajectory.  This is a deeper resolver regularity input, not a
boundary conclusion. -/
def BFormResolverSourceDecay
    (p : CM2Params) (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t < T → Nonempty (SourceCoeffQuadraticDecay p (u t))

/-- The initial heat leg preserves the Neumann condition at the boundary. -/
def BFormInitialHeatLegNeumann
    (_p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ) : Prop :=
  ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
    intervalDomain.normalDeriv
      (fun y : intervalDomainPoint =>
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
          (intervalDomainLift u₀) y.1) x = 0

/-- The ordinary reaction Duhamel leg has homogeneous Neumann boundary
derivative. -/
def BFormLogisticDuhamelLegNeumann
    (p : CM2Params) (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
    intervalDomain.normalDeriv
      (fun y : intervalDomainPoint =>
        bFormLogisticDuhamelLeg p u t y.1) x = 0

/-- The B-kernel chemotaxis Duhamel leg has homogeneous Neumann boundary
derivative once the actual flux has zero boundary trace.  Analytically this is
the compatibility/DCT fact: boundary vanishing replaces the nonintegrable
mixed-kernel singularity by the ordinary heat-kernel gradient bound. -/
def BFormChemotaxisDuhamelLegNeumannFromCompatibleFlux
    (p : CM2Params) (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  BFormChemFluxBoundaryVanishing p T u →
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv
        (fun y : intervalDomainPoint =>
          bFormConjugateDuhamelLeg p u t y.1) x = 0

/-- Algebraic/mild-profile assembly: the normal derivative of the actual
fixed-point profile is the corresponding linear combination of the three named
legs.  The zero boundary condition is derived from this equality and the
separate leg facts. -/
def BFormMildProfileNeumannAssembly
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
    intervalDomain.normalDeriv (u t) x =
      intervalDomain.normalDeriv
          (fun y : intervalDomainPoint =>
            ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t
              (intervalDomainLift u₀) y.1) x
        + (-p.χ₀) *
          intervalDomain.normalDeriv
            (fun y : intervalDomainPoint =>
              bFormConjugateDuhamelLeg p u t y.1) x
        + intervalDomain.normalDeriv
          (fun y : intervalDomainPoint =>
            bFormLogisticDuhamelLeg p u t y.1) x

/-- Named standard facts reducing the B-form Neumann boundary condition to
resolver endpoint cancellation and linear heat-kernel/Duhamel facts on the
actual Picard trajectory. -/
structure BFormNeumannStandardFacts
    (p : CM2Params) (T : ℝ) (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  resolver_source_decay : BFormResolverSourceDecay p T u
  initial_heat_leg : BFormInitialHeatLegNeumann p T u₀
  logistic_duhamel_leg : BFormLogisticDuhamelLegNeumann p T u
  chemotaxis_duhamel_leg :
    BFormChemotaxisDuhamelLegNeumannFromCompatibleFlux p T u
  mild_profile_assembly : BFormMildProfileNeumannAssembly p T u₀ u

/-- Resolver Neumann boundary condition proved from source-decay
termwise-differentiation and the already proved endpoint identities
`resolverGradReal_zero`/`resolverGradReal_one`. -/
theorem intervalNeumannResolverR_normalDeriv_zero_of_sourceDecay_using_resolverGradReal
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    {x : intervalDomainPoint} (hx : x ∈ intervalDomain.boundary) :
    intervalDomain.normalDeriv (intervalNeumannResolverR p u) x = 0 := by
  classical
  change intervalDomainNormalDeriv (intervalNeumannResolverR p u) x = 0
  set S : ℝ → ℝ := fun z : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hS
  have hS0 : HasDerivWithinAt S 0 (Set.Ici (0 : ℝ)) 0 := by
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have h :=
      solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay h0Icc
    have hgrad0 : intervalNeumannResolverRGrad p u ⟨0, h0Icc⟩ = 0 := by
      rw [← resolverGradReal_eq p u ⟨0, h0Icc⟩]
      exact resolverGradReal_zero p u
    have hderiv : HasDerivAt S 0 0 := by
      simpa [S] using h.congr_deriv hgrad0
    exact hderiv.hasDerivWithinAt
  have hS1 : HasDerivWithinAt S 0 (Set.Iic (1 : ℝ)) 1 := by
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have h :=
      solution_resolver_grad_hasDerivAt_of_sourceDecay hdecay h1Icc
    have hgrad1 : intervalNeumannResolverRGrad p u ⟨1, h1Icc⟩ = 0 := by
      rw [← resolverGradReal_eq p u ⟨1, h1Icc⟩]
      exact resolverGradReal_one p u
    have hderiv : HasDerivAt S 0 1 := by
      simpa [S] using h.congr_deriv hgrad1
    exact hderiv.hasDerivWithinAt
  have hEq0 :
      intervalDomainLift (intervalNeumannResolverR p u)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici 0)] S := by
    have hnear :
        ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ici 0),
          y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy0 hy1 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp only [intervalDomainLift, hy, dif_pos]
    rw [resolverR_apply_eq, hS]
  have hEq1 :
      intervalDomainLift (intervalNeumannResolverR p u)
        =ᶠ[nhdsWithin (1 : ℝ) (Set.Iic 1)] S := by
    have hnear :
        ∀ᶠ y in nhdsWithin (1 : ℝ) (Set.Iic 1),
          y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ici_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
        with y hy1 hy0 using ⟨hy0, hy1⟩
    filter_upwards [hnear] with y hy
    simp only [intervalDomainLift, hy, dif_pos]
    rw [resolverR_apply_eq, hS]
  rcases hx with h0 | h1
  · unfold intervalDomainNormalDeriv
    rw [if_pos h0]
    have h0Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hEqAt0 : intervalDomainLift (intervalNeumannResolverR p u) 0 = S 0 := by
      simp only [intervalDomainLift, h0Icc, dif_pos]
      rw [resolverR_apply_eq, hS]
    exact (hS0.congr_of_eventuallyEq hEq0 hEqAt0).derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))
  · unfold intervalDomainNormalDeriv
    rw [if_neg (by rw [h1]; norm_num), if_pos h1]
    have h1Icc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hEqAt1 : intervalDomainLift (intervalNeumannResolverR p u) 1 = S 1 := by
      simp only [intervalDomainLift, h1Icc, dif_pos]
      rw [resolverR_apply_eq, hS]
    exact (hS1.congr_of_eventuallyEq hEq1 hEqAt1).derivWithin
      (uniqueDiffWithinAt_Iic (1 : ℝ))

/-- The chemical concentration is the elliptic resolver, so its Neumann boundary
condition follows from the resolver endpoint cancellation and source-decay
license. -/
theorem bForm_mildChemical_normalDeriv_zero_of_sourceDecay
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (Hdecay : BFormResolverSourceDecay p T u) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv (mildChemicalConcentration p u t) x = 0 := by
  intro t x ht htT hx
  unfold mildChemicalConcentration
  obtain ⟨hdecay⟩ := Hdecay t ht htT
  exact
    intervalNeumannResolverR_normalDeriv_zero_of_sourceDecay_using_resolverGradReal
      hdecay hx

/-- Constructor discharging the B-form `neumann` field.  The proof derives the
`u` boundary condition from flux endpoint compatibility plus the named linear
heat/Duhamel facts, and derives the `v` boundary condition from the resolver
gradient endpoint identities. -/
theorem bForm_neumann_of_standardFacts
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (H : BFormNeumannStandardFacts p T u₀ u) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.boundary →
      intervalDomain.normalDeriv (u t) x = 0 ∧
        intervalDomain.normalDeriv (mildChemicalConcentration p u t) x = 0 := by
  intro t x ht htT hx
  have hflux : BFormChemFluxBoundaryVanishing p T u :=
    bFormChemFluxBoundaryVanishing_of_resolverGradReal_zero p u
  have hinit := H.initial_heat_leg t x ht htT hx
  have hchem := H.chemotaxis_duhamel_leg hflux t x ht htT hx
  have hlog := H.logistic_duhamel_leg t x ht htT hx
  constructor
  · rw [H.mild_profile_assembly t x ht htT hx, hinit, hchem, hlog]
    ring
  · exact bForm_mildChemical_normalDeriv_zero_of_sourceDecay
      H.resolver_source_decay t x ht htT hx

end ShenWork.Paper2.BFormPositiveDatumLocalSq
