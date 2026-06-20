import ShenWork.Paper2.IntervalBFormNeumannDischarge
import ShenWork.PDE.IntervalCoupledRegularityBootstrap

open Filter Topology Set

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint
   intervalDomainClassicalRegularity)
open ShenWork.IntervalMildToClassical
  (mildChemicalConcentration)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumLocalSq

/-- B-form `hpde_v` discharge from the resolver's spectral machinery.

The carried standard fact is the per-slice `SourceCoeffQuadraticDecay`, which is
the termwise-differentiation/summability license for the resolver.  The proof
then consumes the resolver Laplacian bridge, the coefficient-form elliptic
identity, and the source cosine reconstruction; it does not carry the final
elliptic PDE as a field. -/
theorem bForm_mildChemical_hpde_v_of_resolver_source_decay_closedC2
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (Hdecay : BFormResolverSourceDecay p T u)
    (hpos : ∀ t x, 0 < t → t < T → 0 < u t x)
    (hC2 : ∀ t, 0 < t → t < T →
      ContDiffOn ℝ 2 (intervalDomainLift (u t)) (Set.Icc (0 : ℝ) 1))
    (hN0 : ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hN1 : ∀ t, 0 < t → t < T →
      Filter.Tendsto (deriv (intervalDomainLift (u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian (mildChemicalConcentration p u t) x
        - p.μ * mildChemicalConcentration p u t x
        + p.ν * (u t x) ^ p.γ := by
  intro t x ht htT hx
  obtain ⟨hdecay⟩ := Hdecay t ht htT
  have hRLap :=
    ShenWork.IntervalResolverLaplacianBridge.intervalNeumannResolverRLap_elliptic_identity
      hdecay x
  have hlap :
      intervalDomain.laplacian (mildChemicalConcentration p u t) x =
        ShenWork.IntervalResolverLaplacianBridge.intervalNeumannResolverRLap
          p (u t) x := by
    unfold mildChemicalConcentration
    exact
      ShenWork.IntervalCoupledRegularityBootstrap.resolver_laplacian_eq_RLap_of_sourceDecay
        hdecay hx
  have hpos_lift :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift (u t) y := by
    intro y hy
    simp only [intervalDomainLift, hy, dif_pos]
    exact hpos t ⟨y, hy⟩ ht htT
  have hsource :
      ShenWork.IntervalResolverLaplacianBridge.intervalNeumannResolverSourceValue
          p (u t) x =
        p.ν * intervalDomainLift (u t) x.1 ^ p.γ :=
    ShenWork.IntervalCoupledRegularityBootstrap.sourceValue_eq_powerSource_of_closedC2_neumann
      (hC2 t ht htT) (hN0 t ht htT) (hN1 t ht htT) hpos_lift x
  have hxIcc : x.1 ∈ Set.Icc (0 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self hx
  rw [hlap, hRLap, hsource]
  simp only [mildChemicalConcentration, intervalDomainLift, hxIcc, dif_pos]
  have hxsub : (⟨x.1, hxIcc⟩ : intervalDomainPoint) = x := Subtype.ext rfl
  rw [hxsub]
  ring

/-- B-form `hpde_v` constructor from the named resolver source-decay fact plus
the ordinary closed-interval regularity/positivity fields already carried by
the B-form local bundle. -/
theorem bForm_mildChemical_hpde_v_of_resolver_standardFacts
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (Hdecay : BFormResolverSourceDecay p T u)
    (hreg : intervalDomainClassicalRegularity T u
      (mildChemicalConcentration p u))
    (hpos : ∀ t x, 0 < t → t < T → 0 < u t x) :
    ∀ t x, 0 < t → t < T → x ∈ intervalDomain.inside →
      0 = intervalDomain.laplacian (mildChemicalConcentration p u t) x
        - p.μ * mildChemicalConcentration p u t x
        + p.ν * (u t x) ^ p.γ := by
  refine bForm_mildChemical_hpde_v_of_resolver_source_decay_closedC2
    Hdecay hpos ?_ ?_ ?_
  · intro t ht htT
    exact (hreg.2.2.2.2.1 t ⟨ht, htT⟩).1.1
  · intro t ht htT
    exact (hreg.2.2.2.1 t ⟨ht, htT⟩).1.1
  · intro t ht htT
    exact (hreg.2.2.2.1 t ⟨ht, htT⟩).1.2

end ShenWork.Paper2.BFormPositiveDatumLocalSq
