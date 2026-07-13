/-
  Closed spatial regularity of the faithful conjugate mild solution and its
  elliptically coupled chemical concentration.

  The parabolic component supplies closed C2 and genuine Neumann limits.  The
  elliptic component then follows from quadratic cosine-coefficient decay of
  the power source and the existing resolver cosine-series engine.
-/
import ShenWork.Paper2.IntervalDomainMConjugateMildInteriorC2
import ShenWork.PDE.IntervalCoupledRegularityBootstrap
import ShenWork.PDE.IntervalCosineSliceRegularity

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.PDE
  (intervalNeumannResolverCoeff intervalNeumannResolverR)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration
    sourceCoeffQuadraticDecay_of_closedC2_neumann_slice)
open ShenWork.IntervalResolverSpatialC2
  (resolverR_contDiffOn_Icc resolverR_summability)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainCosineSlice_contDiffOn_Ioo
    intervalDomainCosineSlice_neumann_limit_left
    intervalDomainCosineSlice_neumann_limit_right)

/-- On the physical closed interval, the zero-extended elliptic resolver agrees
with its global cosine-series representative. -/
theorem intervalDomainLift_resolverR_eq_cosineSeries_on_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Set.EqOn
      (intervalDomainLift (intervalNeumannResolverR p u))
      (fun x : ℝ ↦ ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [intervalDomainLift, dif_pos hx,
    ShenWork.IntervalResolverGradientBridge.resolverR_apply_eq, cosineMode]

/-- Every positive-time faithful mild slice gives the quadratic source-mode
decay required by the elliptic resolver. -/
def conjugateMildM_sourceCoeffQuadraticDecay
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    SourceCoeffQuadraticDecay p (D.u t) := by
  have hN := conjugateMildM_intervalDomainLift_neumannLimits
    D hu₀ hu₀_meas ht htT
  have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < intervalDomainLift (D.u t) x := by
    intro x hx
    simp only [intervalDomainLift, dif_pos hx]
    exact D.hc.trans_le (D.hfloor t ht htT ⟨x, hx⟩)
  exact sourceCoeffQuadraticDecay_of_closedC2_neumann_slice
    (conjugateMildM_intervalDomainLift_contDiffOn_two_closed
      D hu₀ hu₀_meas ht htT)
    hN.1 hN.2 hpos

/-- Interior spatial C2 regularity of the elliptically coupled chemical
concentration attached to every positive-time faithful mild slice. -/
theorem conjugateMildM_coupledChemical_contDiffOn_two_interior
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContDiffOn ℝ 2
      (intervalDomainLift (coupledChemicalConcentration p D.u t))
      (Set.Ioo (0 : ℝ) 1) := by
  change ContDiffOn ℝ 2
    (intervalDomainLift (intervalNeumannResolverR p (D.u t)))
    (Set.Ioo (0 : ℝ) 1)
  have hdecay := conjugateMildM_sourceCoeffQuadraticDecay
    D hu₀ hu₀_meas ht htT
  exact intervalDomainCosineSlice_contDiffOn_Ioo
    (resolverR_summability hdecay)
    (intervalDomainLift_resolverR_eq_cosineSeries_on_Icc p (D.u t))

/-- Genuine one-sided homogeneous Neumann limits for the elliptically coupled
chemical concentration. -/
theorem conjugateMildM_coupledChemical_neumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    Tendsto
        (deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto
        (deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  change Tendsto
        (deriv (intervalDomainLift (intervalNeumannResolverR p (D.u t))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Tendsto
        (deriv (intervalDomainLift (intervalNeumannResolverR p (D.u t))))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)
  have hdecay := conjugateMildM_sourceCoeffQuadraticDecay
    D hu₀ hu₀_meas ht htT
  have hagree :=
    intervalDomainLift_resolverR_eq_cosineSeries_on_Icc p (D.u t)
  exact ⟨intervalDomainCosineSlice_neumann_limit_left
      (resolverR_summability hdecay) hagree,
    intervalDomainCosineSlice_neumann_limit_right
      (resolverR_summability hdecay) hagree⟩

/-- Closed spatial C2 regularity and the ordinary endpoint derivative package
for the elliptically coupled chemical concentration.  The genuine boundary
content is supplied separately by `conjugateMildM_coupledChemical_neumannLimits`;
the two ordinary endpoint values use the repository's zero-extension
convention. -/
theorem conjugateMildM_coupledChemical_closedC2_endpointDerivs
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) :
    ContDiffOn ℝ 2
        (intervalDomainLift (coupledChemicalConcentration p D.u t))
        (Set.Icc (0 : ℝ) 1) ∧
      deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)) 0 = 0 ∧
      deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)) 1 = 0 := by
  change ContDiffOn ℝ 2
        (intervalDomainLift (intervalNeumannResolverR p (D.u t)))
        (Set.Icc (0 : ℝ) 1) ∧
      deriv (intervalDomainLift (intervalNeumannResolverR p (D.u t))) 0 = 0 ∧
      deriv (intervalDomainLift (intervalNeumannResolverR p (D.u t))) 1 = 0
  have hdecay := conjugateMildM_sourceCoeffQuadraticDecay
    D hu₀ hu₀_meas ht htT
  refine ⟨(resolverR_contDiffOn_Icc hdecay).congr
      (intervalDomainLift_resolverR_eq_cosineSeries_on_Icc p (D.u t)),
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_zero _,
    ShenWork.IntervalFullKernelRegularity.deriv_intervalDomainLift_eq_zero_at_one _⟩

/-- The faithful mild solution and its elliptic resolver jointly discharge the
interior spatial-C2 field of `IntervalClassicalRegularityAtoms`. -/
theorem conjugateMildM_coupled_interiorC2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T →
      ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Ioo (0 : ℝ) 1) ∧
        ContDiffOn ℝ 2
          (intervalDomainLift (coupledChemicalConcentration p D.u t))
          (Set.Ioo (0 : ℝ) 1) := by
  intro t ht
  exact ⟨conjugateMildM_intervalDomainLift_contDiffOn_two_interior
      D hu₀ hu₀_meas ht.1 ht.2.le,
    conjugateMildM_coupledChemical_contDiffOn_two_interior
      D hu₀ hu₀_meas ht.1 ht.2.le⟩

/-- The faithful mild solution and its elliptic resolver jointly discharge the
genuine one-sided Neumann-limit field of `IntervalClassicalRegularityAtoms`. -/
theorem conjugateMildM_coupled_neumannLimits
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T →
      (Tendsto (deriv (intervalDomainLift (D.u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Tendsto (deriv (intervalDomainLift (D.u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) ∧
      (Tendsto
          (deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Tendsto
          (deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0)) := by
  intro t ht
  exact ⟨conjugateMildM_intervalDomainLift_neumannLimits
      D hu₀ hu₀_meas ht.1 ht.2.le,
    conjugateMildM_coupledChemical_neumannLimits
      D hu₀ hu₀_meas ht.1 ht.2.le⟩

/-- The faithful mild solution and its elliptic resolver jointly discharge the
closed spatial-C2 field of `IntervalClassicalRegularityAtoms`. -/
theorem conjugateMildM_coupled_closedC2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀ : ∀ x, |intervalDomainLift u₀ x| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable (intervalDomainLift u₀) (intervalMeasure 1)) :
    ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) D.T →
      (ContDiffOn ℝ 2 (intervalDomainLift (D.u t)) (Set.Icc (0 : ℝ) 1) ∧
          deriv (intervalDomainLift (D.u t)) 0 = 0 ∧
          deriv (intervalDomainLift (D.u t)) 1 = 0) ∧
        (ContDiffOn ℝ 2
            (intervalDomainLift (coupledChemicalConcentration p D.u t))
            (Set.Icc (0 : ℝ) 1) ∧
          deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)) 0 = 0 ∧
          deriv (intervalDomainLift (coupledChemicalConcentration p D.u t)) 1 = 0) := by
  intro t ht
  exact ⟨conjugateMildM_intervalDomainLift_closedC2_endpointDerivs
      D hu₀ hu₀_meas ht.1 ht.2.le,
    conjugateMildM_coupledChemical_closedC2_endpointDerivs
      D hu₀ hu₀_meas ht.1 ht.2.le⟩

end ShenWork.Paper2

#print axioms ShenWork.Paper2.intervalDomainLift_resolverR_eq_cosineSeries_on_Icc
#print axioms ShenWork.Paper2.conjugateMildM_sourceCoeffQuadraticDecay
#print axioms ShenWork.Paper2.conjugateMildM_coupledChemical_contDiffOn_two_interior
#print axioms ShenWork.Paper2.conjugateMildM_coupledChemical_neumannLimits
#print axioms ShenWork.Paper2.conjugateMildM_coupledChemical_closedC2_endpointDerivs
#print axioms ShenWork.Paper2.conjugateMildM_coupled_interiorC2
#print axioms ShenWork.Paper2.conjugateMildM_coupled_neumannLimits
#print axioms ShenWork.Paper2.conjugateMildM_coupled_closedC2
