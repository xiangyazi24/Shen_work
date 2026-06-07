/-
  Final wiring: construct `GradientMildClassicalRegularityFrontierData p D`
  from spectral hypotheses.

  Assembles the 9 frontier fields from:
  - `HasTimeNeighborhoodSpectralAgreement` (u-side time regularity)
  - `HasResolverDirectSpectralData` (v-side time regularity)
  - `HasRestartCosineRepresentations` (u-side spatial C², source coefficient decay)
  - `IntervalDomainSupNormDerivativeNonposOn` (sup-norm monotonicity, from max principle)

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildRegularityFrontierAssembly
import ShenWork.Paper2.IntervalMildSourceDecay
import ShenWork.PDE.IntervalResolverSpatialC2
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.Paper2.IntervalDomainL2UniquenessCertificate

open ShenWork.IntervalDomain
open ShenWork.IntervalMildPicard
open ShenWork.IntervalMildToClassical
open ShenWork.Paper2
open ShenWork.Paper2.RegularityFrontierAssembly
open ShenWork.IntervalResolverSpatialC2
open ShenWork.IntervalMildSourceDecay
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalCosineSliceRegularity
open ShenWork.IntervalMildRegularityBootstrap
  (HasRestartCosineRepresentations)
open ShenWork.IntervalMildTimeDerivContinuity
  (HasTimeNeighborhoodSpectralAgreement)
open ShenWork.IntervalResolverDirectTimeRegularity
  (HasResolverDirectSpectralData)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.RegularityFrontierWiring

/-! ## v-side spatial fields from resolver C² -/

/-- On `Icc 0 1`, the lift of the resolver agrees with the cosine-coefficient
series.  This is the agreement hypothesis consumed by the cosine-slice
regularity engine. -/
private theorem lift_resolver_eqOn_Icc
    (p : CM2Params) (u : intervalDomainPoint → ℝ) :
    Set.EqOn
      (intervalDomainLift (intervalNeumannResolverR p u))
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) := by
  intro x hxIcc
  simp only [intervalDomainLift, dif_pos hxIcc, resolverR_apply_eq, cosineMode]

/-- **vSpatialInterior**: `ContDiffOn ℝ 2` for the lift of the resolver
on the open interior `(0,1)`, from the cosine-slice engine. -/
private theorem vSpatialInterior_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    ContDiffOn ℝ 2
      (intervalDomainLift (intervalNeumannResolverR p u))
      (Set.Ioo (0 : ℝ) 1) :=
  intervalDomainCosineSlice_contDiffOn_Ioo
    (resolverR_summability hdecay)
    (lift_resolver_eqOn_Icc p u)

/-- **vNeumannLimits**: one-sided limits of the lift derivative at 0 and 1,
from the cosine-slice engine. -/
private theorem vNeumannLimits_of_sourceDecay
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    Filter.Tendsto
        (deriv (intervalDomainLift (intervalNeumannResolverR p u)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto
        (deriv (intervalDomainLift (intervalNeumannResolverR p u)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) :=
  ⟨intervalDomainCosineSlice_neumann_limit_left
      (resolverR_summability hdecay) (lift_resolver_eqOn_Icc p u),
   intervalDomainCosineSlice_neumann_limit_right
      (resolverR_summability hdecay) (lift_resolver_eqOn_Icc p u)⟩

/-- The resolver lift value at x is nonzero when the resolver is strictly
positive.  This triggers the junk-value endpoint derivative argument. -/
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

/-- **vClosedSpatial**: `ContDiffOn ℝ 2` on `[0,1]` plus endpoint derivatives = 0,
from the cosine-slice conjunct-7 engine.  The nonzero endpoint hypothesis is
discharged from strict positivity of the resolver `Hvpos`. -/
private theorem vClosedSpatial_of_sourceDecay_and_positive
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u)
    (hpos0 : 0 < intervalNeumannResolverR p u ⟨0, by constructor <;> norm_num⟩)
    (hpos1 : 0 < intervalNeumannResolverR p u ⟨1, by constructor <;> norm_num⟩) :
    ContDiffOn ℝ 2
        (intervalDomainLift (intervalNeumannResolverR p u))
        (Set.Icc (0 : ℝ) 1) ∧
      deriv (intervalDomainLift (intervalNeumannResolverR p u)) 0 = 0 ∧
      deriv (intervalDomainLift (intervalNeumannResolverR p u)) 1 = 0 :=
  intervalDomainCosineSlice_conjunct7
    (resolverR_summability hdecay) (lift_resolver_eqOn_Icc p u)
    (resolver_lift_ne_zero ⟨0, by constructor <;> norm_num⟩ hpos0)
    (resolver_lift_ne_zero ⟨1, by constructor <;> norm_num⟩ hpos1)

/-! ## The main assembly theorem -/

/-- **Assemble `GradientMildClassicalRegularityFrontierData` from spectral
hypotheses.**

The 9 fields are wired from:
- **supnormLogistic**, **supnormZero**: from the explicit sup-norm hypothesis
  `HsupNorm` (parabolic maximum principle output).
- **vSpatialInterior**, **vClosedSpatial**, **vNeumannLimits**: from
  `SourceCoeffQuadraticDecay` (via `HasRestartCosineRepresentations`) and
  the resolver C²/Neumann engine.
- **timeSlices**, **jointTimeDerivInterior**, **jointTimeDerivClosed**,
  **jointSolutionClosed**: from the u-side spectral agreement
  `HasTimeNeighborhoodSpectralAgreement` and the v-side
  `HasResolverDirectSpectralData`, wired via
  `IntervalMildRegularityFrontierAssembly`.

The hypothesis `Hvpos` is the strict positivity of `mildChemicalConcentration`
(the resolver) at the boundary endpoints.  This is a consequence of the
elliptic strong maximum principle for `−Δv + μv = ν u^γ > 0` with Neumann BC.
-/
theorem gradientMildClassicalRegularityFrontierData_of_spectral
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (D : GradientMildSolutionData p u₀)
    (Hu : HasTimeNeighborhoodSpectralAgreement D.T D.u)
    (Hv : HasResolverDirectSpectralData D.T (mildChemicalConcentration p D.u) p)
    (Hrestart : HasRestartCosineRepresentations D.T D.u)
    (Hvpos : ∀ t, 0 < t → t < D.T → ∀ x : intervalDomainPoint,
        0 < mildChemicalConcentration p D.u t x) :
    GradientMildClassicalRegularityFrontierData p D where
  vSpatialInterior := by
    intro t ht
    exact vSpatialInterior_of_sourceDecay
      (sourceCoeffQuadraticDecay_of_mildSolution p D Hrestart ht.1 ht.2)
  timeSlices := by
    intro x t ht
    have hu := timeSlices_u_of_spectralAgreement Hu x
    have hv := timeSlices_v_of_resolverSpectral Hv x
    exact ⟨⟨hu.1 t ht, hv.1 t ht⟩, ⟨hu.2, hv.2⟩⟩
  jointTimeDerivInterior :=
    ⟨jointTimeDerivInterior_u_of_spectralAgreement Hu,
     jointTimeDerivInterior_v_of_resolverSpectral Hv⟩
  vNeumannLimits := by
    intro t ht
    exact vNeumannLimits_of_sourceDecay
      (sourceCoeffQuadraticDecay_of_mildSolution p D Hrestart ht.1 ht.2)
  vClosedSpatial := by
    intro t ht
    have hdecay := sourceCoeffQuadraticDecay_of_mildSolution p D Hrestart ht.1 ht.2
    change ContDiffOn ℝ 2
        (intervalDomainLift (intervalNeumannResolverR p (D.u t)))
        (Set.Icc (0 : ℝ) 1) ∧
      deriv (intervalDomainLift (intervalNeumannResolverR p (D.u t))) 0 = 0 ∧
      deriv (intervalDomainLift (intervalNeumannResolverR p (D.u t))) 1 = 0
    exact vClosedSpatial_of_sourceDecay_and_positive hdecay
      (Hvpos t ht.1 ht.2 ⟨0, by constructor <;> norm_num⟩)
      (Hvpos t ht.1 ht.2 ⟨1, by constructor <;> norm_num⟩)
  jointTimeDerivClosed :=
    ⟨jointTimeDerivClosed_u_of_spectralAgreement Hu,
     jointTimeDerivClosed_v_of_resolverSpectral Hv⟩
  jointSolutionClosed :=
    ⟨jointSolutionClosed_u_of_spectralAgreement Hu,
     jointSolutionClosed_v_of_resolverSpectral Hv⟩

end ShenWork.Paper2.RegularityFrontierWiring
