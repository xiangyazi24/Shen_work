/- Positive-time C2 bridge for the linear and quadratic signal components. -/
import ShenWork.Paper3.IntervalDomainResolvedSourceC2
import ShenWork.Paper3.IntervalDomainSignalStrongBounds
import ShenWork.PDE.IntervalMildSourceDecayHelper

namespace ShenWork.Paper3

open Set
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper

noncomputable section

/-- Exact regularity data supplied by a positive-time classical slice.  It is
qualitative only: the quantitative smallness estimate comes separately from
the strong norm and elliptic identity. -/
structure ResolvedSourceProfileRegularity (f : ℝ → ℝ) where
  weakH2 : IntervalWeakH2Neumann f
  representative : ℝ → ℝ
  representative_continuous : Continuous representative
  representative_fourier_summable :
    Summable (fun n : ℤ => fourierCoeff
      (ShenWork.IntervalCosineInversion.reflCircle representative) n)
  representative_eq : ∀ x ∈ Set.Icc (0 : ℝ) 1, representative x = f x
  coeff_eq : ∀ k, cosineCoeffs f k = cosineCoeffs representative k

theorem ResolvedSourceProfileRegularity.profile_aestronglyMeasurable
    {f : ℝ → ℝ} (H : ResolvedSourceProfileRegularity f) :
    MeasureTheory.AEStronglyMeasurable f (intervalMeasure 1) := by
  have heq : H.representative =ᵐ[intervalMeasure 1] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    exact H.representative_eq x hx
  exact H.representative_continuous.aestronglyMeasurable.congr heq

noncomputable def resolvedSourceCoeffQuadraticDecay_of_profile
    {f : ℝ → ℝ} (H : ResolvedSourceProfileRegularity f) :
    ResolvedSourceCoeffQuadraticDecay (cosineCoeffs f) := by
  let hex := intervalWeakH2Neumann_cosineCoeff_quadratic_decay H.weakH2
  let C := Classical.choose hex
  exact ⟨C, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩

theorem resolvedSourceGradient_hasDerivAt_profile
    (p : CM2Params) {f : ℝ → ℝ}
    (H : ResolvedSourceProfileRegularity f)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (paper3ResolvedSourceGradient p (cosineCoeffs f))
      (p.μ * paper3ResolvedSourceValue p (cosineCoeffs f) x - f x) x := by
  let Hd := resolvedSourceCoeffQuadraticDecay_of_profile H
  have hreconstruct : paper3ResolvedSourceSourceValue (cosineCoeffs f) x = f x := by
    apply paper3ResolvedSourceSourceValue_eq_of_cosineRepresentative
      H.representative_continuous H.representative_fourier_summable
      (fun k => H.coeff_eq k) hx
    exact H.representative_eq x (Set.Ioo_subset_Icc_self hx)
  rw [← hreconstruct,
    ← paper3ResolvedSourceLaplacian_eq_elliptic p Hd x]
  exact paper3ResolvedSourceGradient_hasDerivAt_laplacian p Hd x

theorem paper3LinearSignalGradient_hasDerivAt_laplacian
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (H : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar u))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (paper3LinearSignalGradient p uStar u)
      (paper3LinearSignalLaplacian p uStar u x) x := by
  simpa [paper3LinearSignalGradient, paper3LinearSignalLaplacian,
    paper3LinearSignalValue, paper3LinearEllipticSourceCoeffReal] using
    (resolvedSourceGradient_hasDerivAt_profile p H hx)

theorem paper3QuadraticSignalGradient_hasDerivAt_laplacian
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (H : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar u))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (paper3QuadraticSignalGradient p uStar u)
      (paper3QuadraticSignalLaplacian p uStar u x) x := by
  simpa [paper3QuadraticSignalGradient, paper3QuadraticSignalLaplacian,
    paper3QuadraticSignalValue, paper3QuadraticEllipticSourceCoeffReal] using
    (resolvedSourceGradient_hasDerivAt_profile p H hx)

theorem paper3LinearSignalGradient_continuous
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (H : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar u)) :
    Continuous (paper3LinearSignalGradient p uStar u) := by
  rw [continuous_iff_continuousAt]
  intro x
  have Hd := resolvedSourceCoeffQuadraticDecay_of_profile H
  simpa [paper3LinearSignalGradient, paper3LinearEllipticSourceCoeffReal] using
    (paper3ResolvedSourceGradient_hasDerivAt_laplacian p Hd x).continuousAt

theorem paper3QuadraticSignalGradient_continuous
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (H : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar u)) :
    Continuous (paper3QuadraticSignalGradient p uStar u) := by
  rw [continuous_iff_continuousAt]
  intro x
  have Hd := resolvedSourceCoeffQuadraticDecay_of_profile H
  simpa [paper3QuadraticSignalGradient,
    paper3QuadraticEllipticSourceCoeffReal] using
    (paper3ResolvedSourceGradient_hasDerivAt_laplacian p Hd x).continuousAt

#print axioms resolvedSourceCoeffQuadraticDecay_of_profile
#print axioms ResolvedSourceProfileRegularity.profile_aestronglyMeasurable
#print axioms resolvedSourceGradient_hasDerivAt_profile
#print axioms paper3LinearSignalGradient_hasDerivAt_laplacian
#print axioms paper3QuadraticSignalGradient_hasDerivAt_laplacian
#print axioms paper3LinearSignalGradient_continuous
#print axioms paper3QuadraticSignalGradient_continuous

end

end ShenWork.Paper3
