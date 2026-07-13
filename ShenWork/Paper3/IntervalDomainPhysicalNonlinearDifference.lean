/- Physical `L²` realization of the full polarized route-(a) nonlinearity. -/
import ShenWork.Paper3.IntervalDomainPhysicalFluxDifference
import ShenWork.Paper3.IntervalDomainFullNonlinearRouteA
import ShenWork.Paper3.IntervalDomainStrongDifferenceRealization

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

def paper3ChemFluxRemainderDerivativeDifferenceProfile
    (p : CM2Params) (uStar vStar : ℝ)
    (u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  -p.χ₀ *
    (deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u₁ t) (v₁ t)) x -
      deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u₂ t) (v₂ t)) x)

def paper3RouteAPolarizedChemL2Constant
    (p : CM2Params) (uStar vStar Cself Cdiff : ℝ) : ℝ :=
  let C := paper3RouteAPolarizedPointConstant p Cself Cdiff
  let K := EliminatedFluxDerivativePolarizedPointData.eliminatedFluxDerivativePolarizedConstant
    (paper3SensitivityFactor p.β vStar) C (uStar + 1)
  |p.χ₀| * K

theorem paper3RouteAPolarizedChemL2Constant_nonneg
    (p : CM2Params) {uStar vStar Cself Cdiff : ℝ}
    (huStar : 0 < uStar) (hself : 0 ≤ Cself) (hdiff : 0 ≤ Cdiff) :
    0 ≤ paper3RouteAPolarizedChemL2Constant
      p uStar vStar Cself Cdiff := by
  let C := paper3RouteAPolarizedPointConstant p Cself Cdiff
  have hC : 0 ≤ C :=
    (paper3RouteAPolarizedPointConstant_pos p hself hdiff).le
  have hU : 0 ≤ uStar + 1 := by linarith
  dsimp [paper3RouteAPolarizedChemL2Constant]
  exact mul_nonneg (abs_nonneg _)
    (add_nonneg
      (mul_nonneg
        (mul_nonneg (abs_nonneg _) hC)
        (by linarith))
      (mul_nonneg (sq_nonneg C) (by linarith)))

set_option maxHeartbeats 3000000 in
/-- Once the value/gradient/signal estimates have been produced, the exact
physical chemotaxis and logistic differences realize the modal difference
`N(w1)-N(w2)` in `L²`. -/
theorem exists_fullNonlinearRemainderDifferenceL2Data_of_routeA
    {p : CM2Params} {T t uStar vStar M₁ M₂ D Cself Cdiff Klog : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomain p T u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomain p T u₂ v₂)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hm : p.m = 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit₁ : IntervalSolutionSignalSplitData p uStar (u₁ t))
    (Hsplit₂ : IntervalSolutionSignalSplitData p uStar (u₂ t))
    (Hlin₁ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u₁ t)))
    (Hquad₁ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u₁ t)))
    (Hlin₂ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u₂ t)))
    (Hquad₂ : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u₂ t)))
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hM₁1 : M₁ ≤ 1) (hM₂1 : M₂ ≤ 1) (hD0 : 0 ≤ D)
    (hCself : 0 < Cself) (hCdiff : 0 < Cdiff) (hKlog : 0 ≤ Klog)
    (hw₁ : ∀ x : intervalDomainPoint, |u₁ t x - uStar| ≤ M₁)
    (hw₂ : ∀ x : intervalDomainPoint, |u₂ t x - uStar| ≤ M₂)
    (hwx₁ : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ t)) x| ≤ M₁)
    (hwx₂ : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₂ t)) x| ≤ M₂)
    (hwD : ∀ x : intervalDomainPoint, |u₁ t x - u₂ t x| ≤ D)
    (hwxD : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ t)) x -
        deriv (intervalDomainLift (u₂ t)) x| ≤ D)
    (hsignal₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u₁ t) x| ≤ Cself * M₁ ∧
      |paper3LinearSignalGradient p uStar (u₁ t) x| ≤ Cself * M₁ ∧
      |paper3LinearSignalLaplacian p uStar (u₁ t) x| ≤ Cself * M₁ ∧
      |paper3QuadraticSignalValue p uStar (u₁ t) x| ≤ Cself * M₁ ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u₁ t) x| ≤ Cself * M₁ ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u₁ t) x| ≤ Cself * M₁ ^ 2)
    (hsignal₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u₂ t) x| ≤ Cself * M₂ ∧
      |paper3LinearSignalGradient p uStar (u₂ t) x| ≤ Cself * M₂ ∧
      |paper3LinearSignalLaplacian p uStar (u₂ t) x| ≤ Cself * M₂ ∧
      |paper3QuadraticSignalValue p uStar (u₂ t) x| ≤ Cself * M₂ ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u₂ t) x| ≤ Cself * M₂ ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u₂ t) x| ≤ Cself * M₂ ^ 2)
    (hsignalD : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u₁ t) x -
          paper3LinearSignalValue p uStar (u₂ t) x| ≤ Cdiff * D ∧
      |paper3LinearSignalGradient p uStar (u₁ t) x -
          paper3LinearSignalGradient p uStar (u₂ t) x| ≤ Cdiff * D ∧
      |paper3LinearSignalLaplacian p uStar (u₁ t) x -
          paper3LinearSignalLaplacian p uStar (u₂ t) x| ≤ Cdiff * D ∧
      |paper3QuadraticSignalValue p uStar (u₁ t) x -
          paper3QuadraticSignalValue p uStar (u₂ t) x| ≤
            Cdiff * (M₁ + M₂) * D ∧
      |paper3QuadraticSignalGradient p uStar (u₁ t) x -
          paper3QuadraticSignalGradient p uStar (u₂ t) x| ≤
            Cdiff * (M₁ + M₂) * D ∧
      |paper3QuadraticSignalLaplacian p uStar (u₁ t) x -
          paper3QuadraticSignalLaplacian p uStar (u₂ t) x| ≤
            Cdiff * (M₁ + M₂) * D)
    (hfluxInt₁ : IntervalIntegrable
      (deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u₁ t) (v₁ t))) volume 0 1)
    (hfluxInt₂ : IntervalIntegrable
      (deriv (paper3ChemFluxRemainderProfileM
        p uStar vStar (u₂ t) (v₂ t))) volume 0 1)
    (hreact₁ : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u₁ t) x))
      volume 0 1)
    (hreact₂ : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u₂ t) x))
      volume 0 1)
    (hphi₁Int : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u₁ t)) volume 0 1)
    (hphi₂Int : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u₂ t)) volume 0 1)
    (hlogMem : MemLp
      (paper3IntervalLogisticRemainderDifferenceProfile
        p uStar (u₁ t) (u₂ t)) 2 (intervalMeasure 1))
    (hlogL2 : intervalL2Size
      (paper3IntervalLogisticRemainderDifferenceProfile
        p uStar (u₁ t) (u₂ t)) ≤ Klog * (M₁ + M₂) * D) :
    ∃ H : FullNonlinearRemainderDifferenceL2Data
        (fun n => paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u₁ v₁ t n -
          paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u₂ v₂ t n),
      H.M1 = M₁ ∧ H.M2 = M₂ ∧ H.D = D ∧
      H.Kchem = paper3RouteAPolarizedChemL2Constant
        p uStar vStar Cself Cdiff ∧ H.Klog = Klog := by
  let C := paper3RouteAPolarizedPointConstant p Cself Cdiff
  let Kflux :=
    EliminatedFluxDerivativePolarizedPointData.eliminatedFluxDerivativePolarizedConstant
      (paper3SensitivityFactor p.β vStar) C (uStar + 1)
  let Kchem := paper3RouteAPolarizedChemL2Constant
    p uStar vStar Cself Cdiff
  let chemProfile : ℝ → ℝ :=
    paper3ChemFluxRemainderDerivativeDifferenceProfile
      p uStar vStar u₁ v₁ u₂ v₂ t
  let logProfile : ℝ → ℝ :=
    paper3IntervalLogisticRemainderDifferenceProfile
      p uStar (u₁ t) (u₂ t)
  have hKchem : 0 ≤ Kchem := by
    simpa [Kchem] using paper3RouteAPolarizedChemL2Constant_nonneg
      p heq.u_pos hCself.le hCdiff.le
  have hpointRaw := paper3ChemFluxRemainder_deriv_difference_pointwise
    hsol₁ hsol₂ ht hm heq Hsplit₁ Hsplit₂ Hlin₁ Hquad₁ Hlin₂ Hquad₂
      hM₁0 hM₂0 hM₁1 hM₂1 hD0 hCself hCdiff hw₁ hw₂ hwx₁ hwx₂
      hwD hwxD hsignal₁ hsignal₂ hsignalD
  have hchemPoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |chemProfile x| ≤ Kchem * (M₁ + M₂) * D := by
    intro x hx
    have hp := hpointRaw x hx
    dsimp [chemProfile, paper3ChemFluxRemainderDerivativeDifferenceProfile]
    rw [abs_mul, abs_neg]
    calc
      _ ≤ |p.χ₀| * (Kflux * (M₁ + M₂) * D) :=
        mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = Kchem * (M₁ + M₂) * D := by
        dsimp [Kchem, paper3RouteAPolarizedChemL2Constant, Kflux, C]
        ring
  have hB : 0 ≤ Kchem * (M₁ + M₂) * D :=
    mul_nonneg (mul_nonneg hKchem (add_nonneg hM₁0 hM₂0)) hD0
  have hchemMeas : AEStronglyMeasurable chemProfile (intervalMeasure 1) := by
    dsimp [chemProfile, paper3ChemFluxRemainderDerivativeDifferenceProfile]
    exact (measurable_const.mul
      ((measurable_deriv _).sub (measurable_deriv _))).aestronglyMeasurable
  have hone : MemLp (fun _x : ℝ => (1 : ℝ)) 2 (intervalMeasure 1) := memLp_const 1
  have hchemMem : MemLp chemProfile 2 (intervalMeasure 1) :=
    memLp_two_of_pointwise_mul_Ioo hB hchemMeas hone (by
      intro x hx
      simpa using hchemPoint x hx)
  have hchemL2 : intervalL2Size chemProfile ≤ Kchem * (M₁ + M₂) * D := by
    have hmul := intervalL2Size_le_of_pointwise_mul hB hchemMem hone (by
      intro x hx
      simpa using hchemPoint x hx)
    simpa [intervalL2Size_const (c := (1 : ℝ)) (by norm_num)] using hmul
  let H : FullNonlinearRemainderDifferenceL2Data
      (fun n => paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u₁ v₁ t n -
        paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u₂ v₂ t n) :=
    { M1 := M₁
      M2 := M₂
      D := D
      Kchem := Kchem
      Klog := Klog
      chemProfile := chemProfile
      logProfile := logProfile
      M1_nonneg := hM₁0
      M2_nonneg := hM₂0
      D_nonneg := hD0
      Kchem_nonneg := hKchem
      Klog_nonneg := hKlog
      chem_memLp := hchemMem
      log_memLp := by simpa [logProfile] using hlogMem
      chem_l2 := hchemL2
      log_l2 := by simpa [logProfile] using hlogL2
      coeff_eq := by
        intro n
        have hchem₁ := paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine
          hsol₁ ht hm heq Hsplit₁ Hlin₁ Hquad₁ hfluxInt₁ n
        have hchem₂ := paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine
          hsol₂ ht hm heq Hsplit₂ Hlin₂ Hquad₂ hfluxInt₂ n
        have hlog₁ := paper3LogisticRemainderCoeffM_eq_cosine
          p uStar u₁ t n hreact₁ hphi₁Int
        have hlog₂ := paper3LogisticRemainderCoeffM_eq_cosine
          p uStar u₂ t n hreact₂ hphi₂Int
        have hchemCoeff : cosineCoeffs chemProfile n =
            cosineCoeffs (fun x => -p.χ₀ *
              deriv (paper3ChemFluxRemainderProfileM
                p uStar vStar (u₁ t) (v₁ t)) x) n -
            cosineCoeffs (fun x => -p.χ₀ *
              deriv (paper3ChemFluxRemainderProfileM
                p uStar vStar (u₂ t) (v₂ t)) x) n := by
          rw [show chemProfile = fun x =>
              (-p.χ₀ * deriv (paper3ChemFluxRemainderProfileM
                p uStar vStar (u₁ t) (v₁ t)) x) -
              (-p.χ₀ * deriv (paper3ChemFluxRemainderProfileM
                p uStar vStar (u₂ t) (v₂ t)) x) by
            funext x
            dsimp [chemProfile,
              paper3ChemFluxRemainderDerivativeDifferenceProfile]
            ring]
          exact cosineCoeffs_sub_of_intervalIntegrable n
            (hfluxInt₁.const_mul (-p.χ₀)) (hfluxInt₂.const_mul (-p.χ₀))
        have hlogCoeff : cosineCoeffs logProfile n =
            cosineCoeffs
                (paper3IntervalLogisticRemainderProfile p uStar (u₁ t)) n -
              cosineCoeffs
                (paper3IntervalLogisticRemainderProfile p uStar (u₂ t)) n := by
          dsimp [logProfile, paper3IntervalLogisticRemainderDifferenceProfile]
          exact cosineCoeffs_sub_of_intervalIntegrable n
            (hreact₁.add (hphi₁Int.const_mul (p.a * p.α)))
            (hreact₂.add (hphi₂Int.const_mul (p.a * p.α)))
        rw [paper3FullModeNonlinearRemainderCoeffM_eq_parts,
          paper3FullModeNonlinearRemainderCoeffM_eq_parts,
          hchem₁, hchem₂, hlog₁, hlog₂, hchemCoeff, hlogCoeff]
        ring }
  exact ⟨H, rfl, rfl, rfl, rfl, rfl⟩

#print axioms paper3RouteAPolarizedChemL2Constant_nonneg
#print axioms exists_fullNonlinearRemainderDifferenceL2Data_of_routeA

end

end ShenWork.Paper3
