/- Full positive-time Route-A nonlinear snapshot for faithful general `m`. -/
import ShenWork.Paper3.IntervalDomainRouteAFluxL2GeneralM
import ShenWork.Paper3.IntervalDomainFluxDerivativeIntegrabilityGeneralM
import ShenWork.Paper3.IntervalDomainLogisticRemainderCoeffs

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

/-- Uniform full nonlinear coefficient constant for the faithful general-`m`
Route-A snapshot. -/
def paper3RouteAFullQuadraticConstantGeneralM
    (p : CM2Params) (uStar vStar C Klog : ℝ) : ℝ :=
  2 * Real.sqrt 2 *
    (|p.χ₀| * paper3RouteAFluxL2ConstantGeneralM p uStar vStar C + Klog)

/-- Assemble the faithful general-`m` chemotaxis and logistic remainders on
one strong positive slice.  All power losses are recorded in
`flux.bounds.M`; the signal scale remains `flux.bounds.L = M`. -/
theorem exists_fullNonlinearRemainderRouteAData_of_strong_slice_with_constants_generalM
    {p : CM2Params} {T t uStar vStar M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (Hsplit : IntervalSolutionSignalSplitData p uStar (u t))
    (Hlin : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticLinearProfile p uStar (u t)))
    (Hquad : ResolvedSourceProfileRegularity
      (paper3IntervalEllipticRemainderProfile p uStar (u t)))
    (C Klog : ℝ) (hC : 0 < C) (hKlog : 0 < Klog)
    (hsignal : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar (u t) x| ≤ C * M ∧
      |paper3LinearSignalGradient p uStar (u t) x| ≤ C * M ∧
      |paper3LinearSignalLaplacian p uStar (u t) x| ≤ C * M ∧
      |paper3QuadraticSignalValue p uStar (u t) x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar (u t) x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar (u t) x| ≤ C * M ^ 2)
    (hlogQuad : ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |paper3LogisticReaction p x + p.a * p.α * (x - uStar)| ≤
        Klog * |x - uStar| ^ 2)
    (hM0 : 0 ≤ M)
    (hscaledM1 : paper3RouteAPowerFactor p uStar * M ≤ 1)
    (hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hphi : MemLp (paper3IntervalPerturbationProfile uStar (u t)) 2
      (intervalMeasure 1))
    (hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u t) x| ≤ M)
    (hphi_l2 : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u t)) ≤ M)
    (hphiInt : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u t)) volume 0 1)
    (hreact : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u t) x))
      volume 0 1)
    (hlog_meas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderProfile p uStar (u t))
      (intervalMeasure 1))
    (hwx : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u t)) x| ≤ M) :
    ∃ H : FullNonlinearRemainderRouteAData
        (paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v t),
      H.flux.bounds.M = paper3RouteAPowerFactor p uStar * M ∧
        H.flux.bounds.L = M ∧
        H.toL2Data.quadraticConstant =
          paper3RouteAFullQuadraticConstantGeneralM
            p uStar vStar C Klog := by
  rcases exists_routeAFluxL2Data_of_strong_slice_generalM
      hsol ht heq Hsplit Hlin Hquad C hC hsignal hM0 hscaledM1
        hu_near hphi_sup hwx with
    ⟨Hflux, hBM, hBL, hprofile, hz1xx, hfluxConst⟩
  have hlogPoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3IntervalLogisticRemainderProfile p uStar (u t) x| ≤
        (Klog * M) * |paper3IntervalPerturbationProfile uStar (u t) x| := by
    intro x hx
    have hq := hlogQuad (intervalDomainLift (u t) x)
      (hu_near x (Set.Ioo_subset_Icc_self hx))
    have hs := hphi_sup x (Set.Ioo_subset_Icc_self hx)
    dsimp [paper3IntervalLogisticRemainderProfile,
      paper3IntervalPerturbationProfile, paper3LogisticRemainder] at hq ⊢
    calc
      _ ≤ Klog * |intervalDomainLift (u t) x - uStar| ^ 2 := hq
      _ ≤ (Klog * M) * |intervalDomainLift (u t) x - uStar| := by
        have hnonneg : 0 ≤ |intervalDomainLift (u t) x - uStar| := abs_nonneg _
        have hprod : 0 ≤ Klog * |intervalDomainLift (u t) x - uStar| *
            (M - |intervalDomainLift (u t) x - uStar|) :=
          mul_nonneg (mul_nonneg hKlog.le hnonneg) (sub_nonneg.mpr hs)
        nlinarith
  have hlog_mem : MemLp
      (paper3IntervalLogisticRemainderProfile p uStar (u t)) 2
      (intervalMeasure 1) :=
    memLp_two_of_pointwise_mul_Ioo
      (mul_nonneg hKlog.le hM0) hlog_meas hphi hlogPoint
  have hlog_l2_raw : intervalL2Size
      (paper3IntervalLogisticRemainderProfile p uStar (u t)) ≤
        Klog * M * M := by
    have hmul := intervalL2Size_le_of_pointwise_mul
      (mul_nonneg hKlog.le hM0) hlog_mem hphi hlogPoint
    calc
      _ ≤ (Klog * M) * intervalL2Size
          (paper3IntervalPerturbationProfile uStar (u t)) := hmul
      _ ≤ (Klog * M) * M :=
        mul_le_mul_of_nonneg_left hphi_l2 (mul_nonneg hKlog.le hM0)
  have hP1 : 1 ≤ paper3RouteAPowerFactor p uStar :=
    paper3RouteAPowerFactor_one_le p uStar
  have hM_le_scaled : M ≤ paper3RouteAPowerFactor p uStar * M := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP1) hM0]
  have hlog_l2_scaled : intervalL2Size
      (paper3IntervalLogisticRemainderProfile p uStar (u t)) ≤
        Klog * (paper3RouteAPowerFactor p uStar * M) * M := by
    calc
      _ ≤ Klog * M * M := hlog_l2_raw
      _ ≤ Klog * (paper3RouteAPowerFactor p uStar * M) * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hM_le_scaled hKlog.le) hM0
  have hz1xxMem : MemLp
      (paper3LinearSignalLaplacian p uStar (u t)) 2
      (intervalMeasure 1) := by
    rw [← hz1xx]
    exact Hflux.z1xx_memLp
  have hfluxDerivInt :=
    paper3ChemFluxRemainder_deriv_intervalIntegrable_generalM
      (vStar := vStar) hsol ht Hlin hz1xxMem
  let Hfull : FullNonlinearRemainderRouteAData
      (paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v t) :=
    { chi := p.χ₀
      flux := Hflux
      Klog := Klog
      logProfile := paper3IntervalLogisticRemainderProfile p uStar (u t)
      Klog_nonneg := hKlog.le
      log_memLp := hlog_mem
      log_l2 := by simpa [hBM, hBL] using hlog_l2_scaled
      coeff_eq := by
        intro n
        rw [paper3FullModeNonlinearRemainderCoeffM_eq_parts,
          paper3ChemotaxisRemainderCoeffM_eq_routeA_cosine_generalM
            hsol ht heq Hsplit Hlin Hquad hfluxDerivInt n,
          paper3LogisticRemainderCoeffM_eq_cosine
            p uStar u t n hreact hphiInt]
        rw [hprofile] }
  refine ⟨Hfull, ?_, ?_, ?_⟩
  · exact hBM
  · exact hBL
  · simp only [Hfull, FullNonlinearRemainderRouteAData.toL2Data,
      FullNonlinearRemainderL2Data.quadraticConstant,
      FullNonlinearRemainderRouteAData.chemConstant,
      paper3RouteAFullQuadraticConstantGeneralM]
    rw [hfluxConst]

#print axioms paper3RouteAFullQuadraticConstantGeneralM
#print axioms
  exists_fullNonlinearRemainderRouteAData_of_strong_slice_with_constants_generalM

end

end ShenWork.Paper3
