/- Produce linear and quadratic signal regularity on classical positive slices. -/
import ShenWork.Paper3.IntervalDomainWeakH2Algebra
import ShenWork.Paper3.IntervalDomainSignalStrongBounds
import ShenWork.Paper3.IntervalDomainSolutionSignalDecomposition
import ShenWork.Paper2.IntervalDomainL2UEnergyInequality
import ShenWork.Paper2.IntervalResolverWeakBounds
import ShenWork.Paper2.IntervalSpectralBasicLemmas
import ShenWork.PDE.IntervalDomainExistence

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.PDE.IntervalMildSourceDecayHelper
open ShenWork.Paper2

noncomputable section

/-- Both eliminated elliptic source components are genuine weak `H²_N`
profiles on every positive classical slice.  The nonlinear component is
obtained algebraically as full source minus its constant and linear parts;
this avoids imposing false global smoothness on the interval zero extension. -/
theorem paper3SignalSourceRegularity_of_classical_slice
    {p : CM2Params} {T t uStar vStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (_heq : Paper3ConstantEquilibrium p uStar vStar) :
    Nonempty
      (ResolvedSourceProfileRegularity
          (paper3IntervalEllipticLinearProfile p uStar (u t)) ×
        ResolvedSourceProfileRegularity
          (paper3IntervalEllipticRemainderProfile p uStar (u t))) := by
  let phi : ℝ → ℝ := paper3IntervalPerturbationProfile uStar (u t)
  let lin : ℝ → ℝ := paper3IntervalEllipticLinearProfile p uStar (u t)
  let src : ℝ → ℝ := fun x => p.ν * intervalDomainLift (u t) x ^ p.γ
  let eqSrc : ℝ → ℝ := fun _x => p.ν * uStar ^ p.γ
  let quad : ℝ → ℝ := paper3IntervalEllipticRemainderProfile p uStar (u t)
  have huC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  obtain ⟨huN0, huN1⟩ := (hsol.regularity.2.2.2.1 t ht).1
  have hubc0 : deriv (intervalDomainLift (u t)) 0 = 0 :=
    (hsol.regularity.2.2.2.2.1 t ht).1.2.1
  have hubc1 : deriv (intervalDomainLift (u t)) 1 = 0 :=
    (hsol.regularity.2.2.2.2.1 t ht).1.2.2
  have hphiC2 : ContDiffOn ℝ 2 phi (Set.Icc (0 : ℝ) 1) := by
    simpa [phi, paper3IntervalPerturbationProfile] using
      huC2.sub contDiffOn_const
  have hlinC2 : ContDiffOn ℝ 2 lin (Set.Icc (0 : ℝ) 1) := by
    simpa [lin, paper3IntervalEllipticLinearProfile,
      paper3IntervalPerturbationProfile] using
      contDiffOn_const.mul (huC2.sub contDiffOn_const)
  have hlinDeriv : deriv lin = fun x =>
      (p.ν * paper3PowerDeriv p.γ uStar) *
        deriv (intervalDomainLift (u t)) x := by
    funext x
    change deriv (fun y =>
      (p.ν * paper3PowerDeriv p.γ uStar) *
        (intervalDomainLift (u t) y - uStar)) x = _
    rw [deriv_const_mul_field, deriv_sub_const]
  have hlinN0 : Filter.Tendsto (deriv lin)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [hlinDeriv]
    simpa using tendsto_const_nhds.mul huN0
  have hlinN1 : Filter.Tendsto (deriv lin)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    rw [hlinDeriv]
    simpa using tendsto_const_nhds.mul huN1
  have hlinbc0 : deriv lin 0 = 0 := by
    rw [hlinDeriv]
    change (p.ν * paper3PowerDeriv p.γ uStar) *
      deriv (intervalDomainLift (u t)) 0 = 0
    rw [hubc0, mul_zero]
  have hlinbc1 : deriv lin 1 = 0 := by
    rw [hlinDeriv]
    change (p.ν * paper3PowerDeriv p.γ uStar) *
      deriv (intervalDomainLift (u t)) 1 = 0
    rw [hubc1, mul_zero]
  let HlinWeak : IntervalWeakH2Neumann lin :=
    intervalWeakH2Neumann_of_contDiffOn
      hlinC2 hlinN0 hlinN1 hlinbc0 hlinbc1
  have hlinCont : ContinuousOn lin (Set.Icc (0 : ℝ) 1) := hlinC2.continuousOn
  let Hlin : ResolvedSourceProfileRegularity lin :=
    resolvedSourceProfileRegularity_of_weakH2 HlinWeak hlinCont
  have hsrcC2 : ContDiffOn ℝ 2 src (Set.Icc (0 : ℝ) 1) := by
    simpa [src] using source_contDiffOn_Icc hsol ht
  obtain ⟨hsrcN0, hsrcN1⟩ := source_deriv_tendsto_endpoint hsol ht
  have hsrcbc0 : deriv src 0 = 0 := by
    simpa [src] using source_deriv_endpoint_eq_zero hsol ht (Or.inl rfl)
  have hsrcbc1 : deriv src 1 = 0 := by
    simpa [src] using source_deriv_endpoint_eq_zero hsol ht (Or.inr rfl)
  let HsrcWeak : IntervalWeakH2Neumann src :=
    intervalWeakH2Neumann_of_contDiffOn
      hsrcC2 hsrcN0 hsrcN1 hsrcbc0 hsrcbc1
  let HeqWeak : IntervalWeakH2Neumann eqSrc := intervalWeakH2Neumann_const _
  have hsrcInt : IntervalIntegrable src volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hsrcC2.continuousOn
  have heqInt : IntervalIntegrable eqSrc volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_const
  have hlinInt : IntervalIntegrable lin volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hlinCont
  let HsrcMinusEq : IntervalWeakH2Neumann (fun x => src x - eqSrc x) :=
    ShenWork.Paper3.IntervalWeakH2Neumann.sub
      HsrcWeak HeqWeak hsrcInt heqInt
  let HquadRaw : IntervalWeakH2Neumann
      (fun x => (src x - eqSrc x) - lin x) :=
    ShenWork.Paper3.IntervalWeakH2Neumann.sub
      HsrcMinusEq HlinWeak (hsrcInt.sub heqInt) hlinInt
  have hquadEq : (fun x => (src x - eqSrc x) - lin x) = quad := by
    funext x
    dsimp [src, eqSrc, lin, quad, paper3IntervalEllipticLinearProfile,
      paper3IntervalPerturbationProfile, paper3IntervalEllipticRemainderProfile,
      paper3EllipticSourceRemainder, paper3PowerLinearizationRemainder]
    ring
  have HquadWeak : IntervalWeakH2Neumann quad := by
    rw [← hquadEq]
    exact HquadRaw
  have hquadCont : ContinuousOn quad (Set.Icc (0 : ℝ) 1) := by
    rw [← hquadEq]
    exact (hsrcC2.continuousOn.sub continuousOn_const).sub hlinCont
  let Hquad : ResolvedSourceProfileRegularity quad :=
    resolvedSourceProfileRegularity_of_weakH2 HquadWeak hquadCont
  exact ⟨⟨by simpa [lin] using Hlin, by simpa [quad] using Hquad⟩⟩

#print axioms paper3SignalSourceRegularity_of_classical_slice

/-- The exact physical resolver split data are automatic on a positive
classical slice.  All four square-summability fields come from the interval
cosine Bessel estimate, not from a carried spectral hypothesis. -/
theorem intervalSolutionSignalSplitData_of_classical_slice
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    IntervalSolutionSignalSplitData p uStar (u t) := by
  have huC2 : ContDiffOn ℝ 2 (intervalDomainLift (u t))
      (Set.Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 t ht).1.1
  have huCont := huC2.continuousOn
  let lin : ℝ → ℝ := paper3IntervalEllipticLinearProfile p uStar (u t)
  let src : ℝ → ℝ := fun x => p.ν * intervalDomainLift (u t) x ^ p.γ
  let eqSrc : ℝ → ℝ := fun _x => p.ν * uStar ^ p.γ
  let quad : ℝ → ℝ := paper3IntervalEllipticRemainderProfile p uStar (u t)
  have hlinCont : ContinuousOn lin (Set.Icc (0 : ℝ) 1) := by
    dsimp [lin, paper3IntervalEllipticLinearProfile,
      paper3IntervalPerturbationProfile]
    exact continuousOn_const.mul (huCont.sub continuousOn_const)
  have hsrcCont : ContinuousOn src (Set.Icc (0 : ℝ) 1) := by
    simpa [src] using source_continuousOn_Icc hsol ht
  have hquadEq : (fun x => (src x - eqSrc x) - lin x) = quad := by
    funext x
    dsimp [src, eqSrc, lin, quad, paper3IntervalEllipticLinearProfile,
      paper3IntervalPerturbationProfile, paper3IntervalEllipticRemainderProfile,
      paper3EllipticSourceRemainder, paper3PowerLinearizationRemainder]
    ring
  have hquadCont : ContinuousOn quad (Set.Icc (0 : ℝ) 1) := by
    rw [← hquadEq]
    exact (hsrcCont.sub continuousOn_const).sub hlinCont
  have hlinLp : MemLp lin 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hlinCont
  have hquadLp : MemLp quad 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hquadCont
  have hlinSum :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hlinLp).1
  have hquadSum :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hquadLp).1
  let srcEq : ℝ → ℝ := fun x =>
    p.ν * intervalDomainLift (fun _ : intervalDomainPoint => uStar) x ^ p.γ
  have hconstCont : ContinuousOn
      (intervalDomainLift (fun _ : intervalDomainPoint => uStar))
      (Set.Icc (0 : ℝ) 1) := by
    have hc : ContinuousOn (fun _x : ℝ => uStar)
        (Set.Icc (0 : ℝ) 1) := continuousOn_const
    refine hc.congr ?_
    intro x hx
    simp [intervalDomainLift, hx]
  have hsrcEqCont : ContinuousOn srcEq (Set.Icc (0 : ℝ) 1) := by
    dsimp [srcEq]
    exact continuousOn_const.mul
      (hconstCont.rpow_const (fun _ _ => Or.inr p.hγ.le))
  have hsrcLp : MemLp src 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hsrcCont
  have hsrcEqLp : MemLp srcEq 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hsrcEqCont
  have hsrcSum :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hsrcLp).1
  have hsrcEqSum :=
    (ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hsrcEqLp).1
  refine
    { linear_integrable := by
        apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hlinCont
      remainder_integrable := by
        apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hquadCont
      source_sq_summable := by
        refine hsrcSum.congr (fun k => ?_)
        rw [show (ShenWork.PDE.intervalNeumannResolverSourceCoeff p (u t) k).re =
            cosineCoeffs src k by
          simp only [ShenWork.PDE.intervalNeumannResolverSourceCoeff,
            Complex.ofReal_re, cosineCoeffs, src]]
      equilibrium_source_sq_summable := by
        refine hsrcEqSum.congr (fun k => ?_)
        rw [show (ShenWork.PDE.intervalNeumannResolverSourceCoeff p
            (fun _ : intervalDomainPoint => uStar) k).re = cosineCoeffs srcEq k by
          simp only [ShenWork.PDE.intervalNeumannResolverSourceCoeff,
            Complex.ofReal_re, cosineCoeffs, srcEq]]
      linear_source_sq_summable := by
        simpa [paper3LinearEllipticSourceCoeffReal, lin] using hlinSum
      remainder_source_sq_summable := by
        simpa [paper3QuadraticEllipticSourceCoeffReal, quad] using hquadSum }

#print axioms intervalSolutionSignalSplitData_of_classical_slice

end

end ShenWork.Paper3
