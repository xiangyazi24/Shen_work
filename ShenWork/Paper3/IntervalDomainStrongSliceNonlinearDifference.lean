/- Strong-ball production of the actual polarized Nemytskii estimate. -/
import ShenWork.Paper3.IntervalDomainPhysicalNonlinearDifference
import ShenWork.Paper3.IntervalDomainStrongSliceNonlinearEstimate

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel
open ShenWork.Paper2

noncomputable section

theorem ResolvedSourceProfileRegularity.memLp_two
    {f : ℝ → ℝ} (H : ResolvedSourceProfileRegularity f) :
    MemLp f 2 (intervalMeasure 1) := by
  have hrep : MemLp H.representative 2 (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc
      H.representative_continuous.continuousOn
  have heq : f =ᵐ[intervalMeasure 1] H.representative := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (H.representative_eq x hx).symm
  exact (memLp_congr_ae heq).2 hrep

def intervalDomainX2SigmaUniformNemytskiiLipschitzConstant
    (p : CM2Params) (sigma uStar vStar : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  let Cself := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Cdiff := paper3UniformSignalDifferenceConstant p uStar heq.u_pos
  let Kchem := paper3RouteAPolarizedChemL2Constant
    p uStar vStar Cself Cdiff
  let Klog := paper3UniformLogisticPolarConstant p heq
  2 * Real.sqrt 2 * (Kchem + Klog) *
    intervalDomainX2SigmaC1Envelope sigma ^ 2

theorem intervalDomainX2SigmaUniformNemytskiiLipschitzConstant_pos
    (p : CM2Params) (sigma uStar vStar : ℝ)
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    0 < intervalDomainX2SigmaUniformNemytskiiLipschitzConstant
      p sigma uStar vStar heq := by
  let Cself := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Cdiff := paper3UniformSignalDifferenceConstant p uStar heq.u_pos
  let Kchem := paper3RouteAPolarizedChemL2Constant
    p uStar vStar Cself Cdiff
  let Klog := paper3UniformLogisticPolarConstant p heq
  have hCself : 0 < Cself := by
    simpa [Cself] using paper3UniformSignalStrongConstant_pos
      p uStar heq.u_pos
  have hCdiff : 0 < Cdiff := by
    simpa [Cdiff] using paper3UniformSignalDifferenceConstant_pos
      p uStar heq.u_pos
  have hKchem : 0 ≤ Kchem := by
    simpa [Kchem] using paper3RouteAPolarizedChemL2Constant_nonneg
      p heq.u_pos hCself.le hCdiff.le
  have hKlog : 0 < Klog := by
    simpa [Klog] using paper3UniformLogisticPolarConstant_pos p heq
  unfold intervalDomainX2SigmaUniformNemytskiiLipschitzConstant
  dsimp only
  exact mul_pos
    (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
      (by linarith))
    (sq_pos_of_pos (intervalDomainX2SigmaC1Envelope_pos sigma))

set_option maxHeartbeats 5000000 in
/-- Actual uniform polarized L12 estimate.  Positivity is imposed separately
on both strong states; the difference norm has no positivity role. -/
theorem paper3FullModeNonlinearRemainderCoeffM_uniform_difference_bound
    {p : CM2Params} {sigma uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ {T t : ℝ}
      {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ},
      IsPaper2ClassicalSolution intervalDomain p T u₁ v₁ →
      IsPaper2ClassicalSolution intervalDomain p T u₂ v₂ →
      t ∈ Set.Ioo (0 : ℝ) T →
      3 / 4 < sigma →
      p.m = 1 →
      IntervalDomainX2SigmaPerturbation sigma uStar (u₁ t) →
      IntervalDomainX2SigmaPerturbation sigma uStar (u₂ t) →
      IntervalDomainX2SigmaPairPerturbation sigma (u₁ t) (u₂ t) →
      intervalDomainX2SigmaDistance sigma uStar (u₁ t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar →
      intervalDomainX2SigmaDistance sigma uStar (u₂ t) ≤
        intervalDomainX2SigmaLocalNemytskiiRadius sigma uStar →
      Summable (fun n : ℕ =>
        ‖((paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u₁ v₁ t n -
          paper3FullModeNonlinearRemainderCoeffM
            p uStar vStar u₂ v₂ t n : ℝ) : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => ((paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u₁ v₁ t n -
            paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u₂ v₂ t n : ℝ) : ℂ)) ≤
        intervalDomainX2SigmaUniformNemytskiiLipschitzConstant
          p sigma uStar vStar heq *
        (intervalDomainX2SigmaDistance sigma uStar (u₁ t) +
          intervalDomainX2SigmaDistance sigma uStar (u₂ t)) *
        intervalDomainX2SigmaPairDistance sigma (u₁ t) (u₂ t) := by
  intro T t u₁ v₁ u₂ v₂ hsol₁ hsol₂ ht hsigma hm
    hmem₁ hmem₂ hmemD hsmall₁ hsmall₂
  have hsolM₁ := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol₁
  have hsolM₂ := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one
    p hm hsol₂
  have hcont₁ : Continuous (u₁ t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM₁ ht
  have hcont₂ : Continuous (u₂ t) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsolM₂ ht
  have Hreal₁ : IntervalDomainX2SigmaRealizationBounds sigma uStar (u₁ t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous hsigma hcont₁ hmem₁
  have Hreal₂ : IntervalDomainX2SigmaRealizationBounds sigma uStar (u₂ t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous hsigma hcont₂ hmem₂
  have HrealD : IntervalDomainX2SigmaRealizationBounds sigma 0
      (intervalDomainX2SigmaDifferenceProfile (u₁ t) (u₂ t)) :=
    intervalDomainX2SigmaPairRealizationBounds_of_continuous
      hsigma hcont₁ hcont₂ hmemD
  let Cenv := intervalDomainX2SigmaC1Envelope sigma
  let d₁ := intervalDomainX2SigmaDistance sigma uStar (u₁ t)
  let d₂ := intervalDomainX2SigmaDistance sigma uStar (u₂ t)
  let dD := intervalDomainX2SigmaPairDistance sigma (u₁ t) (u₂ t)
  let M₁ := Cenv * d₁
  let M₂ := Cenv * d₂
  let D := Cenv * dD
  have henv₁ := Hreal₁.local_envelope_bounds hsmall₁
  have henv₂ := Hreal₂.local_envelope_bounds hsmall₂
  have henvD := HrealD.envelope_bounds
  have hM₁0 : 0 ≤ M₁ := by simpa [M₁, Cenv, d₁] using henv₁.1
  have hM₂0 : 0 ≤ M₂ := by simpa [M₂, Cenv, d₂] using henv₂.1
  have hM₁1 : M₁ ≤ 1 := by simpa [M₁, Cenv, d₁] using henv₁.2.1
  have hM₂1 : M₂ ≤ 1 := by simpa [M₂, Cenv, d₂] using henv₂.2.1
  have hD0 : 0 ≤ D := by
    exact mul_nonneg (intervalDomainX2SigmaC1Envelope_pos sigma).le
      (intervalDomainX2SigmaPairDistance_nonneg sigma (u₁ t) (u₂ t))
  have hw₁ : ∀ x : intervalDomainPoint, |u₁ t x - uStar| ≤ M₁ := by
    simpa [M₁, Cenv, d₁] using henv₁.2.2.1
  have hw₂ : ∀ x : intervalDomainPoint, |u₂ t x - uStar| ≤ M₂ := by
    simpa [M₂, Cenv, d₂] using henv₂.2.2.1
  have hgrad₁ : ∀ x : intervalDomainPoint,
      intervalDomain.gradNorm (fun y => u₁ t y - uStar) x ≤ M₁ := by
    simpa [M₁, Cenv, d₁] using henv₁.2.2.2
  have hgrad₂ : ∀ x : intervalDomainPoint,
      intervalDomain.gradNorm (fun y => u₂ t y - uStar) x ≤ M₂ := by
    simpa [M₂, Cenv, d₂] using henv₂.2.2.2
  have hwD : ∀ x : intervalDomainPoint, |u₁ t x - u₂ t x| ≤ D := by
    intro x
    have h := henvD.1 x
    simpa [D, Cenv, dD, intervalDomainX2SigmaPairDistance,
      intervalDomainX2SigmaDifferenceProfile] using h
  have hgradD : ∀ x : intervalDomainPoint,
      intervalDomain.gradNorm
        (fun y => (u₁ t y - u₂ t y) - 0) x ≤ D := by
    simpa [D, Cenv, dD, intervalDomainX2SigmaPairDistance,
      intervalDomainX2SigmaDifferenceProfile] using henvD.2
  have hwx₁ : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ t)) x| ≤ M₁ := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
    have hg := hgrad₁ xp
    change |deriv (intervalDomainLift (fun y => u₁ t y - uStar)) x| ≤ M₁ at hg
    have hevent : Filter.EventuallyEq (nhds x)
        (intervalDomainLift (fun y => u₁ t y - uStar))
        (fun y => intervalDomainLift (u₁ t) y - uStar) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx) ?_
      intro y hy
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hevent.deriv_eq, deriv_sub_const] at hg
    exact hg
  have hwx₂ : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₂ t)) x| ≤ M₂ := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
    have hg := hgrad₂ xp
    change |deriv (intervalDomainLift (fun y => u₂ t y - uStar)) x| ≤ M₂ at hg
    have hevent : Filter.EventuallyEq (nhds x)
        (intervalDomainLift (fun y => u₂ t y - uStar))
        (fun y => intervalDomainLift (u₂ t) y - uStar) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx) ?_
      intro y hy
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hevent.deriv_eq, deriv_sub_const] at hg
    exact hg
  have hwxD : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |deriv (intervalDomainLift (u₁ t)) x -
        deriv (intervalDomainLift (u₂ t)) x| ≤ D := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, Set.Ioo_subset_Icc_self hx⟩
    have hg := hgradD xp
    change |deriv (intervalDomainLift
      (fun y => (u₁ t y - u₂ t y) - 0)) x| ≤ D at hg
    have hevent : Filter.EventuallyEq (nhds x)
        (intervalDomainLift (fun y => (u₁ t y - u₂ t y) - 0))
        (fun y => intervalDomainLift (u₁ t) y - intervalDomainLift (u₂ t) y) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hx) ?_
      intro y hy
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hevent.deriv_eq] at hg
    have huDiff : DifferentiableAt ℝ (intervalDomainLift (u₁ t)) x :=
      ((hsol₁.regularity.2.2.2.2.1 t ht).1.1.differentiableOn
        (by norm_num)).differentiableAt
        (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx)
          Set.Ioo_subset_Icc_self)
    have hvDiff : DifferentiableAt ℝ (intervalDomainLift (u₂ t)) x :=
      ((hsol₂.regularity.2.2.2.2.1 t ht).1.1.differentiableOn
        (by norm_num)).differentiableAt
        (Filter.mem_of_superset (IsOpen.mem_nhds isOpen_Ioo hx)
          Set.Ioo_subset_Icc_self)
    have hderivSub := (huDiff.hasDerivAt.sub hvDiff.hasDerivAt).deriv
    have hderivSub' :
        deriv (fun y => intervalDomainLift (u₁ t) y -
          intervalDomainLift (u₂ t) y) x =
        deriv (intervalDomainLift (u₁ t)) x -
          deriv (intervalDomainLift (u₂ t)) x := by
      simpa only [Pi.sub_apply] using hderivSub
    rw [hderivSub'] at hg
    exact hg
  have hnearAbs₁ : ∀ x : intervalDomainPoint,
      |u₁ t x - uStar| ≤ uStar / 2 := by
    intro x
    let Cinf := intervalDomainX2SigmaValueTrace sigma
    have hCinf : 0 ≤ Cinf := intervalDomainX2SigmaValueTrace_nonneg sigma
    have hden : 0 < 1 + Cinf := by linarith
    have hdistPos : d₁ ≤ intervalDomainX2SigmaPositivityRadius sigma uStar :=
      hsmall₁.trans (min_le_left _ _)
    calc
      |u₁ t x - uStar| ≤ Cinf * d₁ := Hreal₁.value_bound x
      _ ≤ Cinf * intervalDomainX2SigmaPositivityRadius sigma uStar :=
        mul_le_mul_of_nonneg_left hdistPos hCinf
      _ = (uStar / 2) * (Cinf / (1 + Cinf)) := by
        dsimp [Cinf, intervalDomainX2SigmaPositivityRadius]
        field_simp [hden.ne']
      _ ≤ uStar / 2 := by
        have hfrac : Cinf / (1 + Cinf) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        simpa using mul_le_mul_of_nonneg_left hfrac (by linarith [heq.u_pos])
  have hnearAbs₂ : ∀ x : intervalDomainPoint,
      |u₂ t x - uStar| ≤ uStar / 2 := by
    intro x
    let Cinf := intervalDomainX2SigmaValueTrace sigma
    have hCinf : 0 ≤ Cinf := intervalDomainX2SigmaValueTrace_nonneg sigma
    have hden : 0 < 1 + Cinf := by linarith
    have hdistPos : d₂ ≤ intervalDomainX2SigmaPositivityRadius sigma uStar :=
      hsmall₂.trans (min_le_left _ _)
    calc
      |u₂ t x - uStar| ≤ Cinf * d₂ := Hreal₂.value_bound x
      _ ≤ Cinf * intervalDomainX2SigmaPositivityRadius sigma uStar :=
        mul_le_mul_of_nonneg_left hdistPos hCinf
      _ = (uStar / 2) * (Cinf / (1 + Cinf)) := by
        dsimp [Cinf, intervalDomainX2SigmaPositivityRadius]
        field_simp [hden.ne']
      _ ≤ uStar / 2 := by
        have hfrac : Cinf / (1 + Cinf) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        simpa using mul_le_mul_of_nonneg_left hfrac (by linarith [heq.u_pos])
  have hu₁_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u₁ t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    have ha := hnearAbs₁ xp
    have hlift : intervalDomainLift (u₁ t) x = u₁ t xp := by
      simp [intervalDomainLift, xp, hx]
    rw [hlift]
    exact ⟨by linarith [neg_le_of_abs_le ha], by linarith [le_of_abs_le ha]⟩
  have hu₂_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (u₂ t) x ∈ Set.Icc (uStar / 2) (3 * uStar / 2) := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    have ha := hnearAbs₂ xp
    have hlift : intervalDomainLift (u₂ t) x = u₂ t xp := by
      simp [intervalDomainLift, xp, hx]
    rw [hlift]
    exact ⟨by linarith [neg_le_of_abs_le ha], by linarith [le_of_abs_le ha]⟩
  have huCont₁ : ContinuousOn (intervalDomainLift (u₁ t)) (Set.Icc (0 : ℝ) 1) :=
    ((hsol₁.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  have huCont₂ : ContinuousOn (intervalDomainLift (u₂ t)) (Set.Icc (0 : ℝ) 1) :=
    ((hsol₂.regularity.2.2.2.2.1 t ht).1.1).continuousOn
  have hphiCont₁ : ContinuousOn
      (paper3IntervalPerturbationProfile uStar (u₁ t)) (Set.Icc (0 : ℝ) 1) :=
    huCont₁.sub continuousOn_const
  have hphiCont₂ : ContinuousOn
      (paper3IntervalPerturbationProfile uStar (u₂ t)) (Set.Icc (0 : ℝ) 1) :=
    huCont₂.sub continuousOn_const
  have hphi₁ : MemLp (paper3IntervalPerturbationProfile uStar (u₁ t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont₁
  have hphi₂ : MemLp (paper3IntervalPerturbationProfile uStar (u₂ t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hphiCont₂
  have hphiSup₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u₁ t) x| ≤ M₁ := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    simpa [paper3IntervalPerturbationProfile, intervalDomainLift, xp, hx]
      using hw₁ xp
  have hphiSup₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar (u₂ t) x| ≤ M₂ := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    simpa [paper3IntervalPerturbationProfile, intervalDomainLift, xp, hx]
      using hw₂ xp
  have hphiL2₁ : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u₁ t)) ≤ M₁ :=
    intervalL2Size_le_of_pointwise_abs_bound hM₁0 hphi₁
      (fun x hx => hphiSup₁ x (Set.Ioo_subset_Icc_self hx))
  have hphiL2₂ : intervalL2Size
      (paper3IntervalPerturbationProfile uStar (u₂ t)) ≤ M₂ :=
    intervalL2Size_le_of_pointwise_abs_bound hM₂0 hphi₂
      (fun x hx => hphiSup₂ x (Set.Ioo_subset_Icc_self hx))
  have hdiffCont : ContinuousOn
      (paper3IntervalPerturbationDifferenceProfile (u₁ t) (u₂ t))
      (Set.Icc (0 : ℝ) 1) := by
    exact huCont₁.sub huCont₂
  have hdiff : MemLp
      (paper3IntervalPerturbationDifferenceProfile (u₁ t) (u₂ t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hdiffCont
  have hdiffSup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationDifferenceProfile (u₁ t) (u₂ t) x| ≤ D := by
    intro x hx
    let xp : intervalDomainPoint := ⟨x, hx⟩
    simpa [paper3IntervalPerturbationDifferenceProfile, intervalDomainLift, xp, hx]
      using hwD xp
  have hdiffL2 : intervalL2Size
      (paper3IntervalPerturbationDifferenceProfile (u₁ t) (u₂ t)) ≤ D :=
    intervalL2Size_le_of_pointwise_abs_bound hD0 hdiff
      (fun x hx => hdiffSup x (Set.Ioo_subset_Icc_self hx))
  have hphi₁Int : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u₁ t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hphiCont₁
  have hphi₂Int : IntervalIntegrable
      (paper3IntervalPerturbationProfile uStar (u₂ t)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hphiCont₂
  rcases paper3SignalSourceRegularity_of_classical_slice hsol₁ ht heq with
    ⟨⟨Hlin₁, Hquad₁⟩⟩
  rcases paper3SignalSourceRegularity_of_classical_slice hsol₂ ht heq with
    ⟨⟨Hlin₂, Hquad₂⟩⟩
  let Hsplit₁ := intervalSolutionSignalSplitData_of_classical_slice
    (p := p) (uStar := uStar) hsol₁ ht
  let Hsplit₂ := intervalSolutionSignalSplitData_of_classical_slice
    (p := p) (uStar := uStar) hsol₂ ht
  let Cself := paper3UniformSignalStrongConstant p uStar heq.u_pos
  let Cdiff := paper3UniformSignalDifferenceConstant p uStar heq.u_pos
  have hCself : 0 < Cself := by
    simpa [Cself] using paper3UniformSignalStrongConstant_pos p uStar heq.u_pos
  have hCdiff : 0 < Cdiff := by
    simpa [Cdiff] using paper3UniformSignalDifferenceConstant_pos p uStar heq.u_pos
  have hsignal₁ := paper3SignalComponents_strong_bounds_uniform
    p heq.u_pos hM₁0 (u₁ t) hu₁_near hphi₁
      Hlin₁.profile_aestronglyMeasurable Hquad₁.profile_aestronglyMeasurable
      hphiSup₁ hphiL2₁
  have hsignal₂ := paper3SignalComponents_strong_bounds_uniform
    p heq.u_pos hM₂0 (u₂ t) hu₂_near hphi₂
      Hlin₂.profile_aestronglyMeasurable Hquad₂.profile_aestronglyMeasurable
      hphiSup₂ hphiL2₂
  have hlin₁Lp := Hlin₁.memLp_two
  have hlin₂Lp := Hlin₂.memLp_two
  have hquad₁Lp := Hquad₁.memLp_two
  have hquad₂Lp := Hquad₂.memLp_two
  have hsignalD := paper3SignalComponents_strong_difference_bounds_uniform
    p heq.u_pos hM₁0 hM₂0 hD0 (u₁ t) (u₂ t) hu₁_near hu₂_near
      hdiff hlin₁Lp hlin₂Lp hquad₁Lp hquad₂Lp
      Hsplit₁.linear_integrable Hsplit₂.linear_integrable
      Hsplit₁.remainder_integrable Hsplit₂.remainder_integrable
      hphiSup₁ hphiSup₂ hdiffSup hdiffL2
  have hz1xxMem₁ : MemLp
      (paper3LinearSignalLaplacian p uStar (u₁ t)) 2 (intervalMeasure 1) := by
    apply memLp_two_of_hasDerivAt_Ioo_and_abs_bound_Icc
      (mul_nonneg hCself.le hM₁0)
    · intro x hx
      exact paper3LinearSignalGradient_hasDerivAt_laplacian
        p uStar (u₁ t) Hlin₁ hx
    · intro x hx
      exact (hsignal₁ x hx).2.2.1
  have hz1xxMem₂ : MemLp
      (paper3LinearSignalLaplacian p uStar (u₂ t)) 2 (intervalMeasure 1) := by
    apply memLp_two_of_hasDerivAt_Ioo_and_abs_bound_Icc
      (mul_nonneg hCself.le hM₂0)
    · intro x hx
      exact paper3LinearSignalGradient_hasDerivAt_laplacian
        p uStar (u₂ t) Hlin₂ hx
    · intro x hx
      exact (hsignal₂ x hx).2.2.1
  have hfluxInt₁ := paper3ChemFluxRemainder_deriv_intervalIntegrable
    (vStar := vStar) hsol₁ ht hm Hlin₁ hz1xxMem₁
  have hfluxInt₂ := paper3ChemFluxRemainder_deriv_intervalIntegrable
    (vStar := vStar) hsol₂ ht hm Hlin₂ hz1xxMem₂
  have hreactCont₁ : ContinuousOn
      (fun x => paper3LogisticReaction p (intervalDomainLift (u₁ t) x))
      (Set.Icc (0 : ℝ) 1) := by
    have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (u₁ t) x ≠ 0 := by
      intro x hx
      simp [intervalDomainLift, hx, (hsol₁.u_pos' ht.1 ht.2).ne']
    unfold paper3LogisticReaction
    exact huCont₁.mul (continuousOn_const.sub
      (continuousOn_const.mul
        (huCont₁.rpow_const (fun x hx => Or.inl (hpos x hx)))))
  have hreactCont₂ : ContinuousOn
      (fun x => paper3LogisticReaction p (intervalDomainLift (u₂ t) x))
      (Set.Icc (0 : ℝ) 1) := by
    have hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        intervalDomainLift (u₂ t) x ≠ 0 := by
      intro x hx
      simp [intervalDomainLift, hx, (hsol₂.u_pos' ht.1 ht.2).ne']
    unfold paper3LogisticReaction
    exact huCont₂.mul (continuousOn_const.sub
      (continuousOn_const.mul
        (huCont₂.rpow_const (fun x hx => Or.inl (hpos x hx)))))
  have hreact₁ : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u₁ t) x))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hreactCont₁
  have hreact₂ : IntervalIntegrable
      (fun x => paper3LogisticReaction p (intervalDomainLift (u₂ t) x))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hreactCont₂
  have hlogCont₁ : ContinuousOn
      (paper3IntervalLogisticRemainderProfile p uStar (u₁ t))
      (Set.Icc (0 : ℝ) 1) := by
    unfold paper3IntervalLogisticRemainderProfile paper3LogisticRemainder
    exact hreactCont₁.add (continuousOn_const.mul hphiCont₁)
  have hlogCont₂ : ContinuousOn
      (paper3IntervalLogisticRemainderProfile p uStar (u₂ t))
      (Set.Icc (0 : ℝ) 1) := by
    unfold paper3IntervalLogisticRemainderProfile paper3LogisticRemainder
    exact hreactCont₂.add (continuousOn_const.mul hphiCont₂)
  have hlogLp₁ : MemLp
      (paper3IntervalLogisticRemainderProfile p uStar (u₁ t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hlogCont₁
  have hlogLp₂ : MemLp
      (paper3IntervalLogisticRemainderProfile p uStar (u₂ t)) 2
      (intervalMeasure 1) :=
    BFormPositiveDatumNegPart.memLp_two_of_continuousOn_Icc hlogCont₂
  let Klog := paper3UniformLogisticPolarConstant p heq
  have hKlog : 0 < Klog := by
    simpa [Klog] using paper3UniformLogisticPolarConstant_pos p heq
  have hlogDiff := paper3IntervalLogisticRemainderDifference_uniform_l2
    p heq hM₁0 hM₂0 (u₁ t) (u₂ t) hu₁_near hu₂_near hdiff
      (hlogLp₁.1.sub hlogLp₂.1) hphiSup₁ hphiSup₂ hdiffL2
  rcases exists_fullNonlinearRemainderDifferenceL2Data_of_routeA
      hsol₁ hsol₂ ht hm heq Hsplit₁ Hsplit₂ Hlin₁ Hquad₁ Hlin₂ Hquad₂
      hM₁0 hM₂0 hM₁1 hM₂1 hD0 hCself hCdiff hKlog.le
      hw₁ hw₂ hwx₁ hwx₂ hwD hwxD hsignal₁ hsignal₂ hsignalD
      hfluxInt₁ hfluxInt₂ hreact₁ hreact₂ hphi₁Int hphi₂Int
      hlogDiff.1 hlogDiff.2 with
      ⟨H, hHM₁, hHM₂, hHD, hHKchem, hHKlog⟩
  have hcoeff := H.coeffL2Norm_le
  refine ⟨hcoeff.1, ?_⟩
  unfold FullNonlinearRemainderDifferenceL2Data.lipschitzConstant at hcoeff
  rw [hHM₁, hHM₂, hHD, hHKchem, hHKlog] at hcoeff
  calc
    _ ≤ 2 * Real.sqrt 2 *
          (paper3RouteAPolarizedChemL2Constant
              p uStar vStar Cself Cdiff + Klog) *
          (M₁ + M₂) * D := hcoeff.2
    _ = intervalDomainX2SigmaUniformNemytskiiLipschitzConstant
          p sigma uStar vStar heq * (d₁ + d₂) * dD := by
      dsimp [FullNonlinearRemainderDifferenceL2Data.lipschitzConstant,
        intervalDomainX2SigmaUniformNemytskiiLipschitzConstant,
        M₁, M₂, D, Cenv, d₁, d₂, dD, Cself, Cdiff, Klog]
      ring

#print axioms ResolvedSourceProfileRegularity.memLp_two
#print axioms intervalDomainX2SigmaUniformNemytskiiLipschitzConstant_pos
#print axioms paper3FullModeNonlinearRemainderCoeffM_uniform_difference_bound

end

end ShenWork.Paper3
