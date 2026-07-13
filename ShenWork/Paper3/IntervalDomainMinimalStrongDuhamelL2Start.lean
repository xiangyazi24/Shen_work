/- Positive-time strong smoothing from an unweighted mass-constrained slice. -/
import ShenWork.Paper3.IntervalDomainMinimalStrongDuhamel
import ShenWork.Paper3.IntervalDomainStrongDuhamelL2Start

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- The full Duhamel formula regularizes a zero-mean unweighted slice into the
strong space.  Both the datum and nonlinear source remain on the physical mass
hyperplane, so the neutral zeroth mode never enters the estimate. -/
theorem intervalDomainMassX2SigmaPerturbation_and_norm_le_of_L2_restart
    {p : CM2Params} {T a t sigma uStar vStar gap B : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (ha : 0 < a) (hat : a < t) (htT : t < T)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar)
    (hma0 : Summable fun n : ℕ =>
      ‖intervalDomainPerturbationCosineCoeff uStar (u a) n‖ ^ 2)
    (hN : ∀ s ∈ Set.Ioo a t, Summable fun n : ℕ =>
      ‖((paper3FullModeNonlinearRemainderCoeffM
        p uStar vStar u v s n : ℝ) : ℂ)‖ ^ 2)
    (hB : 0 ≤ B)
    (hNnorm : ∀ s ∈ Set.Ioo a t,
      coeffL2Norm (fun n =>
        ((paper3FullModeNonlinearRemainderCoeffM
          p uStar vStar u v s n : ℝ) : ℂ)) ≤ B) :
    IntervalDomainX2SigmaPerturbation sigma uStar (u t) ∧
      intervalDomainX2SigmaDistance sigma uStar (u t) ≤
        unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma * (t - a) ^ (-sigma) *
          Real.exp (-(gap / 2) * (t - a)) *
            coeffL2Norm
              (intervalDomainPerturbationCosineCoeff uStar (u a)) +
        B * restartedKernelMassPositive
          (unitIntervalLinearizedStrongSmoothingConstant
            p uStar vStar gap sigma) sigma (gap / 2) := by
  have haLe : a ≤ t := hat.le
  have hgapTime : 0 < t - a := sub_pos.mpr hat
  let C := unitIntervalLinearizedStrongSmoothingConstant
    p uStar vStar gap sigma
  have hC : 0 < C := by
    simpa [C] using unitIntervalLinearizedStrongSmoothingConstant_pos
      p hgap.1 hsigma
  have hzeroA := intervalDomainPerturbationCosineCoeff_zero_of_physicalMass
    hsol (show a ∈ Set.Ioo (0 : ℝ) T from ⟨ha, hat.trans htT⟩) hmass
  have hlinear : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma
        (diagonalSemigroupCoeff
          (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
          (intervalDomainPerturbationCosineCoeff uStar (u a))) n :=
    unitIntervalLinearizedMass_fractionalPower_summable
      p heq hgap hsigma hgapTime hma0 hzeroA
  have hint := paper3MassStrongDuhamelIntegrand_intervalIntegrable
    hsol hm ha0 hb0 ha haLe htT heq hgap hsigma hsigma1 hN hB hNnorm
  have htarget : IntervalDomainX2SigmaPerturbation sigma uStar (u t) :=
    fractionalPowerEnergy_summable_of_mild
      (L := 1) (sigma := sigma) (a := a) (t := t)
      (growth := unitIntervalLinearizedGrowth p uStar vStar)
      (c := fun r => intervalDomainPerturbationCosineCoeff uStar (u r))
      (source := fun r =>
        paper3WindowedNonlinearCoeff p uStar vStar a t u v r)
      hlinear
      (paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
        p ha0 hb0 u v heq hgap hsigma hN)
      hint
      (intervalDomainPerturbationCosineCoeff_full_restart_windowed
        hsol hm ha haLe htT)
  refine ⟨htarget, ?_⟩
  have hmild :
      weightedCoeffToLp 1 sigma
          (intervalDomainPerturbationCosineCoeff uStar (u t)) htarget =
        weightedCoeffToLp 1 sigma
            (diagonalSemigroupCoeff
              (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
              (intervalDomainPerturbationCosineCoeff uStar (u a))) hlinear +
          ∫ s in a..t,
            paper3MassStrongDuhamelIntegrand
              p ha0 hb0 u v heq hgap hsigma hN s := by
    apply weightedCoeffToLp_mild_eq
      (hsource := paper3WindowedNonlinearCoeff_mass_X2SigmaSummable
        p ha0 hb0 u v heq hgap hsigma hN)
      (hint := hint)
    exact intervalDomainPerturbationCosineCoeff_full_restart_windowed
      hsol hm ha haLe htT
  let linear : CoeffL2 := weightedCoeffToLp 1 sigma
    (diagonalSemigroupCoeff
      (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
      (intervalDomainPerturbationCosineCoeff uStar (u a))) hlinear
  have hlinearNorm : ‖linear‖ ≤
      C * (t - a) ^ (-sigma) *
        Real.exp (-(gap / 2) * (t - a)) *
          coeffL2Norm
            (intervalDomainPerturbationCosineCoeff uStar (u a)) := by
    rw [show ‖linear‖ = Real.sqrt (∑' n : ℕ,
        fractionalPowerEnergyTerm 1 sigma
          (diagonalSemigroupCoeff
            (unitIntervalLinearizedGrowth p uStar vStar) (t - a)
            (intervalDomainPerturbationCosineCoeff uStar (u a))) n) by
      exact norm_weightedCoeffToLp _ _ _ _]
    simpa [C] using unitIntervalLinearizedMass_fractionalPowerNorm_le
      p heq hgap hsigma hgapTime hma0 hzeroA
  let major : ℝ → ℝ := fun s =>
    B * restartedSmoothingKernel C sigma (gap / 2) (t - s)
  have hkernel : IntervalIntegrable
      (restartedSmoothingKernel C sigma (gap / 2)) volume 0 (t - a) :=
    restartedSmoothingKernel_intervalIntegrable_positive
      hsigma hsigma1 (by linarith [hgap.1]) hgapTime.le
  have hmajorInt : IntervalIntegrable major volume a t := by
    have hcomp : IntervalIntegrable
        (fun s => restartedSmoothingKernel C sigma (gap / 2) (t - s))
        volume a t := by
      simpa using (hkernel.comp_sub_left t).symm
    simpa [major] using hcomp.const_mul B
  have hintegralMajor :
      ‖∫ s in a..t,
          paper3MassStrongDuhamelIntegrand
            p ha0 hb0 u v heq hgap hsigma hN s‖ ≤
        ∫ s in a..t, major s := by
    apply intervalIntegral.norm_integral_le_of_norm_le haLe
      (Filter.Eventually.of_forall fun s hs => ?_) hmajorInt
    by_cases hst : s = t
    · subst s
      have hnot : t ∉ Set.Ioo a t := by simp
      have hintegrand : paper3MassStrongDuhamelIntegrand
          p ha0 hb0 u v heq hgap hsigma hN t = 0 := by
        ext n
        change paper3MassStrongDuhamelIntegrand
          p ha0 hb0 u v heq hgap hsigma hN t n = (0 : ℂ)
        simp [paper3MassStrongDuhamelIntegrand, weightedCoeffSequence,
          diagonalSemigroupCoeff, paper3WindowedNonlinearCoeff, hnot]
      rw [hintegrand, norm_zero]
      have hrzero : 0 ≤ (t - t) ^ (-sigma) :=
        Real.rpow_nonneg (by linarith) _
      exact mul_nonneg hB (by
        dsimp [major, restartedSmoothingKernel]
        exact mul_nonneg
          (mul_nonneg hC.le (add_nonneg zero_le_one hrzero))
          (Real.exp_nonneg _))
    have hsopen : s ∈ Set.Ioo a t :=
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hsmooth := paper3MassStrongDuhamelIntegrand_norm_le
      p ha0 hb0 u v heq hgap hsigma hN hs
    have hfactor : 0 ≤ C * (t - s) ^ (-sigma) *
        Real.exp (-(gap / 2) * (t - s)) :=
      mul_nonneg
        (mul_nonneg hC.le
          (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
        (Real.exp_nonneg _)
    refine hsmooth.trans ?_
    calc
      C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) *
          coeffL2Norm (fun n =>
            ((paper3FullModeNonlinearRemainderCoeffM
              p uStar vStar u v s n : ℝ) : ℂ)) ≤
        C * (t - s) ^ (-sigma) * Real.exp (-(gap / 2) * (t - s)) * B := by
          exact mul_le_mul_of_nonneg_left (hNnorm s hsopen) hfactor
      _ ≤ major s := by
        dsimp [major, restartedSmoothingKernel]
        have hrpow : 0 ≤ (t - s) ^ (-sigma) :=
          Real.rpow_nonneg (sub_nonneg.mpr hs.2) _
        have hexp : 0 ≤ Real.exp (-(gap / 2) * (t - s)) :=
          Real.exp_nonneg _
        nlinarith [mul_nonneg hB (mul_nonneg hC.le hexp),
          mul_nonneg (add_nonneg zero_le_one hrpow) hexp]
  have hmajorMass : (∫ s in a..t, major s) ≤
      B * restartedKernelMassPositive C sigma (gap / 2) := by
    have heqInt : (∫ s in a..t, major s) =
        B * (∫ r in (0 : ℝ)..(t - a),
          restartedSmoothingKernel C sigma (gap / 2) r) := by
      dsimp [major]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simpa only [sub_self] using (intervalIntegral.integral_comp_sub_left
        (f := restartedSmoothingKernel C sigma (gap / 2))
        (a := a) (b := t) t)
    rw [heqInt]
    exact mul_le_mul_of_nonneg_left
      (restartedSmoothingKernel_integral_le_positive
        hC.le hsigma hsigma1 (by linarith [hgap.1]) hgapTime.le) hB
  rw [show intervalDomainX2SigmaDistance sigma uStar (u t) =
      ‖weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) htarget‖ by
    symm
    simpa [intervalDomainX2SigmaDistance] using
      norm_weightedCoeffToLp 1 sigma
        (intervalDomainPerturbationCosineCoeff uStar (u t)) htarget]
  rw [hmild]
  have htri := norm_add_le linear
    (∫ s in a..t,
      paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN s)
  change ‖linear + ∫ s in a..t,
      paper3MassStrongDuhamelIntegrand
        p ha0 hb0 u v heq hgap hsigma hN s‖ ≤ _
  exact htri.trans (add_le_add hlinearNorm (hintegralMajor.trans hmajorMass))

#print axioms
  intervalDomainMassX2SigmaPerturbation_and_norm_le_of_L2_restart

end

end ShenWork.Paper3
