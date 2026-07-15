import ShenWork.Paper3.IntervalDomainMinimalWeakSupBasinEntry

/-!
# Finite-horizon weak-sup entry for the mass-constrained minimal model
-/

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.PDE
open ShenWork.PDE.FractionalPower
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Finite-horizon Stage-B entry.  Unlike the public global-orbit interface,
this theorem only assumes that the fixed weak restart window lies strictly
inside the current classical horizon.  It is the continuation-safe form used
to rule out a finite maximal lifespan. -/
theorem intervalDomainMassSupToStrongBasinEntry_of_contraction_of_solution
    (p : CM2Params)
    {sigma uStar vStar T gap CL Htime : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (hm : p.m = 1) (ha0 : p.a = 0) (hb0 : p.b = 0)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hgap : UnitIntervalLinearMassSpectralGap p uStar vStar gap)
    (hT : 0 < T) (hCL : 0 < CL)
    (hCLlip : ∀ r s : ℝ,
      |r| ≤ intervalDomainWeakSupConeCeiling uStar →
      |s| ≤ intervalDomainWeakSupConeCeiling uStar →
      |r * (p.a - p.b * r ^ p.α) -
        s * (p.a - p.b * s ^ p.α)| ≤ CL * |r - s|)
    (hcontract :
      intervalDomainWeakSupContractionCoefficient p uStar CL T < 1 / 4)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hclose : SupCloseToConstant intervalDomain u₀ uStar
      (paper3WeakSupBasinDelta p sigma uStar vStar T gap heq))
    (hsol : IsPaper2ClassicalSolution intervalDomain p Htime u v)
    (hHT : 5 * T / 4 < Htime)
    (htrace : InitialTrace intervalDomain u₀ u)
    (hmass : HasEquilibriumMassOnPositiveTimes intervalDomain u uStar) :
    IntervalDomainX2SigmaPerturbation sigma uStar (u T) ∧
      intervalDomainX2SigmaDistance sigma uStar (u T) ≤
        intervalDomainStrongBootstrapRadius
          p sigma uStar vStar gap heq / 2 := by
  let rho := (sigma + 1) / 2
  let theta := sigma / rho
  let q := 1 - theta
  let Hbound := paper3WeakWindowStrongSmoothingBound
    p uStar vStar T gap rho heq
  let R := intervalDomainStrongBootstrapRadius
    p sigma uStar vStar gap heq
  let delta := paper3WeakSupBasinDelta p sigma uStar vStar T gap heq
  have hsigma : 0 < sigma := by linarith
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have hsigmaRho : sigma < rho := by dsimp [rho]; linarith
  have hrho1 : rho < 1 := by dsimp [rho]; linarith
  have htheta : 0 < theta := div_pos hsigma hrho
  have htheta1 : theta < 1 := (div_lt_one hrho).2 hsigmaRho
  have hq : 0 < q := by dsimp [q]; linarith
  have hdelta : 0 < delta := by
    simpa [delta] using paper3WeakSupBasinDelta_pos_of_gap_pos
      p hsigmaStrong hsigma1 heq hgap.1 hT
  have hdeltaStar : delta ≤ uStar / 16 := by
    simpa [delta] using paper3WeakSupBasinDelta_le_equilibrium
      p sigma uStar vStar T gap heq
  have hdeltaQuarter : delta ≤ 1 / 4 := by
    simpa [delta] using paper3WeakSupBasinDelta_le_quarter
      p sigma uStar vStar T gap heq
  have hdeltaOne : 4 * delta ≤ 1 := by linarith
  have hHbound : 0 < Hbound := by
    simpa [Hbound] using paper3WeakWindowStrongSmoothingBound_pos
      p heq hT hgap.1 hrho hrho1
  have hR : 0 < R := by
    simpa [R] using intervalDomainStrongBootstrapRadius_pos
      p heq hgap.1 hsigma hsigma1
  rcases intervalDomainWeakSupRestartWindowData_of_contraction_of_solution
      p hm heq hT hCL hCLlip hcontract hdelta hdeltaStar hu₀
        (by simpa [delta] using hclose) hsol hHT htrace with ⟨D⟩
  have haTH : D.a + T < Htime := by
    calc
      D.a + T ≤ T / 4 + T := by linarith [D.a_le_quarter]
      _ = 5 * T / 4 := by ring
      _ < Htime := hHT
  have hhigh := weakRestart_target_uniform_mass_X2Rho_of_solution
    D hm ha0 hb0 heq hgap hmass hsol haTH hdelta.le hdeltaStar
      hdeltaOne hrho hrho1
  let rtarget := T - D.a
  have htargetMem : rtarget ∈ Set.Icc (0 : ℝ) T := by
    dsimp [rtarget]
    constructor
    · linarith [D.a_le_quarter, hT]
    · linarith [D.a_pos]
  have htarget0Raw := weakRestart_perturbationCoeff_L2_of_solution
    D hm hsol haTH hdelta.le htargetMem
  have htarget0 :
      Summable (fun n : ℕ =>
        ‖intervalDomainPerturbationCosineCoeff uStar (u T) n‖ ^ 2) ∧
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ≤
        8 * delta := by
    simpa [rtarget] using htarget0Raw
  have hinterpEnergy := fractionalPowerEnergy_interpolation
    hsigma hsigmaRho htarget0.1 hhigh.1
  have hmem : IntervalDomainX2SigmaPerturbation sigma uStar (u T) := by
    simpa [IntervalDomainX2SigmaPerturbation] using hinterpEnergy.1
  have hinterp := fractionalPowerNorm_interpolation
    hsigma hsigmaRho htarget0.1 hhigh.1
  have hcoeffPow :
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q ≤
        (8 * delta) ^ q :=
    Real.rpow_le_rpow (coeffL2Norm_nonneg _) htarget0.2 hq.le
  have hhighPow :
      intervalDomainX2SigmaDistance rho uStar (u T) ^ theta ≤
        Hbound ^ theta :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (by simpa [Hbound] using hhigh.2)
      htheta.le
  have hproduct :
      coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q *
          intervalDomainX2SigmaDistance rho uStar (u T) ^ theta ≤
        (8 * delta) ^ q * Hbound ^ theta :=
    mul_le_mul hcoeffPow hhighPow
      (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (Real.rpow_nonneg (mul_nonneg (by norm_num) hdelta.le) _)
  have hchosen : (8 * delta) ^ q * Hbound ^ theta ≤ R / 2 := by
    simpa [delta, rho, theta, q, Hbound, R] using
      paper3WeakSupBasinDelta_interpolation_bound_of_gap_pos
        p hsigmaStrong hsigma1 heq hgap.1 hT
  refine ⟨hmem, ?_⟩
  calc
    intervalDomainX2SigmaDistance sigma uStar (u T) ≤
        coeffL2Norm (intervalDomainPerturbationCosineCoeff uStar (u T)) ^ q *
          intervalDomainX2SigmaDistance rho uStar (u T) ^ theta := by
      simpa [intervalDomainX2SigmaDistance, q, theta] using hinterp
    _ ≤ (8 * delta) ^ q * Hbound ^ theta := hproduct
    _ ≤ R / 2 := hchosen
    _ = intervalDomainStrongBootstrapRadius
        p sigma uStar vStar gap heq / 2 := by rfl


#print axioms intervalDomainMassSupToStrongBasinEntry_of_contraction_of_solution

end

end ShenWork.Paper3
