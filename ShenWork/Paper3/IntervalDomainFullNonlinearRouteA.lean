/- Assemble the route-(a) flux and logistic profiles into the full modal source. -/
import ShenWork.Paper3.IntervalDomainRouteAFluxL2

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

structure FullNonlinearRemainderRouteAData
    (rem : ℕ → ℝ) where
  chi : ℝ
  flux : EliminatedFluxDerivativeRouteAL2Data
  Klog : ℝ
  logProfile : ℝ → ℝ
  Klog_nonneg : 0 ≤ Klog
  log_memLp : MemLp logProfile 2 (intervalMeasure 1)
  log_l2 : intervalL2Size logProfile ≤ Klog * flux.bounds.M * flux.bounds.L
  coeff_eq : ∀ n,
    rem n = cosineCoeffs (fun x => -chi * flux.profile x) n +
      cosineCoeffs logProfile n

namespace FullNonlinearRemainderRouteAData

def chemConstant {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderRouteAData rem) : ℝ :=
  |H.chi| * H.flux.l2Constant

theorem chemConstant_nonneg {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderRouteAData rem) :
    0 ≤ H.chemConstant :=
  mul_nonneg (abs_nonneg _) H.flux.l2Constant_nonneg

def toL2Data {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderRouteAData rem) :
    FullNonlinearRemainderL2Data rem where
  M := H.flux.bounds.M
  L := H.flux.bounds.L
  Kchem := H.chemConstant
  Klog := H.Klog
  chemProfile := fun x => -H.chi * H.flux.profile x
  logProfile := H.logProfile
  M_nonneg := H.flux.bounds.M_nonneg
  L_nonneg := H.flux.bounds.L_nonneg
  Kchem_nonneg := H.chemConstant_nonneg
  Klog_nonneg := H.Klog_nonneg
  chem_memLp := H.flux.profile_memLp.const_mul (-H.chi)
  log_memLp := H.log_memLp
  chem_l2 := by
    have hcoef : 0 ≤ |H.chi| := abs_nonneg _
    have hprofile := H.flux.intervalL2Size_le
    have hmul := intervalL2Size_le_of_pointwise_mul
      (f := fun x => -H.chi * H.flux.profile x)
      (g := H.flux.profile) (B := |H.chi|) hcoef
      (H.flux.profile_memLp.const_mul (-H.chi)) H.flux.profile_memLp (by
        intro x _
        rw [abs_mul, abs_neg])
    calc
      intervalL2Size (fun x => -H.chi * H.flux.profile x) ≤
          |H.chi| * intervalL2Size H.flux.profile := hmul
      _ ≤ |H.chi| *
          (H.flux.l2Constant * H.flux.bounds.M * H.flux.bounds.L) :=
        mul_le_mul_of_nonneg_left hprofile hcoef
      _ = H.chemConstant * H.flux.bounds.M * H.flux.bounds.L := by
        unfold chemConstant
        ring
  log_l2 := H.log_l2
  coeff_eq := H.coeff_eq

/-- Complete one-trajectory route-(a) Nemytskii coefficient estimate. -/
theorem coeffL2Norm_le {rem : ℕ → ℝ}
    (H : FullNonlinearRemainderRouteAData rem) :
    Summable (fun n : ℕ => ‖(rem n : ℂ)‖ ^ 2) ∧
      ShenWork.PDE.SectorialOperator.coeffL2Norm
          (fun n => (rem n : ℂ)) ≤
        H.toL2Data.quadraticConstant *
          H.flux.bounds.M * H.flux.bounds.L :=
  H.toL2Data.coeffL2Norm_le

#print axioms FullNonlinearRemainderRouteAData.coeffL2Norm_le

end FullNonlinearRemainderRouteAData

end

end ShenWork.Paper3
