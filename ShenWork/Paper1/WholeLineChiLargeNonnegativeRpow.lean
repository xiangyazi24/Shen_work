import ShenWork.Paper1.WholeLineChiLargeCommittedExponent
import ShenWork.Paper1.WholeLineLocalMomentEnergy

/-!
# Nonnegative real-power calculus for the large-critical exponent

The existing whole-line local-moment energy package assumes strict positivity
solely to use real-power derivative and addition formulas.  In the committed
large-critical window one can choose `P > 2m`, hence `P > 2`.  At these
exponents Mathlib's real-power derivative is valid at zero as well.  This file
records the pointwise replacements needed by a nonnegative version of the
energy package.
-/

open Filter MeasureTheory Real Set Topology

noncomputable section

namespace ShenWork.Paper1

theorem hasDerivAt_wholeLineLocalLpTest_of_nonneg
    {P κ t x₀ x : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 2 ≤ P)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    HasDerivAt (wholeLineLocalLpTest P κ u t x₀)
      (wholeLineLocalLpTestDeriv P κ u t x₀ x) x := by
  have hpow := hu.rpow_const (p := P - 1) (Or.inr (by linarith))
  have hw := hasDerivAt_localizingWeightAt κ x₀ x
  have hprod := hpow.mul hw
  convert hprod using 1
  unfold wholeLineLocalLpTestDeriv
  rw [deriv_localizingWeightAt,
    show P - 1 - 1 = P - 2 by ring]
  ring

theorem hasDerivAt_wholeLineLocalChemotaxisFlux_of_nonneg
    {p : CMParams} {t x : ℝ} {u v : ℝ → ℝ → ℝ}
    (hu : HasDerivAt (u t) (deriv (u t) x) x)
    (hv₂ : HasDerivAt (deriv (v t)) (iteratedDeriv 2 (v t) x) x) :
    HasDerivAt (wholeLineLocalChemotaxisFlux p u v t)
      (deriv (wholeLineLocalChemotaxisFlux p u v t) x) x := by
  have hpow := hu.rpow_const (p := p.m) (Or.inr p.hm)
  have hprod := hpow.mul hv₂
  have hprod' : HasDerivAt (wholeLineLocalChemotaxisFlux p u v t)
      (deriv (u t) x * p.m * (u t x) ^ (p.m - 1) * deriv (v t) x +
        (u t x) ^ p.m * iteratedDeriv 2 (v t) x) x := by
    simpa [wholeLineLocalChemotaxisFlux, Pi.mul_apply] using hprod
  exact hprod'.congr_deriv hprod'.deriv.symm

theorem hasDerivAt_wholeLineLocalChemotaxisPower_of_nonneg
    {p : CMParams} {P t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 2 ≤ P)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    HasDerivAt (fun y : ℝ => (u t y) ^ (P + p.m - 1))
      ((P + p.m - 1) * (u t x) ^ (P + p.m - 2) *
        deriv (u t) x) x := by
  have hpow := hu.rpow_const (p := P + p.m - 1)
    (Or.inr (by linarith [p.hm]))
  convert hpow using 1
  ring

theorem wholeLineLocalLpHalfPower_deriv_of_nonneg
    {P t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 2 ≤ P)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    deriv (fun y : ℝ => (u t y) ^ (P / 2)) x =
      (P / 2) * (u t x) ^ (P / 2 - 1) * deriv (u t) x := by
  have hpow := hu.rpow_const (p := P / 2) (Or.inr (by linarith))
  rw [hpow.deriv]
  ring

theorem wholeLineLocalLpHalfPower_deriv_sq_of_nonneg
    {P t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hP : 2 ≤ P) (hu0 : 0 ≤ u t x)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    (deriv (fun y : ℝ => (u t y) ^ (P / 2)) x) ^ 2 =
      (P / 2) ^ 2 *
        ((u t x) ^ (P - 2) * (deriv (u t) x) ^ 2) := by
  rw [wholeLineLocalLpHalfPower_deriv_of_nonneg hP hu]
  have ha : 0 ≤ P / 2 - 1 := by linarith
  have hpow : ((u t x) ^ (P / 2 - 1)) ^ 2 =
      (u t x) ^ (P - 2) := by
    calc
      ((u t x) ^ (P / 2 - 1)) ^ 2 =
          (u t x) ^ (P / 2 - 1) *
            (u t x) ^ (P / 2 - 1) := by ring
      _ = (u t x) ^ ((P / 2 - 1) + (P / 2 - 1)) := by
        rw [Real.rpow_add_of_nonneg hu0 ha ha]
      _ = (u t x) ^ (P - 2) := by
        congr 1
        ring
  calc
    ((P / 2) * (u t x) ^ (P / 2 - 1) * deriv (u t) x) ^ 2 =
        (P / 2) ^ 2 *
          (((u t x) ^ (P / 2 - 1)) ^ 2 * (deriv (u t) x) ^ 2) := by
      ring
    _ = (P / 2) ^ 2 *
        ((u t x) ^ (P - 2) * (deriv (u t) x) ^ 2) := by
      rw [hpow]

theorem wholeLineLocalLpTestDeriv_mul_flux_of_nonneg
    {P κ t x₀ x : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ} (hP : 2 ≤ P) (hu0 : 0 ≤ u t x) :
    wholeLineLocalLpTestDeriv P κ u t x₀ x *
        wholeLineLocalChemotaxisFlux p u v t x =
      (P - 1) *
          ((u t x) ^ (P + p.m - 2) * deriv (u t) x *
            deriv (v t) x * localizingWeightAt κ x₀ x) +
        (u t x) ^ (P + p.m - 1) * deriv (v t) x *
          deriv (localizingWeightAt κ x₀) x := by
  have hPm2 : 0 ≤ P - 2 := by linarith
  have hPm1 : 0 ≤ P - 1 := by linarith
  have hm0 : 0 ≤ p.m := zero_le_one.trans p.hm
  have hpow₁ :
      (u t x) ^ (P - 2) * (u t x) ^ p.m =
        (u t x) ^ (P + p.m - 2) := by
    calc
      (u t x) ^ (P - 2) * (u t x) ^ p.m =
          (u t x) ^ ((P - 2) + p.m) := by
        rw [Real.rpow_add_of_nonneg hu0 hPm2 hm0]
      _ = (u t x) ^ (P + p.m - 2) := by
        congr 1
        ring
  have hpow₂ :
      (u t x) ^ (P - 1) * (u t x) ^ p.m =
        (u t x) ^ (P + p.m - 1) := by
    calc
      (u t x) ^ (P - 1) * (u t x) ^ p.m =
          (u t x) ^ ((P - 1) + p.m) := by
        rw [Real.rpow_add_of_nonneg hu0 hPm1 hm0]
      _ = (u t x) ^ (P + p.m - 1) := by
        congr 1
        ring
  unfold wholeLineLocalLpTestDeriv wholeLineLocalChemotaxisFlux
  calc
    (((P - 1) * (u t x) ^ (P - 2) * deriv (u t) x *
          localizingWeightAt κ x₀ x +
        (u t x) ^ (P - 1) * deriv (localizingWeightAt κ x₀) x) *
      ((u t x) ^ p.m * deriv (v t) x)) =
        (P - 1) *
            (((u t x) ^ (P - 2) * (u t x) ^ p.m) * deriv (u t) x *
              deriv (v t) x * localizingWeightAt κ x₀ x) +
          ((u t x) ^ (P - 1) * (u t x) ^ p.m) * deriv (v t) x *
            deriv (localizingWeightAt κ x₀) x := by
      ring
    _ = (P - 1) *
          ((u t x) ^ (P + p.m - 2) * deriv (u t) x *
            deriv (v t) x * localizingWeightAt κ x₀ x) +
        (u t x) ^ (P + p.m - 1) * deriv (v t) x *
          deriv (localizingWeightAt κ x₀) x := by
      rw [hpow₁, hpow₂]

/-- The old fixed-time energy structure cannot even describe the identically
zero solution, independently of all PDE and integrability fields. -/
theorem not_wholeLineLocalMomentEnergyData_zero
    (p : CMParams) (P κ T t x₀ : ℝ) :
    IsEmpty (WholeLineLocalMomentEnergyData p P κ T t x₀
      (fun _ _ => 0) (fun _ _ => 0)) := by
  constructor
  intro H
  have hzero : (0 : ℝ) < 0 := by simpa using H.u_pos 0
  exact (lt_irrefl 0 hzero)

section AxiomAudit

#print axioms hasDerivAt_wholeLineLocalLpTest_of_nonneg
#print axioms hasDerivAt_wholeLineLocalChemotaxisFlux_of_nonneg
#print axioms hasDerivAt_wholeLineLocalChemotaxisPower_of_nonneg
#print axioms wholeLineLocalLpHalfPower_deriv_sq_of_nonneg
#print axioms wholeLineLocalLpTestDeriv_mul_flux_of_nonneg
#print axioms not_wholeLineLocalMomentEnergyData_zero

end AxiomAudit

end ShenWork.Paper1
