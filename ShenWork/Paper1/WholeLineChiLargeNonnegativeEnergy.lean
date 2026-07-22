import ShenWork.Paper1.WholeLineChiLargeNonnegativeRpow
import ShenWork.Paper1.WholeLineLocalMomentBound

/-!
# Nonnegative local-moment energy package in the large-critical window

This parallel package removes the strict-positivity field from
`WholeLineLocalMomentEnergyData`. The committed exponent satisfies
`P > 2m ≥ 2`, so the weighted energy calculation remains valid at zeros.
-/

open Filter MeasureTheory Real Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper1

structure WholeLineLocalMomentNonnegativeEnergyData
    (p : CMParams) (P κ T t x₀ : ℝ)
    (u v : ℝ → ℝ → ℝ) where
  hP : 1 < P
  hPtwo : 2 ≤ P
  hκ : 0 < κ
  ht0 : 0 < t
  htT : t < T
  solution : IsClassicalSolution p T u v
  u_nonnegative : ∀ x, 0 ≤ u t x
  time : WholeLineLocalMomentTimeData P κ t x₀ u
    (fun s x => deriv (fun r => u r x) s)
  diffusion : WholeLineIBPData
    (wholeLineLocalLpTest P κ u t x₀)
    (wholeLineLocalLpTestDeriv P κ u t x₀)
    (deriv (u t)) (iteratedDeriv 2 (u t))
  diffusionWeight : WholeLineIBPData
    (fun x : ℝ => (1 / P) * (u t x) ^ P)
    (fun x : ℝ => (u t x) ^ (P - 1) * deriv (u t) x)
    (deriv (localizingWeightAt κ x₀))
    (iteratedDeriv 2 (localizingWeightAt κ x₀))
  chemotaxisFirst : WholeLineIBPData
    (wholeLineLocalLpTest P κ u t x₀)
    (wholeLineLocalLpTestDeriv P κ u t x₀)
    (wholeLineLocalChemotaxisFlux p u v t)
    (deriv (wholeLineLocalChemotaxisFlux p u v t))
  chemotaxisSecond : WholeLineIBPData
    (fun x : ℝ => (u t x) ^ (P + p.m - 1))
    (fun x : ℝ => (P + p.m - 1) *
      (u t x) ^ (P + p.m - 2) * deriv (u t) x)
    (fun x : ℝ => deriv (v t) x * localizingWeightAt κ x₀ x)
    (fun x : ℝ =>
      iteratedDeriv 2 (v t) x * localizingWeightAt κ x₀ x +
        deriv (v t) x * deriv (localizingWeightAt κ x₀) x)
  diffusion_dissipation_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P - 2) * (deriv (u t) x) ^ 2 *
      localizingWeightAt κ x₀ x)
  diffusion_weightCross_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P - 1) * deriv (u t) x *
      deriv (localizingWeightAt κ x₀) x)
  weightSecond_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ P * iteratedDeriv 2 (localizingWeightAt κ x₀) x)
  chemotaxis_firstCross_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.m - 2) * deriv (u t) x *
      deriv (v t) x * localizingWeightAt κ x₀ x)
  moment_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ P * localizingWeightAt κ x₀ x)
  logistic_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x)
  chemotaxis_high_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.m + p.γ - 1) * localizingWeightAt κ x₀ x)
  signal_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.m - 1) * v t x *
      localizingWeightAt κ x₀ x)
  signal_secondDerivative_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.m - 1) * iteratedDeriv 2 (v t) x *
      localizingWeightAt κ x₀ x)
  signal_weightCross_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.m - 1) * deriv (v t) x *
      deriv (localizingWeightAt κ x₀) x)
  signal_gradient_abs_integrable : Integrable (fun x : ℝ =>
    (u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
      localizingWeightAt κ x₀ x)

/-! ## Diffusion calculation -/

theorem wholeLineLocalLpHalfPowerGradient_eq_dissipation_of_nonnegativeData
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    wholeLineLocalLpHalfPowerGradient P κ u t x₀ =
      (P / 2) ^ 2 *
        wholeLineLocalLpDiffusionDissipation P κ u t x₀ := by
  unfold wholeLineLocalLpHalfPowerGradient
  unfold wholeLineLocalLpDiffusionDissipation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hu := (H.solution.u_smooth t x H.ht0 H.htT).2.hasDerivAt
  rw [wholeLineLocalLpHalfPower_deriv_sq_of_nonneg H.hPtwo (H.u_nonnegative x) hu]
  ring

theorem WholeLineLocalMomentNonnegativeEnergyData.diffusion_first_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    (∫ x : ℝ,
      wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) =
      -(P - 1) * wholeLineLocalLpDiffusionDissipation P κ u t x₀ -
        wholeLineLocalLpDiffusionWeightCross P κ u t x₀ := by
  have hibp := H.diffusion.integral_mul_deriv
  calc
    (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) =
        -∫ x : ℝ,
          wholeLineLocalLpTestDeriv P κ u t x₀ x * deriv (u t) x := hibp
    _ = -(P - 1) * wholeLineLocalLpDiffusionDissipation P κ u t x₀ -
          wholeLineLocalLpDiffusionWeightCross P κ u t x₀ := by
      rw [show (∫ x : ℝ,
          wholeLineLocalLpTestDeriv P κ u t x₀ x * deriv (u t) x) =
          ∫ x : ℝ,
            (P - 1) *
                ((u t x) ^ (P - 2) * (deriv (u t) x) ^ 2 *
                  localizingWeightAt κ x₀ x) +
              (u t x) ^ (P - 1) * deriv (u t) x *
                deriv (localizingWeightAt κ x₀) x by
        congr 1
        funext x
        unfold wholeLineLocalLpTestDeriv
        ring]
      rw [integral_add
        (H.diffusion_dissipation_integrable.const_mul (P - 1))
        H.diffusion_weightCross_integrable]
      rw [integral_const_mul]
      unfold wholeLineLocalLpDiffusionDissipation
      unfold wholeLineLocalLpDiffusionWeightCross
      ring

theorem WholeLineLocalMomentNonnegativeEnergyData.diffusion_weight_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    -wholeLineLocalLpDiffusionWeightCross P κ u t x₀ =
      (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ := by
  have hibp := H.diffusionWeight.integral_mul_deriv
  calc
    -wholeLineLocalLpDiffusionWeightCross P κ u t x₀ =
        -∫ x : ℝ,
          (u t x) ^ (P - 1) * deriv (u t) x *
            deriv (localizingWeightAt κ x₀) x := by
      rfl
    _ = ∫ x : ℝ,
        ((1 / P) * (u t x) ^ P) *
          iteratedDeriv 2 (localizingWeightAt κ x₀) x := hibp.symm
    _ = (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ := by
      unfold wholeLineLocalLpWeightSecond
      rw [← integral_const_mul]
      congr 1
      funext x
      ring

theorem WholeLineLocalMomentNonnegativeEnergyData.diffusion_identity
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    (∫ x : ℝ,
      wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) =
      -(4 * (P - 1) / P ^ 2) *
          wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
        (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ := by
  have hfirst := H.diffusion_first_ibp
  have hweight := H.diffusion_weight_ibp
  have hgrad := wholeLineLocalLpHalfPowerGradient_eq_dissipation_of_nonnegativeData H
  calc
    (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) =
        -(P - 1) * wholeLineLocalLpDiffusionDissipation P κ u t x₀ -
          wholeLineLocalLpDiffusionWeightCross P κ u t x₀ := hfirst
    _ = -(P - 1) * wholeLineLocalLpDiffusionDissipation P κ u t x₀ +
          (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ := by
      linarith
    _ = -(4 * (P - 1) / P ^ 2) *
          wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ := by
      rw [hgrad]
      field_simp [ne_of_gt (lt_trans zero_lt_one H.hP)]
      ring

/-! ## Chemotaxis calculation -/


theorem WholeLineLocalMomentNonnegativeEnergyData.chemotaxis_first_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    -p.χ * (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x *
          deriv (wholeLineLocalChemotaxisFlux p u v t) x) =
      p.χ * (P - 1) *
          wholeLineLocalLpChemotaxisFirstCross p P κ u v t x₀ +
        p.χ * wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ := by
  have hibp := H.chemotaxisFirst.integral_mul_deriv
  calc
    -p.χ * (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x *
          deriv (wholeLineLocalChemotaxisFlux p u v t) x) =
        -p.χ * (-∫ x : ℝ,
          wholeLineLocalLpTestDeriv P κ u t x₀ x *
            wholeLineLocalChemotaxisFlux p u v t x) := by
      rw [hibp]
    _ = p.χ * (∫ x : ℝ,
        wholeLineLocalLpTestDeriv P κ u t x₀ x *
          wholeLineLocalChemotaxisFlux p u v t x) := by ring
    _ = p.χ * (∫ x : ℝ,
        (P - 1) *
            ((u t x) ^ (P + p.m - 2) * deriv (u t) x *
              deriv (v t) x * localizingWeightAt κ x₀ x) +
          (u t x) ^ (P + p.m - 1) * deriv (v t) x *
            deriv (localizingWeightAt κ x₀) x) := by
      congr 2
      funext x
      exact wholeLineLocalLpTestDeriv_mul_flux_of_nonneg H.hPtwo (H.u_nonnegative x)
    _ = p.χ * (P - 1) *
          wholeLineLocalLpChemotaxisFirstCross p P κ u v t x₀ +
        p.χ * wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ := by
      rw [integral_add
        (H.chemotaxis_firstCross_integrable.const_mul (P - 1))
        H.signal_weightCross_integrable]
      rw [integral_const_mul]
      unfold wholeLineLocalLpChemotaxisFirstCross
      unfold wholeLineLocalLpChemotaxisWeightCross
      ring

theorem WholeLineLocalMomentNonnegativeEnergyData.signal_secondDerivative_integral
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    (∫ x : ℝ,
      (u t x) ^ (P + p.m - 1) * iteratedDeriv 2 (v t) x *
        localizingWeightAt κ x₀ x) =
      wholeLineLocalLpSignalTerm p P κ u v t x₀ -
        wholeLineLocalLpMoment (P + p.m + p.γ - 1) κ u t x₀ := by
  calc
    (∫ x : ℝ,
        (u t x) ^ (P + p.m - 1) * iteratedDeriv 2 (v t) x *
          localizingWeightAt κ x₀ x) =
        ∫ x : ℝ,
          (u t x) ^ (P + p.m - 1) * v t x *
              localizingWeightAt κ x₀ x -
            (u t x) ^ (P + p.m + p.γ - 1) *
              localizingWeightAt κ x₀ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hpde := H.solution.pde_v t x H.ht0 H.htT
      have hvxx : iteratedDeriv 2 (v t) x =
          v t x - (u t x) ^ p.γ := by
        linarith
      have hpow :
          (u t x) ^ (P + p.m - 1) * (u t x) ^ p.γ =
            (u t x) ^ (P + p.m + p.γ - 1) := by
        calc
          (u t x) ^ (P + p.m - 1) * (u t x) ^ p.γ =
              (u t x) ^ ((P + p.m - 1) + p.γ) := by
            rw [← Real.rpow_add_of_nonneg (H.u_nonnegative x)
              (by linarith [H.hP, p.hm]) (by linarith [p.hγ])]
          _ = (u t x) ^ (P + p.m + p.γ - 1) := by
            congr 1
            ring
      rw [hvxx]
      calc
        (u t x) ^ (P + p.m - 1) *
              (v t x - (u t x) ^ p.γ) * localizingWeightAt κ x₀ x =
            (u t x) ^ (P + p.m - 1) * v t x *
                localizingWeightAt κ x₀ x -
              ((u t x) ^ (P + p.m - 1) * (u t x) ^ p.γ) *
                localizingWeightAt κ x₀ x := by ring
        _ = (u t x) ^ (P + p.m - 1) * v t x *
                localizingWeightAt κ x₀ x -
              (u t x) ^ (P + p.m + p.γ - 1) *
                localizingWeightAt κ x₀ x := by
          rw [hpow]
    _ = wholeLineLocalLpSignalTerm p P κ u v t x₀ -
        wholeLineLocalLpMoment (P + p.m + p.γ - 1) κ u t x₀ := by
      rw [integral_sub H.signal_integrable H.chemotaxis_high_integrable]
      rfl

theorem WholeLineLocalMomentNonnegativeEnergyData.chemotaxis_second_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    (P + p.m - 1) *
        wholeLineLocalLpChemotaxisFirstCross p P κ u v t x₀ =
      -wholeLineLocalLpSignalTerm p P κ u v t x₀ +
        wholeLineLocalLpMoment (P + p.m + p.γ - 1) κ u t x₀ -
        wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ := by
  have hibp := H.chemotaxisSecond.integral_mul_deriv
  have hleft :
      (∫ x : ℝ,
        (u t x) ^ (P + p.m - 1) *
          (iteratedDeriv 2 (v t) x * localizingWeightAt κ x₀ x +
            deriv (v t) x * deriv (localizingWeightAt κ x₀) x)) =
        (∫ x : ℝ,
          (u t x) ^ (P + p.m - 1) * iteratedDeriv 2 (v t) x *
            localizingWeightAt κ x₀ x) +
          wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ := by
    rw [show (fun x : ℝ =>
        (u t x) ^ (P + p.m - 1) *
          (iteratedDeriv 2 (v t) x * localizingWeightAt κ x₀ x +
            deriv (v t) x * deriv (localizingWeightAt κ x₀) x)) =
        (fun x : ℝ =>
          (u t x) ^ (P + p.m - 1) * iteratedDeriv 2 (v t) x *
            localizingWeightAt κ x₀ x) +
        (fun x : ℝ =>
          (u t x) ^ (P + p.m - 1) * deriv (v t) x *
            deriv (localizingWeightAt κ x₀) x) by
      funext x
      simp only [Pi.add_apply]
      ring]
    change (∫ x : ℝ,
        (u t x) ^ (P + p.m - 1) * iteratedDeriv 2 (v t) x *
            localizingWeightAt κ x₀ x +
          (u t x) ^ (P + p.m - 1) * deriv (v t) x *
            deriv (localizingWeightAt κ x₀) x) = _
    rw [integral_add H.signal_secondDerivative_integrable
      H.signal_weightCross_integrable]
    rfl
  have hright :
      (∫ x : ℝ,
        ((P + p.m - 1) * (u t x) ^ (P + p.m - 2) *
          deriv (u t) x) *
          (deriv (v t) x * localizingWeightAt κ x₀ x)) =
        (P + p.m - 1) *
          wholeLineLocalLpChemotaxisFirstCross p P κ u v t x₀ := by
    calc
      (∫ x : ℝ,
          ((P + p.m - 1) * (u t x) ^ (P + p.m - 2) *
            deriv (u t) x) *
            (deriv (v t) x * localizingWeightAt κ x₀ x)) =
          ∫ x : ℝ, (P + p.m - 1) *
            ((u t x) ^ (P + p.m - 2) * deriv (u t) x *
              deriv (v t) x * localizingWeightAt κ x₀ x) := by
        congr 1
        funext x
        ring
      _ = (P + p.m - 1) *
          (∫ x : ℝ,
            (u t x) ^ (P + p.m - 2) * deriv (u t) x *
              deriv (v t) x * localizingWeightAt κ x₀ x) := by
        rw [integral_const_mul]
      _ = (P + p.m - 1) *
          wholeLineLocalLpChemotaxisFirstCross p P κ u v t x₀ := by
        rfl
  rw [hleft, hright] at hibp
  rw [H.signal_secondDerivative_integral] at hibp
  linarith

theorem WholeLineLocalMomentNonnegativeEnergyData.chemotaxis_identity
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    -p.χ * (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x *
          deriv (wholeLineLocalChemotaxisFlux p u v t) x) =
      -wholeLineLocalChemotaxisCoefficient p P *
          wholeLineLocalLpSignalTerm p P κ u v t x₀ +
        (p.χ * p.m / (P + p.m - 1)) *
          wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ +
        wholeLineLocalChemotaxisCoefficient p P *
          wholeLineLocalLpMoment (P + p.m + p.γ - 1) κ u t x₀ := by
  have hfirst := H.chemotaxis_first_ibp
  have hsecond := H.chemotaxis_second_ibp
  have hd : 0 < P + p.m - 1 := by linarith [H.hP, p.hm]
  have hcross :
      wholeLineLocalLpChemotaxisFirstCross p P κ u v t x₀ =
        (-wholeLineLocalLpSignalTerm p P κ u v t x₀ +
            wholeLineLocalLpMoment (P + p.m + p.γ - 1) κ u t x₀ -
            wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀) /
          (P + p.m - 1) := by
    apply (eq_div_iff hd.ne').2
    nlinarith
  rw [hfirst, hcross]
  unfold wholeLineLocalChemotaxisCoefficient
  field_simp [hd.ne']
  ring

/-! ## Testing the PDE and the exact local energy identity -/

theorem WholeLineLocalMomentNonnegativeEnergyData.energy_hasDerivAt
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    HasDerivAt
      (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀)
      (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x *
          deriv (fun r : ℝ => u r x) t) t := by
  have hmoment := (H.time.hasDerivAt H.hP).const_mul (1 / P)
  have hP0 : P ≠ 0 := ne_of_gt (lt_trans zero_lt_one H.hP)
  convert hmoment using 1
  unfold wholeLineLocalLpTest
  rw [show (∫ x : ℝ,
      ((u t x) ^ (P - 1) * localizingWeightAt κ x₀ x) *
        deriv (fun r : ℝ => u r x) t) =
      ∫ x : ℝ,
        (u t x) ^ (P - 1) * deriv (fun r : ℝ => u r x) t *
          localizingWeightAt κ x₀ x by
    congr 1
    funext x
    ring]
  field_simp [hP0]

theorem WholeLineLocalMomentNonnegativeEnergyData.tested_pde_pointwise
    {P κ T t x₀ x : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    wholeLineLocalLpTest P κ u t x₀ x *
        deriv (fun r : ℝ => u r x) t =
      wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x +
        (-p.χ) *
          (wholeLineLocalLpTest P κ u t x₀ x *
            deriv (wholeLineLocalChemotaxisFlux p u v t) x) +
        (u t x) ^ P * localizingWeightAt κ x₀ x -
        (u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x := by
  rw [H.solution.pde_u t x H.ht0 H.htT]
  have hpow₁ : (u t x) ^ (P - 1) * u t x = (u t x) ^ P := by
    calc
      (u t x) ^ (P - 1) * u t x =
          (u t x) ^ (P - 1) * (u t x) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (u t x) ^ ((P - 1) + 1) := by
        rw [← Real.rpow_add_of_nonneg (H.u_nonnegative x)
          (by linarith [H.hP]) (by norm_num)]
      _ = (u t x) ^ P := by
        congr 1
        ring
  have hpow₂ : (u t x) ^ P * (u t x) ^ p.α =
      (u t x) ^ (P + p.α) := by
    rw [← Real.rpow_add_of_nonneg (H.u_nonnegative x)
      (by linarith [H.hP]) (by linarith [p.hα])]
  unfold wholeLineLocalLpTest
  unfold wholeLineLocalChemotaxisFlux
  calc
    ((u t x) ^ (P - 1) * localizingWeightAt κ x₀ x) *
        (iteratedDeriv 2 (u t) x -
          p.χ * deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x +
          u t x * (1 - (u t x) ^ p.α)) =
      ((u t x) ^ (P - 1) * localizingWeightAt κ x₀ x) *
          iteratedDeriv 2 (u t) x +
        (-p.χ) *
          (((u t x) ^ (P - 1) * localizingWeightAt κ x₀ x) *
            deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x) +
        ((u t x) ^ (P - 1) * u t x) *
            localizingWeightAt κ x₀ x -
        (((u t x) ^ (P - 1) * u t x) * (u t x) ^ p.α) *
            localizingWeightAt κ x₀ x := by
      ring
    _ = ((u t x) ^ (P - 1) * localizingWeightAt κ x₀ x) *
          iteratedDeriv 2 (u t) x +
        (-p.χ) *
          (((u t x) ^ (P - 1) * localizingWeightAt κ x₀ x) *
            deriv (fun y => (u t y) ^ p.m * deriv (v t) y) x) +
        (u t x) ^ P * localizingWeightAt κ x₀ x -
        (u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x := by
      rw [hpow₁, hpow₂]

theorem WholeLineLocalMomentNonnegativeEnergyData.tested_pde
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    (∫ x : ℝ,
      wholeLineLocalLpTest P κ u t x₀ x *
        deriv (fun r : ℝ => u r x) t) =
      (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) -
        p.χ * (∫ x : ℝ,
          wholeLineLocalLpTest P κ u t x₀ x *
            deriv (wholeLineLocalChemotaxisFlux p u v t) x) +
        wholeLineLocalLpMoment P κ u t x₀ -
        wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
  let fDiff : ℝ → ℝ := fun x =>
    wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x
  let fChem : ℝ → ℝ := fun x =>
    wholeLineLocalLpTest P κ u t x₀ x *
      deriv (wholeLineLocalChemotaxisFlux p u v t) x
  let fMoment : ℝ → ℝ := fun x =>
    (u t x) ^ P * localizingWeightAt κ x₀ x
  let fLogistic : ℝ → ℝ := fun x =>
    (u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x
  have hchem_int : Integrable (fun x : ℝ => (-p.χ) * fChem x) :=
    H.chemotaxisFirst.left_integrable.const_mul (-p.χ)
  have hfirst_int : Integrable (fun x : ℝ => fDiff x + (-p.χ) * fChem x) :=
    H.diffusion.left_integrable.add hchem_int
  have hthree_int : Integrable
      (fun x : ℝ => fDiff x + (-p.χ) * fChem x + fMoment x) :=
    hfirst_int.add H.moment_integrable
  calc
    (∫ x : ℝ,
        wholeLineLocalLpTest P κ u t x₀ x *
          deriv (fun r : ℝ => u r x) t) =
        ∫ x : ℝ,
          fDiff x + (-p.χ) * fChem x + fMoment x - fLogistic x := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact H.tested_pde_pointwise
    _ = (∫ x : ℝ, fDiff x) + (∫ x : ℝ, (-p.χ) * fChem x) +
          (∫ x : ℝ, fMoment x) - (∫ x : ℝ, fLogistic x) := by
      rw [integral_sub hthree_int H.logistic_integrable]
      rw [integral_add hfirst_int H.moment_integrable]
      rw [integral_add H.diffusion.left_integrable hchem_int]
    _ = (∫ x : ℝ,
          wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) -
        p.χ * (∫ x : ℝ,
          wholeLineLocalLpTest P κ u t x₀ x *
            deriv (wholeLineLocalChemotaxisFlux p u v t) x) +
        wholeLineLocalLpMoment P κ u t x₀ -
        wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
      rw [integral_const_mul]
      simp only [fDiff, fChem, fMoment, fLogistic,
        wholeLineLocalLpMoment]
      ring

/-- The exact weighted local-energy identity obtained from the four whole-line
integrations by parts and the elliptic equation for `v`. -/
theorem WholeLineLocalMomentNonnegativeEnergyData.energy_identity
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpSignalTerm p P κ u v t x₀ +
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ =
      wholeLineLocalLpMoment P κ u t x₀ +
          (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ +
          (p.χ * p.m / (P + p.m - 1)) *
            wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpMoment
              (P + p.m + p.γ - 1) κ u t x₀ := by
  have htime := H.energy_hasDerivAt.deriv
  have hpde := H.tested_pde
  have hdiff := H.diffusion_identity
  have hchem := H.chemotaxis_identity
  rw [hpde, hdiff] at htime
  linarith [hchem]

/-! ## The weighted local-energy inequality -/


theorem WholeLineLocalMomentNonnegativeEnergyData.weightSecond_le
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    wholeLineLocalLpWeightSecond P κ u t x₀ ≤
      (κ + κ ^ 2) * wholeLineLocalLpMoment P κ u t x₀ := by
  have hrhs_int : Integrable (fun x : ℝ =>
      (κ + κ ^ 2) *
        ((u t x) ^ P * localizingWeightAt κ x₀ x)) :=
    H.moment_integrable.const_mul (κ + κ ^ 2)
  have hmono :
      (∫ x : ℝ,
        (u t x) ^ P * iteratedDeriv 2 (localizingWeightAt κ x₀) x) ≤
        ∫ x : ℝ,
          (κ + κ ^ 2) *
            ((u t x) ^ P * localizingWeightAt κ x₀ x) := by
    apply integral_mono_ae H.weightSecond_integrable hrhs_int
    filter_upwards [] with x
    have huP : 0 ≤ (u t x) ^ P := Real.rpow_nonneg (H.u_nonnegative x) P
    calc
      (u t x) ^ P * iteratedDeriv 2 (localizingWeightAt κ x₀) x ≤
          (u t x) ^ P *
            |iteratedDeriv 2 (localizingWeightAt κ x₀) x| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) huP
      _ ≤ (u t x) ^ P *
          ((κ + κ ^ 2) * localizingWeightAt κ x₀ x) :=
        mul_le_mul_of_nonneg_left
          (abs_iteratedDeriv_two_localizingWeightAt_le H.hκ.le x₀ x) huP
      _ = (κ + κ ^ 2) *
          ((u t x) ^ P * localizingWeightAt κ x₀ x) := by ring
  calc
    wholeLineLocalLpWeightSecond P κ u t x₀ =
        ∫ x : ℝ,
          (u t x) ^ P * iteratedDeriv 2 (localizingWeightAt κ x₀) x := rfl
    _ ≤ ∫ x : ℝ,
        (κ + κ ^ 2) *
          ((u t x) ^ P * localizingWeightAt κ x₀ x) := hmono
    _ = (κ + κ ^ 2) * wholeLineLocalLpMoment P κ u t x₀ := by
      rw [integral_const_mul]
      rfl

theorem WholeLineLocalMomentNonnegativeEnergyData.signalWeightCross_le
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v) :
    wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ ≤
      κ * wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ := by
  have hrhs_int : Integrable (fun x : ℝ =>
      κ * ((u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
        localizingWeightAt κ x₀ x)) :=
    H.signal_gradient_abs_integrable.const_mul κ
  have hmono :
      (∫ x : ℝ,
        (u t x) ^ (P + p.m - 1) * deriv (v t) x *
          deriv (localizingWeightAt κ x₀) x) ≤
        ∫ x : ℝ,
          κ * ((u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
            localizingWeightAt κ x₀ x) := by
    apply integral_mono_ae H.signal_weightCross_integrable hrhs_int
    filter_upwards [] with x
    have huPow : 0 ≤ (u t x) ^ (P + p.m - 1) :=
      Real.rpow_nonneg (H.u_nonnegative x) _
    have hvWeight :
        |deriv (v t) x| * |deriv (localizingWeightAt κ x₀) x| ≤
          |deriv (v t) x| * (κ * localizingWeightAt κ x₀ x) :=
      mul_le_mul_of_nonneg_left
        (abs_deriv_localizingWeightAt_le H.hκ.le x₀ x) (abs_nonneg _)
    calc
      (u t x) ^ (P + p.m - 1) * deriv (v t) x *
          deriv (localizingWeightAt κ x₀) x =
          (u t x) ^ (P + p.m - 1) *
            (deriv (v t) x * deriv (localizingWeightAt κ x₀) x) := by ring
      _ ≤ (u t x) ^ (P + p.m - 1) *
          |deriv (v t) x * deriv (localizingWeightAt κ x₀) x| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) huPow
      _ = (u t x) ^ (P + p.m - 1) *
          (|deriv (v t) x| * |deriv (localizingWeightAt κ x₀) x|) := by
        rw [abs_mul]
      _ ≤ (u t x) ^ (P + p.m - 1) *
          (|deriv (v t) x| * (κ * localizingWeightAt κ x₀ x)) :=
        mul_le_mul_of_nonneg_left hvWeight huPow
      _ = κ * ((u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
          localizingWeightAt κ x₀ x) := by ring
  calc
    wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ =
        ∫ x : ℝ,
          (u t x) ^ (P + p.m - 1) * deriv (v t) x *
            deriv (localizingWeightAt κ x₀) x := rfl
    _ ≤ ∫ x : ℝ,
        κ * ((u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
          localizingWeightAt κ x₀ x) := hmono
    _ = κ * wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ := by
      rw [integral_const_mul]
      rfl

theorem WholeLineLocalMomentNonnegativeEnergyData.signalTerm_nonneg
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hv_nonneg : ∀ x, 0 ≤ v t x) :
    0 ≤ wholeLineLocalLpSignalTerm p P κ u v t x₀ := by
  unfold wholeLineLocalLpSignalTerm
  exact integral_nonneg fun x =>
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (H.u_nonnegative x) _) (hv_nonneg x))
      (localizingWeightAt_pos κ x₀ x).le

/-- Paper-style local weighted energy inequality.  The two weight-derivative
terms are bounded using `|ψₓ| ≤ κψ` and `|ψₓₓ| ≤ (κ+κ²)ψ`. -/
theorem WholeLineLocalMomentNonnegativeEnergyData.energy_inequality
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpSignalTerm p P κ u v t x₀ +
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      (1 + (κ + κ ^ 2) / P) *
          wholeLineLocalLpMoment P κ u t x₀ +
        (p.χ * p.m * κ / (P + p.m - 1)) *
          wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ +
        wholeLineLocalChemotaxisCoefficient p P *
          wholeLineLocalLpMoment
            (P + p.m + p.γ - 1) κ u t x₀ := by
  have hPpos : 0 < P := lt_trans zero_lt_one H.hP
  have hd : 0 < P + p.m - 1 := by linarith [H.hP, p.hm]
  have hweight := H.weightSecond_le
  have hdrift := H.signalWeightCross_le
  have hweight_scaled :
      (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ ≤
        (1 / P) * ((κ + κ ^ 2) *
          wholeLineLocalLpMoment P κ u t x₀) :=
    mul_le_mul_of_nonneg_left hweight (one_div_nonneg.mpr hPpos.le)
  have hb : 0 ≤ p.χ * p.m / (P + p.m - 1) :=
    div_nonneg (mul_nonneg hχ (le_trans zero_le_one p.hm)) hd.le
  have hdrift_scaled :
      (p.χ * p.m / (P + p.m - 1)) *
          wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ ≤
        (p.χ * p.m / (P + p.m - 1)) *
          (κ * wholeLineLocalLpSignalGradientAbs p P κ u v t x₀) :=
    mul_le_mul_of_nonneg_left hdrift hb
  calc
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpSignalTerm p P κ u v t x₀ +
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ =
        wholeLineLocalLpMoment P κ u t x₀ +
          (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ +
          (p.χ * p.m / (P + p.m - 1)) *
            wholeLineLocalLpChemotaxisWeightCross p P κ u v t x₀ +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpMoment
              (P + p.m + p.γ - 1) κ u t x₀ := H.energy_identity
    _ ≤ wholeLineLocalLpMoment P κ u t x₀ +
          (1 / P) * ((κ + κ ^ 2) *
            wholeLineLocalLpMoment P κ u t x₀) +
          (p.χ * p.m / (P + p.m - 1)) *
            (κ * wholeLineLocalLpSignalGradientAbs p P κ u v t x₀) +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpMoment
              (P + p.m + p.γ - 1) κ u t x₀ := by
      linarith
    _ = (1 + (κ + κ ^ 2) / P) *
          wholeLineLocalLpMoment P κ u t x₀ +
        (p.χ * p.m * κ / (P + p.m - 1)) *
          wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ +
        wholeLineLocalChemotaxisCoefficient p P *
          wholeLineLocalLpMoment
            (P + p.m + p.γ - 1) κ u t x₀ := by
      field_simp [ne_of_gt hPpos, ne_of_gt hd]

/-- At the critical exponent, admissibility leaves the positive high-power
coefficient `1 - χ(P-1)/(P+m-1)`. -/
theorem WholeLineLocalMomentNonnegativeEnergyData.critical_energy_inequality
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          wholeLineLocalChemotaxisCoefficient p P *
            wholeLineLocalLpSignalTerm p P κ u v t x₀ +
          (1 - wholeLineLocalChemotaxisCoefficient p P) *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      (1 + (κ + κ ^ 2) / P) *
          wholeLineLocalLpMoment P κ u t x₀ +
        (p.χ * p.m * κ / (P + p.m - 1)) *
          wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ := by
  have hineq := H.energy_inequality hχ
  have hexp : P + p.m + p.γ - 1 = P + p.α := by
    rw [hcritical]
    ring
  rw [hexp] at hineq
  linarith

theorem WholeLineLocalMomentNonnegativeEnergyData.critical_energy_inequality_drop_signal
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ) (hcritical : p.α = p.m + p.γ - 1)
    (hv_nonneg : ∀ x, 0 ≤ v t x) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          (1 - wholeLineLocalChemotaxisCoefficient p P) *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      (1 + (κ + κ ^ 2) / P) *
          wholeLineLocalLpMoment P κ u t x₀ +
        (p.χ * p.m * κ / (P + p.m - 1)) *
          wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ := by
  have hineq := H.critical_energy_inequality hχ hcritical
  have hcoeff := wholeLineLocalChemotaxisCoefficient_nonneg p hχ H.hP
  have hsignal := H.signalTerm_nonneg hv_nonneg
  nlinarith


theorem WholeLineLocalMomentNonnegativeEnergyData.resolverGradient_estimate
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    Integrable (fun x : ℝ =>
        |deriv (v t) x| ^ (wholeLineLocalResolverExponent p P) *
          localizingWeightAt κ x₀ x) ∧
      (∫ x : ℝ,
          |deriv (v t) x| ^ (wholeLineLocalResolverExponent p P) *
            localizingWeightAt κ x₀ x) ≤
        wholeLineLocalResolverConstant p P *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
  let q : ℝ := wholeLineLocalResolverExponent p P
  let psi : ExponentialWeight :=
    localizingWeightAtExponentialWeight κ x₀ H.hκ
  have hq : 1 ≤ q :=
    (wholeLineLocalResolverExponent_gt_one p H.hP hcritical).le
  have hγq : p.γ * q = P + p.α := by
    dsimp [q, wholeLineLocalResolverExponent]
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one p.hγ)]
  have hint : Integrable (fun x : ℝ =>
      (u t x) ^ (p.γ * q) * psi.weight x) := by
    simpa only [hγq, psi, localizingWeightAtExponentialWeight] using
      H.logistic_integrable
  obtain ⟨hgrad_int, hgrad_le⟩ :=
    Lemma_2_5_with_explicit_k_original_power psi one_pos one_pos hq
      (lt_of_lt_of_le zero_lt_one p.hγ) H.hκ.le
      (by
        rw [Real.sqrt_one]
        linarith)
      (by
        intro z
        exact abs_deriv_localizingWeightAt_le H.hκ.le x₀ z)
      hu hu_nonneg hint
  have hvfun : v t = fun z => Psi (fun y => (u t y) ^ p.γ) 1 1 z := by
    simpa only [frozenElliptic] using hv_resolver
  have hconstant := wholeLineLocalExplicitResolverConstant_le
    (p := p) (P := P) H.hκ hκhalf
  have hhigh_nonneg :
      0 ≤ wholeLineLocalLpMoment (P + p.α) κ u t x₀ :=
    wholeLineLocalLpMoment_nonneg hu_nonneg
  have hrhs_eq :
      (∫ x : ℝ, (u t x) ^ (p.γ * q) * psi.weight x) =
        wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
    simp only [hγq, psi, localizingWeightAtExponentialWeight]
    rfl
  rw [hrhs_eq] at hgrad_le
  rw [hvfun]
  change Integrable (fun x : ℝ =>
      |deriv (fun z => Psi (fun y => (u t y) ^ p.γ) 1 1 z) x| ^ q *
        psi.weight x) ∧
    (∫ x : ℝ,
      |deriv (fun z => Psi (fun y => (u t y) ^ p.γ) 1 1 z) x| ^ q *
        psi.weight x) ≤
      wholeLineLocalResolverConstant p P *
        wholeLineLocalLpMoment (P + p.α) κ u t x₀
  refine ⟨hgrad_int, hgrad_le.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hconstant hhigh_nonneg

/-- Young's inequality followed by Lemma 2.5 bounds the remaining mixed
signal-gradient moment by the critical high-power moment. -/
theorem WholeLineLocalMomentNonnegativeEnergyData.signalGradientAbs_le_high
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
      wholeLineLocalSignalAbsorptionConstant p P *
        wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
  let q : ℝ := wholeLineLocalResolverExponent p P
  let CY : ℝ := wholeLineLocalYoungConstant p P
  obtain ⟨hgrad_int, hgrad_le⟩ :=
    H.resolverGradient_estimate hκhalf hcritical hu hu_nonneg hv_resolver
  have hCY : 0 ≤ CY :=
    (wholeLineLocalYoungConstant_pos p H.hP hcritical).le
  have hgrad_le' :
      (∫ x : ℝ, |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) ≤
        wholeLineLocalResolverConstant p P *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
    simpa only [q] using hgrad_le
  have hhigh_scaled : Integrable (fun x : ℝ =>
      (1 / 4 : ℝ) *
        ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x)) :=
    H.logistic_integrable.const_mul (1 / 4)
  have hgrad_scaled : Integrable (fun x : ℝ =>
      CY * (|deriv (v t) x| ^ q * localizingWeightAt κ x₀ x)) :=
    hgrad_int.const_mul CY
  have hpoint : ∀ x : ℝ,
      (u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
          localizingWeightAt κ x₀ x ≤
        (1 / 4 : ℝ) *
            ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
          CY * (|deriv (v t) x| ^ q *
            localizingWeightAt κ x₀ x) := by
    intro x
    have hy := critical_local_signal_scaled_young p H.hP hcritical
      (hu_nonneg x) (abs_nonneg (deriv (v t) x))
    change
      (u t x) ^ (P + p.m - 1) * |deriv (v t) x| ≤
        (1 / 4 : ℝ) * (u t x) ^ (P + p.α) +
          CY * |deriv (v t) x| ^ q at hy
    have hw : 0 ≤ localizingWeightAt κ x₀ x :=
      (localizingWeightAt_pos κ x₀ x).le
    have := mul_le_mul_of_nonneg_right hy hw
    nlinarith
  have hintegral :
      wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
        (1 / 4 : ℝ) * wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (∫ x : ℝ,
            |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) := by
    unfold wholeLineLocalLpSignalGradientAbs
    calc
      (∫ x : ℝ, (u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
          localizingWeightAt κ x₀ x) ≤
          ∫ x : ℝ,
            (1 / 4 : ℝ) *
                ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
              CY * (|deriv (v t) x| ^ q *
                localizingWeightAt κ x₀ x) := by
        exact integral_mono H.signal_gradient_abs_integrable
          (hhigh_scaled.add hgrad_scaled) hpoint
      _ = (1 / 4 : ℝ) *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (∫ x : ℝ,
            |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) := by
        rw [integral_add hhigh_scaled hgrad_scaled,
          integral_const_mul, integral_const_mul]
        rfl
  calc
    wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
        (1 / 4 : ℝ) * wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (∫ x : ℝ,
            |deriv (v t) x| ^ q * localizingWeightAt κ x₀ x) := hintegral
    _ ≤ (1 / 4 : ℝ) * wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
          CY * (wholeLineLocalResolverConstant p P *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hgrad_le' hCY)
    _ = wholeLineLocalSignalAbsorptionConstant p P *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ := by
      unfold wholeLineLocalSignalAbsorptionConstant CY
      ring

/-! ## Absorbed critical energy inequality -/


theorem WholeLineLocalMomentNonnegativeEnergyData.critical_energy_absorbed
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          (4 * (P - 1) / P ^ 2) *
            wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
          wholeLineLocalMomentAbsorption p P κ *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      wholeLineLocalMomentLinearCoefficient P κ *
        wholeLineLocalLpMoment P κ u t x₀ := by
  have hv_nonneg : ∀ x, 0 ≤ v t x := by
    intro x
    rw [hv_resolver]
    exact frozenElliptic_nonneg p hu_nonneg x
  have henergy := H.critical_energy_inequality_drop_signal
    hχ hcritical hv_nonneg
  have hsignal := H.signalGradientAbs_le_high hκhalf hcritical
    hu hu_nonneg hv_resolver
  have hd : 0 < P + p.m - 1 := by linarith [H.hP, p.hm]
  have hmix :
      (p.χ * p.m * κ / (P + p.m - 1)) *
          wholeLineLocalLpSignalGradientAbs p P κ u v t x₀ ≤
        (p.χ * p.m * κ / (P + p.m - 1)) *
          (wholeLineLocalSignalAbsorptionConstant p P *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀) := by
    exact mul_le_mul_of_nonneg_left hsignal
      (div_nonneg (mul_nonneg (mul_nonneg hχ (le_trans zero_le_one p.hm))
        H.hκ.le) hd.le)
  unfold wholeLineLocalMomentAbsorption
  unfold wholeLineLocalMomentLinearCoefficient
  linarith


theorem WholeLineLocalMomentNonnegativeEnergyData.critical_energy_absorbed_drop_gradient
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
          wholeLineLocalMomentAbsorption p P κ *
            wholeLineLocalLpMoment (P + p.α) κ u t x₀ ≤
      wholeLineLocalMomentLinearCoefficient P κ *
        wholeLineLocalLpMoment P κ u t x₀ := by
  have hmain := H.critical_energy_absorbed hχ hκhalf hcritical
    hu hu_nonneg hv_resolver
  have hcoef : 0 ≤ 4 * (P - 1) / P ^ 2 := by
    exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr H.hP.le))
      (sq_nonneg P)
  have hgrad := wholeLineLocalLpHalfPowerGradient_nonneg
    (P := P) (κ := κ) (t := t) (x₀ := x₀) (u := u)
  nlinarith

/-! ## Lower-order power absorption and scalar damping -/


theorem WholeLineLocalMomentNonnegativeEnergyData.lowerOrder_integral_absorption
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (habsorb : 0 < wholeLineLocalMomentAbsorption p P κ)
    (hu_nonneg : ∀ x, 0 ≤ u t x) :
    wholeLineLocalMomentYoungCoefficient p P κ *
        wholeLineLocalLpMoment P κ u t x₀ ≤
      wholeLineLocalMomentAbsorption p P κ *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
        wholeLineLocalMomentYoungRemainder p P κ *
          ∫ x : ℝ, localizingWeightAt κ x₀ x := by
  let A := wholeLineLocalMomentYoungCoefficient p P κ
  let delta := wholeLineLocalMomentAbsorption p P κ
  let B := wholeLineLocalMomentYoungRemainder p P κ
  have hleft : Integrable (fun x : ℝ =>
      A * ((u t x) ^ P * localizingWeightAt κ x₀ x)) :=
    H.moment_integrable.const_mul A
  have hhigh : Integrable (fun x : ℝ =>
      delta * ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x)) :=
    H.logistic_integrable.const_mul delta
  have hconst : Integrable (fun x : ℝ =>
      B * localizingWeightAt κ x₀ x) :=
    (localizingWeightAt_integrable H.hκ x₀).const_mul B
  have hpoint : ∀ x : ℝ,
      A * ((u t x) ^ P * localizingWeightAt κ x₀ x) ≤
        delta * ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
          B * localizingWeightAt κ x₀ x := by
    intro x
    have hy := wholeLineLocalMoment_lowerOrder_pointwise p H.hP H.hκ
      habsorb (hu_nonneg x)
    have hw := (localizingWeightAt_pos κ x₀ x).le
    have := mul_le_mul_of_nonneg_right hy hw
    dsimp [A, delta, B]
    nlinarith
  calc
    wholeLineLocalMomentYoungCoefficient p P κ *
        wholeLineLocalLpMoment P κ u t x₀ =
      ∫ x : ℝ, A *
        ((u t x) ^ P * localizingWeightAt κ x₀ x) := by
        rw [integral_const_mul]
        rfl
    _ ≤ ∫ x : ℝ,
        delta * ((u t x) ^ (P + p.α) * localizingWeightAt κ x₀ x) +
          B * localizingWeightAt κ x₀ x :=
      integral_mono hleft (hhigh.add hconst) hpoint
    _ = wholeLineLocalMomentAbsorption p P κ *
          wholeLineLocalLpMoment (P + p.α) κ u t x₀ +
        wholeLineLocalMomentYoungRemainder p P κ *
          ∫ x : ℝ, localizingWeightAt κ x₀ x := by
      rw [integral_add hhigh hconst, integral_const_mul,
        integral_const_mul]
      rfl

theorem WholeLineLocalMomentNonnegativeEnergyData.critical_energy_damping
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentNonnegativeEnergyData p P κ T t x₀ u v)
    (hχ : 0 ≤ p.χ)
    (hκhalf : κ < 1 / 2)
    (hcritical : p.α = p.m + p.γ - 1)
    (habsorb : 0 < wholeLineLocalMomentAbsorption p P κ)
    (hu : IsCUnifBdd (u t))
    (hu_nonneg : ∀ x, 0 ≤ u t x)
    (hv_resolver : v t = frozenElliptic p (u t)) :
    deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
        wholeLineLocalLpEnergy P κ u t x₀ ≤
      wholeLineLocalMomentDampingRhs p P κ := by
  have henergy := H.critical_energy_absorbed_drop_gradient
    hχ hκhalf hcritical hu hu_nonneg hv_resolver
  have hyoung := H.lowerOrder_integral_absorption habsorb hu_nonneg
  have hP0 : 0 < P := lt_trans zero_lt_one H.hP
  have hB : 0 ≤ wholeLineLocalMomentYoungRemainder p P κ :=
    (wholeLineLocalMomentYoungRemainder_pos p H.hP H.hκ habsorb).le
  have hweight := integral_localizingWeightAt_le_two_div H.hκ x₀
  have hweight_scaled :
      wholeLineLocalMomentYoungRemainder p P κ *
          (∫ x : ℝ, localizingWeightAt κ x₀ x) ≤
        wholeLineLocalMomentYoungRemainder p P κ * (2 / κ) :=
    mul_le_mul_of_nonneg_left hweight hB
  change deriv (fun s : ℝ => wholeLineLocalLpEnergy P κ u s x₀) t +
      (1 / P) * wholeLineLocalLpMoment P κ u t x₀ ≤
        wholeLineLocalMomentDampingRhs p P κ
  unfold wholeLineLocalMomentYoungCoefficient at hyoung
  unfold wholeLineLocalMomentDampingRhs
  nlinarith


section AxiomAudit

#print axioms WholeLineLocalMomentNonnegativeEnergyData.energy_identity
#print axioms WholeLineLocalMomentNonnegativeEnergyData.critical_energy_damping

end AxiomAudit

end ShenWork.Paper1

