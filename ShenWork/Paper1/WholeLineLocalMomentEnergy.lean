import ShenWork.Paper1.WholeLineLocalMoment
import ShenWork.Paper1.Proposition11PositiveErrata
import ShenWork.PaperOne.WholeLineDiffusionIBPDecay
import ShenWork.PaperOne.WholeLineChemotaxisIBP
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The weighted local-moment energy identity on the whole line

This file formalizes the calculation on pp. 17--18 of Paper 1.  At a fixed
time, the parabolic equation is tested against `u^(P-1) ψ`; the chemotaxis
term is integrated by parts a second time and `vₓₓ = v - u^γ` is substituted.

`IsClassicalSolution` records the pointwise PDE but does not itself contain
the global integrability, decay, second-spatial-derivative, or dominated
time-differentiation facts needed for a whole-line energy calculation.  The
structure below therefore exposes those analytic hypotheses explicitly.  Its
fields are primitive regularity/integrability/decay statements, not the IBP
identities proved from them in this file.
-/

open Filter MeasureTheory Real Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper1

/-! ## Exponent and energy densities -/

/-- The admissible exponent supplied by the faithful critical threshold. -/
theorem exists_paper1PositiveCritical_admissibleExponent
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hthreshold : paper1PositiveCriticalThreshold p) :
    ∃ P : ℝ, max 1 (max p.m p.γ) < P ∧ P < p.m + p.γ ∧
      p.χ * (P - 1) < P + p.m - 1 :=
  (paper1PositiveCriticalThreshold_iff_exists_admissible_exponent p hχ).mp
    hthreshold

/-- The coefficient of the top chemotaxis power after the second IBP. -/
def wholeLineLocalChemotaxisCoefficient (p : CMParams) (P : ℝ) : ℝ :=
  p.χ * (P - 1) / (P + p.m - 1)

theorem wholeLineLocalChemotaxisCoefficient_lt_one
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hadm : p.χ * (P - 1) < P + p.m - 1) :
    wholeLineLocalChemotaxisCoefficient p P < 1 := by
  unfold wholeLineLocalChemotaxisCoefficient
  rw [div_lt_one (by linarith [p.hm] : 0 < P + p.m - 1)]
  exact hadm

/-- The test function `u^(P-1) ψ`. -/
def wholeLineLocalLpTest
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ x : ℝ) : ℝ :=
  (u t x) ^ (P - 1) * localizingWeightAt κ x₀ x

/-- Its displayed spatial derivative. -/
def wholeLineLocalLpTestDeriv
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ x : ℝ) : ℝ :=
  (P - 1) * (u t x) ^ (P - 2) * deriv (u t) x *
      localizingWeightAt κ x₀ x +
    (u t x) ^ (P - 1) * deriv (localizingWeightAt κ x₀) x

/-- The physical chemotaxis flux `u^m vₓ` at a fixed time. -/
def wholeLineLocalChemotaxisFlux
    (p : CMParams) (u v : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  (u t x) ^ p.m * deriv (v t) x

/-- The diffusion dissipation in the form printed in (3.5). -/
def wholeLineLocalLpDiffusionDissipation
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ (P - 2) * (deriv (u t) x) ^ 2 *
    localizingWeightAt κ x₀ x

/-- The same dissipation written as the gradient of `u^(P/2)`. -/
def wholeLineLocalLpHalfPowerGradient
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (deriv (fun y : ℝ => (u t y) ^ (P / 2)) x) ^ 2 *
    localizingWeightAt κ x₀ x

/-- The weight-derivative cross term left by diffusion IBP. -/
def wholeLineLocalLpDiffusionWeightCross
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ (P - 1) * deriv (u t) x *
    deriv (localizingWeightAt κ x₀) x

/-- The first chemotaxis cross term after moving the flux divergence. -/
def wholeLineLocalLpChemotaxisFirstCross
    (p : CMParams) (P κ : ℝ) (u v : ℝ → ℝ → ℝ)
    (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ (P + p.m - 2) * deriv (u t) x *
    deriv (v t) x * localizingWeightAt κ x₀ x

/-- The `vₓ ψₓ` term after the second chemotaxis IBP. -/
def wholeLineLocalLpChemotaxisWeightCross
    (p : CMParams) (P κ : ℝ) (u v : ℝ → ℝ → ℝ)
    (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ (P + p.m - 1) * deriv (v t) x *
    deriv (localizingWeightAt κ x₀) x

/-- The nonnegative signal term discarded in the upper energy inequality. -/
def wholeLineLocalLpSignalTerm
    (p : CMParams) (P κ : ℝ) (u v : ℝ → ℝ → ℝ)
    (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ (P + p.m - 1) * v t x *
    localizingWeightAt κ x₀ x

/-- The absolute-gradient moment used to dominate `vₓ ψₓ`. -/
def wholeLineLocalLpSignalGradientAbs
    (p : CMParams) (P κ : ℝ) (u v : ℝ → ℝ → ℝ)
    (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ (P + p.m - 1) * |deriv (v t) x| *
    localizingWeightAt κ x₀ x

/-- Time derivative density of `u^P ψ`. -/
def wholeLineLocalLpMomentTimeDensity
    (P κ : ℝ) (u u_t : ℝ → ℝ → ℝ) (t x₀ x : ℝ) : ℝ :=
  P * (u t x) ^ (P - 1) * u_t t x * localizingWeightAt κ x₀ x

/-! ## Pointwise derivative formulas -/

theorem hasDerivAt_wholeLineLocalLpTest
    {P κ t x₀ x : ℝ} {u : ℝ → ℝ → ℝ}
    (hu_pos : 0 < u t x)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    HasDerivAt (wholeLineLocalLpTest P κ u t x₀)
      (wholeLineLocalLpTestDeriv P κ u t x₀ x) x := by
  have hpow := hu.rpow_const (p := P - 1) (Or.inl hu_pos.ne')
  have hw := hasDerivAt_localizingWeightAt κ x₀ x
  have hprod := hpow.mul hw
  convert hprod using 1
  unfold wholeLineLocalLpTestDeriv
  rw [deriv_localizingWeightAt,
    show P - 1 - 1 = P - 2 by ring]
  ring

theorem hasDerivAt_wholeLineLocalChemotaxisFlux
    {p : CMParams} {t x : ℝ} {u v : ℝ → ℝ → ℝ}
    (hu_pos : 0 < u t x)
    (hu : HasDerivAt (u t) (deriv (u t) x) x)
    (hv₂ : HasDerivAt (deriv (v t)) (iteratedDeriv 2 (v t) x) x) :
    HasDerivAt (wholeLineLocalChemotaxisFlux p u v t)
      (deriv (wholeLineLocalChemotaxisFlux p u v t) x) x := by
  have hpow := hu.rpow_const (p := p.m) (Or.inl hu_pos.ne')
  have hprod := hpow.mul hv₂
  have hprod' : HasDerivAt (wholeLineLocalChemotaxisFlux p u v t)
      (deriv (u t) x * p.m * (u t x) ^ (p.m - 1) * deriv (v t) x +
        (u t x) ^ p.m * iteratedDeriv 2 (v t) x) x := by
    simpa [wholeLineLocalChemotaxisFlux, Pi.mul_apply] using hprod
  exact hprod'.congr_deriv hprod'.deriv.symm

theorem hasDerivAt_wholeLineLocalChemotaxisPower
    {p : CMParams} {P t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hu_pos : 0 < u t x)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    HasDerivAt (fun y : ℝ => (u t y) ^ (P + p.m - 1))
      ((P + p.m - 1) * (u t x) ^ (P + p.m - 2) *
        deriv (u t) x) x := by
  have hpow := hu.rpow_const (p := P + p.m - 1) (Or.inl hu_pos.ne')
  convert hpow using 1
  ring

theorem hasDerivAt_signalGradient_mul_localizingWeightAt
    {κ t x₀ x : ℝ} {v : ℝ → ℝ → ℝ}
    (hv₂ : HasDerivAt (deriv (v t)) (iteratedDeriv 2 (v t) x) x) :
    HasDerivAt
      (fun y : ℝ => deriv (v t) y * localizingWeightAt κ x₀ y)
      (iteratedDeriv 2 (v t) x * localizingWeightAt κ x₀ x +
        deriv (v t) x * deriv (localizingWeightAt κ x₀) x) x := by
  have hprod := hv₂.mul (hasDerivAt_localizingWeightAt κ x₀ x)
  convert hprod using 1
  rw [deriv_localizingWeightAt]

/-! ## Dominated time differentiation and raw whole-line IBP data -/

/-- Differentiation in time of a translated weighted local moment, under an
explicit local dominated-differentiation package. -/
theorem wholeLineLocalLpMoment_hasDerivAt_of_dominated
    {P κ t x₀ δ : ℝ} {u u_t : ℝ → ℝ → ℝ} {bound : ℝ → ℝ}
    (hP : 1 < P)
    (hδ : 0 < δ)
    (hF_meas :
      ∀ᶠ s in 𝓝 t,
        AEStronglyMeasurable
          (fun x : ℝ =>
            (u s x) ^ P * localizingWeightAt κ x₀ x) volume)
    (hF_int :
      Integrable
        (fun x : ℝ =>
          (u t x) ^ P * localizingWeightAt κ x₀ x) volume)
    (hF'_meas :
      AEStronglyMeasurable
        (fun x : ℝ =>
          P * ((u t x) ^ (P - 1) * u_t t x *
            localizingWeightAt κ x₀ x)) volume)
    (h_bound :
      ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t δ,
        ‖P * ((u s x) ^ (P - 1) * u_t s x *
          localizingWeightAt κ x₀ x)‖ ≤ bound x)
    (hbound_int : Integrable bound volume)
    (hu_hasDeriv :
      ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t δ,
        HasDerivAt (fun r : ℝ => u r x) (u_t s x) s) :
    HasDerivAt
      (fun s : ℝ => wholeLineLocalLpMoment P κ u s x₀)
      (P * ∫ x : ℝ,
        (u t x) ^ (P - 1) * u_t t x *
          localizingWeightAt κ x₀ x) t := by
  let F : ℝ → ℝ → ℝ := fun s x =>
    (u s x) ^ P * localizingWeightAt κ x₀ x
  let F' : ℝ → ℝ → ℝ := fun s x =>
    P * ((u s x) ^ (P - 1) * u_t s x *
      localizingWeightAt κ x₀ x)
  have h_diff :
      ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t δ,
        HasDerivAt (fun r : ℝ => F r x) (F' s x) s := by
    filter_upwards [hu_hasDeriv] with x hx_deriv s hs
    have hrpow :=
      (hx_deriv s hs).rpow_const (p := P) (Or.inr hP.le)
    have hmul := hrpow.mul_const (localizingWeightAt κ x₀ x)
    convert hmul using 1
    simp only [F']
    ring
  have hmain :
      HasDerivAt
        (fun s : ℝ => ∫ x : ℝ, F s x)
        (∫ x : ℝ, F' t x) t :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (bound := bound) (F := F) (F' := F')
      (x₀ := t) (s := Metric.ball t δ)
      (Metric.ball_mem_nhds t hδ) hF_meas hF_int hF'_meas
      h_bound hbound_int h_diff).2
  have hderiv :
      (∫ x : ℝ, F' t x) =
        P * ∫ x : ℝ,
          (u t x) ^ (P - 1) * u_t t x *
            localizingWeightAt κ x₀ x := by
    simp only [F']
    rw [integral_const_mul]
  rw [hderiv] at hmain
  simpa only [F, wholeLineLocalLpMoment] using hmain

/-- Primitive hypotheses for differentiating a local moment in time. -/
structure WholeLineLocalMomentTimeData
    (P κ t x₀ : ℝ) (u u_t : ℝ → ℝ → ℝ) where
  δ : ℝ
  bound : ℝ → ℝ
  hδ : 0 < δ
  integrand_aeStronglyMeasurable :
    ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable
        (fun x : ℝ =>
          (u s x) ^ P * localizingWeightAt κ x₀ x) volume
  integrand_integrable :
    Integrable
      (fun x : ℝ =>
        (u t x) ^ P * localizingWeightAt κ x₀ x) volume
  derivative_aeStronglyMeasurable :
    AEStronglyMeasurable
      (fun x : ℝ =>
        P * ((u t x) ^ (P - 1) * u_t t x *
          localizingWeightAt κ x₀ x)) volume
  derivative_bound :
    ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t δ,
      ‖P * ((u s x) ^ (P - 1) * u_t s x *
        localizingWeightAt κ x₀ x)‖ ≤ bound x
  bound_integrable : Integrable bound volume
  hasDerivAt_u :
    ∀ᵐ x ∂volume, ∀ s ∈ Metric.ball t δ,
      HasDerivAt (fun r : ℝ => u r x) (u_t s x) s

theorem WholeLineLocalMomentTimeData.hasDerivAt
    {P κ t x₀ : ℝ} {u u_t : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentTimeData P κ t x₀ u u_t)
    (hP : 1 < P) :
    HasDerivAt
      (fun s : ℝ => wholeLineLocalLpMoment P κ u s x₀)
      (P * ∫ x : ℝ,
        (u t x) ^ (P - 1) * u_t t x *
          localizingWeightAt κ x₀ x) t :=
  wholeLineLocalLpMoment_hasDerivAt_of_dominated hP H.hδ
    H.integrand_aeStronglyMeasurable H.integrand_integrable
    H.derivative_aeStronglyMeasurable H.derivative_bound
    H.bound_integrable H.hasDerivAt_u

/-- The raw hypotheses of one whole-line integration by parts.  This packages
only derivative, integrability, and boundary-decay data, not its conclusion. -/
structure WholeLineIBPData (f fx g gx : ℝ → ℝ) : Prop where
  hasDerivAt_left : ∀ x ∈ tsupport g, HasDerivAt f (fx x) x
  hasDerivAt_right : ∀ x ∈ tsupport f, HasDerivAt g (gx x) x
  left_integrable : Integrable (fun x : ℝ => f x * gx x)
  right_integrable : Integrable (fun x : ℝ => fx x * g x)
  decay_atBot : Tendsto (fun x : ℝ => f x * g x) atBot (𝓝 0)
  decay_atTop : Tendsto (fun x : ℝ => f x * g x) atTop (𝓝 0)

theorem WholeLineIBPData.integral_mul_deriv
    {f fx g gx : ℝ → ℝ} (H : WholeLineIBPData f fx g gx) :
    (∫ x : ℝ, f x * gx x) = -∫ x : ℝ, fx x * g x :=
  ShenWork.PaperOne.wholeLine_chemotaxis_postIBP_with_derivatives
    f fx g gx H.hasDerivAt_left H.hasDerivAt_right
    H.left_integrable H.right_integrable H.decay_atBot H.decay_atTop

/-! ## The fixed-time energy package -/

/-- The normalized local energy `(1/P) ∫ u^P ψ`. -/
def wholeLineLocalLpEnergy
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ : ℝ) : ℝ :=
  (1 / P) * wholeLineLocalLpMoment P κ u t x₀

/-- The term `(1/P) ∫ u^P ψₓₓ` obtained by integrating the diffusion
weight-cross term once more. -/
def wholeLineLocalLpWeightSecond
    (P κ : ℝ) (u : ℝ → ℝ → ℝ) (t x₀ : ℝ) : ℝ :=
  ∫ x : ℝ, (u t x) ^ P *
    iteratedDeriv 2 (localizingWeightAt κ x₀) x

/-- Raw fixed-time analytic data needed for the two diffusion and two
chemotaxis integrations by parts. -/
structure WholeLineLocalMomentEnergyData
    (p : CMParams) (P κ T t x₀ : ℝ)
    (u v : ℝ → ℝ → ℝ) where
  hP : 1 < P
  hκ : 0 < κ
  ht0 : 0 < t
  htT : t < T
  solution : IsClassicalSolution p T u v
  u_pos : ∀ x, 0 < u t x
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

theorem wholeLineLocalLpHalfPower_deriv
    {P t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hu_pos : 0 < u t x)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    deriv (fun y : ℝ => (u t y) ^ (P / 2)) x =
      (P / 2) * (u t x) ^ (P / 2 - 1) * deriv (u t) x := by
  have hpow := hu.rpow_const (p := P / 2) (Or.inl hu_pos.ne')
  rw [hpow.deriv]
  ring

theorem wholeLineLocalLpHalfPower_deriv_sq
    {P t x : ℝ} {u : ℝ → ℝ → ℝ}
    (hu_pos : 0 < u t x)
    (hu : HasDerivAt (u t) (deriv (u t) x) x) :
    (deriv (fun y : ℝ => (u t y) ^ (P / 2)) x) ^ 2 =
      (P / 2) ^ 2 *
        ((u t x) ^ (P - 2) * (deriv (u t) x) ^ 2) := by
  rw [wholeLineLocalLpHalfPower_deriv hu_pos hu]
  have hpow : ((u t x) ^ (P / 2 - 1)) ^ 2 =
      (u t x) ^ (P - 2) := by
    calc
      ((u t x) ^ (P / 2 - 1)) ^ 2 =
          (u t x) ^ (P / 2 - 1) *
            (u t x) ^ (P / 2 - 1) := by ring
      _ = (u t x) ^ ((P / 2 - 1) + (P / 2 - 1)) := by
        rw [Real.rpow_add hu_pos]
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

theorem wholeLineLocalLpHalfPowerGradient_eq_dissipation
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
    wholeLineLocalLpHalfPowerGradient P κ u t x₀ =
      (P / 2) ^ 2 *
        wholeLineLocalLpDiffusionDissipation P κ u t x₀ := by
  unfold wholeLineLocalLpHalfPowerGradient
  unfold wholeLineLocalLpDiffusionDissipation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hu := (H.solution.u_smooth t x H.ht0 H.htT).2.hasDerivAt
  rw [wholeLineLocalLpHalfPower_deriv_sq (H.u_pos x) hu]
  ring

theorem WholeLineLocalMomentEnergyData.diffusion_first_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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

theorem WholeLineLocalMomentEnergyData.diffusion_weight_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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

theorem WholeLineLocalMomentEnergyData.diffusion_identity
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
    (∫ x : ℝ,
      wholeLineLocalLpTest P κ u t x₀ x * iteratedDeriv 2 (u t) x) =
      -(4 * (P - 1) / P ^ 2) *
          wholeLineLocalLpHalfPowerGradient P κ u t x₀ +
        (1 / P) * wholeLineLocalLpWeightSecond P κ u t x₀ := by
  have hfirst := H.diffusion_first_ibp
  have hweight := H.diffusion_weight_ibp
  have hgrad := wholeLineLocalLpHalfPowerGradient_eq_dissipation H
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

theorem wholeLineLocalLpTestDeriv_mul_flux
    {P κ t x₀ x : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ} (hu_pos : 0 < u t x) :
    wholeLineLocalLpTestDeriv P κ u t x₀ x *
        wholeLineLocalChemotaxisFlux p u v t x =
      (P - 1) *
          ((u t x) ^ (P + p.m - 2) * deriv (u t) x *
            deriv (v t) x * localizingWeightAt κ x₀ x) +
        (u t x) ^ (P + p.m - 1) * deriv (v t) x *
          deriv (localizingWeightAt κ x₀) x := by
  have hpow₁ :
      (u t x) ^ (P - 2) * (u t x) ^ p.m =
        (u t x) ^ (P + p.m - 2) := by
    calc
      (u t x) ^ (P - 2) * (u t x) ^ p.m =
          (u t x) ^ ((P - 2) + p.m) := by
        rw [Real.rpow_add hu_pos]
      _ = (u t x) ^ (P + p.m - 2) := by
        congr 1
        ring
  have hpow₂ :
      (u t x) ^ (P - 1) * (u t x) ^ p.m =
        (u t x) ^ (P + p.m - 1) := by
    calc
      (u t x) ^ (P - 1) * (u t x) ^ p.m =
          (u t x) ^ ((P - 1) + p.m) := by
        rw [Real.rpow_add hu_pos]
      _ = (u t x) ^ (P + p.m - 1) := by
        congr 1
        ring
  unfold wholeLineLocalLpTestDeriv
  unfold wholeLineLocalChemotaxisFlux
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

theorem WholeLineLocalMomentEnergyData.chemotaxis_first_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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
      exact wholeLineLocalLpTestDeriv_mul_flux (H.u_pos x)
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

theorem WholeLineLocalMomentEnergyData.signal_secondDerivative_integral
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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
            rw [Real.rpow_add (H.u_pos x)]
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

theorem WholeLineLocalMomentEnergyData.chemotaxis_second_ibp
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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

theorem WholeLineLocalMomentEnergyData.chemotaxis_identity
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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

theorem WholeLineLocalMomentEnergyData.energy_hasDerivAt
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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

theorem WholeLineLocalMomentEnergyData.tested_pde_pointwise
    {P κ T t x₀ x : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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
        rw [Real.rpow_add (H.u_pos x)]
      _ = (u t x) ^ P := by
        congr 1
        ring
  have hpow₂ : (u t x) ^ P * (u t x) ^ p.α =
      (u t x) ^ (P + p.α) := by
    rw [Real.rpow_add (H.u_pos x)]
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

theorem WholeLineLocalMomentEnergyData.tested_pde
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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
theorem WholeLineLocalMomentEnergyData.energy_identity
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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

theorem wholeLineLocalChemotaxisCoefficient_nonneg
    (p : CMParams) {P : ℝ} (hχ : 0 ≤ p.χ) (hP : 1 < P) :
    0 ≤ wholeLineLocalChemotaxisCoefficient p P := by
  unfold wholeLineLocalChemotaxisCoefficient
  exact div_nonneg
    (mul_nonneg hχ (sub_nonneg.mpr hP.le))
    (by linarith [p.hm] : 0 ≤ P + p.m - 1)

theorem exists_admissible_localMomentExponent
    (p : CMParams) (hχ : 0 ≤ p.χ)
    (hthreshold : paper1PositiveCriticalThreshold p) :
    ∃ P : ℝ, max 1 (max p.m p.γ) < P ∧ P < p.m + p.γ ∧
      0 ≤ wholeLineLocalChemotaxisCoefficient p P ∧
      wholeLineLocalChemotaxisCoefficient p P < 1 := by
  obtain ⟨P, hP, hupper, hadm⟩ :=
    exists_paper1PositiveCritical_admissibleExponent p hχ hthreshold
  have hone : 1 < P := lt_of_le_of_lt (le_max_left 1 (max p.m p.γ)) hP
  exact ⟨P, hP, hupper,
    wholeLineLocalChemotaxisCoefficient_nonneg p hχ hone,
    wholeLineLocalChemotaxisCoefficient_lt_one p hone hadm⟩

theorem wholeLineLocalCriticalAbsorptionCoefficient_pos
    (p : CMParams) {P : ℝ} (hP : 1 < P)
    (hadm : p.χ * (P - 1) < P + p.m - 1) :
    0 < 1 - wholeLineLocalChemotaxisCoefficient p P := by
  linarith [wholeLineLocalChemotaxisCoefficient_lt_one p hP hadm]

theorem WholeLineLocalMomentEnergyData.weightSecond_le
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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
    have huP : 0 ≤ (u t x) ^ P := Real.rpow_nonneg (H.u_pos x).le P
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

theorem WholeLineLocalMomentEnergyData.signalWeightCross_le
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v) :
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
      Real.rpow_nonneg (H.u_pos x).le _
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

theorem WholeLineLocalMomentEnergyData.signalTerm_nonneg
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
    (hv_nonneg : ∀ x, 0 ≤ v t x) :
    0 ≤ wholeLineLocalLpSignalTerm p P κ u v t x₀ := by
  unfold wholeLineLocalLpSignalTerm
  exact integral_nonneg fun x =>
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (H.u_pos x).le _) (hv_nonneg x))
      (localizingWeightAt_pos κ x₀ x).le

/-- Paper-style local weighted energy inequality.  The two weight-derivative
terms are bounded using `|ψₓ| ≤ κψ` and `|ψₓₓ| ≤ (κ+κ²)ψ`. -/
theorem WholeLineLocalMomentEnergyData.energy_inequality
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
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
theorem WholeLineLocalMomentEnergyData.critical_energy_inequality
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
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

theorem WholeLineLocalMomentEnergyData.critical_energy_inequality_drop_signal
    {P κ T t x₀ : ℝ} {p : CMParams}
    {u v : ℝ → ℝ → ℝ}
    (H : WholeLineLocalMomentEnergyData p P κ T t x₀ u v)
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

#print axioms wholeLineLocalLpMoment_hasDerivAt_of_dominated
#print axioms WholeLineLocalMomentEnergyData.energy_identity
#print axioms WholeLineLocalMomentEnergyData.energy_inequality
#print axioms WholeLineLocalMomentEnergyData.critical_energy_inequality_drop_signal
#print axioms exists_admissible_localMomentExponent

end ShenWork.Paper1
