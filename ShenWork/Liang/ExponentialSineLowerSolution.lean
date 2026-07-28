/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import ShenWork.Liang.FiniteBlockSpreading
import ShenWork.Liang.LinearDeterminacy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Exponential--sine profiles for scalar inside spreading

The scalar inside-spreading construction of Li--Bewick--Barnard--Fagan joins
two compactly truncated exponential--sine flanks to a positive plateau.  This
file begins its formalization with the exact convolution identity for the
untruncated flank.  Compact support of the kernel makes all weighted
trigonometric moments integrable.
-/

open MeasureTheory

namespace ShenWork.Liang

noncomputable section

/-- Exponentially weighted cosine moment of a dispersal kernel. -/
def kernelCosMoment (K : ℝ → ℝ) (μ γ : ℝ) : ℝ :=
  ∫ z, K z * Real.exp (μ * z) * Real.cos (γ * z)

/-- Exponentially weighted sine moment of a dispersal kernel. -/
def kernelSinMoment (K : ℝ → ℝ) (μ γ : ℝ) : ℝ :=
  ∫ z, K z * Real.exp (μ * z) * Real.sin (γ * z)

/-- Amplitude of the two weighted trigonometric moments. -/
def kernelSineAmplitude (K : ℝ → ℝ) (μ γ : ℝ) : ℝ :=
  Real.sqrt
    (kernelCosMoment K μ γ ^ 2 + kernelSinMoment K μ γ ^ 2)

/-- Spatial phase shift of an exponential--sine flank. -/
def kernelSineShift (K : ℝ → ℝ) (μ γ : ℝ) : ℝ :=
  Real.arctan
    (kernelSinMoment K μ γ / kernelCosMoment K μ γ) / γ

/-- Multiplier remaining after the convolution is written as a translated
exponential--sine flank. -/
def kernelSineMultiplier (K : ℝ → ℝ) (μ γ : ℝ) : ℝ :=
  kernelSineAmplitude K μ γ *
    Real.exp (-μ * kernelSineShift K μ γ)

/-- The untruncated exponential--sine flank. -/
def exponentialSineProfile (μ γ x : ℝ) : ℝ :=
  Real.exp (-μ * x) * Real.sin (γ * x)

/-- Compact truncation of an exponential--sine flank to `[0, π / γ]`. -/
def truncatedExponentialSine
    (amplitude μ γ x : ℝ) : ℝ :=
  if x ∈ Set.Icc 0 (Real.pi / γ) then
    amplitude * exponentialSineProfile μ γ x
  else 0

theorem truncatedExponentialSine_nonneg
    {amplitude μ γ x : ℝ}
    (hamplitude : 0 ≤ amplitude) (hγ : 0 < γ) :
    0 ≤ truncatedExponentialSine amplitude μ γ x := by
  unfold truncatedExponentialSine
  split_ifs with hx
  · have harg_nonneg : 0 ≤ γ * x :=
      mul_nonneg hγ.le hx.1
    have harg_le_pi : γ * x ≤ Real.pi := by
      have := (le_div_iff₀ hγ).mp hx.2
      nlinarith
    exact mul_nonneg hamplitude
      (mul_nonneg (Real.exp_pos _).le
        (Real.sin_nonneg_of_nonneg_of_le_pi
          harg_nonneg harg_le_pi))
  · exact le_rfl

theorem kernel_weighted_cos_integrable
    {K : ℝ → ℝ} (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K) (μ γ : ℝ) :
    Integrable
      (fun z => K z * Real.exp (μ * z) * Real.cos (γ * z)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact hKcompact.mul_right.mul_right

theorem kernel_weighted_sin_integrable
    {K : ℝ → ℝ} (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K) (μ γ : ℝ) :
    Integrable
      (fun z => K z * Real.exp (μ * z) * Real.sin (γ * z)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact hKcompact.mul_right.mul_right

/-- If every jump is at least `minStep`, then the positive exponential
moment is at least `exp (μ * minStep)`. -/
theorem exp_minStep_le_kernelMoment
    {K : ℝ → ℝ} {minStep μ : ℝ}
    (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ z, 0 ≤ K z)
    (hKmass : ∫ z, K z = 1)
    (hKleft : ∀ z < minStep, K z = 0)
    (hμ : 0 ≤ μ) :
    Real.exp (μ * minStep) ≤
      ShenWork.Analysis.kernelMoment K μ := by
  have hKint : Integrable K :=
    hKcont.integrable_of_hasCompactSupport hKcompact
  have hweighted :
      Integrable (fun z => K z * Real.exp (μ * z)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact hKcompact.mul_right
  calc
    Real.exp (μ * minStep) =
        ∫ z, Real.exp (μ * minStep) * K z := by
      rw [integral_const_mul, hKmass]
      ring
    _ ≤ ∫ z, K z * Real.exp (μ * z) := by
      apply integral_mono
        (hKint.const_mul (Real.exp (μ * minStep))) hweighted
      intro z
      by_cases hz : z < minStep
      · simp [hKleft z hz]
      · have hzle : minStep ≤ z := le_of_not_gt hz
        have hexp :
            Real.exp (μ * minStep) ≤ Real.exp (μ * z) := by
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hzle hμ)
        nlinarith [mul_le_mul_of_nonneg_left hexp (hKnonneg z)]
    _ = ShenWork.Analysis.kernelMoment K μ := rfl

/-- Under favorable growth strictly greater than one, every positive
exponential weight predicts a rightward speed strictly above a hard minimum
jump.  This makes the asymmetric-drift counterexample compatible with the
printed rightward speed inequality. -/
theorem minStep_lt_kernelSpeedAt
    {K : ℝ → ℝ} {growth minStep μ : ℝ}
    (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K)
    (hKnonneg : ∀ z, 0 ≤ K z)
    (hKmass : ∫ z, K z = 1)
    (hKleft : ∀ z < minStep, K z = 0)
    (hgrowth : 1 < growth)
    (hμ : 0 < μ) :
    minStep < kernelSpeedAt K growth μ := by
  have hmoment :=
    exp_minStep_le_kernelMoment hKcont hKcompact hKnonneg
      hKmass hKleft hμ.le
  have hmoment_pos :
      0 < ShenWork.Analysis.kernelMoment K μ :=
    (Real.exp_pos (μ * minStep)).trans_le hmoment
  have hproduct :
      Real.exp (μ * minStep) <
        growth * ShenWork.Analysis.kernelMoment K μ := by
    calc
      Real.exp (μ * minStep) ≤
          ShenWork.Analysis.kernelMoment K μ := hmoment
      _ < growth * ShenWork.Analysis.kernelMoment K μ := by
        nlinarith
  have hlog :=
    Real.log_lt_log (Real.exp_pos (μ * minStep)) hproduct
  rw [Real.log_exp] at hlog
  unfold kernelSpeedAt exponentialSpeed
  exact (lt_div_iff₀ hμ).2 (by nlinarith)

/-- Polar-form identity used to turn the two weighted trigonometric moments
into an amplitude and a spatial phase shift. -/
theorem cos_sin_moment_eq_amplitude_sin_sub_phase
    {C S θ : ℝ} (hC : 0 < C) :
    C * Real.sin θ - S * Real.cos θ =
      Real.sqrt (C ^ 2 + S ^ 2) *
        Real.sin (θ - Real.arctan (S / C)) := by
  have hCne : C ≠ 0 := hC.ne'
  have hrad :
      C ^ 2 + S ^ 2 =
        C ^ 2 * (1 + (S / C) ^ 2) := by
    field_simp
  have hsqrt :
      Real.sqrt (C ^ 2 + S ^ 2) =
        C * Real.sqrt (1 + (S / C) ^ 2) := by
    rw [hrad, Real.sqrt_mul (sq_nonneg C),
      Real.sqrt_sq_eq_abs, abs_of_pos hC]
  have hden :
      Real.sqrt (1 + (S / C) ^ 2) ≠ 0 := by positivity
  rw [hsqrt, Real.sin_sub, Real.sin_arctan, Real.cos_arctan]
  field_simp

/-- Exact action of dispersal on an exponential--sine flank.  The cosine
moment multiplies the sine component and the sine moment produces the phase
shift. -/
theorem dispersal_exponentialSineProfile
    {K : ℝ → ℝ} (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K) (μ γ x : ℝ) :
    ShenWork.Analysis.dispersal K (exponentialSineProfile μ γ) x =
      Real.exp (-μ * x) *
        (kernelCosMoment K μ γ * Real.sin (γ * x) -
          kernelSinMoment K μ γ * Real.cos (γ * x)) := by
  rw [ShenWork.Analysis.dispersal_eq_shift]
  have hcos :=
    kernel_weighted_cos_integrable hKcont hKcompact μ γ
  have hsin :=
    kernel_weighted_sin_integrable hKcont hKcompact μ γ
  have hpoint :
      (fun z =>
        K z * exponentialSineProfile μ γ (x - z)) =
      fun z =>
        Real.exp (-μ * x) *
          (Real.sin (γ * x) *
              (K z * Real.exp (μ * z) * Real.cos (γ * z)) -
            Real.cos (γ * x) *
              (K z * Real.exp (μ * z) * Real.sin (γ * z))) := by
    funext z
    rw [exponentialSineProfile, show -μ * (x - z) =
      -μ * x + μ * z by ring, Real.exp_add,
      show γ * (x - z) = γ * x - γ * z by ring,
      Real.sin_sub]
    ring
  rw [hpoint, integral_const_mul,
    integral_sub (hcos.const_mul (Real.sin (γ * x)))
      (hsin.const_mul (Real.cos (γ * x))),
    integral_const_mul, integral_const_mul]
  simp only [kernelCosMoment, kernelSinMoment]
  ring

/-- When the weighted cosine moment is positive, convolution translates the
exponential--sine flank by `kernelSineShift` and multiplies it by
`kernelSineMultiplier`. -/
theorem dispersal_exponentialSineProfile_eq_shift
    {K : ℝ → ℝ} (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K) {μ γ x : ℝ}
    (hγ : γ ≠ 0)
    (hcos : 0 < kernelCosMoment K μ γ) :
    ShenWork.Analysis.dispersal K (exponentialSineProfile μ γ) x =
      kernelSineMultiplier K μ γ *
        exponentialSineProfile μ γ
          (x - kernelSineShift K μ γ) := by
  rw [dispersal_exponentialSineProfile hKcont hKcompact]
  rw [cos_sin_moment_eq_amplitude_sin_sub_phase hcos]
  let s := kernelSineShift K μ γ
  have hphase :
      γ * (x - s) =
        γ * x -
          Real.arctan
            (kernelSinMoment K μ γ /
              kernelCosMoment K μ γ) := by
    simp only [s, kernelSineShift]
    field_simp
  have hexp :
      Real.exp (-μ * s) * Real.exp (-μ * (x - s)) =
        Real.exp (-μ * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change
    Real.exp (-μ * x) *
        (kernelSineAmplitude K μ γ *
          Real.sin
            (γ * x -
              Real.arctan
                (kernelSinMoment K μ γ /
                  kernelCosMoment K μ γ))) =
      kernelSineMultiplier K μ γ *
        exponentialSineProfile μ γ (x - s)
  rw [← hphase]
  unfold kernelSineMultiplier exponentialSineProfile
  change
    Real.exp (-μ * x) *
        (kernelSineAmplitude K μ γ *
          Real.sin (γ * (x - s))) =
      (kernelSineAmplitude K μ γ * Real.exp (-μ * s)) *
        (Real.exp (-μ * (x - s)) * Real.sin (γ * (x - s)))
  rw [← hexp]
  ring

/-- Away from both truncation endpoints by one kernel radius, compactly
supported dispersal cannot see the truncation. -/
theorem dispersal_truncatedExponentialSine_eq
    {K : ℝ → ℝ} {radius amplitude μ γ x : ℝ}
    (hKsupport : ∀ z, radius < |z| → K z = 0)
    (hxleft : radius ≤ x)
    (hxright : x ≤ Real.pi / γ - radius) :
    ShenWork.Analysis.dispersal K
        (truncatedExponentialSine amplitude μ γ) x =
      amplitude *
        ShenWork.Analysis.dispersal K
          (exponentialSineProfile μ γ) x := by
  rw [ShenWork.Analysis.dispersal_eq_shift,
    ShenWork.Analysis.dispersal_eq_shift, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : |z| ≤ radius
  · have hz_bounds := abs_le.mp hz
    have hmem : x - z ∈ Set.Icc 0 (Real.pi / γ) := by
      constructor <;> linarith
    simp [truncatedExponentialSine, hmem]
    ring
  · have hz_strict : radius < |z| := lt_of_not_ge hz
    simp [hKsupport z hz_strict]

/-- Exact weighted-moment formula for the compactly truncated flank at every
point whose kernel window remains inside the truncation interval. -/
theorem dispersal_truncatedExponentialSine_formula
    {K : ℝ → ℝ} {radius amplitude μ γ x : ℝ}
    (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K)
    (hKsupport : ∀ z, radius < |z| → K z = 0)
    (hxleft : radius ≤ x)
    (hxright : x ≤ Real.pi / γ - radius) :
    ShenWork.Analysis.dispersal K
        (truncatedExponentialSine amplitude μ γ) x =
      amplitude * Real.exp (-μ * x) *
        (kernelCosMoment K μ γ * Real.sin (γ * x) -
          kernelSinMoment K μ γ * Real.cos (γ * x)) := by
  rw [dispersal_truncatedExponentialSine_eq
      hKsupport hxleft hxright,
    dispersal_exponentialSineProfile hKcont hKcompact]
  ring

/-- Translation-and-multiplier form for the truncated flank at interior
points.  This is the exact one-step identity used by the moving lower
solution before the two flanks are joined to a plateau. -/
theorem dispersal_truncatedExponentialSine_eq_shift
    {K : ℝ → ℝ} {radius amplitude μ γ x : ℝ}
    (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K)
    (hKsupport : ∀ z, radius < |z| → K z = 0)
    (hγ : γ ≠ 0)
    (hcos : 0 < kernelCosMoment K μ γ)
    (hxleft : radius ≤ x)
    (hxright : x ≤ Real.pi / γ - radius) :
    ShenWork.Analysis.dispersal K
        (truncatedExponentialSine amplitude μ γ) x =
      amplitude * kernelSineMultiplier K μ γ *
        exponentialSineProfile μ γ
          (x - kernelSineShift K μ γ) := by
  rw [dispersal_truncatedExponentialSine_eq
      hKsupport hxleft hxright,
    dispersal_exponentialSineProfile_eq_shift
      hKcont hKcompact hγ hcos]
  ring

/-- One moving flank is a linear subsolution on every point whose convolution
window stays away from the truncation endpoints, provided the growth factor
times the phase-corrected kernel multiplier is at least one. -/
theorem truncatedExponentialSine_le_linearDispersalStep
    {K : ℝ → ℝ}
    {radius amplitude μ γ slope x : ℝ}
    (hKcont : Continuous K)
    (hKcompact : HasCompactSupport K)
    (hKsupport : ∀ z, radius < |z| → K z = 0)
    (hamplitude : 0 ≤ amplitude)
    (hγ : 0 < γ)
    (hcos : 0 < kernelCosMoment K μ γ)
    (hmultiplier :
      1 ≤ slope * kernelSineMultiplier K μ γ)
    (hxleft : radius ≤ x)
    (hxright : x ≤ Real.pi / γ - radius)
    (htarget :
      x - kernelSineShift K μ γ ∈
        Set.Icc 0 (Real.pi / γ)) :
    truncatedExponentialSine amplitude μ γ
        (x - kernelSineShift K μ γ) ≤
      ShenWork.Analysis.linearDispersalStep K slope
        (truncatedExponentialSine amplitude μ γ) x := by
  rw [show
      truncatedExponentialSine amplitude μ γ
          (x - kernelSineShift K μ γ) =
        amplitude *
          exponentialSineProfile μ γ
            (x - kernelSineShift K μ γ) by
      simp [truncatedExponentialSine, htarget]]
  unfold ShenWork.Analysis.linearDispersalStep
  rw [dispersal_truncatedExponentialSine_eq_shift
      hKcont hKcompact hKsupport hγ.ne' hcos hxleft hxright]
  have hprofile :
      0 ≤
        amplitude *
          exponentialSineProfile μ γ
            (x - kernelSineShift K μ γ) := by
    simpa [truncatedExponentialSine, htarget] using
      truncatedExponentialSine_nonneg
        (x := x - kernelSineShift K μ γ) hamplitude hγ
  calc
    amplitude *
        exponentialSineProfile μ γ
          (x - kernelSineShift K μ γ) =
      1 *
        (amplitude *
          exponentialSineProfile μ γ
            (x - kernelSineShift K μ γ)) := by ring
    _ ≤
      (slope * kernelSineMultiplier K μ γ) *
        (amplitude *
          exponentialSineProfile μ γ
            (x - kernelSineShift K μ γ)) :=
      mul_le_mul_of_nonneg_right hmultiplier hprofile
    _ =
      slope *
        (amplitude * kernelSineMultiplier K μ γ *
          exponentialSineProfile μ γ
            (x - kernelSineShift K μ γ)) := by ring

section AxiomAudit

#print axioms cos_sin_moment_eq_amplitude_sin_sub_phase
#print axioms minStep_lt_kernelSpeedAt
#print axioms dispersal_exponentialSineProfile
#print axioms dispersal_exponentialSineProfile_eq_shift
#print axioms dispersal_truncatedExponentialSine_formula
#print axioms dispersal_truncatedExponentialSine_eq_shift
#print axioms truncatedExponentialSine_le_linearDispersalStep

end AxiomAudit

end

end ShenWork.Liang
