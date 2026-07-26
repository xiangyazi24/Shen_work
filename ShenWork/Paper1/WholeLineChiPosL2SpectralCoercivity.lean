import ShenWork.Paper1.WholeLineChiPosDispersionSharp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# L² spectral coercivity for the far-left deficit

For the normalized `m = γ = α = 1` equation, the linearized deficit
`p = q - 1` has Fourier growth symbol

`dispersion 1 χ s = -1 - s + χs / (1 + s)`, `s = (2πξ)²`.

The positive sub-Turing gap used here is

`farLeftL2Gap χ = 2√χ - χ = √χ(2 - √χ)`.

This file proves the exact mode bound and integrates it for complex-valued
Schwartz deficits.  `farLeftL2QuadraticForm` includes the co-moving drift
symbol `i c (2πξ)`; its real part vanishes identically, so the coercivity
constant is independent of `c`.  Plancherel then returns the physical
`L²` norm on the left-hand side.
-/

open MeasureTheory Real
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace ShenWork.Paper1

/-- The explicit positive spectral gap on `0 < χ < 4`. -/
def farLeftL2Gap (chi : ℝ) : ℝ :=
  2 * Real.sqrt chi - chi

/-- The nonnegative mode variable `s = (2πξ)²` for Mathlib's Fourier
normalization. -/
def fourierFrequencySq (xi : ℝ) : ℝ :=
  (2 * Real.pi * xi) ^ 2

/-- The negative real spectral energy of a Schwartz deficit. -/
def farLeftL2SpectralDissipation
    (chi : ℝ) (p : SchwartzMap ℝ ℂ) : ℝ :=
  ∫ xi : ℝ,
    (-dispersion 1 chi (fourierFrequencySq xi)) * ‖(𝓕 p) xi‖ ^ 2

/-- Fourier symbol of the co-moving linearized deficit operator. -/
def farLeftL2LinearSymbol (chi c xi : ℝ) : ℂ :=
  (dispersion 1 chi (fourierFrequencySq xi) : ℂ) +
    Complex.I * (c * (2 * Real.pi * xi))

/-- Negative real part of the co-moving linearized quadratic form. -/
def farLeftL2QuadraticForm
    (chi c : ℝ) (p : SchwartzMap ℝ ℂ) : ℝ :=
  ∫ xi : ℝ,
    -((star ((𝓕 p) xi)) * farLeftL2LinearSymbol chi c xi *
      (𝓕 p) xi).re

/-- The drift is purely imaginary and contributes zero to the real quadratic
form. -/
theorem farLeftL2QuadraticForm_eq_spectralDissipation
    (chi c : ℝ) (p : SchwartzMap ℝ ℂ) :
    farLeftL2QuadraticForm chi c p =
      farLeftL2SpectralDissipation chi p := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with xi
  let z : ℂ := (𝓕 p) xi
  have hrearrange :
      star z * farLeftL2LinearSymbol chi c xi * z =
        farLeftL2LinearSymbol chi c xi * (star z * z) := by
    ring
  change
    -(star z * farLeftL2LinearSymbol chi c xi * z).re =
      (-dispersion 1 chi (fourierFrequencySq xi)) * ‖z‖ ^ 2
  have hconj :
      star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    calc
      star z * z = (‖z‖ : ℂ) ^ 2 := by
        simpa only using Complex.conj_mul' z
      _ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by norm_cast
  rw [hrearrange, hconj]
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp [farLeftL2LinearSymbol, Complex.mul_re, Complex.mul_im]

/-- `2√χ - χ` is strictly positive exactly on the strict positive part of the
sub-Turing range. -/
theorem farLeftL2Gap_pos
    {chi : ℝ} (hchi : 0 < chi) (hchi4 : chi < 4) :
    0 < farLeftL2Gap chi := by
  have hsqrt_pos : 0 < Real.sqrt chi := Real.sqrt_pos.2 hchi
  have hsqrt_lt : Real.sqrt chi < 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    norm_num
    exact hchi4
  have hsq : (Real.sqrt chi) ^ 2 = chi := Real.sq_sqrt hchi.le
  unfold farLeftL2Gap
  nlinarith

/-- Direct specialization of the landed sharp dispersion theorem to
`α = 1`, whose threshold is `χ < 4`. -/
theorem dispersion_lt_zero_of_pos_lt_four
    {chi : ℝ} (hchi : 0 < chi) (hchi4 : chi < 4)
    {s : ℝ} (hs : 0 ≤ s) :
    dispersion 1 chi s < 0 := by
  apply ShenWork.Paper1.dispersion_le_of_lt_turing
    1 chi (by norm_num) hchi.le
  · norm_num
    exact hchi4
  · exact hs

/-- Quantitative version of the modewise dispersion bound:
`dispersion 1 χ s ≤ -(2√χ - χ)` for every `s ≥ 0`. -/
theorem dispersion_le_neg_farLeftL2Gap
    {chi : ℝ} (hchi : 0 ≤ chi) {s : ℝ} (hs : 0 ≤ s) :
    dispersion 1 chi s ≤ -farLeftL2Gap chi := by
  have hden : 0 < 1 + s := by linarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt chi := Real.sqrt_nonneg chi
  have hsq : (Real.sqrt chi) ^ 2 = chi := Real.sq_sqrt hchi
  have hfrac :
      chi * s / (1 + s) ≤ s + (Real.sqrt chi - 1) ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (1 + s - Real.sqrt chi)]
  unfold dispersion farLeftL2Gap
  nlinarith

private theorem schwartz_integrable_norm_sq
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hC : 0 ≤ C := by
    positivity
  have hbase : Integrable (fun x : ℝ => ‖f x‖) := f.integrable.norm
  have hdom : Integrable (fun x : ℝ => C * ‖f x‖) :=
    hbase.const_mul C
  refine hdom.mono ((f.continuous.norm.pow 2).aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hfx := SchwartzMap.norm_le_seminorm ℂ f x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hC,
    abs_of_nonneg (norm_nonneg _)]
  nlinarith [norm_nonneg (f x)]

private theorem schwartz_integrable_frequencySq_mul_norm_sq
    (f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => fourierFrequencySq x * ‖f x‖ ^ 2) := by
  let C : ℝ := SchwartzMap.seminorm ℂ 0 0 f
  have hC : 0 ≤ C := by
    positivity
  have hbase :
      Integrable (fun x : ℝ => ‖x‖ ^ 2 * ‖f x‖) :=
    f.integrable_pow_mul volume 2
  let K : ℝ := (2 * Real.pi) ^ 2 * C
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) hC
  have hdom :
      Integrable (fun x : ℝ => K * (‖x‖ ^ 2 * ‖f x‖)) :=
    hbase.const_mul K
  refine hdom.mono
    (((continuous_const.mul continuous_id).pow 2).mul
      (f.continuous.norm.pow 2) |>.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hfx := SchwartzMap.norm_le_seminorm ℂ f x
  have hfreq :
      fourierFrequencySq x = (2 * Real.pi) ^ 2 * ‖x‖ ^ 2 := by
    simp only [fourierFrequencySq, Real.norm_eq_abs]
    rw [sq_abs]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
    abs_mul, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (norm_nonneg _), hfreq]
  dsimp [K, C]
  calc
    (2 * Real.pi) ^ 2 * |x| ^ 2 * ‖f x‖ ^ 2 =
        ((2 * Real.pi) ^ 2 * |x| ^ 2 * ‖f x‖) * ‖f x‖ := by
      ring
    _ ≤ ((2 * Real.pi) ^ 2 * |x| ^ 2 * ‖f x‖) *
        SchwartzMap.seminorm ℂ 0 0 f := by
      exact mul_le_mul_of_nonneg_left hfx
        (mul_nonneg
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (norm_nonneg _))
    _ = (2 * Real.pi) ^ 2 * SchwartzMap.seminorm ℂ 0 0 f *
        (|x| ^ 2 * ‖f x‖) := by
      ring

private theorem schwartz_integrable_one_add_frequencySq_mul_norm_sq
    (f : SchwartzMap ℝ ℂ) :
    Integrable
      (fun x : ℝ => (1 + fourierFrequencySq x) * ‖f x‖ ^ 2) := by
  have h0 := schwartz_integrable_norm_sq f
  have h2 := schwartz_integrable_frequencySq_mul_norm_sq f
  simpa only [add_mul, one_mul] using h0.add h2

private theorem farLeftL2SpectralDissipation_integrable
    {chi : ℝ} (hchi : 0 ≤ chi) (p : SchwartzMap ℝ ℂ) :
    Integrable (fun xi : ℝ =>
      (-dispersion 1 chi (fourierFrequencySq xi)) * ‖(𝓕 p) xi‖ ^ 2) := by
  let f : SchwartzMap ℝ ℂ := 𝓕 p
  have henv0 :
      Integrable (fun xi : ℝ =>
        (1 + chi) *
          ((1 + fourierFrequencySq xi) * ‖f xi‖ ^ 2)) :=
    (schwartz_integrable_one_add_frequencySq_mul_norm_sq f).const_mul (1 + chi)
  refine henv0.mono ?_ ?_
  · have hfreq : Continuous fourierFrequencySq := by
      unfold fourierFrequencySq
      fun_prop
    have hdisp : Continuous
        (fun xi : ℝ => dispersion 1 chi (fourierFrequencySq xi)) := by
      unfold dispersion
      exact (continuous_const.sub hfreq).add
        ((continuous_const.mul hfreq).div
          (continuous_const.add hfreq) (fun xi => by
            have hs : 0 ≤ fourierFrequencySq xi := sq_nonneg _
            linarith))
    exact (hdisp.neg.mul (f.continuous.norm.pow 2)).aestronglyMeasurable
  · filter_upwards [] with xi
    let s := fourierFrequencySq xi
    have hs : 0 ≤ s := sq_nonneg _
    have hden : 0 < 1 + s := by linarith
    have hratio0 : 0 ≤ chi * s / (1 + s) :=
      div_nonneg (mul_nonneg hchi hs) hden.le
    have hratio_le : chi * s / (1 + s) ≤ chi := by
      rw [div_le_iff₀ hden]
      nlinarith
    have hsymbol :
        |-(dispersion 1 chi s)| ≤ (1 + chi) * (1 + s) := by
      unfold dispersion
      rw [abs_neg]
      calc
        |-1 - s + chi * s / (1 + s)| ≤
            1 + s + chi * s / (1 + s) := by
          rw [abs_le]
          constructor <;> nlinarith
        _ ≤ 1 + s + chi := by linarith
        _ ≤ (1 + chi) * (1 + s) := by nlinarith
    have hsqnorm : 0 ≤ ‖f xi‖ ^ 2 := sq_nonneg _
    have henv_nonneg :
        0 ≤ (1 + chi) * ((1 + s) * ‖f xi‖ ^ 2) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) hsqnorm)
    change
      ‖(-dispersion 1 chi s) * ‖f xi‖ ^ 2‖ ≤
        ‖(1 + chi) * ((1 + s) * ‖f xi‖ ^ 2)‖
    calc
      ‖(-dispersion 1 chi s) * ‖f xi‖ ^ 2‖ =
          |-(dispersion 1 chi s)| * ‖f xi‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsqnorm]
      _ ≤ ((1 + chi) * (1 + s)) * ‖f xi‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsymbol hsqnorm
      _ = ‖(1 + chi) * ((1 + s) * ‖f xi‖ ^ 2)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg henv_nonneg]
        ring

/-- Plancherel-integrated spectral coercivity for every Schwartz deficit. -/
theorem farLeftL2_spectral_coercivity
    {chi : ℝ} (hchi : 0 < chi) (hchi4 : chi < 4)
    (p : SchwartzMap ℝ ℂ) :
    0 < farLeftL2Gap chi ∧
      farLeftL2Gap chi * (∫ x : ℝ, ‖p x‖ ^ 2) ≤
        farLeftL2SpectralDissipation chi p := by
  refine ⟨farLeftL2Gap_pos hchi hchi4, ?_⟩
  have hleft :
      Integrable (fun xi : ℝ =>
        farLeftL2Gap chi * ‖(𝓕 p) xi‖ ^ 2) :=
    (schwartz_integrable_norm_sq (𝓕 p)).const_mul (farLeftL2Gap chi)
  have hright :=
    farLeftL2SpectralDissipation_integrable hchi.le p
  have hmode : ∀ xi : ℝ,
      farLeftL2Gap chi * ‖(𝓕 p) xi‖ ^ 2 ≤
        (-dispersion 1 chi (fourierFrequencySq xi)) * ‖(𝓕 p) xi‖ ^ 2 := by
    intro xi
    exact mul_le_mul_of_nonneg_right
      (by
        have h := dispersion_le_neg_farLeftL2Gap hchi.le
          (show 0 ≤ fourierFrequencySq xi from sq_nonneg _)
        linarith)
      (sq_nonneg _)
  have hint := MeasureTheory.integral_mono hleft hright hmode
  rw [MeasureTheory.integral_const_mul] at hint
  rw [SchwartzMap.integral_norm_sq_fourier] at hint
  exact hint

/-- **L² spectral coercivity.**  The negative real part of the full co-moving
linearized quadratic form controls the physical `L²` deficit with the positive
gap `2√χ - χ`; the constant is independent of the drift `c`. -/
theorem farLeftL2_quadratic_coercivity
    {chi : ℝ} (hchi : 0 < chi) (hchi4 : chi < 4)
    (c : ℝ) (p : SchwartzMap ℝ ℂ) :
    0 < farLeftL2Gap chi ∧
      farLeftL2Gap chi * (∫ x : ℝ, ‖p x‖ ^ 2) ≤
        farLeftL2QuadraticForm chi c p := by
  rw [farLeftL2QuadraticForm_eq_spectralDissipation]
  exact farLeftL2_spectral_coercivity hchi hchi4 p

section AxiomAudit

#print axioms farLeftL2Gap_pos
#print axioms dispersion_lt_zero_of_pos_lt_four
#print axioms dispersion_le_neg_farLeftL2Gap
#print axioms farLeftL2QuadraticForm_eq_spectralDissipation
#print axioms farLeftL2_spectral_coercivity
#print axioms farLeftL2_quadratic_coercivity

end AxiomAudit

end ShenWork.Paper1
