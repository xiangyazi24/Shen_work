import ShenWork.Paper2.IntervalSharpSpectralCalculus
import Mathlib.Topology.MetricSpace.Holder

/-!
# Sharp Hilbert-to-Hölder embedding for the unit-interval Neumann spectrum

This file fills the fractional exponent gap in the `q = 2` branch of Paper 2,
Lemma 2.2.  The proof is entirely spectral: interpolate the uniform and
Lipschitz bounds of each cosine mode, and then apply weighted Cauchy--Schwarz.
-/

noncomputable section

namespace ShenWork.Paper2.IntervalSharpSpectralHolderEmbedding

open ShenWork.PDE.FractionalPower
open ShenWork.Paper2.IntervalSharpSpectralCalculus

/-- Reciprocal trace for a spatial Hölder exponent `theta`.  Since the
frequency is `sqrt(lambda_n)`, the squared trace weight is
`lambda_n^theta (1 + lambda_n)^(-2 sigma)`. -/
def holderReciprocalFractionalPowerWeight
    (sigma theta : ℝ) (n : ℕ) : ℝ :=
  neumannEigenvalue 1 n ^ theta *
    reciprocalFractionalPowerWeight 1 sigma n

theorem holderReciprocalFractionalPowerWeight_nonneg
    (sigma theta : ℝ) (n : ℕ) :
    0 ≤ holderReciprocalFractionalPowerWeight sigma theta n := by
  exact mul_nonneg
    (Real.rpow_nonneg (neumannEigenvalue_nonneg 1 n) theta)
    (reciprocalFractionalPowerWeight_nonneg 1 sigma n)

/-- The Hölder trace is dominated by the ordinary reciprocal trace at the
reduced fractional order `sigma - theta/2`. -/
theorem holderReciprocalFractionalPowerWeight_le_reduced
    {sigma theta : ℝ} (htheta : 0 ≤ theta) (n : ℕ) :
    holderReciprocalFractionalPowerWeight sigma theta n ≤
      reciprocalFractionalPowerWeight 1 (sigma - theta / 2) n := by
  let lam : ℝ := neumannEigenvalue 1 n
  let b : ℝ := 1 + lam
  have hlam : 0 ≤ lam := neumannEigenvalue_nonneg 1 n
  have hb : 0 < b := by dsimp [b]; linarith
  have hlam_le : lam ≤ b := by dsimp [b]; linarith
  have hpow : lam ^ theta ≤ b ^ theta :=
    Real.rpow_le_rpow hlam hlam_le htheta
  have hrecip : 0 ≤ reciprocalFractionalPowerWeight 1 sigma n :=
    reciprocalFractionalPowerWeight_nonneg 1 sigma n
  calc
    holderReciprocalFractionalPowerWeight sigma theta n =
        lam ^ theta * reciprocalFractionalPowerWeight 1 sigma n := by
      rfl
    _ ≤ b ^ theta * reciprocalFractionalPowerWeight 1 sigma n :=
      mul_le_mul_of_nonneg_right hpow hrecip
    _ = reciprocalFractionalPowerWeight 1 (sigma - theta / 2) n := by
      dsimp [reciprocalFractionalPowerWeight, fractionalPowerWeight, b, lam]
      rw [← Real.rpow_neg (one_add_neumannEigenvalue_pos 1 n).le,
        ← Real.rpow_neg (one_add_neumannEigenvalue_pos 1 n).le,
        ← Real.rpow_add (one_add_neumannEigenvalue_pos 1 n)]
      congr 1
      ring

/-- Exact one-dimensional trace condition for the Hilbert Hölder embedding. -/
theorem holderReciprocalFractionalPowerWeight_summable
    {sigma theta : ℝ} (htheta : 0 ≤ theta)
    (hgap : theta < 2 * sigma - 1 / 2) :
    Summable fun n : ℕ =>
      holderReciprocalFractionalPowerWeight sigma theta n := by
  have hreduced : 1 / 4 < sigma - theta / 2 := by linarith
  exact Summable.of_nonneg_of_le
    (holderReciprocalFractionalPowerWeight_nonneg sigma theta)
    (holderReciprocalFractionalPowerWeight_le_reduced htheta)
    (reciprocalFractionalPowerWeight_summable_of_sigma_gt_quarter
      (L := (1 : ℝ)) (sigma := sigma - theta / 2) (by norm_num) hreduced)

/-- Absolute coefficient weight appropriate for a `theta`-Hölder difference. -/
def holderCoeffNorm (theta : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℝ :=
  neumannEigenvalue 1 n ^ (theta / 2) * ‖a n‖

theorem holderCoeffNorm_nonneg
    (theta : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    0 ≤ holderCoeffNorm theta a n := by
  exact mul_nonneg
    (Real.rpow_nonneg (neumannEigenvalue_nonneg 1 n) (theta / 2))
    (norm_nonneg _)

theorem neumannEigenvalue_rpow_half_sq
    {theta : ℝ} (n : ℕ) :
    (neumannEigenvalue 1 n ^ (theta / 2)) ^ 2 =
      neumannEigenvalue 1 n ^ theta := by
  have hlam : 0 ≤ neumannEigenvalue 1 n := neumannEigenvalue_nonneg 1 n
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hlam]
  congr 1
  ring

theorem sqrt_fractionalEnergy_mul_sqrt_holderTrace_eq_holderCoeffNorm
    (sigma theta : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n) *
        Real.sqrt (holderReciprocalFractionalPowerWeight sigma theta n) =
      holderCoeffNorm theta a n := by
  have henergy : 0 ≤ fractionalPowerEnergyTerm 1 sigma a n :=
    fractionalPowerEnergyTerm_nonneg 1 sigma a n
  rw [← Real.sqrt_mul henergy]
  have hwpos : 0 < fractionalPowerWeight 1 sigma n :=
    fractionalPowerWeight_pos 1 sigma n
  have hprod :
      fractionalPowerEnergyTerm 1 sigma a n *
          holderReciprocalFractionalPowerWeight sigma theta n =
        (holderCoeffNorm theta a n) ^ 2 := by
    unfold fractionalPowerEnergyTerm
      holderReciprocalFractionalPowerWeight holderCoeffNorm
      reciprocalFractionalPowerWeight
    field_simp [hwpos.ne']
    rw [neumannEigenvalue_rpow_half_sq]
  rw [hprod, Real.sqrt_sq (holderCoeffNorm_nonneg theta a n)]

/-- Weighted Cauchy--Schwarz controls the absolute Hölder coefficients by the
fractional graph energy and the sharp Hölder trace. -/
theorem summable_and_tsum_holderCoeffNorm_le
    {sigma theta : ℝ} (a : ℕ → ℂ)
    (henergy : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma a n)
    (htrace : Summable fun n : ℕ =>
      holderReciprocalFractionalPowerWeight sigma theta n) :
    (Summable fun n : ℕ => holderCoeffNorm theta a n) ∧
      (∑' n : ℕ, holderCoeffNorm theta a n) ≤
        (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) ^
            (1 / (2 : ℝ)) *
          (∑' n : ℕ,
            holderReciprocalFractionalPowerWeight sigma theta n) ^
              (1 / (2 : ℝ)) := by
  let f : ℕ → ℝ := fun n =>
    Real.sqrt (fractionalPowerEnergyTerm 1 sigma a n)
  let g : ℕ → ℝ := fun n =>
    Real.sqrt (holderReciprocalFractionalPowerWeight sigma theta n)
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => Real.sqrt_nonneg _
  have hg_nonneg : ∀ n, 0 ≤ g n := fun n => Real.sqrt_nonneg _
  have hf_sum : Summable fun n : ℕ => f n ^ (2 : ℝ) := by
    dsimp [f]
    convert henergy using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt (fractionalPowerEnergyTerm_nonneg 1 sigma a n)]
  have hg_sum : Summable fun n : ℕ => g n ^ (2 : ℝ) := by
    dsimp [g]
    convert htrace using 1
    ext n
    rw [Real.rpow_two,
      Real.sq_sqrt
        (holderReciprocalFractionalPowerWeight_nonneg sigma theta n)]
  have hholder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hf_nonneg hg_nonneg hf_sum hg_sum
  constructor
  · dsimp [f, g] at hholder
    simpa
      [sqrt_fractionalEnergy_mul_sqrt_holderTrace_eq_holderCoeffNorm]
      using hholder.1
  · dsimp [f, g] at hholder
    simpa
      [sqrt_fractionalEnergy_mul_sqrt_holderTrace_eq_holderCoeffNorm,
        Real.rpow_two, Real.sq_sqrt,
        fractionalPowerEnergyTerm_nonneg,
        holderReciprocalFractionalPowerWeight_nonneg]
      using hholder.2

/-- Scalar interpolation between the bounded and Lipschitz cosine estimates. -/
theorem abs_cos_sub_cos_le_rpow
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (x y : ℝ) :
    |Real.cos x - Real.cos y| ≤
      2 ^ (1 - theta) * |x - y| ^ theta := by
  let d : ℝ := |x - y|
  have hd : 0 ≤ d := abs_nonneg _
  have hbounded : |Real.cos x - Real.cos y| ≤ 2 := by
    calc
      |Real.cos x - Real.cos y| ≤ |Real.cos x| + |Real.cos y| :=
        abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_cos_le_one x) (Real.abs_cos_le_one y)
      _ = 2 := by norm_num
  have hlip : |Real.cos x - Real.cos y| ≤ d := by
    simpa [d] using Real.abs_cos_sub_cos_le x y
  by_cases hd2 : d ≤ 2
  · by_cases hd0 : d = 0
    · calc
        |Real.cos x - Real.cos y| ≤ d := hlip
        _ = 0 := hd0
        _ ≤ 2 ^ (1 - theta) * |x - y| ^ theta := by positivity
    · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have hone_sub : 0 ≤ 1 - theta := sub_nonneg.mpr htheta_one
      have hpow : d ^ (1 - theta) ≤ 2 ^ (1 - theta) :=
        Real.rpow_le_rpow hd hd2 hone_sub
      calc
        |Real.cos x - Real.cos y| ≤ d := hlip
        _ = d ^ theta * d ^ (1 - theta) := by
          calc
            d = d ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = d ^ (theta + (1 - theta)) := by
              congr 1
              ring
            _ = d ^ theta * d ^ (1 - theta) :=
              Real.rpow_add hdpos theta (1 - theta)
        _ ≤ d ^ theta * 2 ^ (1 - theta) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hd theta)
        _ = 2 ^ (1 - theta) * |x - y| ^ theta := by
          dsimp [d]
          ring
  · have h2d : 2 ≤ d := le_of_not_ge hd2
    have hpow : 2 ^ theta ≤ d ^ theta :=
      Real.rpow_le_rpow (by norm_num) h2d htheta
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    have hone_sub : 0 ≤ 1 - theta := sub_nonneg.mpr htheta_one
    calc
      |Real.cos x - Real.cos y| ≤ 2 := hbounded
      _ = 2 ^ (1 - theta) * 2 ^ theta := by
        rw [← Real.rpow_add htwo_pos]
        norm_num
      _ ≤ 2 ^ (1 - theta) * d ^ theta :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by norm_num) _)
      _ = 2 ^ (1 - theta) * |x - y| ^ theta := by rfl

theorem unitInterval_neumannFrequency_nonneg (n : ℕ) :
    0 ≤ neumannFrequency 1 n := by
  unfold neumannFrequency
  positivity

theorem unitInterval_frequency_rpow_eq_eigenvalue_rpow_half
    (theta : ℝ) (n : ℕ) :
    |neumannFrequency 1 n| ^ theta =
      neumannEigenvalue 1 n ^ (theta / 2) := by
  have hk : 0 ≤ neumannFrequency 1 n :=
    unitInterval_neumannFrequency_nonneg n
  rw [abs_of_nonneg hk, neumannEigenvalue_eq_neumannFrequency_sq,
    ← Real.rpow_natCast, ← Real.rpow_mul hk]
  congr 1
  ring

/-- A single normalized-frequency cosine term has the interpolated Hölder
bound whose coefficient weight is `lambda_n^(theta/2)`. -/
theorem norm_cosineSeriesTerm_sub_le_holderCoeffNorm
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (a : ℕ → ℂ) (n : ℕ) (x y : ℝ) :
    ‖cosineSeriesTerm 1 a n x - cosineSeriesTerm 1 a n y‖ ≤
      2 ^ (1 - theta) * holderCoeffNorm theta a n *
        |x - y| ^ theta := by
  let k : ℝ := neumannFrequency 1 n
  have hcos := abs_cos_sub_cos_le_rpow htheta htheta_one (k * x) (k * y)
  have harg : |k * x - k * y| = |k| * |x - y| := by
    rw [← mul_sub, abs_mul]
  have hmode : |k| ^ theta = neumannEigenvalue 1 n ^ (theta / 2) := by
    simpa [k] using unitInterval_frequency_rpow_eq_eigenvalue_rpow_half theta n
  change
    ‖a n * (Real.cos (k * x) : ℂ) -
        a n * (Real.cos (k * y) : ℂ)‖ ≤ _
  have hcast :
      (Real.cos (k * x) : ℂ) - (Real.cos (k * y) : ℂ) =
        ((Real.cos (k * x) - Real.cos (k * y) : ℝ) : ℂ) := by
    norm_num
  rw [← mul_sub, hcast, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖a n‖ * |Real.cos (k * x) - Real.cos (k * y)| ≤
        ‖a n‖ * (2 ^ (1 - theta) * |k * x - k * y| ^ theta) :=
      mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
    _ = 2 ^ (1 - theta) * holderCoeffNorm theta a n *
          |x - y| ^ theta := by
      rw [harg, Real.mul_rpow (abs_nonneg k) (abs_nonneg (x - y)), hmode]
      unfold holderCoeffNorm
      ring

/-- Sharp `q = 2` fractional Sobolev--Hölder embedding on `[0,1]` for
`0 <= theta <= 1`: every exponent strictly below
`2 sigma - 1/2` is controlled by the genuine shift-one graph norm. -/
theorem unitInterval_shiftedFractional_embedding_holder
    {sigma theta : ℝ} (u : FractionalPowerSpace 1 sigma)
    (htheta : 0 ≤ theta) (htheta_one : theta ≤ 1)
    (hgap : theta < 2 * sigma - 1 / 2) (x y : ℝ) :
    ‖cosineSeries 1 (u : ℕ → ℂ) x -
        cosineSeries 1 (u : ℕ → ℂ) y‖ ≤
      2 ^ (1 - theta) *
        shiftedSpectralFractionalNorm 1 sigma (u : ℕ → ℂ) *
          (∑' n : ℕ,
            holderReciprocalFractionalPowerWeight sigma theta n) ^
              (1 / (2 : ℝ)) * |x - y| ^ theta := by
  let a : ℕ → ℂ := (u : ℕ → ℂ)
  let F : ℝ := 2 ^ (1 - theta) * |x - y| ^ theta
  have hsigma : 1 / 4 < sigma := by linarith
  have habs : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a] using
      u.coeff_norm_summable_of_sigma_gt_quarter (by norm_num) hsigma
  have hxsum : Summable fun n : ℕ => cosineSeriesTerm 1 a n x :=
    cosineSeriesTerm_summable_of_coeff_norm_summable habs x
  have hysum : Summable fun n : ℕ => cosineSeriesTerm 1 a n y :=
    cosineSeriesTerm_summable_of_coeff_norm_summable habs y
  have htrace : Summable fun n : ℕ =>
      holderReciprocalFractionalPowerWeight sigma theta n :=
    holderReciprocalFractionalPowerWeight_summable htheta hgap
  have hholder := summable_and_tsum_holderCoeffNorm_le
    (a := a) u.property htrace
  have hF : 0 ≤ F := mul_nonneg
    (Real.rpow_nonneg (by norm_num) (1 - theta))
    (Real.rpow_nonneg (abs_nonneg _) theta)
  have hmajor : Summable fun n : ℕ => F * holderCoeffNorm theta a n :=
    hholder.1.mul_left F
  have hterm : ∀ n : ℕ,
      ‖cosineSeriesTerm 1 a n x - cosineSeriesTerm 1 a n y‖ ≤
        F * holderCoeffNorm theta a n := by
    intro n
    have hn := norm_cosineSeriesTerm_sub_le_holderCoeffNorm
      htheta htheta_one a n x y
    calc
      ‖cosineSeriesTerm 1 a n x - cosineSeriesTerm 1 a n y‖ ≤
          2 ^ (1 - theta) * holderCoeffNorm theta a n *
            |x - y| ^ theta := hn
      _ = F * holderCoeffNorm theta a n := by
        dsimp [F]
        ring
  have hdiff : Summable fun n : ℕ =>
      cosineSeriesTerm 1 a n x - cosineSeriesTerm 1 a n y :=
    hxsum.sub hysum
  have hseries :
      (∑' n : ℕ,
        (cosineSeriesTerm 1 a n x - cosineSeriesTerm 1 a n y)) =
        cosineSeries 1 a x - cosineSeries 1 a y := by
    simpa [cosineSeries] using (hxsum.hasSum.sub hysum.hasSum).tsum_eq
  have hsumBound :
      ‖cosineSeries 1 a x - cosineSeries 1 a y‖ ≤
        F * ∑' n : ℕ, holderCoeffNorm theta a n := by
    have h := hdiff.hasSum.norm_le_of_bounded hmajor.hasSum hterm
    rw [hseries] at h
    rw [hholder.1.tsum_mul_left F] at h
    exact h
  have hcoeffBound :
      (∑' n : ℕ, holderCoeffNorm theta a n) ≤
        shiftedSpectralFractionalNorm 1 sigma a *
          (∑' n : ℕ,
            holderReciprocalFractionalPowerWeight sigma theta n) ^
              (1 / (2 : ℝ)) := by
    change (∑' n : ℕ, holderCoeffNorm theta a n) ≤
      Real.sqrt (shiftedSpectralFractionalEnergy 1 sigma a) *
        (∑' n : ℕ,
          holderReciprocalFractionalPowerWeight sigma theta n) ^
            (1 / (2 : ℝ))
    rw [Real.sqrt_eq_rpow,
      shiftedSpectralFractionalEnergy_one_eq_fractionalPowerEnergy]
    simpa [a] using hholder.2
  calc
    ‖cosineSeries 1 (u : ℕ → ℂ) x -
        cosineSeries 1 (u : ℕ → ℂ) y‖ =
        ‖cosineSeries 1 a x - cosineSeries 1 a y‖ := by rfl
    _ ≤ F * ∑' n : ℕ, holderCoeffNorm theta a n := hsumBound
    _ ≤ F *
        (shiftedSpectralFractionalNorm 1 sigma a *
          (∑' n : ℕ,
            holderReciprocalFractionalPowerWeight sigma theta n) ^
              (1 / (2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hcoeffBound hF
    _ = 2 ^ (1 - theta) *
        shiftedSpectralFractionalNorm 1 sigma (u : ℕ → ℂ) *
          (∑' n : ℕ,
            holderReciprocalFractionalPowerWeight sigma theta n) ^
              (1 / (2 : ℝ)) * |x - y| ^ theta := by
      dsimp [F, a]
      ring

#print axioms holderReciprocalFractionalPowerWeight_le_reduced
#print axioms holderReciprocalFractionalPowerWeight_summable
#print axioms holderReciprocalFractionalPowerWeight_nonneg
#print axioms holderCoeffNorm_nonneg
#print axioms neumannEigenvalue_rpow_half_sq
#print axioms sqrt_fractionalEnergy_mul_sqrt_holderTrace_eq_holderCoeffNorm
#print axioms summable_and_tsum_holderCoeffNorm_le
#print axioms abs_cos_sub_cos_le_rpow
#print axioms unitInterval_neumannFrequency_nonneg
#print axioms unitInterval_frequency_rpow_eq_eigenvalue_rpow_half
#print axioms norm_cosineSeriesTerm_sub_le_holderCoeffNorm
#print axioms unitInterval_shiftedFractional_embedding_holder

end ShenWork.Paper2.IntervalSharpSpectralHolderEmbedding
