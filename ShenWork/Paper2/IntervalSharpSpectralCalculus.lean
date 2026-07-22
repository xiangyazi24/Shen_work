import ShenWork.PDE.F1ProbeFractionalSmoothing
import ShenWork.PDE.FractionalPowerDerivative
import ShenWork.PDE.SectorialOperator
import ShenWork.Paper2.IntervalDomainLemma21

/-!
# Sharp spectral estimates for the shifted Neumann semigroup on `[0,1]`

This file supplies the coefficient-Hilbert (`q = 2`) part of the sharp
Paper-2 semigroup estimates.  The generator is

`A_omega = -Delta_N + omega`,

diagonal in the normalized cosine basis, with eigenvalues
`omega + (n * pi)^2`.  In particular, `omega = 1` gives the genuine
fractional graph norm requested in Lemmas 2.1--2.2, rather than the
sigma-independent `L^q` placeholder used by the current concrete data.

All infinite-series results retain their square-summability/domain hypotheses.
This is necessary: a bare function type does not itself carry `L^2` or
fractional-domain membership.
-/

noncomputable section

namespace ShenWork.Paper2.IntervalSharpSpectralCalculus

open ShenWork.PDE.ResolventEstimate
open ShenWork.PDE.AnalyticSemigroupGen
open ShenWork.PDE.F1ProbeFractionalMultiplier
open ShenWork.PDE.F1ProbeFractionalSmoothing
open ShenWork.PDE.FractionalPower

/-- Coefficient action of `(-Delta_N + omega)^sigma`. -/
def shiftedSpectralFractionalCoeff
    (omega sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((shiftedNeumannEigenvalue omega n) ^ sigma : ℝ) * a n

/-- Genuine shifted spectral fractional energy. -/
def shiftedSpectralFractionalEnergy
    (omega sigma : ℝ) (a : ℕ → ℂ) : ℝ :=
  coeffL2Energy (shiftedSpectralFractionalCoeff omega sigma a)

/-- Genuine shifted spectral fractional norm.  For `omega = 1`, its square is
`sum_n (1 + (n*pi)^2)^(2*sigma) * |a_n|^2`. -/
def shiftedSpectralFractionalNorm
    (omega sigma : ℝ) (a : ℕ → ℂ) : ℝ :=
  coeffL2Norm (shiftedSpectralFractionalCoeff omega sigma a)

theorem shiftedSpectralFractionalEnergy_nonneg
    (omega sigma : ℝ) (a : ℕ → ℂ) :
    0 ≤ shiftedSpectralFractionalEnergy omega sigma a := by
  exact tsum_nonneg fun n => sq_nonneg _

theorem shiftedSpectralFractionalNorm_nonneg
    (omega sigma : ℝ) (a : ℕ → ℂ) :
    0 ≤ shiftedSpectralFractionalNorm omega sigma a := by
  exact Real.sqrt_nonneg _

/-- Reusable Parseval lift from a uniform squared multiplier bound to a
coefficient-`L^2` norm bound. -/
theorem coeffL2Norm_le_of_sq_le
    {a b : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2)
    (hle : ∀ n, ‖b n‖ ^ 2 ≤ C ^ 2 * ‖a n‖ ^ 2) :
    coeffL2Norm b ≤ C * coeffL2Norm a := by
  have hb : Summable fun n : ℕ => ‖b n‖ ^ 2 := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) hle
      (ha.mul_left (C ^ 2))
  have hmajor : Summable fun n : ℕ => C ^ 2 * ‖a n‖ ^ 2 :=
    ha.mul_left (C ^ 2)
  have htsum := hb.tsum_le_tsum hle hmajor
  have henergy : coeffL2Energy b ≤ C ^ 2 * coeffL2Energy a := by
    simpa [coeffL2Energy, ha.tsum_mul_left] using htsum
  have hsqrt := Real.sqrt_le_sqrt henergy
  calc
    coeffL2Norm b = Real.sqrt (coeffL2Energy b) := rfl
    _ ≤ Real.sqrt (C ^ 2 * coeffL2Energy a) := hsqrt
    _ = C * coeffL2Norm a := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
      rfl

/-! ### Equivalence of positive spectral shifts -/

/-- Comparison of two positive shifted Neumann eigenvalues. -/
theorem shiftedNeumannEigenvalue_le_max_ratio_mul
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) (n : ℕ) :
    shiftedNeumannEigenvalue alpha n ≤
      max 1 (alpha / beta) * shiftedNeumannEigenvalue beta n := by
  let K : ℝ := max 1 (alpha / beta)
  let lam : ℝ := ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n
  have hlam : 0 ≤ lam := unitIntervalNeumannSpectrum_eigenvalue_nonneg n
  have hK_one : 1 ≤ K := le_max_left 1 (alpha / beta)
  have hK_ratio : alpha / beta ≤ K := le_max_right 1 (alpha / beta)
  have halpha_le : alpha ≤ K * beta := by
    have hmul := mul_le_mul_of_nonneg_right hK_ratio hbeta.le
    calc
      alpha = (alpha / beta) * beta := by
        field_simp [ne_of_gt hbeta]
      _ ≤ K * beta := hmul
  have hlam_le : lam ≤ K * lam := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hK_one hlam
  unfold shiftedNeumannEigenvalue
  change lam + alpha ≤ K * (lam + beta)
  calc
    lam + alpha ≤ K * lam + K * beta := add_le_add hlam_le halpha_le
    _ = K * (lam + beta) := by ring

/-- Per-mode comparison of two positive shifted fractional weights. -/
theorem shiftedSpectralFractionalCoeff_sq_le_of_pos
    {alpha beta sigma : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hsigma : 0 ≤ sigma) (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedSpectralFractionalCoeff alpha sigma a n‖ ^ 2 ≤
      (max 1 (alpha / beta) ^ sigma) ^ 2 *
        ‖shiftedSpectralFractionalCoeff beta sigma a n‖ ^ 2 := by
  let K : ℝ := max 1 (alpha / beta)
  let ra := shiftedNeumannEigenvalue alpha n
  let rb := shiftedNeumannEigenvalue beta n
  have hra : 0 ≤ ra := shiftedNeumannEigenvalue_nonneg halpha.le n
  have hrb : 0 ≤ rb := shiftedNeumannEigenvalue_nonneg hbeta.le n
  have hK : 0 ≤ K := (le_max_left 1 (alpha / beta)).trans' zero_le_one
  have hrle : ra ≤ K * rb := by
    simpa [ra, rb, K] using
      shiftedNeumannEigenvalue_le_max_ratio_mul halpha hbeta n
  have hpow : ra ^ sigma ≤ K ^ sigma * rb ^ sigma := by
    calc
      ra ^ sigma ≤ (K * rb) ^ sigma :=
        Real.rpow_le_rpow hra hrle hsigma
      _ = K ^ sigma * rb ^ sigma := Real.mul_rpow hK hrb
  have hleft : 0 ≤ ra ^ sigma := Real.rpow_nonneg hra sigma
  have hright : 0 ≤ K ^ sigma * rb ^ sigma :=
    mul_nonneg (Real.rpow_nonneg hK sigma) (Real.rpow_nonneg hrb sigma)
  have hmul : ra ^ sigma * ‖a n‖ ≤
      (K ^ sigma * rb ^ sigma) * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
  calc
    ‖shiftedSpectralFractionalCoeff alpha sigma a n‖ ^ 2 =
        (ra ^ sigma * ‖a n‖) ^ 2 := by
      rw [shiftedSpectralFractionalCoeff, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hleft]
    _ ≤ ((K ^ sigma * rb ^ sigma) * ‖a n‖) ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hleft (norm_nonneg _))
        (mul_nonneg hright (norm_nonneg _))).mpr hmul
    _ = (K ^ sigma) ^ 2 *
        ‖shiftedSpectralFractionalCoeff beta sigma a n‖ ^ 2 := by
      rw [shiftedSpectralFractionalCoeff, norm_mul, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hrb sigma)]
      ring
    _ = (max 1 (alpha / beta) ^ sigma) ^ 2 *
        ‖shiftedSpectralFractionalCoeff beta sigma a n‖ ^ 2 := rfl

/-- Fractional-domain membership transports between any two positive shifts. -/
theorem shiftedSpectralFractionalCoeff_l2_summable_of_pos
    {alpha beta sigma : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hsigma : 0 ≤ sigma) {a : ℕ → ℂ}
    (hbetaSum : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff beta sigma a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff alpha sigma a n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    (shiftedSpectralFractionalCoeff_sq_le_of_pos
      halpha hbeta hsigma a)
    (hbetaSum.mul_left ((max 1 (alpha / beta) ^ sigma) ^ 2))

/-- Norm comparison for positive shifted fractional graph norms. -/
theorem shiftedSpectralFractionalNorm_le_of_pos
    {alpha beta sigma : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hsigma : 0 ≤ sigma) {a : ℕ → ℂ}
    (hbetaSum : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff beta sigma a n‖ ^ 2) :
    shiftedSpectralFractionalNorm alpha sigma a ≤
      max 1 (alpha / beta) ^ sigma *
        shiftedSpectralFractionalNorm beta sigma a := by
  apply coeffL2Norm_le_of_sq_le
  · exact Real.rpow_nonneg
      (le_trans zero_le_one (le_max_left 1 (alpha / beta))) sigma
  · exact hbetaSum
  · exact shiftedSpectralFractionalCoeff_sq_le_of_pos
      halpha hbeta hsigma a

/-- Expanded Parseval-series formula for the shifted fractional energy. -/
theorem shiftedSpectralFractionalEnergy_eq_tsum
    {omega sigma : ℝ} (hbase : ∀ n, 0 ≤ shiftedNeumannEigenvalue omega n)
    (a : ℕ → ℂ) :
    shiftedSpectralFractionalEnergy omega sigma a =
      ∑' n : ℕ,
        ((shiftedNeumannEigenvalue omega n) ^ sigma) ^ 2 * ‖a n‖ ^ 2 := by
  unfold shiftedSpectralFractionalEnergy coeffL2Energy
  apply tsum_congr
  intro n
  rw [shiftedSpectralFractionalCoeff, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hbase n) sigma)]
  ring

/-- At shift one, the new energy is exactly the standard
`(I - Delta_N)^sigma` coefficient energy already used by the embedding layer. -/
theorem shiftedSpectralFractionalEnergy_one_eq_fractionalPowerEnergy
    (sigma : ℝ) (a : ℕ → ℂ) :
    shiftedSpectralFractionalEnergy 1 sigma a =
      ∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n := by
  rw [shiftedSpectralFractionalEnergy_eq_tsum]
  · apply tsum_congr
    intro n
    unfold shiftedNeumannEigenvalue fractionalPowerEnergyTerm
      fractionalPowerWeight neumannEigenvalue
    simp only [ShenWork.Paper3.unitIntervalNeumannSpectrum, div_one]
    rw [show ((n : ℝ) * Real.pi) ^ 2 =
        (n : ℝ) ^ 2 * Real.pi ^ 2 by ring]
    have hbase : 0 ≤ 1 + (n : ℝ) ^ 2 * Real.pi ^ 2 := by positivity
    change
      ((((n : ℝ) ^ 2 * Real.pi ^ 2 + 1) ^ sigma) ^ 2) * ‖a n‖ ^ 2 =
        ((1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ (2 * sigma)) * ‖a n‖ ^ 2
    rw [add_comm ((n : ℝ) ^ 2 * Real.pi ^ 2) 1]
    congr 1
    rw [← Real.rpow_natCast]
    calc
      ((1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ sigma) ^ (2 : ℝ) =
          (1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ (sigma * 2) :=
        (Real.rpow_mul hbase sigma 2).symm
      _ = (1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ (2 * sigma) := by ring_nf
  · intro n
    exact shiftedNeumannEigenvalue_nonneg (by norm_num) n

/-- The shifted norm sees the Neumann constant mode.  This is the simplest
formal witness that it is not the old unshifted/degenerate seminorm. -/
theorem shiftedSpectralFractionalNorm_one_constantMode
    (sigma : ℝ) :
    shiftedSpectralFractionalNorm 1 sigma
        (fun n => if n = 0 then (1 : ℂ) else 0) = 1 := by
  unfold shiftedSpectralFractionalNorm coeffL2Norm
    shiftedSpectralFractionalCoeff coeffL2Energy
  rw [tsum_eq_single 0]
  · norm_num [shiftedNeumannEigenvalue,
      ShenWork.Paper3.unitIntervalNeumannSpectrum]
  · intro n hn
    simp [hn]

/-- Sharp `t^{-sigma}` smoothing in the genuine shifted fractional norm. -/
theorem shiftedSpectralFractionalNorm_heat_le
    {omega sigma t : ℝ} (homega : 0 ≤ omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    shiftedSpectralFractionalNorm omega sigma
        (shiftedNeumannHeatCoeff omega t a) ≤
      ((sigma / Real.exp 1) ^ sigma * t ^ (-sigma)) * coeffL2Norm a := by
  simpa [shiftedSpectralFractionalNorm, shiftedSpectralFractionalCoeff,
    shiftedNeumannFractionalGeneratorHeatCoeff] using
    shiftedNeumannFractionalGeneratorHeatCoeff_l2_norm_le
      homega hsigma ht ha

/-! ## Exponentially damped sharp smoothing -/

/-- Scalar time-splitting estimate.  The spectral gap `omega` supplies the
`exp (-delta*t)` factor for every `0 < delta < omega`; the remaining fraction
of time supplies `t^{-sigma}` smoothing. -/
theorem rpow_mul_exp_neg_mul_le_with_decay
    {omega delta sigma r t : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) (hr : 0 ≤ r) (homegar : omega ≤ r)
    (ht : 0 < t) :
    r ^ sigma * Real.exp (-(r * t)) ≤
      ((sigma / Real.exp 1) ^ sigma *
          (1 - delta / omega) ^ (-sigma)) *
        t ^ (-sigma) * Real.exp (-(delta * t)) := by
  let theta : ℝ := delta / omega
  let c : ℝ := 1 - theta
  have htheta_pos : 0 < theta := div_pos hdelta homega
  have htheta_lt_one : theta < 1 := (div_lt_one homega).2 hdeltaomega
  have hc_pos : 0 < c := by
    dsimp [c]
    linarith
  have hfirst :=
    rpow_mul_exp_neg_mul_le hsigma hr (mul_pos hc_pos ht)
  have homega_theta : omega * theta = delta := by
    dsimp [theta]
    field_simp [ne_of_gt homega]
  have hdelta_le_rtheta : delta ≤ r * theta := by
    rw [← homega_theta]
    exact mul_le_mul_of_nonneg_right homegar htheta_pos.le
  have hdelta_t_le : delta * t ≤ r * (theta * t) := by
    calc
      delta * t ≤ (r * theta) * t :=
        mul_le_mul_of_nonneg_right hdelta_le_rtheta ht.le
      _ = r * (theta * t) := by ring
  have hsecond :
      Real.exp (-(r * (theta * t))) ≤ Real.exp (-(delta * t)) :=
    Real.exp_le_exp.mpr (neg_le_neg hdelta_t_le)
  have hfirst_nonneg :
      0 ≤ (sigma / Real.exp 1) ^ sigma * (c * t) ^ (-sigma) :=
    mul_nonneg
      (Real.rpow_nonneg (div_nonneg hsigma (Real.exp_nonneg 1)) sigma)
      (Real.rpow_nonneg (mul_pos hc_pos ht).le (-sigma))
  calc
    r ^ sigma * Real.exp (-(r * t)) =
        (r ^ sigma * Real.exp (-(r * (c * t)))) *
          Real.exp (-(r * (theta * t))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [c, theta]
      ring
    _ ≤ ((sigma / Real.exp 1) ^ sigma * (c * t) ^ (-sigma)) *
          Real.exp (-(r * (theta * t))) :=
      mul_le_mul_of_nonneg_right hfirst (Real.exp_nonneg _)
    _ ≤ ((sigma / Real.exp 1) ^ sigma * (c * t) ^ (-sigma)) *
          Real.exp (-(delta * t)) :=
      mul_le_mul_of_nonneg_left hsecond hfirst_nonneg
    _ = ((sigma / Real.exp 1) ^ sigma *
          (1 - delta / omega) ^ (-sigma)) *
        t ^ (-sigma) * Real.exp (-(delta * t)) := by
      rw [Real.mul_rpow hc_pos.le ht.le]
      dsimp [c, theta]
      ring

/-- Per-mode squared form of exponentially damped fractional smoothing. -/
theorem shiftedSpectralFractionalHeatCoeff_sq_le_with_decay
    {omega delta sigma t : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) (ht : 0 < t)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannHeatCoeff omega t a) n‖ ^ 2 ≤
      ((((sigma / Real.exp 1) ^ sigma *
          (1 - delta / omega) ^ (-sigma)) *
        t ^ (-sigma) * Real.exp (-(delta * t))) ^ 2) * ‖a n‖ ^ 2 := by
  let r := shiftedNeumannEigenvalue omega n
  let C := ((sigma / Real.exp 1) ^ sigma *
      (1 - delta / omega) ^ (-sigma)) *
    t ^ (-sigma) * Real.exp (-(delta * t))
  have hr : 0 ≤ r :=
    shiftedNeumannEigenvalue_nonneg homega.le n
  have homegar : omega ≤ r :=
    shiftedNeumannEigenvalue_ge_shift omega n
  have hcoef : r ^ sigma * Real.exp (-(r * t)) ≤ C := by
    simpa [C] using
      rpow_mul_exp_neg_mul_le_with_decay homega hdelta hdeltaomega
        hsigma hr homegar ht
  have hcoef_nonneg : 0 ≤ r ^ sigma * Real.exp (-(r * t)) :=
    mul_nonneg (Real.rpow_nonneg hr sigma) (Real.exp_nonneg _)
  have hcbase : 0 < 1 - delta / omega := by
    have : delta / omega < 1 := (div_lt_one homega).2 hdeltaomega
    linarith
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmul :
      r ^ sigma * Real.exp (-(r * t)) * ‖a n‖ ≤ C * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  calc
    ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannHeatCoeff omega t a) n‖ ^ 2 =
        (r ^ sigma * Real.exp (-(r * t)) * ‖a n‖) ^ 2 := by
      rw [shiftedSpectralFractionalCoeff, shiftedNeumannHeatCoeff,
        norm_mul, norm_mul]
      change
        (‖((r ^ sigma : ℝ) : ℂ)‖ *
          (‖((Real.exp (-(r * t)) : ℝ) : ℂ)‖ * ‖a n‖)) ^ 2 = _
      rw [Complex.norm_of_nonneg (Real.rpow_nonneg hr sigma),
        Complex.norm_of_nonneg (Real.exp_nonneg _)]
      ring
    _ ≤ (C * ‖a n‖) ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hcoef_nonneg (norm_nonneg _))
        (mul_nonneg hC_nonneg (norm_nonneg _))).mpr hmul
    _ = C ^ 2 * ‖a n‖ ^ 2 := by ring
    _ = ((((sigma / Real.exp 1) ^ sigma *
          (1 - delta / omega) ^ (-sigma)) *
        t ^ (-sigma) * Real.exp (-(delta * t))) ^ 2) * ‖a n‖ ^ 2 := rfl

/-- Lemma-2.1 smoothing shape, at the honest coefficient-`L^2` level, with
the shift `omega` providing the requested exponential decay. -/
theorem shiftedSpectralFractionalNorm_heat_le_with_decay
    {omega delta sigma t : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    shiftedSpectralFractionalNorm omega sigma
        (shiftedNeumannHeatCoeff omega t a) ≤
      ((sigma / Real.exp 1) ^ sigma *
          (1 - delta / omega) ^ (-sigma)) *
        t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a := by
  apply coeffL2Norm_le_of_sq_le
  · have hcbase : 0 < 1 - delta / omega := by
      have : delta / omega < 1 := (div_lt_one homega).2 hdeltaomega
      linarith
    positivity
  · exact ha
  · exact shiftedSpectralFractionalHeatCoeff_sq_le_with_decay
      homega hdelta hdeltaomega hsigma ht a

/-- Existential-constant packaging matching the first branch of Lemma 2.1. -/
theorem shiftedSpectralFractionalNorm_heat_decay_exists
    {omega delta sigma : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ => ‖a n‖ ^ 2) →
      shiftedSpectralFractionalNorm omega sigma
          (shiftedNeumannHeatCoeff omega t a) ≤
        C * t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a := by
  let c : ℝ := 1 - delta / omega
  let C : ℝ := (sigma / Real.exp 1) ^ sigma * c ^ (-sigma)
  have hc : 0 < c := by
    dsimp [c]
    have : delta / omega < 1 := (div_lt_one homega).2 hdeltaomega
    linarith
  have hC : 0 < C := by
    dsimp [C]
    rcases eq_or_lt_of_le hsigma with hzero | hpos
    · subst sigma
      norm_num
    · exact mul_pos
        (Real.rpow_pos_of_pos (div_pos hpos (Real.exp_pos 1)) _)
        (Real.rpow_pos_of_pos hc _)
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  simpa [C, c, mul_assoc] using
    shiftedSpectralFractionalNorm_heat_le_with_decay
      homega hdelta hdeltaomega hsigma ht ha

/-- Lemma-2.1 smoothing with the fixed graph norm
`(1 - Delta_N)^sigma` and the independently shifted heat generator
`omega - Delta_N`.  This is the exact shift convention needed when
`omega = p.mu`. -/
theorem shiftOneSpectralFractionalNorm_heat_decay_exists
    {omega delta sigma : ℝ} (homega : 0 < omega)
    (hdelta : 0 < delta) (hdeltaomega : delta < omega)
    (hsigma : 0 ≤ sigma) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ => ‖a n‖ ^ 2) →
      shiftedSpectralFractionalNorm 1 sigma
          (shiftedNeumannHeatCoeff omega t a) ≤
        C * t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a := by
  rcases shiftedSpectralFractionalNorm_heat_decay_exists
      homega hdelta hdeltaomega hsigma with ⟨C0, hC0, hbase⟩
  let K : ℝ := max 1 (1 / omega)
  let C : ℝ := K ^ sigma * C0
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left 1 (1 / omega))
  have hKpow : 0 < K ^ sigma := Real.rpow_pos_of_pos hK sigma
  have hC : 0 < C := mul_pos hKpow hC0
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  have hweighted : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannHeatCoeff omega t a) n‖ ^ 2 := by
    simpa [shiftedSpectralFractionalCoeff,
      shiftedNeumannFractionalGeneratorHeatCoeff] using
      shiftedNeumannFractionalGeneratorHeatCoeff_l2_summable
        homega.le hsigma ht ha
  have hcompare := shiftedSpectralFractionalNorm_le_of_pos
    (alpha := (1 : ℝ)) (beta := omega) (sigma := sigma)
    (by norm_num) homega hsigma hweighted
  have hsmooth := hbase t ht a ha
  calc
    shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannHeatCoeff omega t a) ≤
      K ^ sigma * shiftedSpectralFractionalNorm omega sigma
        (shiftedNeumannHeatCoeff omega t a) := by
          simpa [K] using hcompare
    _ ≤ K ^ sigma *
        (C0 * t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a) :=
      mul_le_mul_of_nonneg_left hsmooth hKpow.le
    _ = C * t ^ (-sigma) * Real.exp (-(delta * t)) * coeffL2Norm a := by
      dsimp [C]
      ring

/-! ## Fractional time difference -/

/-- Coefficients of `(exp (-t A_omega) - I)a`. -/
def shiftedNeumannHeatDifferenceCoeff
    (omega t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  shiftedNeumannHeatCoeff omega t a n - a n

/-- Per-mode sharp difference estimate
`|(exp (-t r) - 1)a_n| <= t^sigma |r^sigma a_n|`. -/
theorem shiftedNeumannHeatDifferenceCoeff_sq_le
    {omega t sigma : ℝ} (homega : 0 ≤ omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedNeumannHeatDifferenceCoeff omega t a n‖ ^ 2 ≤
      (t ^ sigma) ^ 2 *
        ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2 := by
  let r := shiftedNeumannEigenvalue omega n
  have hr : 0 ≤ r := shiftedNeumannEigenvalue_nonneg homega n
  have h :=
    ShenWork.Paper2.IntervalDomainLemma21.spectralCoeff_heat_difference_sq_le
      (lambda := r) (t := t) (sigma := sigma) (a := a n)
      hr ht hsigma hsigma_one
  calc
    ‖shiftedNeumannHeatDifferenceCoeff omega t a n‖ ^ 2 =
        ‖(((Real.exp (-(t * r)) - 1 : ℝ) : ℂ) * a n)‖ ^ 2 := by
      unfold shiftedNeumannHeatDifferenceCoeff shiftedNeumannHeatCoeff
      change ‖(Real.exp (-(r * t)) : ℂ) * a n - a n‖ ^ 2 = _
      congr 2
      have hexp : Real.exp (-(r * t)) = Real.exp (-(t * r)) := by
        congr 1
        ring
      rw [hexp]
      push_cast
      ring
    _ ≤ ((t ^ sigma * r ^ sigma) ^ 2) * ‖a n‖ ^ 2 := h
    _ = (t ^ sigma) ^ 2 *
        ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2 := by
      rw [shiftedSpectralFractionalCoeff, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr sigma)]
      ring

/-- Sharp `S(t)-I` estimate in the genuine shifted fractional domain. -/
theorem shiftedNeumannHeatDifferenceCoeff_l2_norm_le
    {omega t sigma : ℝ} (homega : 0 ≤ omega) (ht : 0 < t)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1)
    {a : ℕ → ℂ}
    (hfrac : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2) :
    coeffL2Norm (shiftedNeumannHeatDifferenceCoeff omega t a) ≤
      t ^ sigma * shiftedSpectralFractionalNorm omega sigma a := by
  exact coeffL2Norm_le_of_sq_le
    (Real.rpow_nonneg ht.le sigma) hfrac
    (shiftedNeumannHeatDifferenceCoeff_sq_le
      homega ht hsigma hsigma_one a)

/-- Existential-constant packaging matching the second branch of Lemma 2.1. -/
theorem shiftedNeumannHeatDifferenceCoeff_l2_norm_exists
    {omega sigma : ℝ} (homega : 0 ≤ omega)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ =>
        ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2) →
      coeffL2Norm (shiftedNeumannHeatDifferenceCoeff omega t a) ≤
        C * t ^ sigma * shiftedSpectralFractionalNorm omega sigma a := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro t ht a ha
  simpa using
    shiftedNeumannHeatDifferenceCoeff_l2_norm_le
      homega ht hsigma hsigma_one ha

/-- Lemma-2.1 difference estimate for the shifted heat generator, measured
against the fixed shift-one fractional graph norm. -/
theorem shiftedNeumannHeatDifferenceCoeff_shiftOneNorm_exists
    {omega sigma : ℝ} (homega : 0 < omega)
    (hsigma : 0 < sigma) (hsigma_one : sigma ≤ 1) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ =>
        ‖shiftedSpectralFractionalCoeff 1 sigma a n‖ ^ 2) →
      coeffL2Norm (shiftedNeumannHeatDifferenceCoeff omega t a) ≤
        C * t ^ sigma * shiftedSpectralFractionalNorm 1 sigma a := by
  let C : ℝ := max 1 (omega / 1) ^ sigma
  have hK : 0 < max 1 (omega / 1) :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (omega / 1))
  have hC : 0 < C := Real.rpow_pos_of_pos hK sigma
  refine ⟨C, hC, ?_⟩
  intro t ht a hfracOne
  have hfracOmega : Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma a n‖ ^ 2 :=
    shiftedSpectralFractionalCoeff_l2_summable_of_pos
      homega (by norm_num) hsigma.le hfracOne
  have hdiff := shiftedNeumannHeatDifferenceCoeff_l2_norm_le
    homega.le ht hsigma hsigma_one hfracOmega
  have hcompare := shiftedSpectralFractionalNorm_le_of_pos
    (alpha := omega) (beta := (1 : ℝ)) (sigma := sigma)
    homega (by norm_num) hsigma.le hfracOne
  have htfrac : 0 ≤ t ^ sigma := Real.rpow_nonneg ht.le sigma
  calc
    coeffL2Norm (shiftedNeumannHeatDifferenceCoeff omega t a) ≤
        t ^ sigma * shiftedSpectralFractionalNorm omega sigma a := hdiff
    _ ≤ t ^ sigma *
        (max 1 (omega / 1) ^ sigma *
          shiftedSpectralFractionalNorm 1 sigma a) :=
      mul_le_mul_of_nonneg_left hcompare htfrac
    _ = C * t ^ sigma * shiftedSpectralFractionalNorm 1 sigma a := by
      dsimp [C]
      ring

/-! ## Fractional Sobolev embeddings on the unit interval -/

/-- The existing fractional-power subtype is exactly the domain of the new
shift-one spectral norm, term by term. -/
theorem fractionalPowerEnergyTerm_one_eq_shiftedCoeff_sq
    (sigma : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    fractionalPowerEnergyTerm 1 sigma a n =
      ‖shiftedSpectralFractionalCoeff 1 sigma a n‖ ^ 2 := by
  unfold fractionalPowerEnergyTerm fractionalPowerWeight neumannEigenvalue
    shiftedSpectralFractionalCoeff shiftedNeumannEigenvalue
  simp only [ShenWork.Paper3.unitIntervalNeumannSpectrum, div_one]
  rw [show ((n : ℝ) * Real.pi) ^ 2 =
      (n : ℝ) ^ 2 * Real.pi ^ 2 by ring]
  have hbase : 0 ≤ 1 + (n : ℝ) ^ 2 * Real.pi ^ 2 := by positivity
  rw [add_comm ((n : ℝ) ^ 2 * Real.pi ^ 2) 1]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hbase sigma)]
  have hpow :
      ((1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ sigma) ^ 2 =
        (1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ (2 * sigma) := by
    rw [← Real.rpow_natCast
      ((1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ sigma) 2]
    calc
      ((1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ sigma) ^ (2 : ℝ) =
          (1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ (sigma * 2) :=
        (Real.rpow_mul hbase sigma 2).symm
      _ = (1 + (n : ℝ) ^ 2 * Real.pi ^ 2) ^ (2 * sigma) := by ring_nf
  rw [mul_pow, hpow]

theorem fractionalPowerSpace_iff_shiftedCoeff_summable
    (sigma : ℝ) (a : ℕ → ℂ) :
    Summable (fun n : ℕ => fractionalPowerEnergyTerm 1 sigma a n) ↔
      Summable (fun n : ℕ =>
        ‖shiftedSpectralFractionalCoeff 1 sigma a n‖ ^ 2) := by
  constructor
  · intro h
    exact h.congr fun n => fractionalPowerEnergyTerm_one_eq_shiftedCoeff_sq
      sigma a n
  · intro h
    exact h.congr fun n =>
      (fractionalPowerEnergyTerm_one_eq_shiftedCoeff_sq sigma a n).symm

/-- Sharp one-dimensional endpoint `X^sigma_2 -> C^0` for `sigma > 1/4`,
with the right side written using the new genuine spectral norm. -/
theorem unitInterval_shiftedFractional_embedding_C0
    {sigma : ℝ} (u : FractionalPowerSpace 1 sigma)
    (hsigma : 1 / 4 < sigma) (x : ℝ) :
    ‖cosineSeries 1 (u : ℕ → ℂ) x‖ ≤
      shiftedSpectralFractionalNorm 1 sigma (u : ℕ → ℂ) *
        (∑' n : ℕ, reciprocalFractionalPowerWeight 1 sigma n) ^
          (1 / (2 : ℝ)) := by
  change ‖cosineSeries 1 (u : ℕ → ℂ) x‖ ≤
    Real.sqrt (shiftedSpectralFractionalEnergy 1 sigma (u : ℕ → ℂ)) *
      (∑' n : ℕ, reciprocalFractionalPowerWeight 1 sigma n) ^
        (1 / (2 : ℝ))
  rw [Real.sqrt_eq_rpow,
    shiftedSpectralFractionalEnergy_one_eq_fractionalPowerEnergy]
  exact u.norm_cosineSeries_le_energy_trace_of_sigma_gt_quarter
    (by norm_num) hsigma x

/-- The embedded cosine representative is continuous at the sharp Hilbert
threshold `sigma > 1/4`. -/
theorem unitInterval_shiftedFractional_embedding_C0_continuous
    {sigma : ℝ} (u : FractionalPowerSpace 1 sigma)
    (hsigma : 1 / 4 < sigma) :
    Continuous fun x : ℝ => cosineSeries 1 (u : ℕ → ℂ) x :=
  u.continuous_cosineSeries_of_sigma_gt_quarter (by norm_num) hsigma

/-- Sharp one-derivative endpoint `X^sigma_2 -> C^1` for `sigma > 3/4`,
again with the genuine spectral norm on the right. -/
theorem unitInterval_shiftedFractional_embedding_C1_derivative
    {sigma : ℝ} (u : FractionalPowerSpace 1 sigma)
    (hsigma : 3 / 4 < sigma) (x : ℝ) :
    ‖cosineSeriesDerivative 1 (u : ℕ → ℂ) x‖ ≤
      shiftedSpectralFractionalNorm 1 sigma (u : ℕ → ℂ) *
        (∑' n : ℕ,
          derivativeReciprocalFractionalPowerWeight 1 sigma n) ^
            (1 / (2 : ℝ)) := by
  change ‖cosineSeriesDerivative 1 (u : ℕ → ℂ) x‖ ≤
    Real.sqrt (shiftedSpectralFractionalEnergy 1 sigma (u : ℕ → ℂ)) *
      (∑' n : ℕ,
        derivativeReciprocalFractionalPowerWeight 1 sigma n) ^
          (1 / (2 : ℝ))
  rw [Real.sqrt_eq_rpow,
    shiftedSpectralFractionalEnergy_one_eq_fractionalPowerEnergy]
  exact u.norm_cosineSeriesDerivative_le_energy_trace_of_sigma_gt_three_quarters
    (by norm_num) hsigma x

/-- The formal derivative series is continuous at the sharp Hilbert threshold
`sigma > 3/4`. -/
theorem unitInterval_shiftedFractional_embedding_C1_derivative_continuous
    {sigma : ℝ} (u : FractionalPowerSpace 1 sigma)
    (hsigma : 3 / 4 < sigma) :
    Continuous fun x : ℝ =>
      cosineSeriesDerivative 1 (u : ℕ → ℂ) x :=
  u.continuous_cosineSeriesDerivative_of_sigma_gt_three_quarters
    (by norm_num) hsigma

/-! ## Divergence/gradient heat decay -/

/-- In one space dimension, divergence after Neumann heat flow has the sine
coefficient multiplier `sqrt(lambda_n) exp (-(lambda_n + omega)t)`. -/
def shiftedNeumannDivergenceHeatCoeff
    (omega t : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n) ^
      (1 / 2 : ℝ) : ℝ) * shiftedNeumannHeatCoeff omega t a n

/-- Separate the spectral shift from the half-generator multiplier. -/
theorem shiftedNeumannDivergenceHeatCoeff_eq_exp_mul_halfGenerator
    (omega t : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    shiftedNeumannDivergenceHeatCoeff omega t a n =
      (Real.exp (-(omega * t)) : ℂ) *
        shiftedNeumannFractionalGeneratorHeatCoeff
          0 (1 / 2 : ℝ) t a n := by
  unfold shiftedNeumannDivergenceHeatCoeff
    shiftedNeumannFractionalGeneratorHeatCoeff shiftedNeumannHeatCoeff
    shiftedNeumannEigenvalue
  rw [show
      -((ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n + omega) * t) =
        -(omega * t) +
          -(ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n * t) by ring,
    Real.exp_add]
  simp only [add_zero]
  push_cast
  ring

/-- Per-mode sharp `t^{-1/2} exp (-omega*t)` divergence estimate. -/
theorem shiftedNeumannDivergenceHeatCoeff_sq_le
    {omega t : ℝ} (ht : 0 < t)
    (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedNeumannDivergenceHeatCoeff omega t a n‖ ^ 2 ≤
      ((((1 / 2 : ℝ) / Real.exp 1) ^ (1 / 2 : ℝ) *
          t ^ (-(1 / 2 : ℝ)) * Real.exp (-(omega * t))) ^ 2) *
        ‖a n‖ ^ 2 := by
  have hhalf :=
    shiftedNeumannFractionalGeneratorHeatCoeff_sq_le
      (ω := (0 : ℝ)) (σ := (1 / 2 : ℝ)) (t := t)
      (by norm_num) (by norm_num) ht a n
  rw [shiftedNeumannDivergenceHeatCoeff_eq_exp_mul_halfGenerator,
    norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
  calc
    (Real.exp (-(omega * t)) *
        ‖shiftedNeumannFractionalGeneratorHeatCoeff
          0 (1 / 2 : ℝ) t a n‖) ^ 2 ≤
      (Real.exp (-(omega * t))) ^ 2 *
        (((((1 / 2 : ℝ) / Real.exp 1) ^ (1 / 2 : ℝ) *
          t ^ (-(1 / 2 : ℝ))) ^ 2) * ‖a n‖ ^ 2) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hhalf (sq_nonneg _)
    _ = ((((1 / 2 : ℝ) / Real.exp 1) ^ (1 / 2 : ℝ) *
          t ^ (-(1 / 2 : ℝ)) * Real.exp (-(omega * t))) ^ 2) *
        ‖a n‖ ^ 2 := by ring

/-- Coefficient-`L^2` sharp divergence decay, stronger than the
`(1+t^{-1/2})` form in Lemma 2.3. -/
theorem shiftedNeumannDivergenceHeatCoeff_l2_norm_le
    {omega t : ℝ} (ht : 0 < t)
    {a : ℕ → ℂ} (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    coeffL2Norm (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
      (((1 / 2 : ℝ) / Real.exp 1) ^ (1 / 2 : ℝ) *
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-(omega * t))) * coeffL2Norm a := by
  apply coeffL2Norm_le_of_sq_le
  · positivity
  · exact ha
  · exact shiftedNeumannDivergenceHeatCoeff_sq_le ht a

/-- Lemma-2.3 factor packaging at `q=2`. -/
theorem shiftedNeumannDivergenceHeatCoeff_l2_decay_exists
    (omega : ℝ) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ => ‖a n‖ ^ 2) →
      coeffL2Norm (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
        C * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(omega * t)) * coeffL2Norm a := by
  let C : ℝ := ((1 / 2 : ℝ) / Real.exp 1) ^ (1 / 2 : ℝ)
  have hC : 0 < C := by
    exact Real.rpow_pos_of_pos
      (div_pos (by norm_num) (Real.exp_pos 1)) _
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  calc
    coeffL2Norm (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
        C * t ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(omega * t)) * coeffL2Norm a := by
      simpa [C] using
        shiftedNeumannDivergenceHeatCoeff_l2_norm_le ht ha
    _ ≤ C * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-(omega * t)) * coeffL2Norm a := by
      have htinv : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
      have hCx :
          C * t ^ (-(1 / 2 : ℝ)) ≤
            C * (1 + t ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (by linarith) hC.le
      have htail :
          0 ≤ Real.exp (-(omega * t)) * coeffL2Norm a :=
        mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
      calc
        C * t ^ (-(1 / 2 : ℝ)) * Real.exp (-(omega * t)) * coeffL2Norm a =
            (C * t ^ (-(1 / 2 : ℝ))) *
              (Real.exp (-(omega * t)) * coeffL2Norm a) := by ring
        _ ≤ (C * (1 + t ^ (-(1 / 2 : ℝ)))) *
              (Real.exp (-(omega * t)) * coeffL2Norm a) :=
          mul_le_mul_of_nonneg_right hCx htail
        _ = C * (1 + t ^ (-(1 / 2 : ℝ))) *
              Real.exp (-(omega * t)) * coeffL2Norm a := by ring

/-! ## Fractional divergence decay -/

/-- Scalar multiplier core for Lemma 2.4.  The factor
`r^sigma sqrt(lambda)` is bounded by `r^(sigma+1/2)`, after which the damped
fractional smoothing estimate applies at decay rate `omega/2`. -/
theorem shiftedFractionalDivergence_multiplier_le
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (n : ℕ) :
    (shiftedNeumannEigenvalue omega n) ^ sigma *
        (ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n) ^
          (1 / 2 : ℝ) *
        Real.exp (-(shiftedNeumannEigenvalue omega n * t)) ≤
      (((sigma + 1 / 2 : ℝ) / Real.exp 1) ^ (sigma + 1 / 2 : ℝ) *
          (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
        t ^ (-(sigma + 1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t)) := by
  let lam := ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n
  let r := shiftedNeumannEigenvalue omega n
  let rho : ℝ := sigma + 1 / 2
  have hlam : 0 ≤ lam :=
    unitIntervalNeumannSpectrum_eigenvalue_nonneg n
  have hr : 0 ≤ r := shiftedNeumannEigenvalue_nonneg homega.le n
  have homegar : omega ≤ r := shiftedNeumannEigenvalue_ge_shift omega n
  have hr_pos : 0 < r := homega.trans_le homegar
  have hlamr : lam ≤ r := by
    dsimp [lam, r, shiftedNeumannEigenvalue]
    linarith
  have hhalf : lam ^ (1 / 2 : ℝ) ≤ r ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hlam hlamr (by norm_num)
  have hpower :
      r ^ sigma * lam ^ (1 / 2 : ℝ) ≤
        r ^ sigma * r ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hr sigma)
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    linarith
  have hdelta : 0 < omega / 2 := by linarith
  have hdeltaomega : omega / 2 < omega := by linarith
  have hdamped :=
    rpow_mul_exp_neg_mul_le_with_decay
      (omega := omega) (delta := omega / 2) (sigma := rho)
      (r := r) (t := t) homega hdelta hdeltaomega hrho hr homegar ht
  calc
    r ^ sigma * lam ^ (1 / 2 : ℝ) * Real.exp (-(r * t)) ≤
        (r ^ sigma * r ^ (1 / 2 : ℝ)) * Real.exp (-(r * t)) :=
      mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _)
    _ = r ^ rho * Real.exp (-(r * t)) := by
      dsimp [rho]
      rw [Real.rpow_add hr_pos]
    _ ≤ (((rho / Real.exp 1) ^ rho *
          (1 - (omega / 2) / omega) ^ (-rho)) *
        t ^ (-rho) * Real.exp (-((omega / 2) * t))) := hdamped
    _ = (((sigma + 1 / 2 : ℝ) / Real.exp 1) ^
          (sigma + 1 / 2 : ℝ) *
          (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
        t ^ (-(sigma + 1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t)) := by rfl

/-- Per-mode squared fractional-divergence estimate. -/
theorem shiftedFractionalDivergenceHeatCoeff_sq_le
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) (a : ℕ → ℂ) (n : ℕ) :
    ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) n‖ ^ 2 ≤
      (((((sigma + 1 / 2 : ℝ) / Real.exp 1) ^
          (sigma + 1 / 2 : ℝ) *
          (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
        t ^ (-(sigma + 1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t))) ^ 2) * ‖a n‖ ^ 2 := by
  let lam := ShenWork.Paper3.unitIntervalNeumannSpectrum.eigenvalue n
  let r := shiftedNeumannEigenvalue omega n
  let C := (((sigma + 1 / 2 : ℝ) / Real.exp 1) ^
      (sigma + 1 / 2 : ℝ) *
      (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
    t ^ (-(sigma + 1 / 2 : ℝ)) * Real.exp (-((omega / 2) * t))
  have hlam : 0 ≤ lam := unitIntervalNeumannSpectrum_eigenvalue_nonneg n
  have hr : 0 ≤ r := shiftedNeumannEigenvalue_nonneg homega.le n
  have hcoef :
      r ^ sigma * lam ^ (1 / 2 : ℝ) * Real.exp (-(r * t)) ≤ C := by
    simpa [lam, r, C] using
      shiftedFractionalDivergence_multiplier_le homega hsigma ht n
  have hcoef_nonneg :
      0 ≤ r ^ sigma * lam ^ (1 / 2 : ℝ) * Real.exp (-(r * t)) :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hr sigma)
        (Real.rpow_nonneg hlam (1 / 2 : ℝ)))
      (Real.exp_nonneg _)
  have hratio : (omega / 2) / omega = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt homega]
  have hC : 0 ≤ C := by
    dsimp [C]
    rw [hratio]
    positivity
  have hmul :
      (r ^ sigma * lam ^ (1 / 2 : ℝ) * Real.exp (-(r * t))) * ‖a n‖ ≤
        C * ‖a n‖ :=
    mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  calc
    ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) n‖ ^ 2 =
        ((r ^ sigma * lam ^ (1 / 2 : ℝ) * Real.exp (-(r * t))) *
          ‖a n‖) ^ 2 := by
      unfold shiftedSpectralFractionalCoeff
        shiftedNeumannDivergenceHeatCoeff shiftedNeumannHeatCoeff
      change
        ‖((r ^ sigma : ℝ) : ℂ) *
          (((lam ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            ((Real.exp (-(r * t)) : ℂ) * a n))‖ ^ 2 = _
      rw [norm_mul, norm_mul, norm_mul,
        Complex.norm_of_nonneg (Real.rpow_nonneg hr sigma),
        Complex.norm_of_nonneg (Real.rpow_nonneg hlam (1 / 2 : ℝ)),
        Complex.norm_of_nonneg (Real.exp_nonneg _)]
      ring
    _ ≤ (C * ‖a n‖) ^ 2 :=
      (sq_le_sq₀
        (mul_nonneg hcoef_nonneg (norm_nonneg _))
        (mul_nonneg hC (norm_nonneg _))).mpr hmul
    _ = C ^ 2 * ‖a n‖ ^ 2 := by ring
    _ = (((((sigma + 1 / 2 : ℝ) / Real.exp 1) ^
          (sigma + 1 / 2 : ℝ) *
          (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
        t ^ (-(sigma + 1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t))) ^ 2) * ‖a n‖ ^ 2 := rfl

/-- The fractionally weighted divergence output is square summable for every
square-summable input. -/
theorem shiftedFractionalDivergenceHeatCoeff_l2_summable
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    Summable fun n : ℕ =>
      ‖shiftedSpectralFractionalCoeff omega sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) n‖ ^ 2 := by
  apply Summable.of_nonneg_of_le
    (fun n => sq_nonneg _)
    (shiftedFractionalDivergenceHeatCoeff_sq_le
      homega hsigma ht a)
    (ha.mul_left
      (((((sigma + 1 / 2 : ℝ) / Real.exp 1) ^
          (sigma + 1 / 2 : ℝ) *
          (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
        t ^ (-(sigma + 1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t))) ^ 2))

/-- Strong coefficient-`L^2` fractional-divergence estimate of total order
`sigma+1/2`. -/
theorem shiftedFractionalDivergenceHeatCoeff_l2_norm_le
    {omega sigma t : ℝ} (homega : 0 < omega) (hsigma : 0 ≤ sigma)
    (ht : 0 < t) {a : ℕ → ℂ}
    (ha : Summable fun n : ℕ => ‖a n‖ ^ 2) :
    shiftedSpectralFractionalNorm omega sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
      ((((sigma + 1 / 2 : ℝ) / Real.exp 1) ^
          (sigma + 1 / 2 : ℝ) *
          (1 - (omega / 2) / omega) ^ (-(sigma + 1 / 2 : ℝ))) *
        t ^ (-(sigma + 1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t))) * coeffL2Norm a := by
  apply coeffL2Norm_le_of_sq_le
  · have hratio : (omega / 2) / omega = (1 / 2 : ℝ) := by
      field_simp [ne_of_gt homega]
    rw [hratio]
    positivity
  · exact ha
  · exact shiftedFractionalDivergenceHeatCoeff_sq_le
      homega hsigma ht a

/-- Lemma-2.4 factor packaging at `q=2`. -/
theorem shiftedFractionalDivergenceHeatCoeff_l2_decay_exists
    {omega sigma : ℝ} (homega : 0 < omega) (hsigma : 0 < sigma) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ => ‖a n‖ ^ 2) →
      shiftedSpectralFractionalNorm omega sigma
          (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by
  let rho : ℝ := sigma + 1 / 2
  let C : ℝ := (rho / Real.exp 1) ^ rho *
    (1 - (omega / 2) / omega) ^ (-rho)
  have hrho : 0 < rho := by
    dsimp [rho]
    linarith
  have hratio : (omega / 2) / omega = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt homega]
  have hC : 0 < C := by
    dsimp [C]
    rw [hratio]
    exact mul_pos
      (Real.rpow_pos_of_pos (div_pos hrho (Real.exp_pos 1)) _)
      (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  have hstrong :=
    shiftedFractionalDivergenceHeatCoeff_l2_norm_le
      homega hsigma.le ht ha
  have hsplit :
      t ^ (-rho) = t ^ (-sigma) * t ^ (-(1 / 2 : ℝ)) := by
    calc
      t ^ (-rho) = t ^ ((-sigma) + (-(1 / 2 : ℝ))) := by
        congr 1
        dsimp [rho]
        ring
      _ = t ^ (-sigma) * t ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_add ht (-sigma) (-(1 / 2 : ℝ))
  calc
    shiftedSpectralFractionalNorm omega sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
      C * t ^ (-rho) * Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by
        simpa [C, rho] using hstrong
    _ = C * t ^ (-sigma) * t ^ (-(1 / 2 : ℝ)) *
          Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by
        rw [hsplit]
        ring
    _ ≤ C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by
      have hx : t ^ (-(1 / 2 : ℝ)) ≤ 1 + t ^ (-(1 / 2 : ℝ)) := by
        linarith [Real.rpow_nonneg ht.le (-(1 / 2 : ℝ))]
      have hleft : 0 ≤ C * t ^ (-sigma) :=
        mul_nonneg hC.le (Real.rpow_nonneg ht.le _)
      have htail :
          0 ≤ Real.exp (-((omega / 2) * t)) * coeffL2Norm a :=
        mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)
      calc
        C * t ^ (-sigma) * t ^ (-(1 / 2 : ℝ)) *
            Real.exp (-((omega / 2) * t)) * coeffL2Norm a =
          ((C * t ^ (-sigma)) * t ^ (-(1 / 2 : ℝ))) *
            (Real.exp (-((omega / 2) * t)) * coeffL2Norm a) := by ring
        _ ≤ ((C * t ^ (-sigma)) * (1 + t ^ (-(1 / 2 : ℝ)))) *
            (Real.exp (-((omega / 2) * t)) * coeffL2Norm a) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hx hleft) htail
        _ = C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
            Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by ring

/-- Lemma-2.4 packaging with the fixed shift-one fractional graph norm and
the independently shifted generator `omega - Delta_N`. -/
theorem shiftOneFractionalDivergenceHeatCoeff_l2_decay_exists
    {omega sigma : ℝ} (homega : 0 < omega) (hsigma : 0 < sigma) :
    ∃ C > 0, ∀ t > 0, ∀ a : ℕ → ℂ,
      Summable (fun n : ℕ => ‖a n‖ ^ 2) →
      shiftedSpectralFractionalNorm 1 sigma
          (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
        C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by
  rcases shiftedFractionalDivergenceHeatCoeff_l2_decay_exists
      homega hsigma with ⟨C0, hC0, hbase⟩
  let K : ℝ := max 1 (1 / omega)
  let C : ℝ := K ^ sigma * C0
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left 1 (1 / omega))
  have hKpow : 0 < K ^ sigma := Real.rpow_pos_of_pos hK sigma
  have hC : 0 < C := mul_pos hKpow hC0
  refine ⟨C, hC, ?_⟩
  intro t ht a ha
  have hweighted := shiftedFractionalDivergenceHeatCoeff_l2_summable
    homega hsigma.le ht ha
  have hcompare := shiftedSpectralFractionalNorm_le_of_pos
    (alpha := (1 : ℝ)) (beta := omega) (sigma := sigma)
    (by norm_num) homega hsigma.le hweighted
  have hdecay := hbase t ht a ha
  calc
    shiftedSpectralFractionalNorm 1 sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) ≤
      K ^ sigma * shiftedSpectralFractionalNorm omega sigma
        (shiftedNeumannDivergenceHeatCoeff omega t a) := by
          simpa [K] using hcompare
    _ ≤ K ^ sigma *
        (C0 * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) * coeffL2Norm a) :=
      mul_le_mul_of_nonneg_left hdecay hKpow.le
    _ = C * t ^ (-sigma) * (1 + t ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((omega / 2) * t)) * coeffL2Norm a := by
      dsimp [C]
      ring

#print axioms shiftedSpectralFractionalEnergy_nonneg
#print axioms shiftedSpectralFractionalNorm_nonneg
#print axioms coeffL2Norm_le_of_sq_le
#print axioms shiftedSpectralFractionalEnergy_eq_tsum
#print axioms shiftedSpectralFractionalEnergy_one_eq_fractionalPowerEnergy
#print axioms shiftedSpectralFractionalNorm_one_constantMode
#print axioms shiftedSpectralFractionalNorm_heat_le
#print axioms rpow_mul_exp_neg_mul_le_with_decay
#print axioms shiftedSpectralFractionalHeatCoeff_sq_le_with_decay
#print axioms shiftedSpectralFractionalNorm_heat_le_with_decay
#print axioms shiftedSpectralFractionalNorm_heat_decay_exists
#print axioms shiftedNeumannHeatDifferenceCoeff_sq_le
#print axioms shiftedNeumannHeatDifferenceCoeff_l2_norm_le
#print axioms shiftedNeumannHeatDifferenceCoeff_l2_norm_exists
#print axioms fractionalPowerEnergyTerm_one_eq_shiftedCoeff_sq
#print axioms fractionalPowerSpace_iff_shiftedCoeff_summable
#print axioms unitInterval_shiftedFractional_embedding_C0
#print axioms unitInterval_shiftedFractional_embedding_C0_continuous
#print axioms unitInterval_shiftedFractional_embedding_C1_derivative
#print axioms unitInterval_shiftedFractional_embedding_C1_derivative_continuous
#print axioms shiftedNeumannDivergenceHeatCoeff_eq_exp_mul_halfGenerator
#print axioms shiftedNeumannDivergenceHeatCoeff_sq_le
#print axioms shiftedNeumannDivergenceHeatCoeff_l2_norm_le
#print axioms shiftedNeumannDivergenceHeatCoeff_l2_decay_exists
#print axioms shiftedFractionalDivergence_multiplier_le
#print axioms shiftedFractionalDivergenceHeatCoeff_sq_le
#print axioms shiftedFractionalDivergenceHeatCoeff_l2_norm_le
#print axioms shiftedFractionalDivergenceHeatCoeff_l2_decay_exists
#print axioms shiftedNeumannEigenvalue_le_max_ratio_mul
#print axioms shiftedSpectralFractionalCoeff_sq_le_of_pos
#print axioms shiftedSpectralFractionalCoeff_l2_summable_of_pos
#print axioms shiftedSpectralFractionalNorm_le_of_pos
#print axioms shiftOneSpectralFractionalNorm_heat_decay_exists
#print axioms shiftedNeumannHeatDifferenceCoeff_shiftOneNorm_exists
#print axioms shiftedFractionalDivergenceHeatCoeff_l2_summable
#print axioms shiftOneFractionalDivergenceHeatCoeff_l2_decay_exists

end ShenWork.Paper2.IntervalSharpSpectralCalculus
