import ShenWork.Paper2.IntervalBFormCron2MildToWeakSpectral
import ShenWork.Paper2.IntervalBFormCron2NegativePartEnergy
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard
import ShenWork.PDE.IntervalDuhamelCoeffFTC

open MeasureTheory Set
open scoped BigOperators Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum
  (cosineMode cosineMode_neumann_left cosineMode_neumann_right)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- `IntervalDuhamelCoeffFTC`, restated in the sign/order used by the weak
coefficient test: `a'_k = -λ_k a_k + src_k`. -/
theorem localRestartCoeff_hasDerivAt_ode_neg_lam_add
    {a₀ : ℕ → ℝ} {src : ℝ → ℕ → ℝ} {T t : ℝ}
    (ht0 : 0 < t) (htT : t < T) (k : ℕ)
    (hcont : ContinuousOn (fun s => src s k) (Set.Icc (0 : ℝ) T)) :
    HasDerivAt (fun τ => localRestartCoeff a₀ src τ k)
      (-unitIntervalCosineEigenvalue k * localRestartCoeff a₀ src t k
        + src t k) t := by
  have h :=
    ShenWork.IntervalDuhamelCoeffFTC.localRestartCoeff_hasDerivAt_of_contSource_relative
        (a₀ := a₀) (a := src) (T := T) ht0 htT k hcont
  convert h using 1
  ring

/-- Absolute-time version of the restart coefficient ODE. -/
theorem localRestartCoeff_hasDerivAt_absolute_ode_neg_lam_add
    {a₀ : ℕ → ℝ} {src : ℝ → ℕ → ℝ} {c d t : ℝ}
    (hct : c < t) (htd : t < d) (k : ℕ)
    (hcont : ContinuousOn (fun s => src s k) (Set.Icc c d)) :
    HasDerivAt
      (fun τ => localRestartCoeff a₀ (fun ρ n => src (c + ρ) n)
        (τ - c) k)
      (-unitIntervalCosineEigenvalue k *
          localRestartCoeff a₀ (fun ρ n => src (c + ρ) n) (t - c) k
        + src t k) t := by
  have h :=
    ShenWork.IntervalDuhamelCoeffFTC.localRestartCoeff_hasDerivAt_of_contSource
      (a₀ := a₀) (a := src) hct htd k hcont
  convert h using 1
  ring

/-- One Neumann cosine mode tested against a spatial derivative.  This is the
single-mode gradient IBP
`∫ e_n' φ' = λ_n ∫ e_n φ`; the endpoint terms vanish because `e_n'` is zero
at `0` and `1`. -/
theorem cosineMode_gradient_testCoeff_eq
    (n : ℕ) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (φ' x) x)
    (hφ'_int : IntervalIntegrable φ' volume (0 : ℝ) 1) :
    (∫ x in (0 : ℝ)..1, deriv (cosineMode n) x * φ' x)
      = unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
  classical
  set a : ℝ := (n : ℝ) * Real.pi with ha
  have hmode_eq :
      (fun x : ℝ => deriv (cosineMode n) x)
        = fun x : ℝ => -a * Real.sin (a * x) := by
    funext x
    simp [ShenWork.CosineSpectrum.cosineMode_deriv, a]
  have hmode_deriv :
      ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => deriv (cosineMode n) y)
          (-unitIntervalCosineEigenvalue n * cosineMode n x) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
      convert (Real.hasDerivAt_sin (a * x)).comp x hlin using 1
      ring
    rw [hmode_eq]
    convert hsin.const_mul (-a) using 1
    · simp [cosineMode, unitIntervalCosineEigenvalue, a]
      ring
  have hmode'_int :
      IntervalIntegrable
        (fun x : ℝ => -unitIntervalCosineEigenvalue n * cosineMode n x)
        volume (0 : ℝ) 1 := by
    have hc :
        Continuous
          (fun x : ℝ => -unitIntervalCosineEigenvalue n * cosineMode n x) := by
      unfold cosineMode
      fun_prop
    exact hc.intervalIntegrable (0 : ℝ) 1
  have hibp :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x : ℝ => deriv (cosineMode n) x)
      (v := φ)
      (u' := fun x : ℝ => -unitIntervalCosineEigenvalue n * cosineMode n x)
      (v' := φ')
      hmode_deriv hφ hmode'_int hφ'_int
  rw [hibp]
  have hright : (fun x : ℝ => deriv (cosineMode n) x) 1 = 0 :=
    cosineMode_neumann_right n
  have hleft : (fun x : ℝ => deriv (cosineMode n) x) 0 = 0 :=
    cosineMode_neumann_left n
  rw [hright, hleft]
  simp only [zero_mul, sub_self, zero_sub]
  calc
    -(∫ x in (0 : ℝ)..1,
        (-unitIntervalCosineEigenvalue n * cosineMode n x) * φ x)
        =
      -(∫ x in (0 : ℝ)..1,
        (-unitIntervalCosineEigenvalue n) * (cosineMode n x * φ x)) := by
          congr 1
          exact intervalIntegral.integral_congr (fun x _hx => by ring)
    _ = unitIntervalCosineEigenvalue n * cosineTestCoeff φ n := by
          rw [intervalIntegral.integral_const_mul]
          simp [cosineTestCoeff]

/-- Summed tested ODE:
from `a'_k = -λ_k a_k + src_k`, after testing by `φ̂_k` and summing, the
Laplacian sum moves to the left. -/
theorem coefficient_tested_ode_tsum
    {a adot src φhat : ℕ → ℝ}
    (hode : ∀ k, adot k = -unitIntervalCosineEigenvalue k * a k + src k)
    (hlap : Summable (fun k => unitIntervalCosineEigenvalue k * a k * φhat k))
    (hsrc : Summable (fun k => src k * φhat k)) :
    (∑' k : ℕ, adot k * φhat k)
      + (∑' k : ℕ, unitIntervalCosineEigenvalue k * a k * φhat k)
        =
      ∑' k : ℕ, src k * φhat k := by
  classical
  have hsum :
      (∑' k : ℕ, adot k * φhat k)
        =
      -(∑' k : ℕ, unitIntervalCosineEigenvalue k * a k * φhat k)
        + (∑' k : ℕ, src k * φhat k) := by
    calc
      (∑' k : ℕ, adot k * φhat k)
          =
        ∑' k : ℕ,
          (-(unitIntervalCosineEigenvalue k * a k * φhat k)
            + src k * φhat k) := by
            exact tsum_congr (fun k => by
              rw [hode k]
              ring)
      _ =
          (∑' k : ℕ,
            -(unitIntervalCosineEigenvalue k * a k * φhat k))
            + (∑' k : ℕ, src k * φhat k) := by
            exact Summable.tsum_add hlap.neg hsrc
      _ =
          -(∑' k : ℕ, unitIntervalCosineEigenvalue k * a k * φhat k)
            + (∑' k : ℕ, src k * φhat k) := by
            rw [tsum_neg]
  rw [hsum]
  ring

/-- Coefficient-route data for the single test `φ = -u_-(t)`.  The analytic
work is isolated in the three tested-pairing fields: time Leibniz/tsum
interchange, full-series gradient IBP, and source-pairing identification. -/
structure NegativePartCoefficientWeakTestData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) where
  coeff : ℕ → ℝ
  coeffTimeDeriv : ℕ → ℝ
  sourceCoeff : ℕ → ℝ
  coeff_ode :
    ∀ k, coeffTimeDeriv k =
      -unitIntervalCosineEigenvalue k * coeff k + sourceCoeff k
  lap_summable :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * coeff k *
        cosineTestCoeff (negativePartTest u t) k)
  source_summable :
    Summable (fun k : ℕ =>
      sourceCoeff k * cosineTestCoeff (negativePartTest u t) k)
  time_leibniz_tsum :
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u t z) x * negativePartTest u t x
        ∂ intervalMeasure 1)
      =
    ∑' k : ℕ, coeffTimeDeriv k *
      cosineTestCoeff (negativePartTest u t) k
  gradient_ibp_tsum :
    (∫ x,
        deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1)
      =
    ∑' k : ℕ, unitIntervalCosineEigenvalue k * coeff k *
      cosineTestCoeff (negativePartTest u t) k
  source_pairing :
    (∑' k : ℕ, sourceCoeff k * cosineTestCoeff (negativePartTest u t) k)
      =
    p.χ₀ *
      (∫ x,
        truncatedChemFluxLifted p (u t) x
          * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1)
      + (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
        ∂ intervalMeasure 1)

/-- The coefficient route gives the negative-part weak identity, without using
the mild-to-classical bridge. -/
theorem negativePartWeakTestIdentityAt_of_coefficientData
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {t : ℝ}
    (H : NegativePartCoefficientWeakTestData p u t) :
    NegativePartWeakTestIdentityAt p u t := by
  classical
  let φhat : ℕ → ℝ := fun k => cosineTestCoeff (negativePartTest u t) k
  have htested :=
    coefficient_tested_ode_tsum
      (a := H.coeff) (adot := H.coeffTimeDeriv)
      (src := H.sourceCoeff) (φhat := φhat)
      H.coeff_ode H.lap_summable H.source_summable
  unfold NegativePartWeakTestIdentityAt
  calc
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u t z) x * negativePartTest u t x
        ∂ intervalMeasure 1)
      + (∫ x,
          deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
          ∂ intervalMeasure 1)
        =
      (∑' k : ℕ, H.coeffTimeDeriv k * φhat k)
        + (∑' k : ℕ,
            unitIntervalCosineEigenvalue k * H.coeff k * φhat k) := by
          rw [H.time_leibniz_tsum, H.gradient_ibp_tsum]
    _ = ∑' k : ℕ, H.sourceCoeff k * φhat k := htested
    _ =
      p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p (u t) x
            * deriv (negativePartTest u t) x
          ∂ intervalMeasure 1)
        + (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
          ∂ intervalMeasure 1) := H.source_pairing

/-- Horizon-level coefficient-route data for the negative-part weak identity. -/
structure NegativePartCoefficientMildSemigroupWeakData
    (p : CM2Params) (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) where
  coeff_weak :
    ∀ t, 0 < t → t ≤ T → NegativePartCoefficientWeakTestData p u t

/-- Direct coefficient-route constructor for the negative-part mild-to-weak
atom.  This bypasses the standard heat/DCT scaffolding fields: the coefficient
ODE, tested time/gradient pairings, and source pairing have already been
assembled inside `NegativePartCoefficientWeakTestData`. -/
theorem negativePartMildSemigroupWeakAfterFluxTestDuality_of_coefficientWeakTestData
    {p : CM2Params} {T : ℝ} {u₀ : intervalDomainPoint → ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (H : NegativePartCoefficientMildSemigroupWeakData p T u) :
    NegativePartMildSemigroupWeakAfterFluxTestDuality p T u₀ u := by
  intro _hmild t ht htT _hdual
  exact negativePartWeakTestIdentityAt_of_coefficientData
    (H.coeff_weak t ht htT)

/-- Coefficient-route data specialized to the faithful truncated Picard limit. -/
abbrev TruncatedNegativePartCoefficientWeakTestData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DT : TruncatedConjugateMildExistenceData p u₀) (t : ℝ) : Type :=
  NegativePartCoefficientWeakTestData p
    (truncatedConjugatePicardLimit p u₀ DT.T) t

/-- ATOM A1: coefficient-route weak identity for the negative-part test at the
truncated Picard limit. -/
theorem truncatedNegativePartWeakTestIdentityAt_of_coefficientData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DT : TruncatedConjugateMildExistenceData p u₀} {t : ℝ}
    (H : TruncatedNegativePartCoefficientWeakTestData p DT t) :
    NegativePartWeakTestIdentityAt p
      (truncatedConjugatePicardLimit p u₀ DT.T) t :=
  negativePartWeakTestIdentityAt_of_coefficientData H

end ShenWork.Paper2.BFormPositiveDatumNegPart
