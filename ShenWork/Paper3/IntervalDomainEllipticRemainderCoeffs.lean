/-
  Coefficient-space control of the quadratic elliptic source remainder.

  The main estimate is deliberately factored into a generic Bessel bridge and
  the concrete Taylor remainder.  This keeps the only measure-theoretic step
  (turning a pointwise product bound into an `ell^2` coefficient bound) reusable
  for the logistic and chemotactic remainders as well.
-/
import ShenWork.Paper3.IntervalDomainEllipticQuadraticRemainder
import ShenWork.Paper2.IntervalNeumannHeatGradientL2BrickB

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

/-- A pointwise `|f| <= B |g|` bound on the unit interval transfers to the
normalized Neumann cosine coefficients with the explicit Bessel constant `2`.

The functions are allowed to be arbitrary off `[0,1]`; only their restricted
`L^2` classes and the pointwise bound on `[0,1]` matter. -/
theorem cosineCoeffs_l2_norm_le_of_pointwise_mul
    {f g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg : MemLp g 2 (intervalMeasure 1))
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1))
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B * |g x|) :
    Summable (fun n => (cosineCoeffs f n) ^ 2) ∧
      Real.sqrt (∑' n, (cosineCoeffs f n) ^ 2) ≤
        2 * B * Real.sqrt (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
  have hdom_ae : ∀ᵐ x ∂ intervalMeasure 1, ‖f x‖ ≤ ‖B * g x‖ := by
    have hmem : ∀ᵐ x ∂ intervalMeasure 1, x ∈ Set.Icc (0 : ℝ) 1 := by
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem] with x hx
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hB] using hfg x hx
  have hf : MemLp f 2 (intervalMeasure 1) :=
    (hg.const_mul B).mono hf_meas hdom_ae
  rcases ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hf with
    ⟨hsum, hcoeff⟩
  refine ⟨hsum, hcoeff.trans ?_⟩
  have hf_sq_int : IntervalIntegrable (fun x => (f x) ^ 2) volume 0 1 := by
    have hf_sq := hf.integrable_sq
    change IntegrableOn (fun x => (f x) ^ 2) (Set.Icc (0 : ℝ) 1) volume at hf_sq
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hf_sq.mono_set Set.Ioc_subset_Icc_self
  have hg_sq_int : IntervalIntegrable (fun x => (g x) ^ 2) volume 0 1 := by
    have hg_sq := hg.integrable_sq
    change IntegrableOn (fun x => (g x) ^ 2) (Set.Icc (0 : ℝ) 1) volume at hg_sq
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact hg_sq.mono_set Set.Ioc_subset_Icc_self
  have hBg_sq_int : IntervalIntegrable
      (fun x => B ^ 2 * (g x) ^ 2) volume 0 1 :=
    hg_sq_int.const_mul (B ^ 2)
  have hsquares : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (f x) ^ 2 ≤ B ^ 2 * (g x) ^ 2 := by
    intro x hx
    have h := hfg x hx
    have hsquared := mul_self_le_mul_self (abs_nonneg (f x)) h
    calc
      (f x) ^ 2 = |f x| ^ 2 := by rw [sq_abs]
      _ ≤ (B * |g x|) ^ 2 := by simpa [pow_two] using hsquared
      _ = B ^ 2 * (g x) ^ 2 := by rw [mul_pow, sq_abs]
  have hintegral :
      (∫ x in (0 : ℝ)..1, (f x) ^ 2) ≤
        B ^ 2 * (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
    calc
      (∫ x in (0 : ℝ)..1, (f x) ^ 2) ≤
          ∫ x in (0 : ℝ)..1, B ^ 2 * (g x) ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num)
          hf_sq_int hBg_sq_int hsquares
      _ = B ^ 2 * (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
  have hg_integral_nonneg :
      0 ≤ ∫ x in (0 : ℝ)..1, (g x) ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg (g x))
  have hsqrt := Real.sqrt_le_sqrt hintegral
  calc
    2 * Real.sqrt (∫ x in (0 : ℝ)..1, (f x) ^ 2)
        ≤ 2 * Real.sqrt
            (B ^ 2 * (∫ x in (0 : ℝ)..1, (g x) ^ 2)) := by
          gcongr
    _ = 2 * B * Real.sqrt (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq_eq_abs,
            abs_of_nonneg hB]
          ring

/-- Physical perturbation profile on the interval. -/
def paper3IntervalPerturbationProfile
    (uStar : ℝ) (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  intervalDomainLift u x - uStar

/-- Physical nonlinear remainder in the elliptic source. -/
def paper3IntervalEllipticRemainderProfile
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3EllipticSourceRemainder p uStar (intervalDomainLift u x)

/-- On a fixed positive neighborhood of the equilibrium, the elliptic source
remainder has coefficient `ell^2` norm bounded by one sup factor times the
physical `L^2` perturbation. -/
theorem paper3IntervalEllipticRemainder_coeff_l2
    (p : CM2Params) {uStar M : ℝ} (huStar : 0 < uStar) (hM : 0 ≤ M)
    (u : intervalDomainPoint → ℝ)
    (hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hphi : MemLp (paper3IntervalPerturbationProfile uStar u) 2
      (intervalMeasure 1))
    (hrem_meas : AEStronglyMeasurable
      (paper3IntervalEllipticRemainderProfile p uStar u)
      (intervalMeasure 1))
    (hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u x| ≤ M) :
    ∃ K > 0,
      Summable (fun n =>
        (cosineCoeffs
          (paper3IntervalEllipticRemainderProfile p uStar u) n) ^ 2) ∧
      Real.sqrt (∑' n,
        (cosineCoeffs
          (paper3IntervalEllipticRemainderProfile p uStar u) n) ^ 2) ≤
        2 * K * M *
          Real.sqrt (∫ x in (0 : ℝ)..1,
            (paper3IntervalPerturbationProfile uStar u x) ^ 2) := by
  rcases paper3EllipticSource_quadratic_remainder p huStar with
    ⟨K, hK, hquad⟩
  refine ⟨K, hK, ?_⟩
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalEllipticRemainderProfile p uStar u x| ≤
        (K * M) * |paper3IntervalPerturbationProfile uStar u x| := by
    intro x hx
    have hq := hquad (intervalDomainLift u x) (hu_near x hx)
    have hs := hphi_sup x hx
    dsimp [paper3IntervalEllipticRemainderProfile,
      paper3IntervalPerturbationProfile] at hq hs ⊢
    calc
      |paper3EllipticSourceRemainder p uStar (intervalDomainLift u x)|
          ≤ K * |intervalDomainLift u x - uStar| ^ 2 := hq
      _ ≤ (K * M) * |intervalDomainLift u x - uStar| := by
        have hnonneg : 0 ≤ |intervalDomainLift u x - uStar| := abs_nonneg _
        have hprod : 0 ≤ K * |intervalDomainLift u x - uStar| *
            (M - |intervalDomainLift u x - uStar|) :=
          mul_nonneg (mul_nonneg hK.le hnonneg) (sub_nonneg.mpr hs)
        nlinarith
  simpa [mul_assoc] using
    (cosineCoeffs_l2_norm_le_of_pointwise_mul
      (B := K * M) (mul_nonneg hK.le hM) hphi hrem_meas hpoint)

#print axioms cosineCoeffs_l2_norm_le_of_pointwise_mul
#print axioms paper3IntervalEllipticRemainder_coeff_l2

end

end ShenWork.Paper3
