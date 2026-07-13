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
open ShenWork.PDE
open ShenWork.PDE.ResolventEstimate

noncomputable section

/-- Additivity of the normalized cosine coefficient under the minimal
interval-integrability hypotheses. -/
theorem cosineCoeffs_add_of_intervalIntegrable
    {f g : ℝ → ℝ} (k : ℕ)
    (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    cosineCoeffs (fun x => f x + g x) k =
      cosineCoeffs f k + cosineCoeffs g k := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  let w : ℝ → ℝ := fun x => Real.cos ((k : ℝ) * Real.pi * x)
  have hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1) := by
    exact (Real.continuous_cos.comp (by fun_prop)).continuousOn
  have hfw : IntervalIntegrable (fun x => w x * f x) volume 0 1 :=
    hf.continuousOn_mul hw
  have hgw : IntervalIntegrable (fun x => w x * g x) volume 0 1 :=
    hg.continuousOn_mul hw
  have hsplit :
      (∫ x in (0 : ℝ)..1, w x * (f x + g x)) =
        (∫ x in (0 : ℝ)..1, w x * f x) +
          ∫ x in (0 : ℝ)..1, w x * g x := by
    rw [← intervalIntegral.integral_add hfw hgw]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hsplit]
  ring

/-- Scalar linearity of the normalized cosine coefficient under the minimal
interval-integrability hypothesis. -/
theorem cosineCoeffs_const_mul_of_intervalIntegrable
    {f : ℝ → ℝ} (c : ℝ) (k : ℕ)
    (hf : IntervalIntegrable f volume 0 1) :
    cosineCoeffs (fun x => c * f x) k = c * cosineCoeffs f k := by
  rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
  let w : ℝ → ℝ := fun x => Real.cos ((k : ℝ) * Real.pi * x)
  have hw : ContinuousOn w (Set.uIcc (0 : ℝ) 1) := by
    exact (Real.continuous_cos.comp (by fun_prop)).continuousOn
  have hfw : IntervalIntegrable (fun x => w x * f x) volume 0 1 :=
    hf.continuousOn_mul hw
  have hsplit :
      (∫ x in (0 : ℝ)..1, w x * (c * f x)) =
        c * ∫ x in (0 : ℝ)..1, w x * f x := by
    calc
      (∫ x in (0 : ℝ)..1, w x * (c * f x)) =
          ∫ x in (0 : ℝ)..1, c * (w x * f x) := by
        refine intervalIntegral.integral_congr (fun x _ => ?_)
        ring
      _ = c * ∫ x in (0 : ℝ)..1, w x * f x := by
        rw [intervalIntegral.integral_const_mul]
  rw [hsplit]
  ring

/-- Cosine coefficients only depend on values on the physical unit interval. -/
theorem paper3_cosineCoeffs_congr_on_Icc
    {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x = g x) (k : ℕ) :
    cosineCoeffs f k = cosineCoeffs g k := by
  simp only [cosineCoeffs,
    ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff,
    ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff]
  have hint : ∀ m : ℕ,
      (∫ x in (0 : ℝ)..1,
        (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) * (f x : ℂ)) =
      ∫ x in (0 : ℝ)..1,
        (Real.cos ((m : ℝ) * Real.pi * x) : ℂ) * (g x : ℂ) := by
    intro m
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [hfg x hxIcc]
  simp only [hint]

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

/-- Linear part of the elliptic source perturbation. -/
def paper3IntervalEllipticLinearProfile
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  p.ν * paper3PowerDeriv p.γ uStar *
    paper3IntervalPerturbationProfile uStar u x

/-- Exact pointwise Taylor splitting of the eliminated elliptic source. -/
theorem paper3IntervalEllipticSource_pointwise_split
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) :
    p.ν * intervalDomainLift u x ^ p.γ =
      p.ν * uStar ^ p.γ +
        paper3IntervalEllipticLinearProfile p uStar u x +
          paper3IntervalEllipticRemainderProfile p uStar u x := by
  simp only [paper3IntervalEllipticLinearProfile,
    paper3IntervalPerturbationProfile,
    paper3IntervalEllipticRemainderProfile,
    paper3EllipticSourceRemainder,
    paper3PowerLinearizationRemainder]
  ring

/-- Cosine coefficient of the exact nonlinear source remainder. -/
def paper3IntervalEllipticRemainderSourceCoeff
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  (cosineCoeffs
    (paper3IntervalEllipticRemainderProfile p uStar u) k : ℂ)

/-- Cosine coefficient of the exact linear source perturbation. -/
def paper3IntervalEllipticLinearSourceCoeff
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  (cosineCoeffs
    (paper3IntervalEllipticLinearProfile p uStar u) k : ℂ)

/-- Exact source-coefficient split used by the eliminated Duhamel equation. -/
theorem intervalNeumannResolverSourceCoeff_split
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ)
    (hlin : IntervalIntegrable
      (paper3IntervalEllipticLinearProfile p uStar u) volume 0 1)
    (hrem : IntervalIntegrable
      (paper3IntervalEllipticRemainderProfile p uStar u) volume 0 1) :
    intervalNeumannResolverSourceCoeff p u k =
      intervalNeumannResolverSourceCoeff p (fun _ => uStar) k +
        paper3IntervalEllipticLinearSourceCoeff p uStar u k +
          paper3IntervalEllipticRemainderSourceCoeff p uStar u k := by
  let c : ℝ → ℝ := fun _ => p.ν * uStar ^ p.γ
  have hc : IntervalIntegrable c volume 0 1 := intervalIntegrable_const
  have hcl : IntervalIntegrable
      (fun x => c x + paper3IntervalEllipticLinearProfile p uStar u x)
      volume 0 1 := hc.add hlin
  have hadd1 := cosineCoeffs_add_of_intervalIntegrable k hc hlin
  have hadd2 := cosineCoeffs_add_of_intervalIntegrable k hcl hrem
  have hsource : cosineCoeffs
      (fun x => p.ν * intervalDomainLift u x ^ p.γ) k =
      cosineCoeffs c k +
        cosineCoeffs (paper3IntervalEllipticLinearProfile p uStar u) k +
          cosineCoeffs
            (paper3IntervalEllipticRemainderProfile p uStar u) k := by
    calc
      cosineCoeffs (fun x => p.ν * intervalDomainLift u x ^ p.γ) k =
          cosineCoeffs
            (fun x =>
              (c x + paper3IntervalEllipticLinearProfile p uStar u x) +
                paper3IntervalEllipticRemainderProfile p uStar u x) k := by
            apply congrArg (fun f : ℝ → ℝ => cosineCoeffs f k)
            funext x
            exact (paper3IntervalEllipticSource_pointwise_split
              p uStar u x).trans (by rfl)
      _ = cosineCoeffs
            (fun x => c x + paper3IntervalEllipticLinearProfile p uStar u x) k +
          cosineCoeffs
            (paper3IntervalEllipticRemainderProfile p uStar u) k := hadd2
      _ = _ := by rw [hadd1]
  have hconstLift : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift (fun _ : intervalDomainPoint => uStar) x = uStar := by
    intro x hx
    simp [intervalDomainLift, hx]
  have hconstCoeff :
      intervalNeumannResolverSourceCoeff p (fun _ => uStar) k =
        (cosineCoeffs c k : ℂ) := by
    change (cosineCoeffs
      (fun x => p.ν * intervalDomainLift
        (fun _ : intervalDomainPoint => uStar) x ^ p.γ) k : ℂ) =
      (cosineCoeffs c k : ℂ)
    exact_mod_cast paper3_cosineCoeffs_congr_on_Icc
      (fun x hx => by simp [c, hconstLift x hx]) k
  rw [hconstCoeff]
  have hsourceCoeff :
      intervalNeumannResolverSourceCoeff p u k =
        (cosineCoeffs
          (fun x => p.ν * intervalDomainLift u x ^ p.γ) k : ℂ) := by
    rfl
  rw [hsourceCoeff]
  simp only [paper3IntervalEllipticLinearSourceCoeff,
    paper3IntervalEllipticRemainderSourceCoeff]
  exact_mod_cast hsource

/-- The resolved coefficient of the nonlinear elliptic remainder. -/
def paper3IntervalEllipticRemainderResolvedCoeff
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  shiftedNeumannResolventCoeff 0 (p.μ : ℂ)
    (paper3IntervalEllipticRemainderSourceCoeff p uStar u) k

/-- The resolved coefficient of the linear elliptic perturbation. -/
def paper3IntervalEllipticLinearResolvedCoeff
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) : ℂ :=
  shiftedNeumannResolventCoeff 0 (p.μ : ℂ)
    (paper3IntervalEllipticLinearSourceCoeff p uStar u) k

/-- Exact resolved-coefficient split, inherited from diagonal linearity of the
Neumann elliptic resolvent. -/
theorem intervalNeumannResolverCoeff_split
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ)
    (hlin : IntervalIntegrable
      (paper3IntervalEllipticLinearProfile p uStar u) volume 0 1)
    (hrem : IntervalIntegrable
      (paper3IntervalEllipticRemainderProfile p uStar u) volume 0 1) :
    intervalNeumannResolverCoeff p u k =
      intervalNeumannResolverCoeff p (fun _ => uStar) k +
        paper3IntervalEllipticLinearResolvedCoeff p uStar u k +
          paper3IntervalEllipticRemainderResolvedCoeff p uStar u k := by
  have hsource := intervalNeumannResolverSourceCoeff_split
    p uStar u k hlin hrem
  unfold intervalNeumannResolverCoeff
    paper3IntervalEllipticLinearResolvedCoeff
    paper3IntervalEllipticRemainderResolvedCoeff
    shiftedNeumannResolventCoeff
  rw [hsource]
  ring

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
#print axioms cosineCoeffs_const_mul_of_intervalIntegrable
#print axioms intervalNeumannResolverSourceCoeff_split
#print axioms intervalNeumannResolverCoeff_split
#print axioms paper3IntervalEllipticRemainder_coeff_l2

end

end ShenWork.Paper3
