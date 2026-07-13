/- Physical realization of the one-dimensional strong spectral norm. -/
import ShenWork.Paper3.IntervalDomainStrongEmbedding
import ShenWork.PDE.FractionalPowerDerivative
import ShenWork.PDE.IntervalCosineInversion
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.PDE.IntervalChemDivAEMeasurable

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.PDE.FractionalPower
open ShenWork.IntervalCosineInversion
open ShenWork.IntervalNeumannFullKernel
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalMildPicardRegularity
open ShenWork.Paper2

noncomputable section

/-- Absolute summability of the normalized interval cosine coefficients
implies absolute summability of the Fourier coefficients of the even doubled
reflection. -/
theorem fourierCoeff_reflCircle_summable_of_cosineCoeffs_abs
    (f : ℝ → ℝ) (hf : Continuous f)
    (hcos : Summable fun n : ℕ => |cosineCoeffs f n|) :
    Summable fun n : ℤ => fourierCoeff (reflCircle f) n := by
  have hnat : Summable fun n : ℕ => fourierCoeff (reflCircle f) (n : ℤ) := by
    apply Summable.of_norm_bounded hcos
    intro n
    have hreal := fourierCoeff_ofReal_re f hf (n : ℤ)
    have hcoeff := cosineCoeffs_eq f hf n
    rw [← hreal, Complex.norm_real, Real.norm_eq_abs]
    rw [← fourierCoeff_reflCircle] at hcoeff
    by_cases hn : n = 0
    · subst n
      have habs := congrArg abs hcoeff.symm
      simpa using le_of_eq habs
    · simp only [if_neg hn] at hcoeff
      rw [hcoeff]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg (fourierCoeff (reflCircle f) (n : ℤ)).re]
  apply Summable.of_nat_of_neg hnat
  simpa only [fourierCoeff_reflCircle,
    fco_neg f hf] using hnat

/-- Clamp a real coordinate into the unit interval, bundled as an interval
point. -/
def paper3ClampPoint (x : ℝ) : intervalDomainPoint :=
  ⟨max 0 (min x 1), le_max_left 0 _,
    max_le (by norm_num) (min_le_right x 1)⟩

theorem paper3ClampPoint_continuous : Continuous paper3ClampPoint := by
  exact Continuous.subtype_mk
    (continuous_const.max (continuous_id.min continuous_const)) _

theorem paper3ClampPoint_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (paper3ClampPoint x).1 = x := by
  simp only [paper3ClampPoint]
  rw [min_eq_left hx.2, max_eq_right hx.1]

/-- Globally continuous representative of the physical perturbation, obtained
by clamping to `[0,1]`. -/
def paper3ClampedPerturbationProfile
    (uStar : ℝ) (w : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  w (paper3ClampPoint x) - uStar

theorem paper3ClampedPerturbationProfile_continuous
    {uStar : ℝ} {w : intervalDomainPoint → ℝ} (hw : Continuous w) :
    Continuous (paper3ClampedPerturbationProfile uStar w) := by
  exact (hw.comp paper3ClampPoint_continuous).sub continuous_const

theorem paper3ClampedPerturbationProfile_eq_lift
    (uStar : ℝ) (w : intervalDomainPoint → ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    paper3ClampedPerturbationProfile uStar w x =
      intervalDomainLift w x - uStar := by
  unfold paper3ClampedPerturbationProfile
  rw [intervalDomainLift, dif_pos hx]
  congr 2
  exact Subtype.ext (paper3ClampPoint_eq_self hx)

theorem paper3ClampedPerturbationProfile_cosineCoeffs
    (uStar : ℝ) (w : intervalDomainPoint → ℝ) (n : ℕ) :
    cosineCoeffs (paper3ClampedPerturbationProfile uStar w) n =
      cosineCoeffs (fun x => intervalDomainLift w x - uStar) n := by
  simp only [cosineCoeffs_eq_factor_mul_integral]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
    rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  change Real.cos ((n : ℝ) * Real.pi * x) *
      paper3ClampedPerturbationProfile uStar w x =
    Real.cos ((n : ℝ) * Real.pi * x) *
      (intervalDomainLift w x - uStar)
  rw [paper3ClampedPerturbationProfile_eq_lift uStar w hxIcc]

/-- Membership in the unit-interval coefficient realization of `X_2^sigma`,
together with continuity of the physical profile, produces the value and
ordinary-derivative trace bounds used by the local Nemytskii estimate. -/
theorem intervalDomainX2SigmaRealizationBounds_of_continuous
    {sigma uStar : ℝ} {w : intervalDomainPoint → ℝ}
    (hsigma : 3 / 4 < sigma) (hw : Continuous w)
    (hmem : IntervalDomainX2SigmaPerturbation sigma uStar w) :
    IntervalDomainX2SigmaRealizationBounds sigma uStar w := by
  let a : ℕ → ℂ := intervalDomainPerturbationCosineCoeff uStar w
  let f : ℝ → ℝ := paper3ClampedPerturbationProfile uStar w
  let S : ℝ → ℝ := fun x =>
    ∑' n : ℕ, unitIntervalCosineMode n x * cosineCoeffs f n
  have hf : Continuous f := by
    simpa [f] using paper3ClampedPerturbationProfile_continuous hw
  have henergy : Summable fun n : ℕ =>
      fractionalPowerEnergyTerm 1 sigma a n := by
    simpa [a] using hmem
  have htrace : Summable fun n : ℕ =>
      reciprocalFractionalPowerWeight 1 sigma n :=
    reciprocalFractionalPowerWeight_summable_of_sigma_gt_quarter
      (L := 1) (sigma := sigma) (by norm_num) (by linarith)
  have hdtrace : Summable fun n : ℕ =>
      derivativeReciprocalFractionalPowerWeight 1 sigma n :=
    derivativeReciprocalFractionalPowerWeight_summable_of_sigma_gt_three_quarters
      (L := 1) (sigma := sigma) (by norm_num) hsigma
  have hacoeff : ∀ n : ℕ,
      cosineCoeffs f n = (a n).re := by
    intro n
    rw [paper3ClampedPerturbationProfile_cosineCoeffs]
    simp [a, intervalDomainPerturbationCosineCoeff]
  have hacoeffC : ∀ n : ℕ, (a n : ℂ) = (cosineCoeffs f n : ℝ) := by
    intro n
    simp [a, intervalDomainPerturbationCosineCoeff]
    rw [← paper3ClampedPerturbationProfile_cosineCoeffs]
  have haNorm : Summable fun n : ℕ => ‖a n‖ :=
    coeff_norm_summable_of_reciprocal_trace a henergy htrace
  have hfAbs : Summable fun n : ℕ => |cosineCoeffs f n| := by
    convert haNorm using 1
    ext n
    rw [hacoeffC n, Complex.norm_real, Real.norm_eq_abs]
  have hfourier : Summable fun n : ℤ => fourierCoeff (reflCircle f) n :=
    fourierCoeff_reflCircle_summable_of_cosineCoeffs_abs f hf hfAbs
  have hScont : Continuous S := by
    unfold S
    exact continuous_tsum
      (fun n => by unfold unitIntervalCosineMode; fun_prop)
      hfAbs
      (fun n x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |unitIntervalCosineMode n x| * |cosineCoeffs f n| ≤
              1 * |cosineCoeffs f n| :=
            mul_le_mul_of_nonneg_right
              (by
                unfold unitIntervalCosineMode
                exact Real.abs_cos_le_one _)
              (abs_nonneg _)
          _ = |cosineCoeffs f n| := one_mul _)
  have hSeq : Set.EqOn S f (Set.Ioo (0 : ℝ) 1) := by
    intro x hx
    exact (intervalCosine_hasSum_pointwise f hf hx hfourier).tsum_eq
  have hSeqIcc : Set.EqOn S f (Set.Icc (0 : ℝ) 1) := by
    have hclosure := hSeq.closure hScont hf
    intro x hx
    apply hclosure
    simpa using hx
  have hvalueCauchy :=
    tsum_coeff_norm_le_fractionalPowerEnergy_mul_trace a henergy htrace
  have haDeriv : Summable fun n : ℕ =>
      Real.sqrt (neumannEigenvalue 1 n) * ‖a n‖ :=
    sqrt_eigen_mul_coeff_norm_summable a henergy hdtrace
  have hfreq : ∀ n : ℕ,
      Real.sqrt (neumannEigenvalue 1 n) = (n : ℝ) * Real.pi := by
    intro n
    rw [neumannEigenvalue]
    have hfreq0 : 0 ≤ (n : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le
    simpa using Real.sqrt_sq hfreq0
  have hfDeriv : Summable fun n : ℕ =>
      |cosineCoeffs f n| * ((n : ℝ) * Real.pi) := by
    convert haDeriv using 1
    ext n
    rw [hfreq n, hacoeffC n, Complex.norm_real, Real.norm_eq_abs]
    ring
  have hderivCauchy :=
    tsum_sqrt_eigen_mul_coeff_norm_le a henergy hdtrace
  refine
    { value_bound := ?_
      gradient_bound := ?_ }
  · intro x
    have hx := x.2
    have hfx : f x.1 = w x - uStar := by
      change paper3ClampedPerturbationProfile uStar w x.1 = w x - uStar
      rw [paper3ClampedPerturbationProfile_eq_lift uStar w hx]
      simp [intervalDomainLift]
    have hsum : Summable fun n : ℕ =>
        unitIntervalCosineMode n x.1 * cosineCoeffs f n := by
      apply Summable.of_norm_bounded hfAbs
      intro n
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (by
          unfold unitIntervalCosineMode
          exact Real.abs_cos_le_one _)
    have hSbound : |S x.1| ≤ ∑' n : ℕ, |cosineCoeffs f n| :=
      hsum.hasSum.norm_le_of_bounded hfAbs.hasSum (fun n => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _)
          (by
            unfold unitIntervalCosineMode
            exact Real.abs_cos_le_one _))
    calc
      |w x - uStar| = |S x.1| := by rw [hSeqIcc hx, hfx]
      _ ≤ ∑' n : ℕ, |cosineCoeffs f n| := hSbound
      _ = ∑' n : ℕ, ‖a n‖ := by
        apply tsum_congr
        intro n
        rw [hacoeffC n, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n) ^
            (1 / (2 : ℝ)) *
          (∑' n : ℕ, reciprocalFractionalPowerWeight 1 sigma n) ^
            (1 / (2 : ℝ)) := hvalueCauchy
      _ = intervalDomainX2SigmaValueTrace sigma *
          intervalDomainX2SigmaDistance sigma uStar w := by
        simp only [intervalDomainX2SigmaValueTrace,
          intervalDomainX2SigmaDistance, a, Real.sqrt_eq_rpow]
        ring

  · intro x
    change |deriv (intervalDomainLift (fun y => w y - uStar)) x.1| ≤ _
    by_cases hx0 : x.1 = 0
    · rw [hx0, intervalDomainLift_deriv_at_zero_eq_zero]
      simpa using mul_nonneg
        (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
        (Real.sqrt_nonneg
          (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n))
    by_cases hx1 : x.1 = 1
    · rw [hx1, intervalDomainLift_deriv_at_one_eq_zero]
      simpa using mul_nonneg
        (intervalDomainX2SigmaDerivativeTrace_nonneg sigma)
        (Real.sqrt_nonneg
          (∑' n : ℕ, fractionalPowerEnergyTerm 1 sigma a n))
    have hxIoo : x.1 ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne x.2.1 (Ne.symm hx0),
        lt_of_le_of_ne x.2.2 hx1⟩
    let dS : ℝ := ∑' n : ℕ,
      cosineCoeffs f n *
        (-((n : ℝ) * Real.pi) *
          Real.sin ((n : ℝ) * Real.pi * x.1))
    have hSd := cosineSeries_hasDerivAt_of_gradSummable hfDeriv x.1
    have hevent : Filter.EventuallyEq (nhds x.1)
        (intervalDomainLift (fun y => w y - uStar))
        (fun z => ∑' k : ℕ,
          cosineCoeffs f k * Real.cos ((k : ℝ) * Real.pi * z)) := by
      refine Filter.eventuallyEq_of_mem (IsOpen.mem_nhds isOpen_Ioo hxIoo) ?_
      intro y hy
      calc
        intervalDomainLift (fun z => w z - uStar) y = f y := by
          change intervalDomainLift (fun z => w z - uStar) y =
            paper3ClampedPerturbationProfile uStar w y
          simp only [intervalDomainLift, Set.Ioo_subset_Icc_self hy, dif_pos]
          rw [paper3ClampedPerturbationProfile_eq_lift uStar w
            (Set.Ioo_subset_Icc_self hy)]
          simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
        _ = S y := (hSeq hy).symm
        _ = ∑' k : ℕ,
            cosineCoeffs f k * Real.cos ((k : ℝ) * Real.pi * y) := by
          simp only [S, unitIntervalCosineMode]
          apply tsum_congr
          intro k
          ring
    have hphysical : HasDerivAt
        (intervalDomainLift (fun y => w y - uStar)) dS x.1 := by
      simpa [S, dS] using hSd.congr_of_eventuallyEq hevent
    have hdSum : Summable fun n : ℕ =>
        cosineCoeffs f n *
          (-((n : ℝ) * Real.pi) *
            Real.sin ((n : ℝ) * Real.pi * x.1)) := by
      apply Summable.of_norm_bounded hfDeriv
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
      rw [abs_of_nonneg
        (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
      calc
        |cosineCoeffs f n| *
            (((n : ℝ) * Real.pi) *
              |Real.sin ((n : ℝ) * Real.pi * x.1)|) ≤
          |cosineCoeffs f n| * (((n : ℝ) * Real.pi) * 1) := by
            gcongr
            exact Real.abs_sin_le_one _
        _ = |cosineCoeffs f n| * ((n : ℝ) * Real.pi) := by ring
    have hdBound : |dS| ≤
        ∑' n : ℕ, |cosineCoeffs f n| * ((n : ℝ) * Real.pi) := by
      dsimp [dS]
      exact hdSum.hasSum.norm_le_of_bounded hfDeriv.hasSum (fun n => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg]
        rw [abs_of_nonneg
          (mul_nonneg (Nat.cast_nonneg n) Real.pi_pos.le)]
        calc
          |cosineCoeffs f n| *
              (((n : ℝ) * Real.pi) *
                |Real.sin ((n : ℝ) * Real.pi * x.1)|) ≤
            |cosineCoeffs f n| * (((n : ℝ) * Real.pi) * 1) := by
              gcongr
              exact Real.abs_sin_le_one _
          _ = |cosineCoeffs f n| * ((n : ℝ) * Real.pi) := by ring)
    rw [hphysical.deriv]
    calc
      |dS| ≤ ∑' n : ℕ,
          |cosineCoeffs f n| * ((n : ℝ) * Real.pi) := hdBound
      _ = ∑' n : ℕ, Real.sqrt (neumannEigenvalue 1 n) * ‖a n‖ := by
        apply tsum_congr
        intro n
        rw [hfreq n, hacoeffC n, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ Real.sqrt (∑' n : ℕ,
            fractionalPowerEnergyTerm 1 sigma a n) *
          Real.sqrt (∑' n : ℕ,
            derivativeReciprocalFractionalPowerWeight 1 sigma n) :=
        hderivCauchy
      _ = intervalDomainX2SigmaDerivativeTrace sigma *
          intervalDomainX2SigmaDistance sigma uStar w := by
        simp only [intervalDomainX2SigmaDerivativeTrace,
          intervalDomainX2SigmaDistance, a]
        ring

/-- Strong admissible initial data automatically carry the physical
realization bounds; no extra realization record is part of the datum. -/
theorem intervalDomainX2SigmaRealizationBounds_of_positiveInitialDatum
    {sigma uStar : ℝ} {u₀ : intervalDomainPoint → ℝ}
    (hsigma : 3 / 4 < sigma)
    (hu₀ : PositiveInitialDatum intervalDomain u₀)
    (hmem : IntervalDomainX2SigmaPerturbation sigma uStar u₀) :
    IntervalDomainX2SigmaRealizationBounds sigma uStar u₀ :=
  intervalDomainX2SigmaRealizationBounds_of_continuous
    hsigma hu₀.admissible.2 hmem

#print axioms fourierCoeff_reflCircle_summable_of_cosineCoeffs_abs
#print axioms paper3ClampedPerturbationProfile_cosineCoeffs
#print axioms intervalDomainX2SigmaRealizationBounds_of_continuous
#print axioms
  intervalDomainX2SigmaRealizationBounds_of_positiveInitialDatum

end

end ShenWork.Paper3
