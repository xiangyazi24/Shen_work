import ShenWork.PDE.IntervalDomain
import ShenWork.PDE.IntervalEllipticCharacterization
import ShenWork.PDE.GagliardoNirenberg
import ShenWork.Paper2.IntervalDomainLemma41

/-!
# Interval Agmon interpolation audit

This file replaces an unfinished proof skeleton that tried to prove a uniform
one-dimensional Agmon interpolation estimate from assumptions that were too
weak:

* a fundamental-theorem-of-calculus bound needs absolute continuity or an
  equivalent derivative-integrability hypothesis, not just
  `ContinuousOn` plus `DifferentiableOn` on the open interval;
* the raw `L¹ ≤ L²` step needs square-integrability;
* a per-slice constant depending on `f` is not enough to produce
  `LpMassGradientInterpolationEstimate`, whose `Ceps` must be uniform in
  `t ∈ (0,T)`.

The first theorem below records the only elementary fact available at the
old interface: for a single slice whose mass is positive, the present
inequality is satisfiable by choosing a large constant depending on that
slice.  This is honest but intentionally not exported as the paper-level
interpolation frontier.

The PDE-level consumer needs the second, uniform interface:
`UnitIntervalPositiveAgmonInterpolation`, where `Ceps` is chosen from `q`
and `eps` before the solution slice is supplied, and where the slice carries
the closed-interval `C²` regularity available from classical solutions.
-/

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.Paper2

noncomputable section

namespace ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

/-- Strict positivity of the zero-extension on the closed physical interval. -/
theorem intervalDomainLift_pos_on_Icc
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift f y := by
  intro y hy
  simpa [intervalDomainLift, hy] using hf_pos ⟨y, hy⟩

/-- Nonvanishing form of `intervalDomainLift_pos_on_Icc`, for real-power APIs. -/
theorem intervalDomainLift_ne_on_Icc
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift f y ≠ 0 := by
  intro y hy
  exact ne_of_gt (intervalDomainLift_pos_on_Icc hf_pos y hy)

/-- Closed-interval continuity of positive real powers of a C² interval-domain lift. -/
theorem intervalDomainLift_rpow_continuousOn_Icc
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun y => (intervalDomainLift f y) ^ (q / 2)) (Set.Icc (0 : ℝ) 1) :=
  hfC2.continuousOn.rpow_const
    (fun y hy => Or.inl (intervalDomainLift_ne_on_Icc hf_pos y hy))

/-- Interior right-derivative chain rule for `g = (intervalDomainLift f)^(q/2)`. -/
theorem intervalDomainLift_rpow_hasDerivWithinAt_Ioi
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (fun z => (intervalDomainLift f z) ^ (q / 2))
        ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y)
        (Set.Ioi y) y := by
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  have hdiffOn :
      DifferentiableOn ℝ (intervalDomainLift f) (Set.Ioo (0 : ℝ) 1) :=
    (hfC2.differentiableOn (by norm_num)).mono Set.Ioo_subset_Icc_self
  have hdiffAt : DifferentiableAt ℝ (intervalDomainLift f) y :=
    hdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hbase :
      HasDerivAt (intervalDomainLift f) (deriv (intervalDomainLift f) y) y :=
    hdiffAt.hasDerivAt
  have hpow := hbase.rpow_const (p := q / 2)
    (Or.inl (intervalDomainLift_ne_on_Icc hf_pos y hyIcc))
  have hwithin := hpow.hasDerivWithinAt (s := Set.Ioi y)
  convert hwithin using 1
  ring

/-- Real-power half exponent squares back to the original exponent. -/
theorem rpow_half_sq_of_nonneg {a q : ℝ} (ha : 0 ≤ a) :
    (a ^ (q / 2)) ^ 2 = a ^ q := by
  rw [← Real.rpow_mul_natCast ha (q / 2) 2]
  ring_nf

/-- Squared chain-rule factor for `d(a^(q/2))`. -/
theorem rpow_half_deriv_sq_factor {a b q : ℝ} (ha : 0 ≤ a) :
    ((q / 2) * a ^ (q / 2 - 1) * b) ^ 2 =
      (q ^ 2 / 4) * (a ^ (q - 2) * b ^ 2) := by
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast ha (q / 2 - 1) 2]
  ring_nf

/-- Rewrite a subtype power integral as the corresponding lift power integral. -/
theorem intervalDomain_integral_rpow_eq_lift_integral
    {q : ℝ} {f : intervalDomain.Point → ℝ} :
    intervalDomain.integral (fun x => f x ^ q) =
      ∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ q := by
  change (∫ y in (0 : ℝ)..1,
      intervalDomainLift (fun x : intervalDomain.Point => f x ^ q) y) =
    ∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ q
  refine intervalIntegral.integral_congr ?_
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  simp [intervalDomainLift, hyIcc]

/-- The `g²` integral for `g = (intervalDomainLift f)^(q/2)` is the subtype
`f^q` integral. -/
theorem intervalDomainLift_rpow_half_sq_integral_eq
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    (∫ y in (0 : ℝ)..1, ((intervalDomainLift f y) ^ (q / 2)) ^ 2) =
      intervalDomain.integral (fun x => f x ^ q) := by
  rw [intervalDomain_integral_rpow_eq_lift_integral (q := q) (f := f)]
  refine intervalIntegral.integral_congr ?_
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  exact rpow_half_sq_of_nonneg (intervalDomainLift_pos_on_Icc hf_pos y hyIcc).le

/-- Integrability of the `g²` term for
`g = (intervalDomainLift f)^(q/2)`. -/
theorem intervalDomainLift_rpow_half_sq_intervalIntegrable
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun y => ((intervalDomainLift f y) ^ (q / 2)) ^ 2) volume (0 : ℝ) 1 :=
  (((intervalDomainLift_rpow_continuousOn_Icc (q := q) hf_pos hfC2).pow 2).mono
    (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable

/-- Integrability of the `g'²` term for
`g = (intervalDomainLift f)^(q/2)`, using the ordinary derivative representative
on the open interval. -/
theorem intervalDomainLift_rpow_deriv_sq_intervalIntegrable
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun y =>
        ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y) ^ 2)
      volume (0 : ℝ) 1 := by
  set raw : ℝ → ℝ := fun y =>
    ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      deriv (intervalDomainLift f) y) ^ 2
  set rep : ℝ → ℝ := fun y =>
    ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) y) ^ 2
  have hrep_cont : ContinuousOn rep (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hpow : ContinuousOn
        (fun y => (intervalDomainLift f y) ^ (q / 2 - 1)) (Set.Icc (0 : ℝ) 1) :=
      hfC2.continuousOn.rpow_const
        (fun y hy => Or.inl (intervalDomainLift_ne_on_Icc hf_pos y hy))
    have hdw : ContinuousOn
        (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_derivWithin_of_contDiffOn_two hfC2
    exact (((continuousOn_const.mul hpow).mul hdw).pow 2)
  have hrep_int : IntervalIntegrable rep volume 0 1 := hrep_cont.intervalIntegrable
  change IntervalIntegrable raw volume (0 : ℝ) 1
  refine hrep_int.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push Not at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [Set.mem_singleton_iff]
  by_contra hy1
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
  apply hne
  have hderiv_eq :
      derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) y =
        deriv (intervalDomainLift f) y :=
    (deriv_eq_derivWithin_interior hyIoo).symm
  simp only [raw, rep, hderiv_eq]

/-- Integrability of the derivative representative for
`g = (intervalDomainLift f)^(q/2)`. -/
theorem intervalDomainLift_rpow_deriv_intervalIntegrable
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun y =>
        (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y)
      volume (0 : ℝ) 1 := by
  set raw : ℝ → ℝ := fun y =>
    (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      deriv (intervalDomainLift f) y
  set rep : ℝ → ℝ := fun y =>
    (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
      derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) y
  have hrep_cont : ContinuousOn rep (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hpow : ContinuousOn
        (fun y => (intervalDomainLift f y) ^ (q / 2 - 1)) (Set.Icc (0 : ℝ) 1) :=
      hfC2.continuousOn.rpow_const
        (fun y hy => Or.inl (intervalDomainLift_ne_on_Icc hf_pos y hy))
    have hdw : ContinuousOn
        (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_derivWithin_of_contDiffOn_two hfC2
    exact (continuousOn_const.mul hpow).mul hdw
  have hrep_int : IntervalIntegrable rep volume 0 1 := hrep_cont.intervalIntegrable
  change IntervalIntegrable raw volume (0 : ℝ) 1
  refine hrep_int.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push Not at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [Set.mem_singleton_iff]
  by_contra hy1
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
  apply hne
  have hderiv_eq :
      derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) y =
        deriv (intervalDomainLift f) y :=
    (deriv_eq_derivWithin_interior hyIoo).symm
  simp only [raw, rep, hderiv_eq]

/-- The `g'²` integral for `g = (intervalDomainLift f)^(q/2)` is the expected
constant multiple of the interval-domain gradient integral. -/
theorem intervalDomainLift_rpow_deriv_sq_integral_eq
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    (∫ y in (0 : ℝ)..1,
        ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y) ^ 2) =
      (q ^ 2 / 4) * intervalDomain.integral
        (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) := by
  change (∫ y in (0 : ℝ)..1,
        ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
          deriv (intervalDomainLift f) y) ^ 2) =
      (q ^ 2 / 4) *
        (∫ y in (0 : ℝ)..1,
          intervalDomainLift
            (fun x : intervalDomain.Point =>
              f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) y)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr ?_
  intro y hy
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hy
  have hchain := rpow_half_deriv_sq_factor
    (a := intervalDomainLift f y) (b := deriv (intervalDomainLift f) y) (q := q)
    (intervalDomainLift_pos_on_Icc hf_pos y hyIcc).le
  have hlift :
      intervalDomainLift
          (fun x : intervalDomain.Point =>
            f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) y =
        (intervalDomainLift f y) ^ (q - 2) *
          (deriv (intervalDomainLift f) y) ^ 2 := by
    simp [intervalDomainLift, intervalDomain, intervalDomainGradNorm, hyIcc, sq_abs]
  change ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
        deriv (intervalDomainLift f) y) ^ 2 =
      (q ^ 2 / 4) *
        intervalDomainLift
          (fun x : intervalDomain.Point =>
            f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) y
  rw [hchain, hlift]

/-- Integrability of the `g * g'` term for
`g = (intervalDomainLift f)^(q/2)`. -/
theorem intervalDomainLift_rpow_deriv_product_intervalIntegrable
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    IntervalIntegrable
      (fun y =>
        (intervalDomainLift f y) ^ (q / 2) *
          ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
            deriv (intervalDomainLift f) y))
      volume (0 : ℝ) 1 := by
  set raw : ℝ → ℝ := fun y =>
    (intervalDomainLift f y) ^ (q / 2) *
      ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
        deriv (intervalDomainLift f) y)
  set rep : ℝ → ℝ := fun y =>
    (intervalDomainLift f y) ^ (q / 2) *
      ((q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
        derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) y)
  have hrep_cont : ContinuousOn rep (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hpow0 : ContinuousOn
        (fun y => (intervalDomainLift f y) ^ (q / 2)) (Set.Icc (0 : ℝ) 1) :=
      intervalDomainLift_rpow_continuousOn_Icc (q := q) hf_pos hfC2
    have hpow1 : ContinuousOn
        (fun y => (intervalDomainLift f y) ^ (q / 2 - 1)) (Set.Icc (0 : ℝ) 1) :=
      hfC2.continuousOn.rpow_const
        (fun y hy => Or.inl (intervalDomainLift_ne_on_Icc hf_pos y hy))
    have hdw : ContinuousOn
        (derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) :=
      continuousOn_derivWithin_of_contDiffOn_two hfC2
    exact hpow0.mul ((continuousOn_const.mul hpow1).mul hdw)
  have hrep_int : IntervalIntegrable rep volume 0 1 := hrep_cont.intervalIntegrable
  change IntervalIntegrable raw volume (0 : ℝ) 1
  refine hrep_int.congr_ae ?_
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  refine (ae_restrict_iff' measurableSet_Ioc).2 ?_
  have hnull : volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
  refine (MeasureTheory.ae_iff).2 (measure_mono_null ?_ hnull)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  push Not at hy
  obtain ⟨hyIoc, hne⟩ := hy
  simp only [Set.mem_singleton_iff]
  by_contra hy1
  have hyIoo : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hyIoc.1, lt_of_le_of_ne hyIoc.2 hy1⟩
  apply hne
  have hderiv_eq :
      derivWithin (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) y =
      deriv (intervalDomainLift f) y :=
    (deriv_eq_derivWithin_interior hyIoo).symm
  simp only [raw, rep, hderiv_eq]

/-- Endpoint-safe Agmon applied to `g = (intervalDomainLift f)^(q/2)`. -/
theorem intervalDomainLift_rpow_agmon_bound
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (intervalDomainLift f x) ^ q ≤
      2 * intervalDomain.integral (fun z => f z ^ q) +
        2 * Real.sqrt (intervalDomain.integral (fun z => f z ^ q)) *
          Real.sqrt
            ((q ^ 2 / 4) *
              intervalDomain.integral
                (fun z => f z ^ (q - 2) *
                  (intervalDomain.gradNorm f z) ^ 2)) := by
  have hag := ShenWork.GagliardoNirenberg.agmon_inequality_interval_rightDeriv
    (L := 1) (by norm_num : (0 : ℝ) < 1)
    (f := fun y => (intervalDomainLift f y) ^ (q / 2))
    (f' := fun y =>
      (q / 2) * (intervalDomainLift f y) ^ (q / 2 - 1) *
        deriv (intervalDomainLift f) y)
    (intervalDomainLift_rpow_continuousOn_Icc (q := q) hf_pos hfC2)
    (intervalDomainLift_rpow_hasDerivWithinAt_Ioi (q := q) hf_pos hfC2)
    (intervalDomainLift_rpow_deriv_intervalIntegrable (q := q) hf_pos hfC2)
    (intervalDomainLift_rpow_half_sq_intervalIntegrable (q := q) hf_pos hfC2)
    (intervalDomainLift_rpow_deriv_sq_intervalIntegrable (q := q) hf_pos hfC2)
    (intervalDomainLift_rpow_deriv_product_intervalIntegrable (q := q) hf_pos hfC2)
    hx
  have hxpow :
      ((intervalDomainLift f x) ^ (q / 2)) ^ 2 =
        (intervalDomainLift f x) ^ q :=
    rpow_half_sq_of_nonneg (intervalDomainLift_pos_on_Icc hf_pos x hx).le
  rw [hxpow,
    intervalDomainLift_rpow_half_sq_integral_eq (q := q) hf_pos,
    intervalDomainLift_rpow_deriv_sq_integral_eq (q := q) hf_pos] at hag
  norm_num at hag
  simpa [mul_assoc] using hag

/-- Nonnegativity of interval-domain positive real-power integrals. -/
theorem intervalDomain_integral_rpow_nonneg
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    0 ≤ intervalDomain.integral (fun x => f x ^ q) := by
  change 0 ≤ ∫ y in (0 : ℝ)..1,
    intervalDomainLift (fun x : intervalDomain.Point => f x ^ q) y
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y hy => ?_)
  simp [intervalDomainLift, hy, Real.rpow_nonneg (hf_pos ⟨y, hy⟩).le q]

/-- Nonnegativity of the weighted gradient integral appearing in the Agmon
interpolation estimate. -/
theorem intervalDomain_integral_weighted_grad_nonneg
    {q : ℝ} {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x) :
    0 ≤ intervalDomain.integral
      (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) := by
  change 0 ≤ ∫ y in (0 : ℝ)..1,
    intervalDomainLift
      (fun x : intervalDomain.Point =>
        f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) y
  refine intervalIntegral.integral_nonneg (by norm_num) (fun y hy => ?_)
  have hnn :
      0 ≤ f ⟨y, hy⟩ ^ (q - 2) * (deriv (intervalDomainLift f) y) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (hf_pos ⟨y, hy⟩).le _) (sq_nonneg _)
  simpa [intervalDomainLift, intervalDomain, intervalDomainGradNorm, hy, sq_abs] using hnn

/-- A positive C² interval-domain slice has strictly positive mass. -/
theorem intervalDomain_integral_pos
    {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1)) :
    0 < intervalDomain.integral f := by
  change 0 < ∫ y in (0 : ℝ)..1, intervalDomainLift f y
  refine intervalIntegral.integral_pos (by norm_num) hfC2.continuousOn ?_ ?_
  · intro y hy
    exact (intervalDomainLift_pos_on_Icc hf_pos y ⟨le_of_lt hy.1, hy.2⟩).le
  · refine ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    exact intervalDomainLift_pos_on_Icc hf_pos ((1 : ℝ) / 2)
      ⟨by norm_num, by norm_num⟩

/-- The Agmon square-root term after the chain-rule rewrite is
`q * sqrt (Y * G)` for positive `q`. -/
theorem agmon_sqrt_term_eq
    {q Y G : ℝ} (hq : 0 ≤ q) (hY : 0 ≤ Y) :
    2 * Real.sqrt Y * Real.sqrt ((q ^ 2 / 4) * G) =
      q * Real.sqrt (Y * G) := by
  have hqhalf : 0 ≤ q / 2 := div_nonneg hq (by norm_num)
  have hcoef : q ^ 2 / 4 = (q / 2) ^ 2 := by ring
  calc
    2 * Real.sqrt Y * Real.sqrt ((q ^ 2 / 4) * G)
        = 2 * Real.sqrt Y * Real.sqrt (((q / 2) ^ 2) * G) := by
          rw [hcoef]
    _ = 2 * Real.sqrt Y * ((q / 2) * Real.sqrt G) := by
          rw [Real.sqrt_mul (sq_nonneg (q / 2)) G, Real.sqrt_sq hqhalf]
    _ = q * (Real.sqrt Y * Real.sqrt G) := by ring
    _ = q * Real.sqrt (Y * G) := by
          rw [Real.sqrt_mul hY G]

/-- Endpoint-safe Agmon with the derivative integral simplified to
`q * sqrt (Y * G)` under `1 < q`. -/
theorem intervalDomainLift_rpow_agmon_bound_qsqrt
    {q : ℝ} (hq : 1 < q) {f : intervalDomain.Point → ℝ}
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (intervalDomainLift f x) ^ q ≤
      2 * intervalDomain.integral (fun z => f z ^ q) +
        q * Real.sqrt
          (intervalDomain.integral (fun z => f z ^ q) *
            intervalDomain.integral
              (fun z => f z ^ (q - 2) *
                (intervalDomain.gradNorm f z) ^ 2)) := by
  set Y : ℝ := intervalDomain.integral (fun z => f z ^ q)
  set G : ℝ := intervalDomain.integral
    (fun z => f z ^ (q - 2) * (intervalDomain.gradNorm f z) ^ 2)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    exact intervalDomain_integral_rpow_nonneg (q := q) hf_pos
  have hbase := intervalDomainLift_rpow_agmon_bound (q := q) hf_pos hfC2 hx
  have hsqrt :
      2 * Real.sqrt Y * Real.sqrt ((q ^ 2 / 4) * G) =
        q * Real.sqrt (Y * G) :=
    agmon_sqrt_term_eq (le_of_lt (lt_trans zero_lt_one hq)) hY
  simpa [Y, G, hsqrt] using hbase

/-- Scalar Young absorption for real powers, localized here to keep the uniform
Agmon bridge independent of the higher-level a-priori files. -/
theorem scalar_rpow_young_absorb
    {r s A eps x : ℝ} (hr : 0 < r) (hrs : r < s)
    (hA : 0 ≤ A) (heps : 0 < eps) (hx : 0 ≤ x) :
    A * x ^ r ≤ eps * x ^ s +
      ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
        (s / (s - r)) := by
  let pExp : ℝ := s / r
  let qExp : ℝ := s / (s - r)
  have hp_gt : 1 < pExp := by
    dsimp [pExp]
    rw [one_lt_div hr]
    exact hrs
  have hq_gt : 1 < qExp := by
    dsimp [qExp]
    have hsr : 0 < s - r := sub_pos.mpr hrs
    rw [one_lt_div hsr]
    linarith
  have hp_pos : 0 < pExp := lt_trans zero_lt_one hp_gt
  have hp_ne : pExp ≠ 0 := ne_of_gt hp_pos
  have hpq : pExp.HolderConjugate qExp := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp_gt, ?_⟩
    dsimp [pExp, qExp]
    field_simp [ne_of_gt hr, ne_of_gt (sub_pos.mpr hrs),
      ne_of_gt (lt_trans hr hrs)]
    ring
  let B : ℝ := (eps * pExp) ^ (1 / pExp)
  have hB_pos : 0 < B := by
    dsimp [B]
    exact Real.rpow_pos_of_pos (mul_pos heps hp_pos) _
  have hleft_nonneg : 0 ≤ B * x ^ r :=
    mul_nonneg hB_pos.le (Real.rpow_nonneg hx _)
  have hright_nonneg : 0 ≤ A / B := div_nonneg hA hB_pos.le
  have hY := Real.young_inequality_of_nonneg
    (a := B * x ^ r) (b := A / B) hleft_nonneg hright_nonneg hpq
  have hab : (B * x ^ r) * (A / B) = A * x ^ r := by
    field_simp [ne_of_gt hB_pos]
  have hBp : B ^ pExp = eps * pExp := by
    dsimp [B]
    rw [← Real.rpow_mul (mul_pos heps hp_pos).le]
    have : (1 / pExp) * pExp = 1 := by field_simp [hp_ne]
    rw [this, Real.rpow_one]
  have hxrp : (x ^ r) ^ pExp = x ^ s := by
    rw [← Real.rpow_mul hx]
    dsimp [pExp]
    have : r * (s / r) = s := by field_simp [ne_of_gt hr]
    rw [this]
  have hterm1 : (B * x ^ r) ^ pExp / pExp = eps * x ^ s := by
    rw [Real.mul_rpow hB_pos.le (Real.rpow_nonneg hx _), hBp, hxrp]
    field_simp [ne_of_gt hp_pos]
  calc
    A * x ^ r = (B * x ^ r) * (A / B) := hab.symm
    _ ≤ (B * x ^ r) ^ pExp / pExp + (A / B) ^ qExp / qExp := hY
    _ = eps * x ^ s + (A / B) ^ qExp / qExp := by rw [hterm1]
    _ = eps * x ^ s +
        ((A / (eps * (s / r)) ^ (r / s)) ^ (s / (s - r))) /
          (s / (s - r)) := by
      congr 1
      dsimp [B, pExp, qExp]
      congr 2
      rw [show 1 / (s / r) = r / s by
        field_simp [ne_of_gt hr, ne_of_gt (lt_trans hr hrs)]]

/-- Young in the exact mass/supremum form used after Agmon:
`M S^((q-1)/q) ≤ δ S + C(q,δ) M^q`. -/
theorem young_mass_agmon_absorb
    {q δ M S : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hM : 0 ≤ M) (hS : 0 ≤ S) :
    M * S ^ ((q - 1) / q) ≤ δ * S +
      (((1 / ((δ * (q / (q - 1))) ^ ((q - 1) / q))) ^ q) / q) *
        M ^ q := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hqm1_pos : 0 < q - 1 := sub_pos.mpr hq
  have hr_pos : 0 < (q - 1) / q := div_pos hqm1_pos hq_pos
  have hr_lt_one : (q - 1) / q < 1 := by
    rw [div_lt_one hq_pos]
    linarith
  have hy := scalar_rpow_young_absorb
    (r := (q - 1) / q) (s := 1) (A := M) (eps := δ) (x := S)
    hr_pos hr_lt_one hM hδ hS
  have hsr : 1 - (q - 1) / q = 1 / q := by
    field_simp [hq_ne]
    ring
  have hconj : 1 / (1 - (q - 1) / q) = q := by
    rw [hsr]
    field_simp [hq_ne]
  have hp : 1 / ((q - 1) / q) = q / (q - 1) := by
    field_simp [hq_ne, ne_of_gt hqm1_pos]
  set D : ℝ := (δ * (q / (q - 1))) ^ ((q - 1) / q) with hD
  have hD_pos : 0 < D := by
    dsimp [D]
    exact Real.rpow_pos_of_pos
      (mul_pos hδ (div_pos hq_pos hqm1_pos)) _
  have hconst :
      ((M / D) ^ q) / q =
        (((1 / D) ^ q) / q) * M ^ q := by
    rw [div_eq_mul_inv M D,
      Real.mul_rpow hM (inv_nonneg.mpr hD_pos.le)]
    field_simp [ne_of_gt hq_pos]
  calc
    M * S ^ ((q - 1) / q)
        ≤ δ * S +
          ((M / (δ * (q / (q - 1))) ^ ((q - 1) / q)) ^ q) / q := by
          simpa [Real.rpow_one, hconj, hp, div_one] using hy
    _ = δ * S + (((1 / D) ^ q) / q) * M ^ q := by
          rw [hD, hconst]

/-- Convert a pointwise Agmon bound on `f^q` into the mass-supremum
interpolation precursor `∫ f^q ≤ S^((q-1)/q) ∫ f`. -/
theorem intervalDomain_integral_rpow_le_mass_agmon_rpow
    {q S : ℝ} {f : intervalDomain.Point → ℝ}
    (hq : 1 < q)
    (hf_pos : ∀ x, 0 < f x)
    (hfC2 : ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1))
    (hpoint : ∀ y ∈ Set.Icc (0 : ℝ) 1, (intervalDomainLift f y) ^ q ≤ S) :
    intervalDomain.integral (fun x => f x ^ q) ≤
      S ^ ((q - 1) / q) * intervalDomain.integral f := by
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hr_nonneg : 0 ≤ (q - 1) / q :=
    (div_pos (sub_pos.mpr hq) hq_pos).le
  have hleft_cont :
      ContinuousOn (fun y => (intervalDomainLift f y) ^ q) (Set.Icc (0 : ℝ) 1) :=
    hfC2.continuousOn.rpow_const
      (fun y hy => Or.inl (intervalDomainLift_ne_on_Icc hf_pos y hy))
  have hleft_int :
      IntervalIntegrable (fun y => (intervalDomainLift f y) ^ q) volume (0 : ℝ) 1 :=
    (hleft_cont.mono
      (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)])).intervalIntegrable
  have hright_int :
      IntervalIntegrable
        (fun y => S ^ ((q - 1) / q) * intervalDomainLift f y)
        volume (0 : ℝ) 1 := by
    have hright_cont : ContinuousOn
        (fun y => S ^ ((q - 1) / q) * intervalDomainLift f y)
        (Set.uIcc (0 : ℝ) 1) := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact continuousOn_const.mul hfC2.continuousOn
    exact hright_cont.intervalIntegrable
  have hpt :
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        (intervalDomainLift f y) ^ q ≤
          S ^ ((q - 1) / q) * intervalDomainLift f y := by
    intro y hy
    have hpos := intervalDomainLift_pos_on_Icc hf_pos y hy
    have hmono :
        ((intervalDomainLift f y) ^ q) ^ ((q - 1) / q) ≤
          S ^ ((q - 1) / q) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hpos.le q) (hpoint y hy) hr_nonneg
    have hpowr :
        (intervalDomainLift f y) ^ (q - 1) =
          ((intervalDomainLift f y) ^ q) ^ ((q - 1) / q) := by
      have hmul : q * ((q - 1) / q) = q - 1 := by
        field_simp [hq_ne]
      calc
        (intervalDomainLift f y) ^ (q - 1)
            = (intervalDomainLift f y) ^ (q * ((q - 1) / q)) := by rw [hmul]
        _ = ((intervalDomainLift f y) ^ q) ^ ((q - 1) / q) := by
              rw [Real.rpow_mul hpos.le]
    have hsplit :
        (intervalDomainLift f y) ^ q =
          intervalDomainLift f y * (intervalDomainLift f y) ^ (q - 1) := by
      calc
        (intervalDomainLift f y) ^ q
            = (intervalDomainLift f y) ^ ((1 : ℝ) + (q - 1)) := by ring_nf
        _ = (intervalDomainLift f y) ^ (1 : ℝ) *
              (intervalDomainLift f y) ^ (q - 1) := by
              exact Real.rpow_add hpos (1 : ℝ) (q - 1)
        _ = intervalDomainLift f y * (intervalDomainLift f y) ^ (q - 1) := by
              rw [Real.rpow_one]
    calc
      (intervalDomainLift f y) ^ q
          = intervalDomainLift f y * (intervalDomainLift f y) ^ (q - 1) := hsplit
      _ = intervalDomainLift f y *
            ((intervalDomainLift f y) ^ q) ^ ((q - 1) / q) := by rw [hpowr]
      _ ≤ intervalDomainLift f y * S ^ ((q - 1) / q) :=
            mul_le_mul_of_nonneg_left hmono hpos.le
      _ = S ^ ((q - 1) / q) * intervalDomainLift f y := by ring
  rw [intervalDomain_integral_rpow_eq_lift_integral (q := q) (f := f)]
  calc
    (∫ y in (0 : ℝ)..1, (intervalDomainLift f y) ^ q)
        ≤ ∫ y in (0 : ℝ)..1,
            S ^ ((q - 1) / q) * intervalDomainLift f y :=
          intervalIntegral.integral_mono_on
            (by norm_num : (0 : ℝ) ≤ 1) hleft_int hright_int hpt
    _ = S ^ ((q - 1) / q) * intervalDomain.integral f := by
          change (∫ y in (0 : ℝ)..1,
              S ^ ((q - 1) / q) * intervalDomainLift f y) =
            S ^ ((q - 1) / q) * (∫ y in (0 : ℝ)..1, intervalDomainLift f y)
          rw [intervalIntegral.integral_const_mul]

/-- A single-slice mass-gradient interpolation inequality with a constant
allowed to depend on the slice.

This is not the uniform Agmon/Gagliardo-Nirenberg estimate used by the Moser
iteration.  It is a sanity lemma for the current algebraic inequality shape:
if the mass term is positive, a sufficiently large positive coefficient on
that mass term dominates the left side, regardless of the sign of the gradient
integral as represented by the abstract interval integral. -/
theorem intervalDomain_agmon_interpolation_slice
    {f : intervalDomain.Point → ℝ} {q eps : ℝ}
    (hmass : 0 < intervalDomain.integral f) :
    ∃ Ceps > 0,
      intervalDomain.integral (fun x => f x ^ q) ≤
        eps * intervalDomain.integral
          (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) +
        Ceps * (intervalDomain.integral f) ^ q := by
  set A : ℝ := intervalDomain.integral (fun x => f x ^ q)
  set G : ℝ := intervalDomain.integral
    (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2)
  set B : ℝ := (intervalDomain.integral f) ^ q with hB_def
  have hBpos : 0 < B := by
    rw [hB_def]
    exact Real.rpow_pos_of_pos hmass q
  refine ⟨(|A| + |eps * G| + 1) / B, ?_, ?_⟩
  · exact div_pos (by positivity) hBpos
  · have hBne : B ≠ 0 := ne_of_gt hBpos
    have hmul :
        ((|A| + |eps * G| + 1) / B) * B =
          |A| + |eps * G| + 1 := by
      field_simp [hBne]
    have hA_le : A ≤ |A| := le_abs_self A
    have hEG_nonneg : 0 ≤ eps * G + |eps * G| := by
      rcases le_total 0 (eps * G) with hnonneg | hnonpos
      · have habs : |eps * G| = eps * G := abs_of_nonneg hnonneg
        rw [habs]
        nlinarith
      · have habs : |eps * G| = -(eps * G) := abs_of_nonpos hnonpos
        rw [habs]
        ring_nf
        norm_num
    calc
      A ≤ eps * G + (|A| + |eps * G| + 1) := by nlinarith
      _ = eps * G + ((|A| + |eps * G| + 1) / B) * B := by rw [hmul]
      _ = eps * G + ((|A| + |eps * G| + 1) / B) *
          (intervalDomain.integral f) ^ q := by rw [hB_def]

/-- Uniform positive one-dimensional Agmon/Gagliardo-Nirenberg frontier on
the unit interval.

The constant is chosen from `q` and `eps` before the particular positive
slice `f` is supplied.  This is the quantifier order needed by classical
solution slices, whose `LpMassGradientInterpolationEstimate` must use one
constant for all `t ∈ (0,T)`.

The `ContDiffOn ℝ 2` hypothesis is intentionally part of the frontier: the
weaker old `ContinuousOn` plus open-interval differentiability interface did
not carry enough analytic information for the FTC/integrability steps behind
Agmon. -/
def UnitIntervalPositiveAgmonInterpolation : Prop :=
  ∀ q : ℝ, 1 < q →
  ∀ eps : ℝ, 0 < eps →
    ∃ Ceps > 0,
      ∀ f : intervalDomain.Point → ℝ,
        (∀ x, 0 < f x) →
        ContDiffOn ℝ 2 (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) →
          intervalDomain.integral (fun x => f x ^ q) ≤
            eps * intervalDomain.integral
              (fun x => f x ^ (q - 2) *
                (intervalDomain.gradNorm f x) ^ 2) +
            Ceps * (intervalDomain.integral f) ^ q

/-- The positive C² unit-interval Agmon interpolation frontier. -/
theorem unitIntervalPositiveAgmonInterpolation :
    UnitIntervalPositiveAgmonInterpolation := by
  intro q hq eps heps
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_sq_pos : 0 < q ^ 2 := sq_pos_of_ne_zero (ne_of_gt hq_pos)
  let δ : ℝ := min (1 / 8) (eps / (8 * q ^ 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num)
      (div_pos heps (mul_pos (by norm_num) hq_sq_pos))
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδ_le_eighth : δ ≤ 1 / 8 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_lt_quarter : δ < 1 / 4 := by
    linarith
  have hδ_le_eps_q : δ ≤ eps / (8 * q ^ 2) := by
    dsimp [δ]
    exact min_le_right _ _
  have hden_pos : 0 < 1 - 2 * δ := by
    linarith
  have hcoeff_le :
      δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 ≤ eps := by
    have hδq : δ * q ^ 2 ≤ eps / 8 := by
      have hmul := mul_le_mul_of_nonneg_right hδ_le_eps_q (sq_nonneg q)
      have hcancel : eps / (8 * q ^ 2) * q ^ 2 = eps / 8 := by
        field_simp [ne_of_gt hq_sq_pos]
      simpa [hcancel] using hmul
    have hδ2q : δ ^ 2 * q ^ 2 ≤ eps / 64 := by
      nlinarith [hδq, hδ_le_eighth, hδ_nonneg, heps]
    have hden_ge : (1 / 2 : ℝ) ≤ 1 - 2 * δ := by
      nlinarith
    have hden_sq_ge : (1 / 4 : ℝ) ≤ (1 - 2 * δ) ^ 2 := by
      nlinarith [sq_nonneg ((1 - 2 * δ) - (1 / 2 : ℝ))]
    have hmain : δ ^ 2 * q ^ 2 ≤ eps * (1 - 2 * δ) ^ 2 := by
      nlinarith
    rw [div_le_iff₀ (sq_pos_of_pos hden_pos)]
    exact hmain
  let Cyoung : ℝ :=
    ((1 / ((δ * (q / (q - 1))) ^ ((q - 1) / q))) ^ q) / q
  let Ceps : ℝ := max 1 (2 * Cyoung / (1 - 2 * δ))
  have hCeps_pos : 0 < Ceps := by
    dsimp [Ceps]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Ceps, hCeps_pos, ?_⟩
  intro f hf_pos hfC2
  set Y : ℝ := intervalDomain.integral (fun x => f x ^ q) with hY_def
  set G : ℝ := intervalDomain.integral
    (fun x => f x ^ (q - 2) * (intervalDomain.gradNorm f x) ^ 2) with hG_def
  set M : ℝ := intervalDomain.integral f with hM_def
  set S : ℝ := 2 * Y + q * Real.sqrt (Y * G) with hS_def
  have hY_nonneg : 0 ≤ Y := by
    rw [hY_def]
    exact intervalDomain_integral_rpow_nonneg (q := q) hf_pos
  have hG_nonneg : 0 ≤ G := by
    rw [hG_def]
    exact intervalDomain_integral_weighted_grad_nonneg (q := q) hf_pos
  have hM_pos : 0 < M := by
    rw [hM_def]
    exact intervalDomain_integral_pos hf_pos hfC2
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hMp_nonneg : 0 ≤ M ^ q := Real.rpow_nonneg hM_nonneg q
  have hS_nonneg : 0 ≤ S := by
    rw [hS_def]
    have hYG : 0 ≤ Y * G := mul_nonneg hY_nonneg hG_nonneg
    nlinarith [Real.sqrt_nonneg (Y * G), hq_pos]
  have hpoint :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, (intervalDomainLift f y) ^ q ≤ S := by
    intro y hy
    rw [hS_def, hY_def, hG_def]
    exact intervalDomainLift_rpow_agmon_bound_qsqrt hq hf_pos hfC2 hy
  have hmass_sup :
      Y ≤ S ^ ((q - 1) / q) * M := by
    rw [hY_def, hM_def]
    exact intervalDomain_integral_rpow_le_mass_agmon_rpow
      hq hf_pos hfC2 hpoint
  have hCyoung_nonneg : 0 ≤ Cyoung := by
    dsimp [Cyoung]
    exact div_nonneg
      (Real.rpow_nonneg
        (div_nonneg zero_le_one
          (Real.rpow_nonneg
            (mul_nonneg hδ_nonneg (div_nonneg hq_pos.le (sub_pos.mpr hq).le)) _))
        q)
      hq_pos.le
  have hyoung :
      M * S ^ ((q - 1) / q) ≤ δ * S + Cyoung * M ^ q := by
    dsimp [Cyoung]
    exact young_mass_agmon_absorb hq hδ_pos hM_nonneg hS_nonneg
  have hpre : Y ≤ δ * S + Cyoung * M ^ q := by
    calc
      Y ≤ S ^ ((q - 1) / q) * M := hmass_sup
      _ = M * S ^ ((q - 1) / q) := by ring
      _ ≤ δ * S + Cyoung * M ^ q := hyoung
  have hineq :
      Y ≤ 2 * δ * Y + δ * q * Real.sqrt (Y * G) + Cyoung * M ^ q := by
    rw [hS_def] at hpre
    nlinarith
  have habs := ShenWork.Paper2.IntervalDomainLemma41.interpolation_absorption
    (Y := Y) (G := G) (Mp := M ^ q) (δ := δ) (pv := q) (C := Cyoung)
    hY_nonneg hG_nonneg hMp_nonneg hδ_pos hδ_lt_quarter hq_pos
    hCyoung_nonneg hineq
  have hCabs_le : 2 * Cyoung / (1 - 2 * δ) ≤ Ceps := by
    dsimp [Ceps]
    exact le_max_right _ _
  have hfinal :
      Y ≤ eps * G + Ceps * M ^ q := by
    calc
      Y ≤ δ ^ 2 * q ^ 2 / (1 - 2 * δ) ^ 2 * G +
            2 * Cyoung / (1 - 2 * δ) * M ^ q := habs
      _ ≤ eps * G + Ceps * M ^ q := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hcoeff_le hG_nonneg)
              (mul_le_mul_of_nonneg_right hCabs_le hMp_nonneg)
  simpa [Y, G, M] using hfinal

#print axioms intervalDomain_agmon_interpolation_slice
#print axioms intervalDomainLift_rpow_agmon_bound
#print axioms unitIntervalPositiveAgmonInterpolation

end ShenWork.IntervalDomainExistence.IntervalAgmonInterpolation

end
