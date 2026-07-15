import ShenWork.Paper1.WholeLineWeightedRegularityDuhamel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Time cancellation for the weighted `H²` Duhamel term

A raw generator estimate has the non-integrable endpoint kernel `r⁻¹`.
The correct decomposition subtracts the terminal source value inside the
generator and evaluates the constant-source part by the fundamental theorem
of calculus.  If the source is time Hölder with any exponent `theta > 0`,
the remaining kernel is `r⁻¹⁺ᵗʰᵉᵗᵃ`, hence integrable.

This file records that Banach-space core independently of the eventual
concrete realization of the conjugated whole-line heat generator on
`WholeLineRealL2`.
-/

section SingularKernel

/-- The generator kernel after a positive time-Hölder gain is locally
integrable.  The only threshold is `0 < theta`. -/
theorem intervalIntegrable_rpow_neg_one_add
    {theta a b : ℝ} (htheta : 0 < theta) :
    IntervalIntegrable (fun r : ℝ => r ^ (-1 + theta)) volume a b := by
  exact intervalIntegral.intervalIntegrable_rpow' (by linarith)

/-- Exact mass of the cancellation kernel on a finite forward interval. -/
theorem intervalIntegral_rpow_neg_one_add
    {theta h : ℝ} (htheta : 0 < theta) (_hh : 0 ≤ h) :
    (∫ r in (0 : ℝ)..h, r ^ (-1 + theta)) = h ^ theta / theta := by
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -1 + theta))]
  have htheta_ne : theta ≠ 0 := ne_of_gt htheta
  rw [show (-1 + theta : ℝ) + 1 = theta by ring,
    Real.zero_rpow htheta_ne, sub_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Banach-valued integral estimate for the cancellation kernel. -/
theorem intervalIntegral_norm_le_rpow_neg_one_add
    {theta h C : ℝ} (htheta : 0 < theta) (hh : 0 ≤ h)
    {Z : ℝ → E}
    (hZ : IntervalIntegrable Z volume 0 h)
    (hmajor : ∀ r ∈ Icc (0 : ℝ) h,
      ‖Z r‖ ≤ C * r ^ (-1 + theta)) :
    ‖∫ r in (0 : ℝ)..h, Z r‖ ≤ C * (h ^ theta / theta) := by
  let g : ℝ → ℝ := fun r => C * r ^ (-1 + theta)
  have hg : IntervalIntegrable g volume 0 h :=
    (intervalIntegrable_rpow_neg_one_add (a := 0) (b := h) htheta).const_mul C
  calc
    ‖∫ r in (0 : ℝ)..h, Z r‖ ≤ ∫ r in (0 : ℝ)..h, ‖Z r‖ :=
      intervalIntegral.norm_integral_le_integral_norm hh
    _ ≤ ∫ r in (0 : ℝ)..h, g r :=
      intervalIntegral.integral_mono_on hh hZ.norm hg hmajor
    _ = C * ∫ r in (0 : ℝ)..h, r ^ (-1 + theta) := by
      dsimp only [g]
      rw [intervalIntegral.integral_const_mul]
    _ = C * (h ^ theta / theta) := by
      rw [intervalIntegral_rpow_neg_one_add htheta hh]

/-- An `r⁻¹` generator bound combined with a time-Hölder source increment
produces the integrable `r⁻¹⁺ᵗʰᵉᵗᵃ` majorant. -/
theorem generator_holder_remainder_pointwise
    {theta h C H t : ℝ}
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hA : ∀ r ∈ Ioc (0 : ℝ) h, ‖A r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta) :
    ∀ r ∈ Icc (0 : ℝ) h,
      ‖A r (F (t - r) - F t)‖ ≤
        C * H * r ^ (-1 + theta) := by
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp only [sub_zero, sub_self, map_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hC hH)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) _)
  · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    have hAnorm : ‖A r‖ ≤ C * r ^ (-(1 : ℝ)) :=
      hA r ⟨hrpos, hr.2⟩
    have hFnorm : ‖F (t - r) - F t‖ ≤ H * r ^ theta := hF r hr
    calc
      ‖A r (F (t - r) - F t)‖ ≤
          ‖A r‖ * ‖F (t - r) - F t‖ :=
        (A r).le_opNorm (F (t - r) - F t)
      _ ≤ (C * r ^ (-(1 : ℝ))) * (H * r ^ theta) := by
        exact mul_le_mul hAnorm hFnorm (norm_nonneg _) (by positivity)
      _ = C * H * (r ^ (-(1 : ℝ)) * r ^ theta) := by ring
      _ = C * H * r ^ (-1 + theta) := by
        rw [← Real.rpow_add hrpos]

/-- Measurability plus the generator and Hölder bounds automatically give
Bochner integrability of the cancellative remainder. -/
theorem intervalIntegrable_generator_holder_remainder
    {theta h C H t : ℝ}
    (htheta : 0 < theta) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hA : ∀ r ∈ Ioc (0 : ℝ) h, ‖A r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta)
    (hmeas : AEStronglyMeasurable
      (fun r => A r (F (t - r) - F t))
      (volume.restrict (uIoc (0 : ℝ) h))) :
    IntervalIntegrable
      (fun r => A r (F (t - r) - F t)) volume 0 h := by
  have hg : IntervalIntegrable
      (fun r : ℝ => C * H * r ^ (-1 + theta)) volume 0 h :=
    (intervalIntegrable_rpow_neg_one_add
      (a := 0) (b := h) htheta).const_mul (C * H)
  refine IntervalIntegrable.mono_fun' hg hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  have hrIcc : r ∈ Icc (0 : ℝ) h := by
    rw [uIoc_of_le hh] at hr
    exact ⟨hr.1.le, hr.2⟩
  exact generator_holder_remainder_pointwise hC hH hA hF r hrIcc

/-- Integrated form of `generator_holder_remainder_pointwise`. -/
theorem intervalIntegral_generator_holder_remainder_norm_le
    {theta h C H t : ℝ}
    (htheta : 0 < theta) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hA : ∀ r ∈ Ioc (0 : ℝ) h, ‖A r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta)
    (hrem : IntervalIntegrable
      (fun r => A r (F (t - r) - F t)) volume 0 h) :
    ‖∫ r in (0 : ℝ)..h, A r (F (t - r) - F t)‖ ≤
      C * H * (h ^ theta / theta) := by
  apply intervalIntegral_norm_le_rpow_neg_one_add htheta hh hrem
  exact generator_holder_remainder_pointwise hC hH hA hF

end SingularKernel

section GeneratorCancellation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- Banach-valued generator orbit FTC on an arbitrary ordered interval. -/
theorem intervalIntegral_generator_orbit_eq_sub_of_le
    {a b : ℝ} (hab : a ≤ b) {orbit orbit' : ℝ → E}
    (hderiv : ∀ r ∈ Icc a b,
      HasDerivAt orbit (orbit' r) r)
    (hint : IntervalIntegrable orbit' volume a b) :
    (∫ r in a..b, orbit' r) = orbit b - orbit a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · simpa [uIcc_of_le hab] using hderiv
  · exact hint

/-- Banach-valued generator orbit FTC on a forward interval from zero. -/
theorem intervalIntegral_generator_orbit_eq_sub
    {h : ℝ} (hh : 0 ≤ h) {orbit orbit' : ℝ → E}
    (hderiv : ∀ r ∈ Icc (0 : ℝ) h,
      HasDerivAt orbit (orbit' r) r)
    (hint : IntervalIntegrable orbit' volume 0 h) :
    (∫ r in (0 : ℝ)..h, orbit' r) = orbit h - orbit 0 :=
  intervalIntegral_generator_orbit_eq_sub_of_le hh hderiv hint

/-- Truncated semigroup-generator cancellation.  This is the endpoint-safe
form: neither generator history is assumed integrable at `r = 0`.  It is the
identity to use before sending the positive cutoff `eps` to zero. -/
theorem intervalIntegral_generator_duhamel_cancellation_truncated
    {eps h t : ℝ} (hepsh : eps ≤ h)
    {S A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hfull : IntervalIntegrable
      (fun r => A r (F (t - r))) volume eps h)
    (hconst : IntervalIntegrable
      (fun r => A r (F t)) volume eps h)
    (horbit : ∀ r ∈ Icc eps h,
      HasDerivAt (fun q => S q (F t)) (A r (F t)) r) :
    (∫ r in eps..h, A r (F (t - r))) =
      (∫ r in eps..h, A r (F (t - r) - F t)) +
        (S h (F t) - S eps (F t)) := by
  have hrem : IntervalIntegrable
      (fun r => A r (F (t - r) - F t)) volume eps h := by
    simpa only [map_sub] using hfull.sub hconst
  have hftc : (∫ r in eps..h, A r (F t)) =
      S h (F t) - S eps (F t) := by
    exact intervalIntegral_generator_orbit_eq_sub_of_le
      hepsh horbit hconst
  have hsplit :
      (fun r => A r (F (t - r))) =
        fun r => A r (F (t - r) - F t) + A r (F t) := by
    funext r
    rw [map_sub]
    abel
  rw [hsplit, intervalIntegral.integral_add hrem hconst, hftc]

/-- The truncated generator histories converge to the cancellative endpoint
value.  Unlike the strong corollary below, this theorem never assumes that
`r ↦ A r (F t)` is integrable at zero.

The first limit input is supplied by time-Hölder regularity through
`intervalIntegral_generator_holder_remainder_norm_le`; the second is exactly
strong continuity of the heat semigroup at zero. -/
theorem tendsto_truncated_generator_duhamel_integral
    {h t : ℝ} (hh : 0 ≤ h)
    {eps : ℕ → ℝ}
    (heps_pos : ∀ n, 0 < eps n)
    (hepsh : ∀ n, eps n ≤ h)
    (heps : Tendsto eps atTop (𝓝 0))
    {S A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hrem : IntervalIntegrable
      (fun r => A r (F (t - r) - F t)) volume 0 h)
    (hfull : ∀ n, IntervalIntegrable
      (fun r => A r (F (t - r))) volume (eps n) h)
    (hconst : ∀ n, IntervalIntegrable
      (fun r => A r (F t)) volume (eps n) h)
    (horbit : ∀ n, ∀ r ∈ Icc (eps n) h,
      HasDerivAt (fun q => S q (F t)) (A r (F t)) r)
    (hSzero : Tendsto (fun n => S (eps n) (F t)) atTop (𝓝 (F t))) :
    Tendsto
      (fun n => ∫ r in eps n..h, A r (F (t - r)))
      atTop
      (𝓝 ((∫ r in (0 : ℝ)..h, A r (F (t - r) - F t)) +
        (S h - 1) (F t))) := by
  let R : ℝ → E := fun r => A r (F (t - r) - F t)
  let P : ℝ → E := fun e => ∫ r in (0 : ℝ)..e, R r
  have heps_mem : ∀ n, eps n ∈ uIcc (0 : ℝ) h := by
    intro n
    rw [uIcc_of_le hh]
    exact ⟨(heps_pos n).le, hepsh n⟩
  have hPcont : ContinuousOn P (uIcc (0 : ℝ) h) := by
    exact intervalIntegral.continuousOn_primitive_interval'
      (by simpa only [R] using hrem) left_mem_uIcc
  have hepsWithin : Tendsto eps atTop (𝓝[uIcc (0 : ℝ) h] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨heps, Eventually.of_forall heps_mem⟩
  have hPzero : P 0 = 0 := by simp [P]
  have hPtendsto : Tendsto (fun n => P (eps n)) atTop (𝓝 0) := by
    have hcomp := Filter.Tendsto.comp
      (hPcont 0 left_mem_uIcc) hepsWithin
    simpa [hPzero] using hcomp
  have hremTrunc : Tendsto
      (fun n => ∫ r in eps n..h, R r) atTop
      (𝓝 (∫ r in (0 : ℝ)..h, R r)) := by
    have hconstRem : Tendsto
        (fun _ : ℕ => ∫ r in (0 : ℝ)..h, R r) atTop
        (𝓝 (∫ r in (0 : ℝ)..h, R r)) := tendsto_const_nhds
    have ht := hconstRem.sub hPtendsto
    have ht' : Tendsto
        (fun n => (∫ r in (0 : ℝ)..h, R r) - P (eps n)) atTop
        (𝓝 (∫ r in (0 : ℝ)..h, R r)) := by
      simpa using ht
    refine Filter.Tendsto.congr' ?_ ht'
    filter_upwards with n
    have h0e : IntervalIntegrable R volume 0 (eps n) :=
      hrem.mono_set
        (uIcc_subset_uIcc left_mem_uIcc (heps_mem n))
    have heh : IntervalIntegrable R volume (eps n) h :=
      hrem.mono_set
        (uIcc_subset_uIcc (heps_mem n) right_mem_uIcc)
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0e heh
    have heq : (∫ r in eps n..h, R r) =
        (∫ r in (0 : ℝ)..h, R r) - ∫ r in (0 : ℝ)..eps n, R r := by
      rw [← hadd]
      abel
    simpa only [P] using heq.symm
  have horbitTrunc : Tendsto
      (fun n => S h (F t) - S (eps n) (F t)) atTop
      (𝓝 (S h (F t) - F t)) :=
    tendsto_const_nhds.sub hSzero
  have hsum := hremTrunc.add horbitTrunc
  apply hsum.congr'
  filter_upwards with n
  have hc := intervalIntegral_generator_duhamel_cancellation_truncated
    (hepsh n) (hfull n) (hconst n) (horbit n)
  rw [hc]

/-- Strong endpoint corollary of the truncated cancellation theorem.

This form assumes separate interval integrability of the full and
constant-source generator histories down to zero.  That hypothesis generally
fails for an order-one analytic generator, so the concrete weighted `H²`
route must use `tendsto_truncated_generator_duhamel_integral`, not this
corollary. -/
theorem intervalIntegral_generator_duhamel_cancellation
    {h t : ℝ} (hh : 0 ≤ h)
    {S A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hS0 : S 0 = 1)
    (hfull : IntervalIntegrable
      (fun r => A r (F (t - r))) volume 0 h)
    (hconst : IntervalIntegrable
      (fun r => A r (F t)) volume 0 h)
    (horbit : ∀ r ∈ Icc (0 : ℝ) h,
      HasDerivAt (fun q => S q (F t)) (A r (F t)) r) :
    (∫ r in (0 : ℝ)..h, A r (F (t - r))) =
      (∫ r in (0 : ℝ)..h, A r (F (t - r) - F t)) +
        (S h - 1) (F t) := by
  have hrem : IntervalIntegrable
      (fun r => A r (F (t - r) - F t)) volume 0 h := by
    simpa only [map_sub] using hfull.sub hconst
  have hftc : (∫ r in (0 : ℝ)..h, A r (F t)) =
      S h (F t) - S 0 (F t) := by
    exact intervalIntegral_generator_orbit_eq_sub hh horbit hconst
  have hsplit :
      (fun r => A r (F (t - r))) =
        fun r => A r (F (t - r) - F t) + A r (F t) := by
    funext r
    rw [map_sub]
    abel
  rw [hsplit, intervalIntegral.integral_add hrem hconst, hftc, hS0]
  rfl

/-- Norm form of the strong endpoint corollary.  It isolates the two genuine
inputs needed by the concrete weighted heat realization: a positive
time-Hölder modulus of the source and a bound on the semigroup increment.
For the actual singular endpoint, first use the truncated-limit theorem. -/
theorem intervalIntegral_generator_duhamel_norm_le_of_holder
    {theta h C H t : ℝ}
    (htheta : 0 < theta) (hh : 0 ≤ h)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    {S A : ℝ → E →L[ℝ] E} {F : ℝ → E}
    (hS0 : S 0 = 1)
    (hfull : IntervalIntegrable
      (fun r => A r (F (t - r))) volume 0 h)
    (hconst : IntervalIntegrable
      (fun r => A r (F t)) volume 0 h)
    (horbit : ∀ r ∈ Icc (0 : ℝ) h,
      HasDerivAt (fun q => S q (F t)) (A r (F t)) r)
    (hA : ∀ r ∈ Ioc (0 : ℝ) h, ‖A r‖ ≤ C * r ^ (-(1 : ℝ)))
    (hF : ∀ r ∈ Icc (0 : ℝ) h,
      ‖F (t - r) - F t‖ ≤ H * r ^ theta) :
    ‖∫ r in (0 : ℝ)..h, A r (F (t - r))‖ ≤
      C * H * (h ^ theta / theta) + ‖(S h - 1) (F t)‖ := by
  have hrem : IntervalIntegrable
      (fun r => A r (F (t - r) - F t)) volume 0 h := by
    simpa only [map_sub] using hfull.sub hconst
  rw [intervalIntegral_generator_duhamel_cancellation
    hh hS0 hfull hconst horbit]
  exact (norm_add_le _ _).trans
    (add_le_add
      (intervalIntegral_generator_holder_remainder_norm_le
        htheta hh hC hH hA hF hrem)
      le_rfl)

end GeneratorCancellation

section AxiomAudit

#print axioms intervalIntegral_rpow_neg_one_add
#print axioms intervalIntegral_norm_le_rpow_neg_one_add
#print axioms generator_holder_remainder_pointwise
#print axioms intervalIntegrable_generator_holder_remainder
#print axioms intervalIntegral_generator_holder_remainder_norm_le
#print axioms intervalIntegral_generator_orbit_eq_sub_of_le
#print axioms intervalIntegral_generator_orbit_eq_sub
#print axioms intervalIntegral_generator_duhamel_cancellation_truncated
#print axioms tendsto_truncated_generator_duhamel_integral
#print axioms intervalIntegral_generator_duhamel_cancellation
#print axioms intervalIntegral_generator_duhamel_norm_le_of_holder

end AxiomAudit

end ShenWork.Paper1
