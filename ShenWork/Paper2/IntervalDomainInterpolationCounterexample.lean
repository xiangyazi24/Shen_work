import ShenWork.Paper2.IntervalDomainLemma41

/-!
# `IntervalDomainInterpolation` is FALSE as literally stated — counterexample.

⚠️ SOUNDNESS TAKEAWAY (hostile-opus audited 2026-06-11): `not_intervalDomainInterpolation`
below proves the EXACT `IntervalDomainInterpolation` Prop (IntervalDomainLemma41.lean:137)
is FALSE. The Prop quantifies over ALL positive interval functions with `gradNorm` =
the POINTWISE classical derivative `|deriv (intervalDomainLift f)|` (IntervalDomain.lean:2917)
and NO continuity / Sobolev / integrability hypothesis. A positive step function then has
`gradNorm = 0` a.e. (classical deriv vanishes off the jump) yet nonzero L² mass, defeating
the inequality for small `a`.

CONSEQUENCE: the conditional `Lemma_4_1_intervalDomain_of_interpolation` rests on a
hypothesis that can NEVER be satisfied as written — it is vacuously dischargeable, NOT a
real proof of Lemma 4.1. To become a true theorem, `IntervalDomainInterpolation` must add
a regularity hypothesis (continuity / `f ∈ H¹` / `f, f' ∈ L²`), or `gradNorm` must be
upgraded to a weak derivative (so a jump contributes a delta). Gagliardo–Nirenberg holds
for Sobolev functions; the literal Prop does not.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.Paper2.IntervalDomainInterpolationCounterexample

open ShenWork.IntervalDomain
open ShenWork.Paper2.IntervalDomainLemma41

def leftIndicator (a : ℝ) : ℝ → ℝ :=
  ({x : ℝ | x ≤ a} : Set ℝ).indicator fun _ : ℝ => (1 : ℝ)

def intervalStepProfile (a x : ℝ) : ℝ :=
  a ^ 2 + (1 - a ^ 2) * leftIndicator a x

def intervalStep (a : ℝ) : intervalDomainPoint → ℝ :=
  fun x => intervalStepProfile a x.1

lemma ae_ne_singleton (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ a := by
  rw [MeasureTheory.ae_iff]
  simp

lemma leftIndicator_intervalIntegrable (a : ℝ) :
    IntervalIntegrable (leftIndicator a) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  unfold leftIndicator
  exact
    (integrableOn_const
        (hs := by simp [Real.volume_Ioc])
        (hC := by simp) :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc 0 1) volume).indicator
        measurableSet_Iic

lemma leftIndicator_integral_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ x in (0 : ℝ)..1, leftIndicator a x = a := by
  unfold leftIndicator
  rw [intervalIntegral.integral_indicator (show a ∈ Set.Icc (0 : ℝ) 1 from
    ⟨ha0, ha1⟩)]
  rw [intervalIntegral.integral_const]
  simp

lemma interval_integral_const_add_indicator
    {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ x in (0 : ℝ)..1, b + c * leftIndicator a x = b + c * a := by
  have hconst :
      IntervalIntegrable (fun _ : ℝ => b) volume 0 1 :=
    intervalIntegrable_const
  have hind : IntervalIntegrable
      (fun x : ℝ => c * leftIndicator a x) volume 0 1 :=
    (leftIndicator_intervalIntegrable a).const_mul c
  rw [intervalIntegral.integral_add hconst hind]
  rw [intervalIntegral.integral_const_mul]
  rw [leftIndicator_integral_eq ha0 ha1]
  rw [intervalIntegral.integral_const]
  simp

lemma intervalStepProfile_eq_if (a x : ℝ) :
    intervalStepProfile a x = if x ≤ a then 1 else a ^ 2 := by
  by_cases hx : x ≤ a
  · simp [intervalStepProfile, leftIndicator, hx]
  · simp [intervalStepProfile, leftIndicator, hx]

lemma intervalStep_pos {a : ℝ} (ha : 0 < a) (x : intervalDomainPoint) :
    0 < intervalStep a x := by
  rw [intervalStep, intervalStepProfile_eq_if]
  by_cases hx : (x.1 : ℝ) ≤ a
  · simp [hx]
  · simp [hx, sq_pos_of_pos ha]

lemma intervalStep_lift_eq_profile {a x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (intervalStep a) x = intervalStepProfile a x := by
  simp [intervalDomainLift, intervalStep, hx]

lemma intervalStep_mass_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    intervalDomain.integral (intervalStep a) =
      a ^ 2 + (1 - a ^ 2) * a := by
  change ∫ x in (0 : ℝ)..1, intervalDomainLift (intervalStep a) x =
    a ^ 2 + (1 - a ^ 2) * a
  rw [intervalIntegral.integral_congr (fun x hx => by
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    exact intervalStep_lift_eq_profile (a := a) hxIcc)]
  exact interval_integral_const_add_indicator ha0 ha1

lemma intervalStep_mass_le_two_mul {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    intervalDomain.integral (intervalStep a) ≤ 2 * a := by
  rw [intervalStep_mass_eq ha0 ha1]
  nlinarith [sq_nonneg a, mul_nonneg ha0 (sub_nonneg.mpr ha1)]

lemma intervalStep_mass_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ intervalDomain.integral (intervalStep a) := by
  rw [intervalStep_mass_eq ha0 ha1]
  have hnonneg : 0 ≤ a ^ 2 * (1 - a) :=
    mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha1)
  nlinarith

lemma intervalStepProfile_rpow_two_eq (a x : ℝ) :
    (intervalStepProfile a x) ^ (2 : ℝ) =
      a ^ 4 + (1 - a ^ 4) * leftIndicator a x := by
  rw [intervalStepProfile_eq_if]
  by_cases hx : x ≤ a
  · simp [leftIndicator, hx]
  · simp [leftIndicator, hx]
    ring

lemma intervalStep_L2_integral_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    intervalDomain.integral (fun x => (intervalStep a x) ^ (2 : ℝ)) =
      a ^ 4 + (1 - a ^ 4) * a := by
  calc
    intervalDomain.integral (fun x => (intervalStep a x) ^ (2 : ℝ))
        = ∫ x in (0 : ℝ)..1, (intervalStepProfile a x) ^ (2 : ℝ) := by
          change ∫ x in (0 : ℝ)..1,
              intervalDomainLift (fun x => (intervalStep a x) ^ (2 : ℝ)) x =
            ∫ x in (0 : ℝ)..1, (intervalStepProfile a x) ^ (2 : ℝ)
          exact intervalIntegral.integral_congr fun x hx => by
            have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
              simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
            simp [intervalDomainLift, intervalStep, hxIcc]
    _ = ∫ x in (0 : ℝ)..1,
          a ^ 4 + (1 - a ^ 4) * leftIndicator a x := by
          exact intervalIntegral.integral_congr fun x _ =>
            intervalStepProfile_rpow_two_eq a x
    _ = a ^ 4 + (1 - a ^ 4) * a :=
          interval_integral_const_add_indicator ha0 ha1

lemma intervalStep_L2_integral_ge_a {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a ≤ intervalDomain.integral (fun x => (intervalStep a x) ^ (2 : ℝ)) := by
  rw [intervalStep_L2_integral_eq ha0 ha1]
  have hpow4 : 0 ≤ a ^ 4 := by positivity
  have hnonneg : 0 ≤ a ^ 4 * (1 - a) :=
    mul_nonneg hpow4 (sub_nonneg.mpr ha1)
  nlinarith

lemma intervalStep_lift_deriv_eq_zero
    {a x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hxa : x ≠ a) :
    deriv (intervalDomainLift (intervalStep a)) x = 0 := by
  by_cases hle : x ≤ a
  · have hlt : x < a := lt_of_le_of_ne hle hxa
    have hloc :
        intervalDomainLift (intervalStep a) =ᶠ[𝓝 x] fun _ : ℝ => (1 : ℝ) := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2, Iic_mem_nhds hlt] with y hyI hy_le
      have hy_le' : y ≤ a := hy_le
      simp [intervalDomainLift, intervalStep, intervalStepProfile_eq_if, hyI,
        hy_le']
    rw [hloc.deriv_eq]
    simp
  · have hgt : a < x := lt_of_not_ge hle
    have hloc :
        intervalDomainLift (intervalStep a) =ᶠ[𝓝 x] fun _ : ℝ => a ^ 2 := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2, isOpen_Ioi.mem_nhds hgt] with
        y hyI hy_gt
      have hy_not_le : ¬y ≤ a := not_le.mpr hy_gt
      simp [intervalDomainLift, intervalStep, intervalStepProfile_eq_if, hyI,
        hy_not_le]
    rw [hloc.deriv_eq]
    simp

lemma intervalStep_gradient_integral_eq_zero (a : ℝ) :
    intervalDomain.integral (fun x =>
      (intervalStep a x) ^ ((2 : ℝ) - 2) *
        (intervalDomain.gradNorm (intervalStep a) x) ^ 2) = 0 := by
  change ∫ x in (0 : ℝ)..1,
      intervalDomainLift (fun x =>
        (intervalStep a x) ^ ((2 : ℝ) - 2) *
          (intervalDomain.gradNorm (intervalStep a) x) ^ 2) x = 0
  apply intervalIntegral.integral_zero_ae
  filter_upwards [ae_ne_singleton a, ae_ne_singleton (1 : ℝ)] with
    x hx_ne_a hx_ne_one hx_interval
  have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx_interval
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxIoc.1.le, hxIoc.2⟩
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hx_ne_one⟩
  have hderiv := intervalStep_lift_deriv_eq_zero (a := a) hxIoo hx_ne_a
  simp [intervalDomainLift, intervalDomain, intervalDomainGradNorm, hxIcc, hderiv]

theorem not_intervalDomainInterpolation :
    ¬ IntervalDomainInterpolation := by
  intro hGN
  obtain ⟨C, hCpos, hC⟩ := hGN 1 (by norm_num) 2 (by norm_num)
  let a : ℝ := (8 * (C + 1))⁻¹
  have hden_pos : 0 < 8 * (C + 1) := by nlinarith
  have ha_pos : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr hden_pos
  have ha0 : 0 ≤ a := ha_pos.le
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (inv_lt_one_of_one_lt₀ (by nlinarith : 1 < 8 * (C + 1))).le
  have hfourCa_lt_one : 4 * C * a < 1 := by
    have hmul : a * (8 * (C + 1)) = 1 := by
      dsimp [a]
      field_simp [ne_of_gt hden_pos]
    nlinarith
  have hineq := hC (intervalStep a) (fun x _ => intervalStep_pos ha_pos x)
  have hG := intervalStep_gradient_integral_eq_zero a
  have hineq0 :
      intervalDomain.integral (fun x => (intervalStep a x) ^ (2 : ℝ)) ≤
        C * (intervalDomain.integral (intervalStep a)) ^ 2 := by
    have hG0 :
        intervalDomain.integral (fun x =>
          (intervalDomain.gradNorm (intervalStep a) x) ^ 2) = 0 := by
      simpa using hG
    simpa [hG0, Real.rpow_two] using hineq
  have hY_ge :
      a ≤ intervalDomain.integral (fun x => (intervalStep a x) ^ (2 : ℝ)) :=
    intervalStep_L2_integral_ge_a ha0 ha1
  have hM_le :
      intervalDomain.integral (intervalStep a) ≤ 2 * a :=
    intervalStep_mass_le_two_mul ha0 ha1
  have hM_nonneg : 0 ≤ intervalDomain.integral (intervalStep a) :=
    intervalStep_mass_nonneg ha0 ha1
  have htwoa_nonneg : 0 ≤ 2 * a := by linarith
  have hM_sq_le :
      (intervalDomain.integral (intervalStep a)) ^ 2 ≤ (2 * a) ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg hM_nonneg, abs_of_nonneg htwoa_nonneg] using hM_le)
  have hmain : a ≤ C * (2 * a) ^ 2 := by
    calc
      a ≤ intervalDomain.integral (fun x => (intervalStep a x) ^ (2 : ℝ)) := hY_ge
      _ ≤ C * (intervalDomain.integral (intervalStep a)) ^ 2 := hineq0
      _ ≤ C * (2 * a) ^ 2 := mul_le_mul_of_nonneg_left hM_sq_le hCpos.le
  have hstrict : C * (2 * a) ^ 2 < a := by
    calc
      C * (2 * a) ^ 2 = (4 * C * a) * a := by ring
      _ < 1 * a := mul_lt_mul_of_pos_right hfourCa_lt_one ha_pos
      _ = a := by ring
  linarith

#print axioms not_intervalDomainInterpolation

end ShenWork.Paper2.IntervalDomainInterpolationCounterexample

end
