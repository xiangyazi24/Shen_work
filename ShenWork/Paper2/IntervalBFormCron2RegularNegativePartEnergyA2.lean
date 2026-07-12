import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

lemma negativePart_abs_le_abs (r : ℝ) : |negativePart r| ≤ |r| := by
  by_cases hr : 0 ≤ r
  · simp [negativePart_eq_zero_of_nonneg hr]
  · have hrle : r ≤ 0 := le_of_lt (lt_of_not_ge hr)
    simp [negativePart_eq_neg_of_nonpos hrle, abs_neg]

lemma negativePart_sq_abs_le_sq_abs (r : ℝ) :
    |(negativePart r)^2| ≤ |r^2| := by
  have hsq : |negativePart r| ^ 2 ≤ |r| ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (negativePart_abs_le_abs r) 2
  simpa [abs_pow] using hsq

lemma negativePart_sq_hasDerivAt_zero :
    HasDerivAt (fun r : ℝ => (negativePart r)^2) 0 0 := by
  refine HasDerivAt.of_isLittleO ?_
  have hO :
      (fun r : ℝ => (negativePart r)^2) =O[𝓝 (0 : ℝ)]
        fun r : ℝ => r ^ 2 := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [] with r
    simpa [one_mul, Real.norm_eq_abs] using negativePart_sq_abs_le_sq_abs r
  have ho : (fun r : ℝ => r ^ 2) =o[𝓝 (0 : ℝ)] fun r : ℝ => r := by
    simpa using
      (Asymptotics.isLittleO_pow_id (𝕜 := ℝ) (by norm_num : 1 < 2))
  simpa [negativePart_eq_zero_of_nonneg (le_refl (0 : ℝ))]
    using hO.trans_isLittleO ho

theorem negativePart_sq_hasDerivAt (r : ℝ) :
    HasDerivAt (fun y : ℝ => (negativePart y)^2)
      (-2 * negativePart r) r := by
  rcases lt_trichotomy r 0 with hneg | hzero | hpos
  · have hnhds : Set.Iio (0 : ℝ) ∈ 𝓝 r := isOpen_Iio.mem_nhds hneg
    have hev :
        (fun y : ℝ => (negativePart y)^2) =ᶠ[𝓝 r]
          (fun y : ℝ => y^2) := by
      filter_upwards [hnhds] with y hy
      simp [negativePart_eq_neg_of_nonpos (le_of_lt hy)]
    have hsq : HasDerivAt (fun y : ℝ => y^2) (2 * r) r := by
      simpa using (hasDerivAt_pow (2 : ℕ) r)
    have hder : (2 * r : ℝ) = -2 * negativePart r := by
      rw [negativePart_eq_neg_of_nonpos (le_of_lt hneg)]
      ring
    exact (hsq.congr_of_eventuallyEq hev).congr_deriv hder
  · subst r
    simpa [negativePart_eq_zero_of_nonneg (le_refl (0 : ℝ))]
      using negativePart_sq_hasDerivAt_zero
  · have hnhds : Set.Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds hpos
    have hev :
        (fun y : ℝ => (negativePart y)^2) =ᶠ[𝓝 r]
          (fun _ : ℝ => (0 : ℝ)) := by
      filter_upwards [hnhds] with y hy
      simp [negativePart_eq_zero_of_nonneg hy.le]
    simpa [negativePart_eq_zero_of_nonneg hpos.le] using
      (hasDerivAt_const (x := r) (c := (0 : ℝ))).congr_of_eventuallyEq hev

theorem negativePart_sq_deriv :
    deriv (fun y : ℝ => (negativePart y)^2)
      = fun r : ℝ => -2 * negativePart r :=
  deriv_eq negativePart_sq_hasDerivAt

lemma negativePart_continuous : Continuous fun r : ℝ => negativePart r := by
  simpa [negativePart] using (continuous_id.neg.max continuous_const)

theorem negativePart_sq_deriv_continuous :
    Continuous fun r : ℝ => -2 * negativePart r :=
  continuous_const.mul negativePart_continuous

theorem negativePart_sq_contDiff_one :
    ContDiff ℝ 1 fun r : ℝ => (negativePart r)^2 := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r => (negativePart_sq_hasDerivAt r).differentiableAt, ?_⟩
  rw [negativePart_sq_deriv]
  exact negativePart_sq_deriv_continuous

lemma negativePart_sq_time_hasDerivAt
    {v : ℝ → ℝ} {t v' : ℝ} (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => (negativePart (v s))^2)
      ((-2 * negativePart (v t)) * v') t := by
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    (negativePart_sq_hasDerivAt (v t)).comp t hv

lemma truncatedChemFluxLifted_eq_zero_of_lift_nonpos
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {x : ℝ}
    (hx : intervalDomainLift w x ≤ 0) :
    truncatedChemFluxLifted p w x = 0 := by
  have hpp : positivePart (intervalDomainLift w x) = 0 :=
    positivePart_eq_zero_of_nonpos hx
  simp [truncatedChemFluxLifted, hpp]

theorem negativePart_chemFlux_test_integral_eq_zero_regular
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (hdu_zero_on_pos :
      ∀ᵐ x ∂ intervalMeasure 1,
        0 < intervalDomainLift (u t) x →
          deriv (negativePartLift (u t)) x = 0) :
    (∫ x, truncatedChemFluxLifted p (u t) x * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1) = 0 := by
  refine truncatedChemFluxLifted_mul_negDeriv_integral_eq_zero
    (p := p) (w := u t)
    (duNeg := fun x => deriv (negativePartTest u t) x) ?_
  filter_upwards [hdu_zero_on_pos] with x hx hpos
  change deriv (-negativePartLift (u t)) x = 0
  rw [deriv.neg]
  simp [hx hpos]

lemma truncatedLogistic_negativePartTest_le_pointwise
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) :
    truncatedLogisticLifted p (u t) x * negativePartTest u t x
      ≤ p.a * (negativePartLift (u t) x)^2 := by
  simpa [truncatedLogisticLifted, negativePartLift, negativePartTest] using
    truncatedLogisticLocal_mul_neg_negativePart_le p
      (intervalDomainLift (u t) x)

theorem truncatedLogistic_negativePartTest_integral_le
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ)
    (hleft : Integrable
      (fun x => truncatedLogisticLifted p (u t) x * negativePartTest u t x)
      (intervalMeasure 1))
    (hE : Integrable (fun x => (negativePartLift (u t) x)^2)
      (intervalMeasure 1)) :
    (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
        ∂ intervalMeasure 1)
      ≤ p.a * negativePartEnergy u t := by
  have hright : Integrable (fun x => p.a * (negativePartLift (u t) x)^2)
      (intervalMeasure 1) := hE.const_mul p.a
  calc
    (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
        ∂ intervalMeasure 1)
        ≤ ∫ x, p.a * (negativePartLift (u t) x)^2
            ∂ intervalMeasure 1 := by
          exact MeasureTheory.integral_mono hleft hright
            (fun x => truncatedLogistic_negativePartTest_le_pointwise p u t x)
    _ = p.a * negativePartEnergy u t := by
          rw [MeasureTheory.integral_const_mul]
          rfl

theorem negativePart_energy_deriv_le_dissipation_regular
    {p : CM2Params} {T ell : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ} {E' : ℝ → ℝ}
    (H : NegativePartEnergyEstimateRegularData p T u ell E')
    {t : ℝ} (hweakTest : NegativePartWeakTestIdentityAt p u t)
    (ht : 0 < t) (htT : t ≤ T) :
    E' t ≤ -2 * negativePartDissipation u t
      + (2 * ell) * negativePartEnergy u t := by
  have hchem_neg :=
    negativePart_chemFlux_test_integral_eq_zero_regular p u t
      (H.neg_deriv_zero_on_pos t ht htT)
  have hmain :
      (1 / 2 : ℝ) * E' t + negativePartDissipation u t
        =
      (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
          ∂ intervalMeasure 1) := by
    calc
      (1 / 2 : ℝ) * E' t + negativePartDissipation u t
          =
        (∫ x,
            intervalDomainLift
                (fun z : intervalDomainPoint =>
                  intervalDomain.timeDeriv u t z) x * negativePartTest u t x
            ∂ intervalMeasure 1)
          + (∫ x,
              deriv (intervalDomainLift (u t)) x * deriv (negativePartTest u t) x
              ∂ intervalMeasure 1) := by
            rw [H.time_chain t ht htT, H.diffusion_chain t ht htT]
      _ =
          p.χ₀ *
            (∫ x,
              truncatedChemFluxLifted p (u t) x
                * deriv (negativePartTest u t) x
              ∂ intervalMeasure 1)
          + (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
              ∂ intervalMeasure 1) := hweakTest
      _ = (∫ x, truncatedLogisticLifted p (u t) x * negativePartTest u t x
              ∂ intervalMeasure 1) := by
            simp [hchem_neg]
  have hbound := H.reaction_bound t ht htT
  nlinarith

structure TruncatedPicardNegativePartEnergyEstimateA2Data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ} (T : ℝ)
    (E' : ℝ → ℝ) where
  neg_deriv_zero_on_pos :
    ∀ t, 0 < t → t ≤ T →
      ∀ᵐ x ∂ intervalMeasure 1,
        0 < intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t) x →
          deriv (negativePartLift (truncatedConjugatePicardLimit p u₀ T t)) x = 0
  time_chain :
    ∀ t, 0 < t → t ≤ T →
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                intervalDomain.timeDeriv (truncatedConjugatePicardLimit p u₀ T) t z) x
            * negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
          ∂ intervalMeasure 1) = (1 / 2 : ℝ) * E' t
  diffusion_chain :
    ∀ t, 0 < t → t ≤ T →
      (∫ x,
          deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x
            * deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t) x
          ∂ intervalMeasure 1)
        = negativePartDissipation (truncatedConjugatePicardLimit p u₀ T) t
  diffusion_nonneg :
    ∀ t, 0 < t → t ≤ T →
      0 ≤ negativePartDissipation (truncatedConjugatePicardLimit p u₀ T) t
  logistic_integrable :
    ∀ t, 0 < t → t ≤ T →
      Integrable
        (fun x =>
          truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x
            * negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
        (intervalMeasure 1)
  energy_integrable :
    ∀ t, 0 < t → t ≤ T →
      Integrable
        (fun x => (negativePartLift
          (truncatedConjugatePicardLimit p u₀ T t) x)^2)
        (intervalMeasure 1)

def TruncatedPicardNegativePartEnergyEstimateA2Data.toEstimate
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ} {E' : ℝ → ℝ}
    (H : TruncatedPicardNegativePartEnergyEstimateA2Data p (u₀ := u₀) T E') :
    NegativePartEnergyEstimateRegularData p T
      (truncatedConjugatePicardLimit p u₀ T) p.a E' where
  neg_deriv_zero_on_pos := H.neg_deriv_zero_on_pos
  time_chain := H.time_chain
  diffusion_chain := H.diffusion_chain
  diffusion_nonneg := H.diffusion_nonneg
  reaction_bound := by
    intro t ht htT
    exact truncatedLogistic_negativePartTest_integral_le p
      (truncatedConjugatePicardLimit p u₀ T) t
      (H.logistic_integrable t ht htT) (H.energy_integrable t ht htT)

end ShenWork.Paper2.BFormPositiveDatumNegPart
