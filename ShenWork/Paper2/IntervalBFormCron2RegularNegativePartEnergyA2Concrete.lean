import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalChiNegTruncatedRestartStrictPosProducer

open MeasureTheory Set Filter
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure
   intervalMeasure_integrable_of_abs_bound)
open ShenWork.IntervalMildPicard (HasContinuousSlices)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

theorem truncatedPicard_A2_neg_deriv_zero_on_pos
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hcont_lift : ∀ t, 0 < t → t ≤ T →
      ∀ᵐ x ∂ intervalMeasure 1,
        ContinuousAt
          (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x) :
    ∀ t, 0 < t → t ≤ T →
      ∀ᵐ x ∂ intervalMeasure 1,
        0 < intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t) x →
          deriv (negativePartLift (truncatedConjugatePicardLimit p u₀ T t)) x = 0 := by
  intro t ht htT
  filter_upwards [hcont_lift t ht htT] with x hx hpos
  exact deriv_negativePartLift_eq_zero_of_pos hx hpos

theorem truncatedPicard_A2_time_chain
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ} {E' : ℝ → ℝ}
    (hE : ∀ t, 0 < t → t ≤ T →
      E' t =
        2 * (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                ShenWork.IntervalDomain.intervalDomain.timeDeriv
                  (truncatedConjugatePicardLimit p u₀ T) t z) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
          ∂ intervalMeasure 1)) :
    ∀ t, 0 < t → t ≤ T →
      (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                ShenWork.IntervalDomain.intervalDomain.timeDeriv
                  (truncatedConjugatePicardLimit p u₀ T) t z) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
          ∂ intervalMeasure 1)
        = (1 / 2 : ℝ) * E' t := by
  intro t ht htT
  nlinarith [hE t ht htT]

theorem truncatedPicard_A2_diffusion_chain
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T : ℝ}
    (hdiff : ∀ t, 0 < t → t ≤ T →
      (fun x =>
        deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x *
          deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t) x)
        =ᵐ[intervalMeasure 1]
      fun x =>
        (deriv (negativePartLift
          (truncatedConjugatePicardLimit p u₀ T t)) x) ^ 2) :
    ∀ t, 0 < t → t ≤ T →
      (∫ x,
          deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x *
            deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t) x
          ∂ intervalMeasure 1)
        = negativePartDissipation (truncatedConjugatePicardLimit p u₀ T) t := by
  intro t ht htT
  unfold negativePartDissipation
  exact integral_congr_ae (hdiff t ht htT)

theorem truncatedPicard_A2_diffusion_nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T t : ℝ} :
    0 ≤ negativePartDissipation (truncatedConjugatePicardLimit p u₀ T) t := by
  unfold negativePartDissipation
  exact integral_nonneg_of_ae
    (Eventually.of_forall fun x =>
      sq_nonneg (deriv (negativePartLift
        (truncatedConjugatePicardLimit p u₀ T t)) x))

theorem truncatedPicard_A2_logistic_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T R : ℝ}
    (hR : 0 < R)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ T t x| ≤ R)
    (hmeas : ∀ t, 0 < t → t ≤ T →
      AEStronglyMeasurable
        (fun x =>
          truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
        (intervalMeasure 1)) :
    ∀ t, 0 < t → t ≤ T →
      Integrable
        (fun x =>
          truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
        (intervalMeasure 1) := by
  intro t ht htT
  let Mlog : ℝ := R * (p.a + p.b * R ^ p.α)
  refine intervalMeasure_integrable_of_abs_bound (M := Mlog * R)
    (hmeas t ht htT) ?_
  intro y
  have hlog :
      |truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) y|
        ≤ Mlog := by
    simpa [Mlog] using
      truncatedLogisticLifted_bound_of_ball p hR
        (hbound t ht htT) y
  have hneg :
      |negativePartTest (truncatedConjugatePicardLimit p u₀ T) t y| ≤ R := by
    have hlift :
        |intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t) y| ≤ R := by
      by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
      · simpa [intervalDomainLift, hy] using hbound t ht htT ⟨y, hy⟩
      · simp [intervalDomainLift, hy, le_of_lt hR]
    have hneg_lift :
        |negativePartLift (truncatedConjugatePicardLimit p u₀ T t) y| ≤ R :=
      (negativePart_abs_le_abs
        (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t) y)).trans hlift
    simpa [negativePartTest, abs_neg] using hneg_lift
  have hMlog_nonneg : 0 ≤ Mlog := (abs_nonneg _).trans hlog
  rw [abs_mul]
  exact mul_le_mul hlog hneg (abs_nonneg _) hMlog_nonneg

def truncatedPicard_A2Data_of_concrete_fields
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {T R : ℝ} {E' : ℝ → ℝ}
    (hR : 0 < R)
    (hcont_lift : ∀ t, 0 < t → t ≤ T →
      ∀ᵐ x ∂ intervalMeasure 1,
        ContinuousAt
          (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x)
    (hE : ∀ t, 0 < t → t ≤ T →
      E' t =
        2 * (∫ x,
          intervalDomainLift
              (fun z : intervalDomainPoint =>
                ShenWork.IntervalDomain.intervalDomain.timeDeriv
                  (truncatedConjugatePicardLimit p u₀ T) t z) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x
          ∂ intervalMeasure 1))
    (hdiff : ∀ t, 0 < t → t ≤ T →
      (fun x =>
        deriv (intervalDomainLift (truncatedConjugatePicardLimit p u₀ T t)) x *
          deriv (negativePartTest (truncatedConjugatePicardLimit p u₀ T) t) x)
        =ᵐ[intervalMeasure 1]
      fun x =>
        (deriv (negativePartLift
          (truncatedConjugatePicardLimit p u₀ T t)) x) ^ 2)
    (hbound : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ T t x| ≤ R)
    (hmeas : ∀ t, 0 < t → t ≤ T →
      AEStronglyMeasurable
        (fun x =>
          truncatedLogisticLifted p (truncatedConjugatePicardLimit p u₀ T t) x *
            negativePartTest (truncatedConjugatePicardLimit p u₀ T) t x)
        (intervalMeasure 1))
    (henergy : ∀ t, 0 < t → t ≤ T →
      Integrable
        (fun x =>
          (negativePartLift (truncatedConjugatePicardLimit p u₀ T t) x) ^ 2)
        (intervalMeasure 1)) :
    TruncatedPicardNegativePartEnergyEstimateA2Data p (u₀ := u₀) T E' where
  neg_deriv_zero_on_pos :=
    truncatedPicard_A2_neg_deriv_zero_on_pos hcont_lift
  time_chain := truncatedPicard_A2_time_chain hE
  diffusion_chain := truncatedPicard_A2_diffusion_chain hdiff
  diffusion_nonneg := fun _ _ _ => truncatedPicard_A2_diffusion_nonneg
  logistic_integrable :=
    truncatedPicard_A2_logistic_integrable hR hbound hmeas
  energy_integrable := henergy

end ShenWork.Paper2.BFormPositiveDatumNegPart
