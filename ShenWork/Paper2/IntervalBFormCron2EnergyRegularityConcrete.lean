import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergyA2
import ShenWork.Paper2.IntervalMildPicardRegularityEndpoint
import ShenWork.PDE.P3MoserGradientContinuityFromDx

open MeasureTheory Set Filter
open scoped Topology Interval

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalMildPicardRegularityEndpoint
open ShenWork.IntervalDomainExistence.P3MoserGradientIntegrability

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

private theorem intervalMeasure_integral_eq_intervalIntegral
    (f : ℝ → ℝ) :
    (∫ y, f y ∂ intervalMeasure 1) = ∫ y in (0 : ℝ)..1, f y := by
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  change (∫ y in Set.Icc (0 : ℝ) 1, f y ∂volume) =
    ∫ y in (0 : ℝ)..1, f y
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Concrete continuity of negative-part energy from joint continuity on the
closed time-space slab.  This is the dominated-convergence content needed for
`energy_cont`; `HasContinuousSlices` alone supplies only fixed-time spatial
continuity, so the time continuity is recorded explicitly as `hjoint`. -/
theorem energy_cont
    {T : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hjoint :
      ContinuousOn
        (fun z : ℝ × ℝ => intervalDomainLift (u z.1) z.2)
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (negativePartEnergy u) (Set.Icc (0 : ℝ) T) := by
  let F : ℝ → ℝ → ℝ :=
    fun t x => (negativePart (intervalDomainLift (u t) x)) ^ 2
  have hFcont :
      ContinuousOn (Function.uncurry F)
        (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hneg :
        ContinuousOn
          (fun z : ℝ × ℝ => negativePart (intervalDomainLift (u z.1) z.2))
          (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1) :=
      negativePart_continuous.continuousOn.comp hjoint
        (fun _ _ => Set.mem_univ _)
    simpa [F, Function.uncurry] using hneg.pow 2
  have hint :
      ContinuousOn (fun t => ∫ x in (0 : ℝ)..1, F t x)
        (Set.Icc (0 : ℝ) T) :=
    continuousOn_intervalIntegral_zero_one_of_continuousOn_Icc_prod hFcont
  have hrewrite :
      (negativePartEnergy u) = fun t => ∫ x in (0 : ℝ)..1, F t x := by
    funext t
    simp [negativePartEnergy, negativePartLift, F,
      intervalMeasure_integral_eq_intervalIntegral]
  simpa [hrewrite]

/-- Concrete one-sided time derivative of the negative-part energy.  The
pointwise derivative is the chain rule for
`r ↦ (negativePart r)^2`, and the integral derivative is supplied by the
within-set dominated differentiation lemma. -/
theorem energy_has_deriv
    {T t : ℝ} {u : ℝ → intervalDomainPoint → ℝ} {E' : ℝ → ℝ}
    (_ht : t ∈ Set.Ico (0 : ℝ) T)
    (hF_meas :
      ∀ r ∈ Set.Ici t,
        AEStronglyMeasurable
          (fun x => (negativePartLift (u r) x) ^ 2) (intervalMeasure 1))
    (hF_int :
      Integrable (fun x => (negativePartLift (u t) x) ^ 2)
        (intervalMeasure 1))
    (hF'_meas :
      AEStronglyMeasurable
        (fun x =>
          -2 * negativePartLift (u t) x *
            intervalDomainLift
              (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x)
        (intervalMeasure 1))
    (hbound :
      ∃ bound : ℝ → ℝ, Integrable bound (intervalMeasure 1) ∧
        ∀ᵐ x ∂intervalMeasure 1, ∀ r ∈ Set.Ici t,
          |-2 * negativePartLift (u r) x *
              intervalDomainLift
                (fun z : intervalDomainPoint => intervalDomain.timeDeriv u r z) x|
            ≤ bound x)
    (hpoint :
      ∀ᵐ x ∂intervalMeasure 1, ∀ r ∈ Set.Ici t,
        HasDerivWithinAt
          (fun s => intervalDomainLift (u s) x)
          (intervalDomainLift
            (fun z : intervalDomainPoint => intervalDomain.timeDeriv u r z) x)
          (Set.Ici t) r)
    (hE' :
      E' t =
        ∫ x,
          -2 * negativePartLift (u t) x *
            intervalDomainLift
              (fun z : intervalDomainPoint => intervalDomain.timeDeriv u t z) x
          ∂ intervalMeasure 1) :
    HasDerivWithinAt (negativePartEnergy u) (E' t) (Set.Ici t) t := by
  rcases hbound with ⟨bound, hbound_int, hbound_ae⟩
  let F : ℝ → ℝ → ℝ :=
    fun x r => (negativePartLift (u r) x) ^ 2
  let F' : ℝ → ℝ → ℝ :=
    fun x r =>
      -2 * negativePartLift (u r) x *
        intervalDomainLift
          (fun z : intervalDomainPoint => intervalDomain.timeDeriv u r z) x
  have ht_mem : t ∈ Set.Ici t := by
    simp
  have hdiff :
      ∀ᵐ x ∂intervalMeasure 1, ∀ r ∈ Set.Ici t,
        HasDerivWithinAt (fun a => F x a) (F' x r) (Set.Ici t) r := by
    filter_upwards [hpoint] with x hx r hr
    have hsq := negativePart_sq_hasDerivAt (intervalDomainLift (u r) x)
    have hcomp :=
      hsq.comp_hasDerivWithinAt r (hx r hr)
    simpa [F, F', negativePartLift, mul_assoc] using hcomp
  have hraw :
      HasDerivWithinAt (fun r => ∫ x, F x r ∂intervalMeasure 1)
        (∫ x, F' x t ∂intervalMeasure 1) (Set.Ici t) t :=
    hasDerivWithinAt_integral_of_dominated_loc_var
      (convex_Ici t) ht_mem hF_meas hF_int hF'_meas hbound_ae hbound_int hdiff
  have henergy : (fun r => ∫ x, F x r ∂intervalMeasure 1) =
      negativePartEnergy u := by
    funext r
    simp [F, negativePartEnergy]
  have hderiv :
      (∫ x, F' x t ∂intervalMeasure 1) = E' t := by
    rw [hE']
  simpa [henergy, hderiv] using hraw

end ShenWork.Paper2.BFormPositiveDatumNegPart
