/- Positive-strip consequences of weak and strong proximity to a faithful
general-`m` positive equilibrium. -/
import ShenWork.Paper3.IntervalDomainStrongStageAGeneralM
import ShenWork.Paper3.IntervalDomainMWeakSupBootstrap

namespace ShenWork.Paper3

open MeasureTheory Set
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.PDE.SectorialOperator

noncomputable section

/-- Sup-small positive data around a positive equilibrium lie in one fixed
paper-positive strip.  This is the faithful `intervalDomainM` version used by
the maximal-continuation argument. -/
theorem paper3SupClose_initial_positiveStrip_generalM
    {uStar delta : ℝ} {u₀ : intervalDomainPoint → ℝ}
    (huStar : 0 < uStar) (hdelta : delta ≤ uStar / 16)
    (hu₀ : PositiveInitialDatum intervalDomainM u₀)
    (hclose : SupCloseToConstant intervalDomainM u₀ uStar delta) :
    PaperPositiveInitialDatum intervalDomainM u₀ ∧
      (∀ x, |u₀ x| ≤ 2 * uStar + 1) ∧
      (∀ x, uStar / 4 ≤ u₀ x) := by
  have hconstBdd : BddAbove
      (Set.range (fun _x : intervalDomainPoint => |uStar|)) :=
    ⟨|uStar|, by rintro _ ⟨x, rfl⟩; exact le_rfl⟩
  have hdiffBdd : BddAbove
      (Set.range (fun x : intervalDomainPoint => |u₀ x - uStar|)) :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.bddAbove_abs_sub_of_bddAbove_abs_restart
      hu₀.admissible.1 hconstBdd
  have hpoint : ∀ x : intervalDomainPoint, |u₀ x - uStar| < delta :=
    ShenWork.Paper2.BFormPositiveDatumNegPart.intervalDomain_pointwise_abs_lt_of_supNorm_lt_restart
      hdiffBdd hclose.lt
  have hfloor : ∀ x : intervalDomainPoint, uStar / 4 ≤ u₀ x := by
    intro x
    have hlo := (abs_lt.mp (hpoint x)).1
    linarith
  have hbound : ∀ x : intervalDomainPoint, |u₀ x| ≤ 2 * uStar + 1 := by
    intro x
    have htri : |u₀ x| ≤ |u₀ x - uStar| + |uStar| := by
      calc
        |u₀ x| = |(u₀ x - uStar) + uStar| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_of_pos huStar] at htri
    exact htri.trans (by linarith [hpoint x])
  exact ⟨⟨hu₀.admissible, ⟨uStar / 4, by linarith, hfloor⟩⟩,
    hbound, hfloor⟩

/-- Membership in the faithful explicit strong bootstrap ball gives a fixed
two-sided pointwise strip. -/
theorem intervalDomainStrongBootstrapRadiusGeneralM_positiveStrip
    {p : CM2Params} {T t sigma uStar vStar gap : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (hsigmaStrong : 3 / 4 < sigma) (hsigma1 : sigma < 1)
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hdist : intervalDomainX2SigmaDistance sigma uStar (u t) ≤
      intervalDomainStrongBootstrapRadiusGeneralM
        p sigma uStar vStar gap heq) :
    (∀ x, |u t x| ≤ 2 * uStar + 1) ∧
      (∀ x, uStar / 4 ≤ u t x) := by
  have hmem := intervalDomainMX2SigmaPerturbation_of_classical_positive
    (uStar := uStar) hsol ht hsigma1.le
  have hcont : Continuous (u t) := solutionSlice_continuous hsol ht
  have hreal : IntervalDomainX2SigmaRealizationBounds sigma uStar (u t) :=
    intervalDomainX2SigmaRealizationBounds_of_continuous
      hsigmaStrong hcont hmem
  let Ctrace := intervalDomainX2SigmaValueTrace sigma
  let d := intervalDomainX2SigmaDistance sigma uStar (u t)
  have hCtrace : 0 ≤ Ctrace := by
    simpa [Ctrace] using intervalDomainX2SigmaValueTrace_nonneg sigma
  have hd : 0 ≤ d := by dsimp [d]; exact Real.sqrt_nonneg _
  have hlocal : d ≤
      intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM p sigma uStar :=
    hdist.trans (intervalDomainStrongBootstrapRadiusGeneralM_le_positivity
      p sigma uStar vStar gap heq)
  have hposRadius : d ≤ uStar / (2 * (1 + Ctrace)) :=
    hlocal.trans (by
      unfold intervalDomainX2SigmaLocalNemytskiiRadiusGeneralM
        intervalDomainX2SigmaLocalNemytskiiRadius
        intervalDomainX2SigmaPositivityRadius
      simpa [Ctrace] using min_le_left
        (uStar / (2 * (1 + intervalDomainX2SigmaValueTrace sigma)))
        (1 / intervalDomainX2SigmaC1Envelope sigma))
  have hden : 0 < 2 * (1 + Ctrace) := by positivity
  have hratio : Ctrace * (uStar / (2 * (1 + Ctrace))) ≤ uStar / 2 := by
    rw [show Ctrace * (uStar / (2 * (1 + Ctrace))) =
      (Ctrace * uStar) / (2 * (1 + Ctrace)) by ring]
    apply (div_le_iff₀ hden).2
    nlinarith [heq.u_pos, hCtrace]
  have hvalue : ∀ x, |u t x - uStar| ≤ uStar / 2 := by
    intro x
    calc
      |u t x - uStar| ≤ Ctrace * d := by
        simpa [Ctrace, d] using hreal.value_bound x
      _ ≤ Ctrace * (uStar / (2 * (1 + Ctrace))) :=
        mul_le_mul_of_nonneg_left hposRadius hCtrace
      _ ≤ uStar / 2 := hratio
  constructor
  · intro x
    have htri : |u t x| ≤ |u t x - uStar| + |uStar| := by
      calc
        |u t x| = |(u t x - uStar) + uStar| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_of_pos heq.u_pos] at htri
    calc
      |u t x| ≤ |u t x - uStar| + uStar := htri
      _ ≤ uStar / 2 + uStar := add_le_add (hvalue x) le_rfl
      _ ≤ 2 * uStar + 1 := by nlinarith [heq.u_pos]
  · intro x
    have hlo := neg_le_of_abs_le (hvalue x)
    nlinarith [heq.u_pos]

#print axioms paper3SupClose_initial_positiveStrip_generalM
#print axioms intervalDomainStrongBootstrapRadiusGeneralM_positiveStrip

end

end ShenWork.Paper3
