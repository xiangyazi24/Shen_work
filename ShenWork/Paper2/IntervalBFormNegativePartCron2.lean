import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateKernelOperator)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.PDE (intervalNeumannResolverR)
open ShenWork.Paper2

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-!
Cron2 negative-part route for the B-form frontier.

This file keeps the missing weak-solution infrastructure honest.  It proves the
pointwise disjoint-support cancellation used by the weak test `-u_-`, defines
the exact truncated mild/weak interfaces needed for the five-step route, and
derives the `negativePart_zero` field from a named weak-energy/Gronwall
certificate.  No solution-level endpoint flux lemma is used.
-/

/-- Faithful truncated chemotaxis flux for the cron2 route:
the original flux with only the leading `u` factor replaced by `u_+`. -/
def truncatedChemFluxLifted (p : CM2Params)
    (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun y =>
    positivePart (intervalDomainLift w y) * resolverGradReal p w y
      / (1 + intervalDomainLift (intervalNeumannResolverR p w) y) ^ p.β

/-- A nonnegative-friendly local logistic source.  The precise analytic
one-sided estimate is part of the weak-energy certificate below. -/
def truncatedLogisticLocal (p : CM2Params) (r : ℝ) : ℝ :=
  r * (p.a - p.b * (positivePart r) ^ p.α)

/-- Lifted truncated logistic source. -/
def truncatedLogisticLifted (p : CM2Params)
    (w : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun y => truncatedLogisticLocal p (intervalDomainLift w y)

lemma truncatedChemotacticPower_eq_zero_of_nonpos
    (p : CM2Params) {r : ℝ} (hr : r ≤ 0) :
    truncatedChemotacticPower p r = 0 := by
  have hpos : positivePart r = 0 := positivePart_eq_zero_of_nonpos hr
  have hm_ne : p.m ≠ 0 := ne_of_gt p.hm
  simp [truncatedChemotacticPower, hpos, Real.zero_rpow hm_ne]

/-- Pointwise support form of `(u_+)^m (u_-)_x = 0`.

At points with `u x ≤ 0`, the truncated power is zero.  At points with
`0 < u x`, continuity makes `u_-` locally constant equal to zero, so its
classical derivative is zero.  This is the scalar core that the weak energy
argument integrates a.e. -/
lemma truncatedChemotacticPower_mul_deriv_negativePart_eq_zero
    (p : CM2Params) {u : ℝ → ℝ} {x : ℝ}
    (hu : ContinuousAt u x) :
    truncatedChemotacticPower p (u x)
        * deriv (fun y : ℝ => negativePart (u y)) x = 0 := by
  by_cases hpos : 0 < u x
  · have hmem : u x ∈ Set.Ioi (0 : ℝ) := hpos
    have hnhds : Set.Ioi (0 : ℝ) ∈ 𝓝 (u x) :=
      isOpen_Ioi.mem_nhds hmem
    have hev_pos : ∀ᶠ y in 𝓝 x, u y ∈ Set.Ioi (0 : ℝ) :=
      hu hnhds
    have hev :
        (fun y : ℝ => negativePart (u y)) =ᶠ[𝓝 x] (fun _ : ℝ => 0) :=
      hev_pos.mono (fun y hy => negativePart_eq_zero_of_nonneg hy.le)
    have hderiv :
        deriv (fun y : ℝ => negativePart (u y)) x = 0 := by
      rw [hev.deriv_eq]
      simp
    simp [hderiv]
  · have hnonpos : u x ≤ 0 := le_of_not_gt hpos
    have hflux :
        truncatedChemotacticPower p (u x) = 0 :=
      truncatedChemotacticPower_eq_zero_of_nonpos p hnonpos
    simp [hflux]

/-- Truncated B-form mild map, with `Q(u)` replaced by `Q(u_+)`. -/
def truncatedConjugateDuhamelMap (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
    + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s)
          (truncatedChemFluxLifted p (u s)) x.1)
    + ∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (truncatedLogisticLifted p (u s)) x.1

/-- Fixed-point predicate for the truncated B-form construction. -/
def TruncatedConjugateMildSolution (p : CM2Params) (T : ℝ)
    (u₀ : intervalDomainPoint → ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    u t x = truncatedConjugateDuhamelMap p u₀ u t x

/-- Weak local PDE obtained after the regular B-form duality step:

`⟨u_t,φ⟩ + ∫ u_x φ_x = χ₀∫ Q_T(u) φ_x + ∫ L̃(u)φ`.

This is deliberately a concrete integral identity, not an opaque shell. -/
def TruncatedWeakLocalPDE (p : CM2Params) (T : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → ∀ φ : ℝ → ℝ,
    (∫ x,
        intervalDomainLift
            (fun z : intervalDomainPoint =>
              intervalDomain.timeDeriv u t z) x * φ x
        ∂ intervalMeasure 1)
      + (∫ x,
          deriv (intervalDomainLift (u t)) x * deriv φ x
          ∂ intervalMeasure 1)
      =
    p.χ₀ *
        (∫ x,
          truncatedChemFluxLifted p (u t) x * deriv φ x
          ∂ intervalMeasure 1)
      + (∫ x, truncatedLogisticLifted p (u t) x * φ x
          ∂ intervalMeasure 1)

/-- Step 3 bridge: truncated mild fixed point gives the weak local PDE once the
regular flux/test duality and semigroup weak identity are supplied upstream. -/
def TruncatedMildToWeakAvailable
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : Prop :=
  TruncatedConjugateMildSolution p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T) →
    TruncatedWeakLocalPDE p DB.T
      (conjugatePicardLimit p u₀ DB.T)

/-- Endpoint of the weak negative-part energy estimate:

test the weak PDE with `-u_-`, use the pointwise/a.e.
`(u_+)^m (u_-)_x = 0` cancellation, absorb the one-sided source term, and apply
Gronwall with zero initial negative part. -/
def NegativePartEnergyGronwallAvailable
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : Prop :=
  TruncatedWeakLocalPDE p DB.T
      (conjugatePicardLimit p u₀ DB.T) →
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardLimit p u₀ DB.T t x

/-- The named cron2 certificate collecting the five required steps. -/
structure BFormCron2NegativePartHyp
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀) : Prop where
  /-- Step 1: the Picard-limit candidate is supplied by the truncated mild
  construction `Q(u) → Q(u_+)`. -/
  truncated_mild :
    TruncatedConjugateMildSolution p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T)
  /-- Step 3: truncated mild fixed point implies the weak local PDE. -/
  mild_to_weak : TruncatedMildToWeakAvailable p DB
  /-- Step 4: weak negative-part energy plus Gronwall gives `u ≥ 0`. -/
  negative_part_energy : NegativePartEnergyGronwallAvailable p DB

/-- Discharge of the `negativePart_zero` field by the cron2 weak route. -/
theorem bform_negativePart_zero
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : BFormCron2NegativePartHyp p DB) :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      negativePart (conjugatePicardLimit p u₀ DB.T t x) = 0 := by
  intro t ht htT x
  have hweak :
      TruncatedWeakLocalPDE p DB.T
        (conjugatePicardLimit p u₀ DB.T) :=
    H.mild_to_weak H.truncated_mild
  have hnonneg :
      0 ≤ conjugatePicardLimit p u₀ DB.T t x :=
    H.negative_part_energy hweak t ht htT x
  exact negativePart_eq_zero_of_nonneg hnonneg

/-- Step 5: once the negative part is zero, the truncation is inactive
pointwise: `u_+ = u`. -/
theorem bform_truncation_inactive_of_cron2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (H : BFormCron2NegativePartHyp p DB) :
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      positivePart (conjugatePicardLimit p u₀ DB.T t x)
        = conjugatePicardLimit p u₀ DB.T t x := by
  intro t ht htT x
  have hneg := bform_negativePart_zero (p := p) (u₀ := u₀)
    (DB := DB) H t ht htT x
  exact positivePart_eq_self_of_nonneg (negativePart_eq_zero_iff.mp hneg)

/-- Existing lower-barrier route constructor with the `negativePart_zero` input
discharged by the cron2 weak negative-part certificate. -/
def bform_negpart_route_of_cron2_lower_barrier
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀} {C : ℝ}
    (datum : PositiveInitialDatum intervalDomain u₀)
    (F : ShenWork.Paper2.BFormDirectClassical.BFormDirectFrontier p DB)
    (H : BFormCron2NegativePartHyp p DB)
    (hLift_cont :
      ContinuousOn (intervalDomainLift u₀) (Set.Icc (0 : ℝ) 1))
    (hLift_nonneg :
      ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift u₀ y)
    (hLift_pos_somewhere :
      ∃ y₀ ∈ Set.Icc (0 : ℝ) 1, 0 < intervalDomainLift u₀ y₀)
    (hbarrier :
      ∀ t x, 0 < t → t < DB.T →
        Real.exp (-C * t)
            * intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
          ≤ conjugatePicardLimit p u₀ DB.T t x) :
    BFormNegativePartPositivityRoute p DB :=
  bform_negpart_route_of_lower_barrier datum F
    (bform_negativePart_zero H)
    hLift_cont hLift_nonneg hLift_pos_somewhere hbarrier

end ShenWork.Paper2.BFormPositiveDatumNegPart
