import ShenWork.Paper2.IntervalConjugatePicardCoreInhabit
import ShenWork.Paper2.IntervalDomainThm11ChiNegResidual

/-!
# Weak PID to paper PID audit

`conjugateMildExistenceCore_exists` is not merely a bounded-data theorem.
Its proof immediately extracts `paperPositiveFloor hu₀`, includes `floor / 2`
in the small-time target, and uses
`intervalConjugateDuhamelMap_ge_half_floor_of_ball` to fill
`hmapsTo_nn` and `hmapsTo_pos`.  Thus the landed construction depends on the
closed-domain positive floor carried by `PaperPositiveInitialDatum`.

The two open interfaces for the final residual are therefore:

* weak PID restart: produce a paper-positive datum at positive time from a weak
  interval datum, using strict positivity of the heat/mild evolution;
* uniform horizon: replace the present floor-dependent chosen horizon by a
  `delta(M)` uniform over all weak data with `|u₀| <= M`.

The existing compactness bridge in `IntervalPositiveDatumThreshold.lean` closes
only the stronger input: continuous strict positivity on the closed interval
gives `PaperPositiveInitialDatum`.  The heat-semigroup theorem read in
`IntervalHeatSemigroupFlooredSourceTimeData.lean` likewise assumes closed-domain
strict positivity of `u₀`; it is not yet the weak endpoint-vanishing restart.
-/

open Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceCore conjugateMildExistenceCore_exists
   conjugatePicardIter)
open ShenWork.Paper2
  (PaperPositiveInitialDatum PositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.IntervalWeakPIDUpgrade

/-- The standard endpoint-vanishing positive datum on `[0,1]`. -/
def endpointVanishingDatum (x : intervalDomainPoint) : ℝ :=
  x.1 * (1 - x.1)

theorem endpointVanishingDatum_positive :
    PositiveInitialDatum intervalDomain endpointVanishingDatum := by
  refine ⟨?_, ?_⟩
  · constructor
    · refine ⟨1, ?_⟩
      rintro _ ⟨x, rfl⟩
      have hx0 : 0 ≤ (x.1 : ℝ) := x.2.1
      have hx1 : (x.1 : ℝ) ≤ 1 := x.2.2
      have hnonneg : 0 ≤ endpointVanishingDatum x := by
        exact mul_nonneg hx0 (sub_nonneg.mpr hx1)
      have hle : endpointVanishingDatum x ≤ 1 := by
        unfold endpointVanishingDatum
        nlinarith [sq_nonneg ((x.1 : ℝ) - 1)]
      simpa [abs_of_nonneg hnonneg] using hle
    · unfold endpointVanishingDatum
      exact continuous_subtype_val.mul (continuous_const.sub continuous_subtype_val)
  · intro x hx
    change (x.1 : ℝ) ∈ Ioo (0 : ℝ) 1 at hx
    unfold endpointVanishingDatum
    exact mul_pos hx.1 (sub_pos.mpr hx.2)

theorem endpointVanishingDatum_not_paper :
    ¬ PaperPositiveInitialDatum intervalDomain endpointVanishingDatum := by
  intro hpaper
  obtain ⟨η, hη, hfloor⟩ := PaperPositiveInitialDatum.floor hpaper
  let x0 : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
  have hle : η ≤ endpointVanishingDatum x0 := hfloor x0
  have hz : endpointVanishingDatum x0 = 0 := by
    simp [endpointVanishingDatum, x0]
  linarith

/-- Hence there is no general weak-PID to paper-PID upgrade on the interval. -/
theorem not_forall_positiveInitialDatum_to_paperPositiveInitialDatum :
    ¬ (∀ {u₀ : intervalDomainPoint → ℝ},
        PositiveInitialDatum intervalDomain u₀ →
          PaperPositiveInitialDatum intervalDomain u₀) := by
  intro H
  exact endpointVanishingDatum_not_paper (H endpointVanishingDatum_positive)

/-- The uniform core horizon that is still missing from the floor-based proof. -/
def UniformConjugateCoreHorizonFromBound
    (p : CM2Params) (_hα : 1 ≤ p.α) (_hγ : 1 ≤ p.γ) : Prop :=
  ∀ M : ℝ, 0 < M → ∃ delta : ℝ, 0 < delta ∧
    ∀ {u₀ : intervalDomainPoint → ℝ},
      PaperPositiveInitialDatum intervalDomain u₀ →
      (∀ x, |u₀ x| ≤ M) →
        ∃ C : ConjugateMildExistenceCore p u₀, C.T = delta

/-- The heat-smoothing input needed for a weak-PID restart. -/
def HeatStrictPositivityFromWeakPID (p : CM2Params) : Prop :=
  ∀ {u₀ : intervalDomainPoint → ℝ},
    PositiveInitialDatum intervalDomain u₀ →
    ∀ {t : ℝ}, 0 < t →
    ∀ {x : ℝ}, x ∈ Icc (0 : ℝ) 1 →
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 t) x

#check conjugateMildExistenceCore_exists
#check ShenWork.Paper2.ChiNegResidual.CoupledFluxClassicalLocalExistenceResidual

end ShenWork.Paper2.IntervalWeakPIDUpgrade
