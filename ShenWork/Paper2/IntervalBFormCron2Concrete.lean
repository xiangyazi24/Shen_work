/-
  Additive cron2 wiring from the concrete truncated Picard construction.

  This file does not modify `BFormCron2NegativePartHyp`.  It supplies the
  truncated-mild field from the independently constructed truncated Picard
  fixed point plus an explicit bridge identifying that truncated limit with the
  already named `conjugatePicardLimit` on the shared time window.
-/
import ShenWork.Paper2.IntervalBFormCron2TruncatedPicard

open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Concrete bridge saying that the independently constructed truncated Picard
limit is the candidate already used by the B-form route, on the route's time
window.  This is the precise post-construction obligation when the two Picard
schemes are not definitionally the same. -/
def TruncatedConjugateLimitBridge
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀) : Prop :=
  DT.T = DB.T ∧
    ∀ t, 0 < t → t ≤ DB.T → ∀ x : intervalDomainPoint,
      conjugatePicardLimit p u₀ DB.T t x
        = truncatedConjugatePicardLimit p u₀ DT.T t x

/-- The truncated-mild field required by cron2, supplied by the constructed
truncated Picard fixed point and a concrete limit-identification bridge. -/
theorem truncatedConjugateMildSolution_conjugatePicardLimit_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (DB : ConjugateMildExistenceData p u₀)
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (Hbridge : TruncatedConjugateLimitBridge p DB DT) :
    TruncatedConjugateMildSolution p DB.T u₀
      (conjugatePicardLimit p u₀ DB.T) := by
  rcases Hbridge with ⟨hT, hlim⟩
  have Hmild : TruncatedConjugateMildSolution p DT.T u₀
      (truncatedConjugatePicardLimit p u₀ DT.T) :=
    (truncatedConjugateMildSolutionData_of_data DT).hmild
  intro t ht htT x
  have htT' : t ≤ DT.T := by
    rw [hT]
    exact htT
  calc conjugatePicardLimit p u₀ DB.T t x
      = truncatedConjugatePicardLimit p u₀ DT.T t x :=
        hlim t ht htT x
    _ = truncatedConjugateDuhamelMap p u₀
          (truncatedConjugatePicardLimit p u₀ DT.T) t x :=
        Hmild t ht htT' x
    _ = truncatedConjugateDuhamelMap p u₀
          (conjugatePicardLimit p u₀ DB.T) t x := by
        have hslice : ∀ s,
            truncatedConjugatePicardLimit p u₀ DT.T s
              =
            conjugatePicardLimit p u₀ DB.T s := by
          intro s
          by_cases hs : 0 < s ∧ s ≤ DB.T
          · exact funext fun z => (hlim s hs.1 hs.2 z).symm
          · unfold conjugatePicardLimit truncatedConjugatePicardLimit
            have hsT : ¬(0 < s ∧ s ≤ DT.T) := by
              intro hsDT
              exact hs ⟨hsDT.1, by simpa [hT] using hsDT.2⟩
            funext z
            simp [hs, hsT]
        have hflux :
            (fun s : ℝ =>
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p
                  (truncatedConjugatePicardLimit p u₀ DT.T s)) x.1)
              =
            fun s : ℝ =>
              intervalConjugateKernelOperator (t - s)
                (truncatedChemFluxLifted p
                  (conjugatePicardLimit p u₀ DB.T s)) x.1 := by
          funext s
          congr 1
          rw [hslice s]
        have hlog :
            (fun s : ℝ =>
              intervalFullSemigroupOperator (t - s)
                (truncatedLogisticLifted p
                  (truncatedConjugatePicardLimit p u₀ DT.T s)) x.1)
              =
            fun s : ℝ =>
              intervalFullSemigroupOperator (t - s)
                (truncatedLogisticLifted p
                  (conjugatePicardLimit p u₀ DB.T s)) x.1 := by
          funext s
          congr 1
          rw [hslice s]
        unfold truncatedConjugateDuhamelMap
        rw [hflux, hlog]

/-- Constructor for the cron2 certificate once the two genuinely deep analytic
frontiers are supplied, together with the concrete truncated Picard data and
the exact B_N-duality proposition. -/
def bformCron2NegativePartHyp_of_concrete_truncated
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {DB : ConjugateMildExistenceData p u₀}
    (DT : TruncatedConjugateMildExistenceData p u₀)
    (Hbridge : TruncatedConjugateLimitBridge p DB DT)
    (HmildWeak : TruncatedMildToWeakAvailable p DB)
    (Henergy : NegativePartEnergyGronwallAvailable p DB) :
    BFormCron2NegativePartHyp p DB where
  truncated_mild :=
    truncatedConjugateMildSolution_conjugatePicardLimit_of_data DB DT Hbridge
  mild_to_weak := HmildWeak
  negative_part_energy := Henergy

end ShenWork.Paper2.BFormPositiveDatumNegPart
