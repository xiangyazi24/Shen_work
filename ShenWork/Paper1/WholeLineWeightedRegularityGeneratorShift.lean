import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorRestartNatural
import ShenWork.Paper1.WholeLineWeightedRegularityGeneratorClosure

open Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

namespace ShenWork.Paper1

/-!
# Positive generator regularization of a full mild restart

This file records the exact algebra needed before the endpoint-generator
limit.  Applying a positive generator regularization to the full mild state
shifts every heat lag by the same positive amount.  No endpoint generator
domain or time derivative is assumed.
-/

/-- A positive generator regularization commutes through the full mild
candidate.  The only analytic premise is Bochner integrability of the
original heat history; boundedness of the regularizing continuous linear map
then supplies integrability after applying it. -/
theorem weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
    {eta c a t eps : ℝ} (hat : a ≤ t) (heps : 0 < eps)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t) :
    weightedMovingHeatL2Generator eta c eps
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) =
      weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ +
        ∫ q in a..t,
          weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q) := by
  let Aeps : WholeLineRealL2 →L[ℝ] WholeLineRealL2 :=
    weightedMovingHeatL2Generator eta c eps
  have hhom :
      Aeps (weightedMovingHeatL2Semigroup eta c (t - a) Z₀) =
        weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ := by
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) heps (sub_nonneg.mpr hat)
    exact DFunLike.congr_fun hcomp Z₀
  have hcommute := Aeps.intervalIntegral_comp_comm hhist
  have hint :
      Aeps (∫ q in a..t,
          weightedMovingHeatL2Semigroup eta c (t - q) (F q)) =
        ∫ q in a..t,
          weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q) := by
    rw [← hcommute]
    apply intervalIntegral.integral_congr
    intro q hq
    have hqt : q ≤ t := by
      rw [uIcc_of_le hat] at hq
      exact hq.2
    have hcomp := weightedMovingHeatL2Generator_comp_semigroup_add
      (eta := eta) (c := c) heps (sub_nonneg.mpr hqt)
    exact DFunLike.congr_fun hcomp (F q)
  unfold weightedMovingHeatFullGeneratorCandidate
  rw [map_add, hhom, hint]

/-- Time reversal rewrites the shifted generator history in its native lag
coordinate.  This is the coordinate used by the endpoint cancellation
theorem. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_shift_eq_lag
    {eta c a t eps : ℝ} {F : ℝ → WholeLineRealL2} :
    (∫ q in a..t,
        weightedMovingHeatL2Generator eta c (eps + (t - q)) (F q)) =
      ∫ r in (0 : ℝ)..t - a,
        weightedMovingHeatL2Generator eta c (eps + r) (F (t - r)) := by
  let G : ℝ → WholeLineRealL2 := fun r =>
    weightedMovingHeatL2Generator eta c (eps + r) (F (t - r))
  have hchange := intervalIntegral.integral_comp_sub_left
    (f := G) (a := a) (b := t) t
  simpa only [G, sub_sub_cancel, sub_self] using hchange

/-- Lag-coordinate form of positive generator regularization of the full
mild candidate. -/
theorem weightedMovingHeatL2Generator_apply_fullGeneratorCandidate_lag
    {eta c a t eps : ℝ} (hat : a ≤ t) (heps : 0 < eps)
    {F : ℝ → WholeLineRealL2} {Z₀ : WholeLineRealL2}
    (hhist : IntervalIntegrable
      (fun q => weightedMovingHeatL2Semigroup eta c (t - q) (F q))
      volume a t) :
    weightedMovingHeatL2Generator eta c eps
        (weightedMovingHeatFullGeneratorCandidate eta c a Z₀ F t) =
      weightedMovingHeatL2Generator eta c (eps + (t - a)) Z₀ +
        ∫ r in (0 : ℝ)..t - a,
          weightedMovingHeatL2Generator eta c (eps + r) (F (t - r)) := by
  rw [weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
    hat heps hhist]
  rw [intervalIntegral_weightedMovingHeatL2Generator_shift_eq_lag]

/-- Translating the positive generator regularization from the lag variable
to the generator-time variable.  The forcing acquires the matching forward
time shift `eps`. -/
theorem intervalIntegral_weightedMovingHeatL2Generator_add_lag_eq_shift
    {eta c h t eps : ℝ} {F : ℝ → WholeLineRealL2} :
    (∫ r in (0 : ℝ)..h,
        weightedMovingHeatL2Generator eta c (eps + r) (F (t - r))) =
      ∫ q in eps..h + eps,
        weightedMovingHeatL2Generator eta c q (F (t + eps - q)) := by
  let G : ℝ → WholeLineRealL2 := fun q =>
    weightedMovingHeatL2Generator eta c q (F (t + eps - q))
  have hchange := intervalIntegral.integral_comp_add_right
    (f := G) (a := (0 : ℝ)) (b := h) eps
  have hleft : (fun r : ℝ => G (r + eps)) = fun r =>
      weightedMovingHeatL2Generator eta c (eps + r) (F (t - r)) := by
    funext r
    dsimp only [G]
    congr 2 <;> ring
  rw [hleft] at hchange
  simpa only [G, zero_add] using hchange

section AxiomAudit

#print axioms
  weightedMovingHeatL2Generator_apply_fullGeneratorCandidate
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_shift_eq_lag
#print axioms
  weightedMovingHeatL2Generator_apply_fullGeneratorCandidate_lag
#print axioms
  intervalIntegral_weightedMovingHeatL2Generator_add_lag_eq_shift

end AxiomAudit

end ShenWork.Paper1
