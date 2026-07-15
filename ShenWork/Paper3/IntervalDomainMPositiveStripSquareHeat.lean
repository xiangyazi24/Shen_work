import ShenWork.Paper3.IntervalDomainMLinearSuperSolution
import ShenWork.Paper3.IntervalDoubleShiftSquareHeatBarrier
import ShenWork.Paper3.IntervalDomainMPositiveHeatShiftSeed
import ShenWork.Paper2.IntervalDomainMPhysicalRestart

open Set Filter Topology

noncomputable section

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM
open ShenWork.Paper2.BFormPositiveDatumNegPart
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

/-- The discount required by the squared-heat subsolution for the explicit
faithful general-power drift and reaction bounds. -/
def intervalDomainMLinearBarrierDiscount (p : CM2Params) (M : ℝ) : ℝ :=
  intervalDomainMLinearDriftBound p M ^ 2 / 2 +
    intervalDomainMLinearReactionBound p M

theorem intervalDomainMLinearBarrierDiscount_nonneg
    {p : CM2Params} {M : ℝ} (hm : 1 ≤ p.m) (hM : 0 ≤ M) :
    0 ≤ intervalDomainMLinearBarrierDiscount p M := by
  unfold intervalDomainMLinearBarrierDiscount
  exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (intervalDomainMLinearReactionBound_nonneg hm hM)

/-- Complete lower square-heat barrier on a positive physical strip of a
faithful general-`m` classical solution.

The physical restart time and heat-semigroup start time are independent.  In
particular the selected `δ` may be arbitrarily small without moving the
physical slice `u(s)`. -/
theorem intervalDomainM_classical_positiveStrip_squareHeat_lower
    {p : CM2Params} {T s L M δmax : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hm : 1 ≤ p.m)
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs : 0 < s) (hL : 0 < L) (hsLT : s + L < T)
    (hM : 0 ≤ M)
    (hu_le : ∀ r ∈ Set.Icc (0 : ℝ) L,
      ∀ x : intervalDomainPoint, u (s + r) x ≤ M)
    (hδmax : 0 < δmax) :
    ∃ δ : ℝ, 0 < δ ∧ δ < δmax ∧
      ∃ K : ℝ, ∃ f : ℝ → ℝ,
        f = halfRestartSliceSqrtSeed (u s) ∧
        Continuous f ∧
        SquareHeatSeed (intervalDomainLift (u s)) f ∧
        (∀ n, |cosineCoeffs f n| ≤ K) ∧
        Summable (fun n : ℕ => (cosineCoeffs f n) ^ 2) ∧
        ∀ r x, 0 < r → r < L → x ∈ Set.Icc (0 : ℝ) 1 →
          squareHeatBarrier (intervalDomainMLinearBarrierDiscount p M)
              f (δ + r) x ≤
            classicalClampField u (s + r) x := by
  have hsT : s < T := by linarith
  have hw_cont : Continuous (u s) :=
    ShenWork.Paper2.IntervalDomainM.solutionSlice_continuous hsol ⟨hs, hsT⟩
  have hw_pos : ∀ x : intervalDomainPoint, 0 < u s x := by
    intro x
    exact hsol.u_pos' hs hsT
  have hdiscount : 0 ≤ intervalDomainMLinearBarrierDiscount p M :=
    intervalDomainMLinearBarrierDiscount_nonneg hm hM
  rcases positiveHeatShiftSliceSeedData_of_positive
      hw_cont hw_pos hdiscount hδmax with
    ⟨δ, hδ, hδlt, K, f, hf_eq, hf_cont, hseed, hcoeff, hl2, hinitial⟩
  let A : ℝ := intervalDomainMLinearDriftBound p M
  let D : ℝ := intervalDomainMLinearReactionBound p M
  have hcoeff_regular :
      NeumannLinearDriftCoefficientsRegular L
        (restartTimeShift s (intervalDomainMLinearDrift p u v))
        (restartTimeShift s (intervalDomainMLinearReaction p u v)) :=
    intervalDomainM_classical_linearCoefficientsRegular
      hm hsol hs hL.le hsLT hM hu_le
  have hsuper :
      IsClassicalNeumannLinearDriftSuperSolution L
        (restartTimeShift s (intervalDomainMLinearDrift p u v))
        (restartTimeShift s (intervalDomainMLinearReaction p u v))
        (restartTimeShift s (classicalClampField u)) :=
    intervalDomainM_classical_linearSuperSolution
      hsol hs hL.le hsLT hM hu_le
  have hB_bound :
      ∀ r x, 0 < r → r < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        |intervalDomainMLinearDrift p u v (s + r) x| ≤ A := by
    intro r x hr0 hrL hx
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    have hr : r ∈ Set.Icc (0 : ℝ) L := ⟨hr0.le, hrL.le⟩
    exact
      (intervalDomainM_classical_linearCoefficients_abs_le_Icc
        hm hsol ht0 htT hM (hu_le r hr) x
          (Set.Ioo_subset_Icc_self hx)).1
  have hC_bound :
      ∀ r x, 0 < r → r < L → x ∈ Set.Ioo (0 : ℝ) 1 →
        -intervalDomainMLinearReaction p u v (s + r) x ≤ D := by
    intro r x hr0 hrL hx
    have ht0 : 0 < s + r := by linarith
    have htT : s + r < T := by linarith
    have hr : r ∈ Set.Icc (0 : ℝ) L := ⟨hr0.le, hrL.le⟩
    have habs :=
      (intervalDomainM_classical_linearCoefficients_abs_le_Icc
        hm hsol ht0 htT hM (hu_le r hr) x
          (Set.Ioo_subset_Icc_self hx)).2
    exact (neg_le_abs _).trans habs
  have hinitial' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      squareHeatBarrier (intervalDomainMLinearBarrierDiscount p M) f δ x ≤
        classicalClampField u s x := by
    intro x hx
    simpa [classicalClampField_eq_lift (u := u) (t := s) hx] using
      hinitial x hx
  have hcompare :=
    square_heat_hbarrier_of_independent_positive_heat_shift
      hδ hf_cont hcoeff hl2 hL hcoeff_regular hsuper
      (show A ^ 2 / 2 + D ≤ intervalDomainMLinearBarrierDiscount p M by
        rfl)
      hB_bound hC_bound hinitial'
  refine ⟨δ, hδ, hδlt, K, f, hf_eq, hf_cont, hseed, hcoeff, hl2, ?_⟩
  intro r x hr0 hrL hx
  exact hcompare r x hr0 hrL hx

end ShenWork.Paper3

#print axioms ShenWork.Paper3.intervalDomainM_classical_positiveStrip_squareHeat_lower
