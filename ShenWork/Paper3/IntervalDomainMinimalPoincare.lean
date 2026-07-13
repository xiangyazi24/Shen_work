import ShenWork.PDE.PoincareInequality
import ShenWork.Paper2.IntervalDomainMFlux
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

/-!
# Physical Poincare inequality for classical interval slices

`intervalDomainLift` is the zero extension and is discontinuous at the two
endpoints for positive data.  Hence the generic Poincare theorem cannot be
applied to that extension directly.  We instead apply it to the clamped
continuous representative `liftRepr`.  The Neumann conditions make the two
clamping seams differentiable with derivative zero.
-/

open Filter MeasureTheory Set Topology
open scoped Topology Interval

namespace ShenWork.Paper3

open ShenWork.IntervalDomain
open ShenWork.IntervalEllipticCharacterization
open ShenWork.IntervalFullKernelRegularity
open ShenWork.Poincare
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainM

noncomputable section

private theorem liftRepr_eq_left
    (w : intervalDomainPoint → ℝ) {x : ℝ} (hx : x ≤ 0) :
    liftRepr w x = intervalDomainLift w 0 := by
  have hmin : min (1 : ℝ) x = x := min_eq_right (by linarith)
  simp [liftRepr, clamp01, hmin, max_eq_left hx]

private theorem liftRepr_eq_right
    (w : intervalDomainPoint → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    liftRepr w x = intervalDomainLift w 1 := by
  have hmin : min (1 : ℝ) x = 1 := min_eq_left hx
  simp [liftRepr, clamp01, hmin]

/-- The clamped representative of a Neumann `C²` profile has the physical
spatial derivative at every point of the closed interval. -/
theorem liftRepr_hasDerivAt_Icc_of_neumann
    {w : intervalDomainPoint → ℝ}
    (hw : ContDiffOn ℝ 2 (intervalDomainLift w) (Icc (0 : ℝ) 1))
    (hneu0 : derivWithin (intervalDomainLift w) (Icc (0 : ℝ) 1) 0 = 0)
    (hneu1 : derivWithin (intervalDomainLift w) (Icc (0 : ℝ) 1) 1 = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (liftRepr w) (deriv (intervalDomainLift w) x) x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · have hleft : HasDerivWithinAt (liftRepr w) 0 (Iic (0 : ℝ)) 0 := by
      exact (hasDerivAt_const (0 : ℝ) (intervalDomainLift w 0)).hasDerivWithinAt.congr
        (fun y hy ↦ liftRepr_eq_left w hy) (by simp [liftRepr_eq_on_Icc])
    have hright0 : HasDerivWithinAt (intervalDomainLift w) 0
        (Icc (0 : ℝ) 1) 0 := by
      simpa [hneu0] using
        (hw.differentiableOn (by norm_num) 0 ⟨le_rfl, zero_le_one⟩).hasDerivWithinAt
    have hright : HasDerivWithinAt (liftRepr w) 0
        (Icc (0 : ℝ) 1) 0 :=
      hright0.congr_of_mem (fun y hy ↦ liftRepr_eq_on_Icc hy) ⟨le_rfl, zero_le_one⟩
    have hunion := hleft.union hright
    have hnhds : Iic (0 : ℝ) ∪ Icc (0 : ℝ) 1 ∈ nhds (0 : ℝ) := by
      apply mem_of_superset (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      intro y hy
      by_cases hy0 : y ≤ 0
      · exact Or.inl hy0
      · exact Or.inr ⟨le_of_not_ge hy0, hy⟩
    have hzero : HasDerivAt (liftRepr w) 0 0 := hunion.hasDerivAt hnhds
    simpa [deriv_intervalDomainLift_eq_zero_at_zero] using hzero
  · rcases eq_or_lt_of_le hx.2 with rfl | hx1
    · have hleft0 : HasDerivWithinAt (intervalDomainLift w) 0
          (Icc (0 : ℝ) 1) 1 := by
        simpa [hneu1] using
          (hw.differentiableOn (by norm_num) 1 ⟨zero_le_one, le_rfl⟩).hasDerivWithinAt
      have hleft : HasDerivWithinAt (liftRepr w) 0
          (Icc (0 : ℝ) 1) 1 :=
        hleft0.congr_of_mem (fun y hy ↦ liftRepr_eq_on_Icc hy) ⟨zero_le_one, le_rfl⟩
      have hright : HasDerivWithinAt (liftRepr w) 0 (Ici (1 : ℝ)) 1 := by
        exact (hasDerivAt_const (1 : ℝ) (intervalDomainLift w 1)).hasDerivWithinAt.congr
          (fun y hy ↦ liftRepr_eq_right w hy) (by simp [liftRepr_eq_on_Icc])
      have hunion := hleft.union hright
      have hnhds : Icc (0 : ℝ) 1 ∪ Ici (1 : ℝ) ∈ nhds (1 : ℝ) := by
        apply mem_of_superset (Ici_mem_nhds (show (0 : ℝ) < 1 by norm_num))
        intro y hy
        by_cases hy1 : y ≤ 1
        · exact Or.inl ⟨hy, hy1⟩
        · exact Or.inr (le_of_not_ge hy1)
      have hone : HasDerivAt (liftRepr w) 0 1 := hunion.hasDerivAt hnhds
      simpa [deriv_intervalDomainLift_eq_zero_at_one] using hone
    · have hwithin :=
        (hw.differentiableOn (by norm_num) x hx).hasDerivWithinAt
      rw [deriv_eq_derivWithin_interior ⟨hx0, hx1⟩]
      exact (hwithin.congr_of_mem (fun y hy ↦ liftRepr_eq_on_Icc hy) hx).hasDerivAt
        (Icc_mem_nhds hx0 hx1)

/-- Coarse Neumann Poincare inequality for one positive classical slice,
written in the exact lifted fields used by the entropy calculation. -/
theorem intervalDomain_classicalSlice_poincare
    {p : CM2Params} {T t uStar : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht0 : 0 < t) (htT : t < T)
    (hmass : intervalDomain.integral (u t) = uStar) :
    (∫ x in (0 : ℝ)..1,
        (intervalDomainLift (u t) x - uStar) ^ 2) ≤
      ∫ x in (0 : ℝ)..1,
        (deriv (intervalDomainLift (u t)) x) ^ 2 := by
  let U : ℝ → ℝ := intervalDomainLift (u t)
  let F : ℝ → ℝ := liftRepr (u t)
  let Ux : ℝ → ℝ := deriv U
  have ht : t ∈ Ioo (0 : ℝ) T := ⟨ht0, htT⟩
  have hU2 : ContDiffOn ℝ 2 U (Icc (0 : ℝ) 1) := by
    simpa [U] using (hsol.regularity.2.2.2.2.1 t ht).1.1
  have hneu0 : derivWithin U (Icc (0 : ℝ) 1) 0 = 0 := by
    simpa [U] using derivWithin_left_zero hsol ht0 htT u (Or.inl rfl)
  have hneu1 : derivWithin U (Icc (0 : ℝ) 1) 1 = 0 := by
    simpa [U] using derivWithin_right_zero hsol ht0 htT u (Or.inl rfl)
  have hUx1 : ContDiffOn ℝ 1 Ux (Icc (0 : ℝ) 1) := by
    simpa [U, Ux] using deriv_lift_contDiffOn_one_Icc hU2 hneu0 hneu1
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) := by
    exact (liftRepr_continuous hU2.continuousOn).continuousOn
  have hFderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt F (Ux x) x := by
    intro x hx
    simpa [F, U, Ux] using liftRepr_hasDerivAt_Icc_of_neumann hU2 hneu0 hneu1 x hx
  have hUxInt : IntervalIntegrable Ux volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hUx1.continuousOn
  have hUxSqInt : IntervalIntegrable (fun x ↦ Ux x ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hUx1.continuousOn.pow 2
  have hp := poincare_unit_interval_coarse hFcont hFderiv hUxInt hUxSqInt
  have hmean : (∫ x in (0 : ℝ)..1, F x) = uStar := by
    calc
      (∫ x in (0 : ℝ)..1, F x) =
          ∫ x in (0 : ℝ)..1, U x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        exact liftRepr_eq_on_Icc hx
      _ = uStar := hmass
  calc
    (∫ x in (0 : ℝ)..1, (intervalDomainLift (u t) x - uStar) ^ 2) =
        ∫ x in (0 : ℝ)..1, (F x - uStar) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      change (intervalDomainLift (u t) x - uStar) ^ 2 = (F x - uStar) ^ 2
      rw [show F x = intervalDomainLift (u t) x by
        exact liftRepr_eq_on_Icc hx]
    _ ≤ ∫ x in (0 : ℝ)..1, Ux x ^ 2 := by
      simpa [hmean] using hp
    _ = ∫ x in (0 : ℝ)..1,
        (deriv (intervalDomainLift (u t)) x) ^ 2 := by rfl

#print axioms liftRepr_hasDerivAt_Icc_of_neumann
#print axioms intervalDomain_classicalSlice_poincare

end

end ShenWork.Paper3
