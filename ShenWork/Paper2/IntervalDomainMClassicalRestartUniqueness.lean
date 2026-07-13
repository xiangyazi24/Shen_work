import ShenWork.Paper2.IntervalDomainMClassicalRestartPointwise
import ShenWork.Paper2.IntervalDomainMConjugateMapBounds

/-!
# Local restart uniqueness for faithful general-`m` classical solutions

Once two positive classical branches agree at one positive time, the pointwise
B-form restart and the positive-strip contraction make them agree on a uniform
short window.  This is the propagation component of overlap uniqueness.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (logisticReaction_lipschitz_on_pos_Icc)
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds

/-- Equality at one positive time propagates across any restart window on
which the common positive-strip contraction factor is strictly below one. -/
theorem intervalDomainM_classical_restart_unique_of_eq_at
    {p : CM2Params} {T₁ T₂ a h c M CL : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomainM p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomainM p T₂ u₂ v₂)
    (ha : 0 < a) (hh : 0 < h)
    (hahT₁ : a + h < T₁) (hahT₂ : a + h < T₂)
    (hc : 0 < c) (hcM : c ≤ M) (hCL : 0 ≤ CL)
    (hCL_lip : ∀ r s : ℝ, |r| ≤ M → |s| ≤ M →
      |r * (p.a - p.b * r ^ p.α) - s * (p.a - p.b * s ^ p.α)| ≤
        CL * |r - s|)
    (hub₁ : ∀ s, 0 < s → s ≤ h → ∀ x,
      |classicalRestartTrajectoryM a h u₁ s x| ≤ M)
    (huf₁ : ∀ s, 0 < s → s ≤ h → ∀ x,
      c ≤ classicalRestartTrajectoryM a h u₁ s x)
    (hub₂ : ∀ s, 0 < s → s ≤ h → ∀ x,
      |classicalRestartTrajectoryM a h u₂ s x| ≤ M)
    (huf₂ : ∀ s, 0 < s → s ≤ h → ∀ x,
      c ≤ classicalRestartTrajectoryM a h u₂ s x)
    (hcontract :
      |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt h) * chemFluxMLipschitzConstant p c M) +
        h * CL < 1)
    (heq_a : u₁ a = u₂ a) :
    ∀ r, 0 ≤ r → r ≤ h → ∀ x : intervalDomainPoint,
      u₁ (a + r) x = u₂ (a + r) x := by
  let w₁ := classicalRestartTrajectoryM a h u₁
  let w₂ := classicalRestartTrajectoryM a h u₂
  have hw₁cont : Continuous (Function.uncurry w₁) := by
    have hfield := restartField_continuous hsol₁ ha hh.le hahT₁ u₁ (Or.inl rfl)
    have hcomp : Continuous (fun z : ℝ × intervalDomainPoint =>
        restartField a h u₁ z.1 z.2.1) :=
      hfield.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have heq : (fun z : ℝ × intervalDomainPoint =>
        restartField a h u₁ z.1 z.2.1) = Function.uncurry w₁ := by
      funext z
      change intervalDomainLift
          (u₁ (a + restartTimeClamp h z.1)) (clamp01 z.2.1) =
        u₁ (a + restartTimeClamp h z.1) z.2
      rw [clamp01_eq_self z.2.2]
      unfold intervalDomainLift
      split
      · apply congrArg (u₁ (a + restartTimeClamp h z.1))
        exact Subtype.ext rfl
      · rename_i hnot
        exact (hnot (by simpa [intervalDomainPoint] using z.2.2)).elim
    rwa [← heq]
  have hw₂cont : Continuous (Function.uncurry w₂) := by
    have hfield := restartField_continuous hsol₂ ha hh.le hahT₂ u₂ (Or.inl rfl)
    have hcomp : Continuous (fun z : ℝ × intervalDomainPoint =>
        restartField a h u₂ z.1 z.2.1) :=
      hfield.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    have heq : (fun z : ℝ × intervalDomainPoint =>
        restartField a h u₂ z.1 z.2.1) = Function.uncurry w₂ := by
      funext z
      change intervalDomainLift
          (u₂ (a + restartTimeClamp h z.1)) (clamp01 z.2.1) =
        u₂ (a + restartTimeClamp h z.1) z.2
      rw [clamp01_eq_self z.2.2]
      unfold intervalDomainLift
      split
      · apply congrArg (u₂ (a + restartTimeClamp h z.1))
        exact Subtype.ext rfl
      · rename_i hnot
        exact (hnot (by simpa [intervalDomainPoint] using z.2.2)).elim
    rwa [← heq]
  let F : ℝ × intervalDomainPoint → ℝ := fun z => |w₁ z.1 z.2 - w₂ z.1 z.2|
  let K : Set (ℝ × intervalDomainPoint) := Icc (0 : ℝ) h ×ˢ Set.univ
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  have hKne : K.Nonempty := by
    let x₀ : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
    exact ⟨(0, x₀), ⟨by constructor <;> linarith, Set.mem_univ _⟩⟩
  have hFcont : Continuous F := by
    exact (hw₁cont.sub hw₂cont).abs
  obtain ⟨zmax, hzmax, hmax⟩ :=
    hK.exists_isMaxOn hKne hFcont.continuousOn
  let d : ℝ := F zmax
  have hd_nn : 0 ≤ d := abs_nonneg _
  have hd : ∀ s, 0 < s → s ≤ h → ∀ x,
      |w₁ s x - w₂ s x| ≤ d := by
    intro s hs hsh x
    have hz : (s, x) ∈ K := ⟨⟨hs.le, hsh⟩, Set.mem_univ x⟩
    simpa [d] using hmax hz
  have hw₁c : HasContinuousSlices h w₁ := by
    simpa [w₁] using
      classicalRestartTrajectoryM_hasContinuousSlices hsol₁ ha hh.le hahT₁
  have hw₂c : HasContinuousSlices h w₂ := by
    simpa [w₂] using
      classicalRestartTrajectoryM_hasContinuousSlices hsol₂ ha hh.le hahT₂
  have hw₁m : HasJointMeasurability w₁ := by
    simpa [w₁] using
      classicalRestartTrajectoryM_hasJointMeasurability hsol₁ ha hh.le hahT₁
  have hw₂m : HasJointMeasurability w₂ := by
    simpa [w₂] using
      classicalRestartTrajectoryM_hasJointMeasurability hsol₂ ha hh.le hahT₂
  have hd_zero : d = 0 := by
    by_cases hztime : zmax.1 = 0
    · have hw₁zero : w₁ 0 = u₁ a := by
        simpa [w₁] using
          (classicalRestartTrajectoryM_eq
            (a := a) (h := h) (u := u₁) ⟨le_rfl, hh.le⟩)
      have hw₂zero : w₂ 0 = u₂ a := by
        simpa [w₂] using
          (classicalRestartTrajectoryM_eq
            (a := a) (h := h) (u := u₂) ⟨le_rfl, hh.le⟩)
      dsimp [d, F]
      rw [hztime, hw₁zero, hw₂zero, heq_a, sub_self, abs_zero]
    · have hzpos : 0 < zmax.1 := lt_of_le_of_ne hzmax.1.1 (Ne.symm hztime)
      have hzle : zmax.1 ≤ h := hzmax.1.2
      have hrestart₁ := intervalDomainM_classical_bform_restart_pointwise
        hsol₁ ha hh.le hahT₁ hzpos hzle zmax.2
      have hrestart₂ := intervalDomainM_classical_bform_restart_pointwise
        hsol₂ ha hh.le hahT₂ hzpos hzle zmax.2
      have hmap := intervalConjugateDuhamelMapM_diff_bound_of_positive_cone
        p (u₀ := u₁ a) hh hc hcM hCL hCL_lip
        (by simpa [w₁] using hub₁) (by simpa [w₁] using huf₁)
        (by simpa [w₂] using hub₂) (by simpa [w₂] using huf₂)
        hw₁c hw₂c hw₁m hw₂m hd hzpos hzle zmax.2
      have hdatum : u₂ a = u₁ a := heq_a.symm
      rw [hdatum] at hrestart₂
      have hmap' :
          |u₁ (a + zmax.1) zmax.2 - u₂ (a + zmax.1) zmax.2| ≤
            (|p.χ₀| *
                (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                  (2 * Real.sqrt h) * chemFluxMLipschitzConstant p c M) +
              h * CL) * d := by
        rw [hrestart₁, hrestart₂]
        simpa [w₁, w₂] using hmap
      have hdd : d ≤
          (|p.χ₀| *
              (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                (2 * Real.sqrt h) * chemFluxMLipschitzConstant p c M) +
            h * CL) * d := by
        simpa [d, F, w₁, w₂, classicalRestartTrajectoryM,
          restartTimeClamp_eq_self ⟨hzpos.le, hzle⟩] using hmap'
      nlinarith
  intro r hr0 hrh x
  by_cases hr : r = 0
  · subst r
    simpa using congrFun heq_a x
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hle : |w₁ r x - w₂ r x| ≤ d := hd r hrpos hrh x
    rw [hd_zero] at hle
    have heq : w₁ r x = w₂ r x := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
    simpa [w₁, w₂, classicalRestartTrajectoryM,
      restartTimeClamp_eq_self ⟨hr0, hrh⟩] using heq

#print axioms intervalDomainM_classical_restart_unique_of_eq_at

end ShenWork.Paper2.IntervalDomainM
