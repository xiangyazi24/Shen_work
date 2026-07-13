import ShenWork.Paper2.IntervalDomainMClassicalRestartUniqueness
import ShenWork.Paper2.IntervalDomainMMass

/-!
# Initial-trace overlap uniqueness for faithful general-`m` solutions

The positive-time restart contraction is stable under a small discrepancy in
the restart datum.  The discrepancy is propagated only by the Neumann heat
semigroup and therefore has coefficient one.  Sending the restart time to
zero through the common initial trace seeds exact overlap uniqueness.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalDuhamelIntegrability
  (continuousOn_aestronglyMeasurable_intervalMeasure
   intervalFullSemigroupOperator_diff_Linfty_of_integrable)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant_nonneg)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (intervalConjugateDuhamelMapM)
open ShenWork.Paper2.IntervalDomainMConjugateMapBounds
open ShenWork.Paper2.IntervalDomainM

private theorem classical_slice_lift_bounded_integrable
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ y : ℝ, |intervalDomainLift (u t) y| ≤ M) ∧
      Integrable (intervalDomainLift (u t)) (intervalMeasure 1) := by
  obtain ⟨B, hB⟩ := solution_slice_abs_bddAbove hsol ht
  refine ⟨max B 0, le_max_right _ _, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · have hle : |u t ⟨y, hy⟩| ≤ B := hB ⟨⟨y, hy⟩, rfl⟩
      rw [intervalDomainLift, dif_pos hy]
      exact hle.trans (le_max_left _ _)
    · rw [intervalDomainLift, dif_neg hy, abs_zero]
      exact le_max_right _ _
  · have hcont := solution_lift_continuousOn_Icc hsol ht
    have hmeas : AEStronglyMeasurable (intervalDomainLift (u t))
        (intervalMeasure 1) :=
      continuousOn_aestronglyMeasurable_intervalMeasure hcont
    exact ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      (M := max B 0) hmeas (by
        intro y
        by_cases hy : y ∈ Icc (0 : ℝ) 1
        · have hle : |u t ⟨y, hy⟩| ≤ B := hB ⟨⟨y, hy⟩, rfl⟩
          rw [intervalDomainLift, dif_pos hy]
          exact hle.trans (le_max_left B (0 : ℝ))
        · rw [intervalDomainLift, dif_neg hy, abs_zero]
          exact le_max_right _ _)

private theorem lift_sub_bound_of_slice_sub_bound
    {f g : intervalDomainPoint → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hfg : ∀ x, |f x - g x| ≤ e) :
    ∀ y : ℝ, |intervalDomainLift f y - intervalDomainLift g y| ≤ e := by
  intro y
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · simpa [intervalDomainLift, hy] using hfg ⟨y, hy⟩
  · simp [intervalDomainLift, hy, he]

/-- Restart stability with an explicit error in the restart datum. -/
theorem intervalDomainM_classical_restart_diff_bound
    {p : CM2Params} {T₁ T₂ a h c M CL e : ℝ}
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
    (he : 0 ≤ e) (hdatum : ∀ x, |u₁ a x - u₂ a x| ≤ e)
    (hcontract :
      |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt h) * chemFluxMLipschitzConstant p c M) +
        h * CL < 1) :
    ∀ r, 0 ≤ r → r ≤ h → ∀ x : intervalDomainPoint,
      |u₁ (a + r) x - u₂ (a + r) x| ≤
        e / (1 -
          (|p.χ₀| *
              (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
                (2 * Real.sqrt h) * chemFluxMLipschitzConstant p c M) +
            h * CL)) := by
  let q : ℝ :=
    |p.χ₀| *
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt h) * chemFluxMLipschitzConstant p c M) +
      h * CL
  have hq_nn : 0 ≤ q := by
    dsimp [q]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg
            heatGradientLinftyLinftyConstant_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))
          (chemFluxMLipschitzConstant_nonneg p hc hcM)))
      (mul_nonneg hh.le hCL)
  have hq_lt : q < 1 := by simpa [q] using hcontract
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
  have hFcont : Continuous F := (hw₁cont.sub hw₂cont).abs
  obtain ⟨zmax, hzmax, hmax⟩ := hK.exists_isMaxOn hKne hFcont.continuousOn
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
  have hd_main : d ≤ e + q * d := by
    by_cases hztime : zmax.1 = 0
    · have hw₁zero : w₁ 0 = u₁ a := by
        simpa [w₁] using
          (classicalRestartTrajectoryM_eq
            (a := a) (h := h) (u := u₁) ⟨le_rfl, hh.le⟩)
      have hw₂zero : w₂ 0 = u₂ a := by
        simpa [w₂] using
          (classicalRestartTrajectoryM_eq
            (a := a) (h := h) (u := u₂) ⟨le_rfl, hh.le⟩)
      have hde : d ≤ e := by
        dsimp [d, F]
        rw [hztime, hw₁zero, hw₂zero]
        exact hdatum zmax.2
      nlinarith [mul_nonneg hq_nn hd_nn]
    · have hzpos : 0 < zmax.1 :=
        lt_of_le_of_ne hzmax.1.1 (Ne.symm hztime)
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
      obtain ⟨M₁, hM₁, hb₁, hi₁⟩ :=
        classical_slice_lift_bounded_integrable hsol₁
          (show a ∈ Ioo (0 : ℝ) T₁ by constructor <;> linarith)
      obtain ⟨M₂, hM₂, hb₂, hi₂⟩ :=
        classical_slice_lift_bounded_integrable hsol₂
          (show a ∈ Ioo (0 : ℝ) T₂ by constructor <;> linarith)
      have hsemigroup :
          |intervalFullSemigroupOperator zmax.1 (intervalDomainLift (u₁ a)) zmax.2.1 -
              intervalFullSemigroupOperator zmax.1 (intervalDomainLift (u₂ a)) zmax.2.1| ≤ e :=
        intervalFullSemigroupOperator_diff_Linfty_of_integrable
          hzpos hi₁ hi₂ hM₁ hb₁ hM₂ hb₂ he
            (lift_sub_bound_of_slice_sub_bound he hdatum) zmax.2.1
      have hmapDatum :
          |intervalConjugateDuhamelMapM p (u₁ a) w₂ zmax.1 zmax.2 -
              intervalConjugateDuhamelMapM p (u₂ a) w₂ zmax.1 zmax.2| ≤ e := by
        calc
          _ = |intervalFullSemigroupOperator zmax.1
                (intervalDomainLift (u₁ a)) zmax.2.1 -
              intervalFullSemigroupOperator zmax.1
                (intervalDomainLift (u₂ a)) zmax.2.1| := by
              dsimp [intervalConjugateDuhamelMapM]
              congr 1 <;> ring
          _ ≤ e := hsemigroup
      have hactual :
          |u₁ (a + zmax.1) zmax.2 - u₂ (a + zmax.1) zmax.2| ≤ q * d + e := by
        rw [hrestart₁, hrestart₂]
        calc
          _ = |(intervalConjugateDuhamelMapM p (u₁ a) w₁ zmax.1 zmax.2 -
                  intervalConjugateDuhamelMapM p (u₁ a) w₂ zmax.1 zmax.2) +
                (intervalConjugateDuhamelMapM p (u₁ a) w₂ zmax.1 zmax.2 -
                  intervalConjugateDuhamelMapM p (u₂ a) w₂ zmax.1 zmax.2)| := by
              congr 1 <;> ring
          _ ≤ |intervalConjugateDuhamelMapM p (u₁ a) w₁ zmax.1 zmax.2 -
                  intervalConjugateDuhamelMapM p (u₁ a) w₂ zmax.1 zmax.2| +
                |intervalConjugateDuhamelMapM p (u₁ a) w₂ zmax.1 zmax.2 -
                  intervalConjugateDuhamelMapM p (u₂ a) w₂ zmax.1 zmax.2| :=
              abs_add_le _ _
          _ ≤ q * d + e := by
              simpa [q] using add_le_add hmap hmapDatum
      simpa [d, F, w₁, w₂, classicalRestartTrajectoryM,
        restartTimeClamp_eq_self ⟨hzpos.le, hzle⟩, add_comm] using hactual
  have hd_bound : d ≤ e / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq_lt)).2
    nlinarith
  intro r hr0 hrh x
  by_cases hr : r = 0
  · subst r
    have hz : ((0 : ℝ), x) ∈ K :=
      ⟨⟨le_rfl, hh.le⟩, Set.mem_univ x⟩
    have hle0 : |w₁ 0 x - w₂ 0 x| ≤ d := by
      simpa [d] using hmax hz
    simpa [q, w₁, w₂, classicalRestartTrajectoryM,
      restartTimeClamp_eq_self ⟨le_rfl, hh.le⟩] using hle0.trans hd_bound
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hle : |w₁ r x - w₂ r x| ≤ d := hd r hrpos hrh x
    simpa [q, w₁, w₂, classicalRestartTrajectoryM,
      restartTimeClamp_eq_self ⟨hr0, hrh⟩] using hle.trans hd_bound

#print axioms intervalDomainM_classical_restart_diff_bound

end ShenWork.Paper2.IntervalDomainM
