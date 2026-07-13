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

/-- The concrete initial sup-norm trace controls every point of a faithful
general-`m` classical slice. -/
theorem intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
    {p : CM2Params} {T : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (htrace : InitialTrace intervalDomainM u₀ u)
    (hu₀b : BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint, |u t x - u₀ x| < ε := by
  obtain ⟨δtrace, hδtrace, hsmall⟩ := htrace.eventually_small hε
  refine ⟨min δtrace T, lt_min hδtrace hsol.T_pos, ?_⟩
  intro t ht htδ x
  have httrace : t < δtrace := htδ.trans_le (min_le_left _ _)
  have htT : t < T := htδ.trans_le (min_le_right _ _)
  have hbdd := bddAbove_range_abs_diff_of_bddAbove
    (solution_slice_abs_bddAbove hsol ⟨ht, htT⟩) hu₀b
  have hsup : intervalDomainSupNorm (fun y => u t y - u₀ y) < ε := by
    simpa [intervalDomainM] using hsmall t ht httrace
  exact (le_csSup hbdd ⟨x, rfl⟩).trans_lt hsup

/-- Two faithful positive classical solutions with the same paper datum agree
on a nontrivial initial time interval. -/
theorem intervalDomainM_classical_initial_u_unique_on_short
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hsol₁ : IsPaper2ClassicalSolution intervalDomainM p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomainM p T₂ u₂ v₂)
    (htr₁ : InitialTrace intervalDomainM u₀ u₁)
    (htr₂ : InitialTrace intervalDomainM u₀ u₂) :
    ∃ H > 0, ∀ t, 0 < t → t < H →
      ∀ x : intervalDomainPoint, u₁ t x = u₂ t x := by
  have hu₀adm :
      BddAbove (Set.range (fun x : intervalDomainPoint => |u₀ x|)) ∧
        Continuous u₀ := by
    simpa [intervalDomainM] using hu₀.admissible
  obtain ⟨η, hη, hηle⟩ := hu₀.floor
  obtain ⟨B, hB⟩ := hu₀adm.1
  let x₀ : intervalDomainPoint := ⟨0, by constructor <;> norm_num⟩
  have hB_nn : 0 ≤ B := (abs_nonneg (u₀ x₀)).trans (hB ⟨x₀, rfl⟩)
  set c : ℝ := η / 2 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set M : ℝ := B + 1 with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  have hcM : c ≤ M := by
    have hηB : η ≤ B :=
      (hηle x₀).trans ((le_abs_self (u₀ x₀)).trans (hB ⟨x₀, rfl⟩))
    rw [hcdef, hMdef]
    linarith
  set ε₀ : ℝ := min c 1 with hε₀def
  have hε₀ : 0 < ε₀ := lt_min hc one_pos
  obtain ⟨δ₁, hδ₁, hclose₁⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol₁ htr₁ hu₀adm.1 hε₀
  obtain ⟨δ₂, hδ₂, hclose₂⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol₂ htr₂ hu₀adm.1 hε₀
  obtain ⟨CL, hCL, hCL_lip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p hM
  set CQ : ℝ := chemFluxMLipschitzConstant p c M with hCQdef
  have hCQ : 0 ≤ CQ := chemFluxMLipschitzConstant_nonneg p hc hcM
  set A : ℝ := |p.χ₀| *
      (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        2 * CQ) with hAdef
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
          (by norm_num)) hCQ)
  obtain ⟨H₀, hH₀, hsmall₀⟩ :=
    exists_small_contraction_time_target hA hCL.le one_pos
  set R : ℝ := min H₀ (min δ₁ (min δ₂ (min T₁ T₂))) with hRdef
  have hR : 0 < R := lt_min hH₀ (lt_min hδ₁ (lt_min hδ₂
    (lt_min hsol₁.T_pos hsol₂.T_pos)))
  set H : ℝ := R / 3 with hHdef
  have hH : 0 < H := by rw [hHdef]; linarith
  have h2H_R : 2 * H < R := by rw [hHdef]; linarith
  have hH_H₀ : H ≤ H₀ := by
    rw [hHdef]
    exact (div_le_self hR.le (by norm_num)).trans (min_le_left _ _)
  have hcontract :
      |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt H) * chemFluxMLipschitzConstant p c M) +
        H * CL < 1 := by
    have hsqrt : Real.sqrt H ≤ Real.sqrt H₀ :=
      Real.sqrt_le_sqrt hH_H₀
    have hAstep : A * Real.sqrt H ≤ A * Real.sqrt H₀ :=
      mul_le_mul_of_nonneg_left hsqrt hA
    have hCLstep : CL * H ≤ CL * H₀ :=
      mul_le_mul_of_nonneg_left hH_H₀ hCL.le
    have hmono : A * Real.sqrt H + CL * H ≤
        A * Real.sqrt H₀ + CL * H₀ := add_le_add hAstep hCLstep
    rw [hAdef, hCQdef] at hmono
    calc
      _ = |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              2 * chemFluxMLipschitzConstant p c M) * Real.sqrt H +
          CL * H := by ring
      _ ≤ |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              2 * chemFluxMLipschitzConstant p c M) * Real.sqrt H₀ +
          CL * H₀ := hmono
      _ < 1 := hsmall₀
  refine ⟨H, hH, ?_⟩
  intro t ht htH x
  have hq_lt := hcontract
  set q : ℝ :=
    |p.χ₀| *
        (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt H) * chemFluxMLipschitzConstant p c M) +
      H * CL with hqdef
  have hq_lt' : q < 1 := by simpa [q] using hq_lt
  have hq_nn : 0 ≤ q := by
    rw [hqdef]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg heatGradientLinftyLinftyConstant_nonneg
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) hCQ))
      (mul_nonneg hH.le hCL.le)
  by_contra hne
  have hdiff_pos : 0 < |u₁ t x - u₂ t x| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  set e : ℝ := (1 - q) * |u₁ t x - u₂ t x| / 2 with hedef
  have he : 0 < e := by
    rw [hedef]
    exact div_pos (mul_pos (sub_pos.mpr hq_lt') hdiff_pos) (by norm_num)
  obtain ⟨δe₁, hδe₁, htracee₁⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol₁ htr₁ hu₀adm.1 (show 0 < e / 2 by positivity)
  obtain ⟨δe₂, hδe₂, htracee₂⟩ :=
    intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
      hsol₂ htr₂ hu₀adm.1 (show 0 < e / 2 by positivity)
  set a : ℝ := min (t / 2) (min (δe₁ / 2) (δe₂ / 2)) with hadef
  have ha : 0 < a := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hat : a < t := by
    have := min_le_left (t / 2) (min (δe₁ / 2) (δe₂ / 2))
    rw [← hadef] at this
    linarith
  have haδe₁ : a < δe₁ := by
    have := (min_le_right (t / 2) (min (δe₁ / 2) (δe₂ / 2))).trans
      (min_le_left (δe₁ / 2) (δe₂ / 2))
    rw [← hadef] at this
    linarith
  have haδe₂ : a < δe₂ := by
    have := (min_le_right (t / 2) (min (δe₁ / 2) (δe₂ / 2))).trans
      (min_le_right (δe₁ / 2) (δe₂ / 2))
    rw [← hadef] at this
    linarith
  have haH : a < H := hat.trans htH
  have haH_R : a + H < R := by linarith
  have haHT₁ : a + H < T₁ :=
    haH_R.trans_le ((min_le_right H₀ (min δ₁ (min δ₂ (min T₁ T₂)))).trans
      ((min_le_right δ₁ (min δ₂ (min T₁ T₂))).trans
        ((min_le_right δ₂ (min T₁ T₂)).trans (min_le_left _ _))))
  have haHT₂ : a + H < T₂ :=
    haH_R.trans_le ((min_le_right H₀ (min δ₁ (min δ₂ (min T₁ T₂)))).trans
      ((min_le_right δ₁ (min δ₂ (min T₁ T₂))).trans
        ((min_le_right δ₂ (min T₁ T₂)).trans (min_le_right _ _))))
  have htime_bounds : ∀ s, 0 < s → s ≤ H →
      0 < a + s ∧ a + s < δ₁ ∧ a + s < δ₂ := by
    intro s hs hsH
    have hasR : a + s < R := by linarith
    have hRδ₁ : R ≤ δ₁ :=
      (min_le_right H₀ (min δ₁ (min δ₂ (min T₁ T₂)))).trans
        (min_le_left _ _)
    have hRδ₂ : R ≤ δ₂ :=
      (min_le_right H₀ (min δ₁ (min δ₂ (min T₁ T₂)))).trans
        ((min_le_right δ₁ (min δ₂ (min T₁ T₂))).trans (min_le_left _ _))
    exact ⟨by linarith, hasR.trans_le hRδ₁, hasR.trans_le hRδ₂⟩
  have hub₁ : ∀ s, 0 < s → s ≤ H → ∀ y,
      |classicalRestartTrajectoryM a H u₁ s y| ≤ M := by
    intro s hs hsH y
    have hb := htime_bounds s hs hsH
    have hclose := hclose₁ (a + s) hb.1 hb.2.1 y
    have hu₀B : |u₀ y| ≤ B := hB ⟨y, rfl⟩
    rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsH⟩]
    calc
      |u₁ (a + s) y| =
          |(u₁ (a + s) y - u₀ y) + u₀ y| := by congr 1 <;> ring
      _ ≤ |u₁ (a + s) y - u₀ y| + |u₀ y| := abs_add_le _ _
      _ = |u₀ y| + |u₁ (a + s) y - u₀ y| := add_comm _ _
      _ ≤ B + 1 := add_le_add hu₀B ((hclose.le.trans (min_le_right _ _)))
      _ = M := hMdef.symm
  have hub₂ : ∀ s, 0 < s → s ≤ H → ∀ y,
      |classicalRestartTrajectoryM a H u₂ s y| ≤ M := by
    intro s hs hsH y
    have hb := htime_bounds s hs hsH
    have hclose := hclose₂ (a + s) hb.1 hb.2.2 y
    have hu₀B : |u₀ y| ≤ B := hB ⟨y, rfl⟩
    rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsH⟩]
    calc
      |u₂ (a + s) y| =
          |(u₂ (a + s) y - u₀ y) + u₀ y| := by congr 1 <;> ring
      _ ≤ |u₂ (a + s) y - u₀ y| + |u₀ y| := abs_add_le _ _
      _ = |u₀ y| + |u₂ (a + s) y - u₀ y| := add_comm _ _
      _ ≤ B + 1 := add_le_add hu₀B ((hclose.le.trans (min_le_right _ _)))
      _ = M := hMdef.symm
  have huf₁ : ∀ s, 0 < s → s ≤ H → ∀ y,
      c ≤ classicalRestartTrajectoryM a H u₁ s y := by
    intro s hs hsH y
    have hb := htime_bounds s hs hsH
    have hclose := hclose₁ (a + s) hb.1 hb.2.1 y
    rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsH⟩]
    have hfloor := hηle y
    have habs_lower := neg_le_of_abs_le hclose.le
    rw [hε₀def] at habs_lower
    have heps : ε₀ ≤ c := min_le_left _ _
    linarith
  have huf₂ : ∀ s, 0 < s → s ≤ H → ∀ y,
      c ≤ classicalRestartTrajectoryM a H u₂ s y := by
    intro s hs hsH y
    have hb := htime_bounds s hs hsH
    have hclose := hclose₂ (a + s) hb.1 hb.2.2 y
    rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsH⟩]
    have hfloor := hηle y
    have habs_lower := neg_le_of_abs_le hclose.le
    rw [hε₀def] at habs_lower
    have heps : ε₀ ≤ c := min_le_left _ _
    linarith
  have hdatum : ∀ y, |u₁ a y - u₂ a y| ≤ e := by
    intro y
    have h1 := htracee₁ a ha haδe₁ y
    have h2 := htracee₂ a ha haδe₂ y
    calc
      |u₁ a y - u₂ a y| =
          |(u₁ a y - u₀ y) + (u₀ y - u₂ a y)| := by congr 1 <;> ring
      _ ≤ |u₁ a y - u₀ y| + |u₀ y - u₂ a y| := abs_add_le _ _
      _ = |u₁ a y - u₀ y| + |u₂ a y - u₀ y| := by
        rw [abs_sub_comm (u₀ y) (u₂ a y)]
      _ ≤ e := by linarith
  have hdiff := intervalDomainM_classical_restart_diff_bound
    hsol₁ hsol₂ ha hH haHT₁ haHT₂ hc hcM hCL.le hCL_lip
      hub₁ huf₁ hub₂ huf₂ he.le hdatum hcontract
      (t - a) (sub_nonneg.mpr hat.le) (by linarith) x
  have hediv : e / (1 - q) = |u₁ t x - u₂ t x| / 2 := by
    rw [hedef]
    field_simp [ne_of_gt (sub_pos.mpr hq_lt')]
  rw [show a + (t - a) = t by ring, ← hqdef, hediv] at hdiff
  linarith

/-- A faithful positive classical branch has a uniform positive lower bound
and a uniform absolute upper bound on every compact positive-time slab. -/
theorem intervalDomainM_u_two_sided_on_compact
    {p : CM2Params} {T s t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (hs : 0 < s) (hst : s ≤ t) (htT : t < T) :
    ∃ c M : ℝ, 0 < c ∧ c ≤ M ∧
      ∀ τ ∈ Icc s t, ∀ x : intervalDomainPoint,
        c ≤ u τ x ∧ |u τ x| ≤ M := by
  classical
  let K : Set (ℝ × ℝ) := Icc s t ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨(s, 0), ⟨Set.left_mem_Icc.mpr hst, by constructor <;> norm_num⟩⟩
  have hsub : K ⊆ Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1 := by
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩
    exact ⟨⟨hs.trans_le hτ.1, hτ.2.trans_lt htT⟩, hy⟩
  have hfield : ContinuousOn
      (Function.uncurry (fun (τ : ℝ) (y : ℝ) => intervalDomainLift (u τ) y))
      K := (hsol.regularity.2.2.2.2.2.2.1).mono hsub
  obtain ⟨qmin, hqmin, hmin⟩ := hK.exists_isMinOn hKne hfield
  obtain ⟨qmax, hqmax, hmax⟩ := hK.exists_isMaxOn hKne hfield.abs
  set c : ℝ := intervalDomainLift (u qmin.1) qmin.2 with hcdef
  set B : ℝ := |intervalDomainLift (u qmax.1) qmax.2| with hBdef
  set M : ℝ := max c B with hMdef
  have hc : 0 < c := by
    rw [hcdef]
    exact solution_lift_pos_Icc hsol
      ⟨hs.trans_le hqmin.1.1, hqmin.1.2.trans_lt htT⟩ qmin.2 hqmin.2
  have hcM : c ≤ M := by rw [hMdef]; exact le_max_left _ _
  refine ⟨c, M, hc, hcM, ?_⟩
  intro τ hτ x
  have hz : (τ, x.1) ∈ K := ⟨hτ, x.2⟩
  have hlo : c ≤ intervalDomainLift (u τ) x.1 := by
    rw [hcdef]
    exact isMinOn_iff.mp hmin (τ, x.1) hz
  have hup : |intervalDomainLift (u τ) x.1| ≤ M := by
    have hB : |intervalDomainLift (u τ) x.1| ≤ B := by
      rw [hBdef]
      exact isMaxOn_iff.mp hmax (τ, x.1) hz
    exact hB.trans (by rw [hMdef]; exact le_max_right _ _)
  constructor
  · simpa [intervalDomainLift, x.2] using hlo
  · simpa [intervalDomainLift, x.2] using hup

/-- On a positive slice the chemical component is determined uniquely by the
cell-density component through the Neumann elliptic resolver. -/
theorem intervalDomainM_solution_v_eq_of_u_eq
    {p : CM2Params} {T₁ T₂ t : ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hsol₁ : IsPaper2ClassicalSolution intervalDomainM p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomainM p T₂ u₂ v₂)
    (ht₁ : t ∈ Ioo (0 : ℝ) T₁) (ht₂ : t ∈ Ioo (0 : ℝ) T₂)
    (hu : u₁ t = u₂ t) : v₁ t = v₂ t := by
  have hv₁cont : ContinuousOn (intervalDomainLift (v₁ t)) (Icc (0 : ℝ) 1) :=
    (hsol₁.regularity.2.2.2.2.1 t ht₁).2.1.continuousOn
  have hv₂cont : ContinuousOn (intervalDomainLift (v₂ t)) (Icc (0 : ℝ) 1) :=
    (hsol₂.regularity.2.2.2.2.1 t ht₂).2.1.continuousOn
  have hinterior : Set.EqOn (intervalDomainLift (v₁ t))
      (intervalDomainLift (v₂ t)) (Ioo (0 : ℝ) 1) := by
    intro y hy
    rw [← solution_v_eq_resolver_pointwiseM hsol₁ ht₁ hy,
      ← solution_v_eq_resolver_pointwiseM hsol₂ ht₂ hy, hu]
  have hclosed : Set.EqOn (intervalDomainLift (v₁ t))
      (intervalDomainLift (v₂ t)) (Icc (0 : ℝ) 1) := by
    refine hinterior.of_subset_closure hv₁cont hv₂cont Ioo_subset_Icc_self ?_
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  funext x
  simpa [intervalDomainLift, x.2] using hclosed x.2

/-- Faithful overlap uniqueness on the whole common lifespan.  A compact
positive-time slab is covered by finitely many uniform restart-contraction
windows. -/
theorem intervalDomainM_classicalSolution_overlap_unique
    {p : CM2Params} {T₁ T₂ : ℝ}
    {u₀ : intervalDomainPoint → ℝ}
    {u₁ v₁ u₂ v₂ : ℝ → intervalDomainPoint → ℝ}
    (hu₀ : PaperPositiveInitialDatum intervalDomainM u₀)
    (hsol₁ : IsPaper2ClassicalSolution intervalDomainM p T₁ u₁ v₁)
    (hsol₂ : IsPaper2ClassicalSolution intervalDomainM p T₂ u₂ v₂)
    (htr₁ : InitialTrace intervalDomainM u₀ u₁)
    (htr₂ : InitialTrace intervalDomainM u₀ u₂) :
    ∀ t, 0 < t → t < min T₁ T₂ →
      ∀ x : intervalDomainPoint, u₁ t x = u₂ t x ∧ v₁ t x = v₂ t x := by
  obtain ⟨Hinit, hHinit, hinit⟩ :=
    intervalDomainM_classical_initial_u_unique_on_short
      hu₀ hsol₁ hsol₂ htr₁ htr₂
  intro t ht htT x
  set a : ℝ := min (Hinit / 2) (t / 2) with hadef
  have ha : 0 < a := lt_min (by linarith) (by linarith)
  have haH : a < Hinit := by
    have := min_le_left (Hinit / 2) (t / 2)
    rw [← hadef] at this
    linarith
  have hat : a < t := by
    have := min_le_right (Hinit / 2) (t / 2)
    rw [← hadef] at this
    linarith
  have heq_a : u₁ a = u₂ a := by
    funext y
    exact hinit a ha haH y
  have htT₁ : t < T₁ := htT.trans_le (min_le_left _ _)
  have htT₂ : t < T₂ := htT.trans_le (min_le_right _ _)
  obtain ⟨c₁, M₁, hc₁, hcM₁, hb₁⟩ :=
    intervalDomainM_u_two_sided_on_compact hsol₁ ha hat.le htT₁
  obtain ⟨c₂, M₂, hc₂, hcM₂, hb₂⟩ :=
    intervalDomainM_u_two_sided_on_compact hsol₂ ha hat.le htT₂
  set c : ℝ := min c₁ c₂ with hcdef
  set M : ℝ := max M₁ M₂ with hMdef
  have hc : 0 < c := by rw [hcdef]; exact lt_min hc₁ hc₂
  have hcM : c ≤ M := by
    rw [hcdef, hMdef]
    exact (min_le_left _ _).trans (hcM₁.trans (le_max_left _ _))
  obtain ⟨CL, hCL, hCL_lip⟩ :=
    ShenWork.IntervalDomainExistence.intervalLogisticSource_lipschitz p
      (hc.trans_le hcM)
  set CQ : ℝ := chemFluxMLipschitzConstant p c M with hCQdef
  have hCQ : 0 ≤ CQ := chemFluxMLipschitzConstant_nonneg p hc hcM
  set A : ℝ := |p.χ₀| *
      (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        2 * CQ) with hAdef
  have hA : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (abs_nonneg _)
      (mul_nonneg
        (mul_nonneg heatGradientLinftyLinftyConstant_nonneg (by norm_num)) hCQ)
  obtain ⟨h₀, hh₀, hsmall⟩ :=
    exists_small_contraction_time_target hA hCL.le one_pos
  obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / h₀)
  have hratio : 0 < (t - a) / h₀ := div_pos (sub_pos.mpr hat) hh₀
  have hnreal : 0 < (n : ℝ) := hratio.trans hn
  have hnpos : 0 < n := by exact_mod_cast hnreal
  set hstep : ℝ := (t - a) / (n : ℝ) with hstepdef
  have hhstep : 0 < hstep := by
    rw [hstepdef]
    exact div_pos (sub_pos.mpr hat) hnreal
  have hstep_lt : hstep < h₀ := by
    have hmul : t - a < (n : ℝ) * h₀ := (div_lt_iff₀ hh₀).mp hn
    rw [hstepdef]
    exact (div_lt_iff₀ hnreal).2 (by simpa [mul_comm] using hmul)
  have hstep_contract :
      |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt hstep) * chemFluxMLipschitzConstant p c M) +
        hstep * CL < 1 := by
    have hsqrt : Real.sqrt hstep ≤ Real.sqrt h₀ :=
      Real.sqrt_le_sqrt hstep_lt.le
    have hAstep : A * Real.sqrt hstep ≤ A * Real.sqrt h₀ :=
      mul_le_mul_of_nonneg_left hsqrt hA
    have hCLstep : CL * hstep ≤ CL * h₀ :=
      mul_le_mul_of_nonneg_left hstep_lt.le hCL.le
    have hmono := add_le_add hAstep hCLstep
    rw [hAdef, hCQdef] at hmono
    calc
      _ = |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              2 * chemFluxMLipschitzConstant p c M) * Real.sqrt hstep +
          CL * hstep := by ring
      _ ≤ |p.χ₀| *
            (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
              2 * chemFluxMLipschitzConstant p c M) * Real.sqrt h₀ +
          CL * h₀ := hmono
      _ < 1 := hsmall
  have hend : a + (n : ℝ) * hstep = t := by
    rw [hstepdef]
    field_simp [ne_of_gt hnreal]
    <;> ring
  have hgrid : ∀ k : ℕ, k ≤ n →
      u₁ (a + (k : ℝ) * hstep) = u₂ (a + (k : ℝ) * hstep) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using heq_a
    | succ k ih =>
        intro hkn
        have hklt : k < n := Nat.lt_of_succ_le hkn
        have hkle : k ≤ n := hklt.le
        have heqk := ih hkle
        set ak : ℝ := a + (k : ℝ) * hstep with hakdef
        have hak : 0 < ak := by
          rw [hakdef]
          exact add_pos_of_pos_of_nonneg ha
            (mul_nonneg (Nat.cast_nonneg _) hhstep.le)
        have hendk : ak + hstep = a + ((k + 1 : ℕ) : ℝ) * hstep := by
          rw [hakdef, Nat.cast_add, Nat.cast_one]
          ring
        have hkend_le : a + ((k + 1 : ℕ) : ℝ) * hstep ≤ t := by
          rw [← hend]
          gcongr
        have hakT₁ : ak + hstep < T₁ := by rw [hendk]; exact hkend_le.trans_lt htT₁
        have hakT₂ : ak + hstep < T₂ := by rw [hendk]; exact hkend_le.trans_lt htT₂
        have htraj₁ : ∀ s, 0 < s → s ≤ hstep → ∀ y,
            c ≤ classicalRestartTrajectoryM ak hstep u₁ s y ∧
              |classicalRestartTrajectoryM ak hstep u₁ s y| ≤ M := by
          intro s hs hsh y
          have htime_lo : a ≤ ak + s := by
            rw [hakdef]
            have hkterm : 0 ≤ (k : ℝ) * hstep :=
              mul_nonneg (Nat.cast_nonneg _) hhstep.le
            linarith
          have htime_hi : ak + s ≤ t := by
            calc
              ak + s ≤ ak + hstep := by linarith
              _ = a + ((k + 1 : ℕ) : ℝ) * hstep := hendk
              _ ≤ t := hkend_le
          have hb := hb₁ (ak + s) ⟨htime_lo, htime_hi⟩ y
          rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsh⟩]
          exact ⟨(min_le_left _ _).trans hb.1,
            hb.2.trans (by rw [hMdef]; exact le_max_left _ _)⟩
        have htraj₂ : ∀ s, 0 < s → s ≤ hstep → ∀ y,
            c ≤ classicalRestartTrajectoryM ak hstep u₂ s y ∧
              |classicalRestartTrajectoryM ak hstep u₂ s y| ≤ M := by
          intro s hs hsh y
          have htime_lo : a ≤ ak + s := by
            rw [hakdef]
            have hkterm : 0 ≤ (k : ℝ) * hstep :=
              mul_nonneg (Nat.cast_nonneg _) hhstep.le
            linarith
          have htime_hi : ak + s ≤ t := by
            calc
              ak + s ≤ ak + hstep := by linarith
              _ = a + ((k + 1 : ℕ) : ℝ) * hstep := hendk
              _ ≤ t := hkend_le
          have hb := hb₂ (ak + s) ⟨htime_lo, htime_hi⟩ y
          rw [classicalRestartTrajectoryM_eq ⟨hs.le, hsh⟩]
          exact ⟨(min_le_right _ _).trans hb.1,
            hb.2.trans (by rw [hMdef]; exact le_max_right _ _)⟩
        have hnext := intervalDomainM_classical_restart_unique_of_eq_at
          hsol₁ hsol₂ hak hhstep hakT₁ hakT₂ hc hcM hCL.le hCL_lip
          (fun s hs hsh y => (htraj₁ s hs hsh y).2)
          (fun s hs hsh y => (htraj₁ s hs hsh y).1)
          (fun s hs hsh y => (htraj₂ s hs hsh y).2)
          (fun s hs hsh y => (htraj₂ s hs hsh y).1)
          hstep_contract (by simpa [ak, hakdef] using heqk)
          hstep hhstep.le le_rfl
        rw [hendk] at hnext
        funext y
        exact hnext y
  have hu : u₁ t = u₂ t := by
    rw [← hend]
    exact hgrid n le_rfl
  have hv : v₁ t = v₂ t :=
    intervalDomainM_solution_v_eq_of_u_eq hsol₁ hsol₂
      ⟨ht, htT₁⟩ ⟨ht, htT₂⟩ hu
  exact ⟨congrFun hu x, congrFun hv x⟩

#print axioms intervalDomainM_classical_restart_diff_bound
#print axioms intervalDomainM_initialTrace_pointwise_abs_lt_of_classical
#print axioms intervalDomainM_classical_initial_u_unique_on_short
#print axioms intervalDomainM_u_two_sided_on_compact
#print axioms intervalDomainM_solution_v_eq_of_u_eq
#print axioms intervalDomainM_classicalSolution_overlap_unique

end ShenWork.Paper2.IntervalDomainM
