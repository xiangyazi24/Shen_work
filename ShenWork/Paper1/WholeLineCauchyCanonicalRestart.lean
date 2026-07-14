import ShenWork.Paper1.WholeLineCauchyStableCeilingCanonical
import ShenWork.Paper1.WholeLineCauchySemigroupRestart

open Filter Topology MeasureTheory Real Set Function
open scoped BoundedContinuousFunction Interval NNReal

noncomputable section

namespace ShenWork.Paper1

/-!
# Canonical whole-line restart compatibility

The restriction of a canonical trajectory to a later time window is again a
continuous BUC trajectory.  Its recent Duhamel histories are precisely the
translated recent histories of the original trajectory.  These identities
are the analytic input for uniqueness of canonical restarts.
-/

/-- Translate a compact BUC trajectory to a later subwindow. -/
def wholeLineBUCTrajectoryShift
    {T t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (U : WholeLineBUCTrajectory T) : WholeLineBUCTrajectory h := by
  refine ⟨fun z => U ⟨t + z.1,
      ⟨add_nonneg ht z.2.1, by linarith [z.2.2, hth]⟩⟩, ?_⟩
  apply U.continuous.comp
  apply Continuous.subtype_mk
  exact continuous_const.add continuous_subtype_val

@[simp] theorem wholeLineBUCTrajectoryShift_apply
    {T t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (U : WholeLineBUCTrajectory T) (z : Set.Icc (0 : ℝ) h) :
    wholeLineBUCTrajectoryShift ht hh hth U z =
      U ⟨t + z.1,
        ⟨add_nonneg ht z.2.1, by linarith [z.2.2, hth]⟩⟩ :=
  rfl

theorem wholeLineBUCTrajectoryExtend_shift_eq
    {T t h s : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (hT : 0 ≤ T) (U : WholeLineBUCTrajectory T)
    (hs : s ∈ Set.Icc (0 : ℝ) h) :
    wholeLineBUCTrajectoryExtend hh
        (wholeLineBUCTrajectoryShift ht hh hth U) s =
      wholeLineBUCTrajectoryExtend hT U (t + s) := by
  rw [wholeLineBUCTrajectoryExtend_eq hh _ hs]
  rw [wholeLineBUCTrajectoryExtend_eq hT U]
  rfl

theorem wholeLineCauchyFluxSourceTrajectory_shift_eq
    (p : CMParams) {M T t h s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (U : WholeLineBUCTrajectory T) (hs : s ∈ Set.Icc (0 : ℝ) h) :
    wholeLineCauchyFluxSourceTrajectory p hM hh
        (wholeLineBUCTrajectoryShift ht hh hth U) s =
      wholeLineCauchyFluxSourceTrajectory p hM hT U (t + s) := by
  unfold wholeLineCauchyFluxSourceTrajectory
  rw [wholeLineBUCTrajectoryExtend_shift_eq ht hh hth hT U hs]

theorem wholeLineCauchyReactionSourceTrajectory_shift_eq
    (p : CMParams) {M T t h s : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (U : WholeLineBUCTrajectory T) (hs : s ∈ Set.Icc (0 : ℝ) h) :
    wholeLineCauchyReactionSourceTrajectory p hM hh
        (wholeLineBUCTrajectoryShift ht hh hth U) s =
      wholeLineCauchyReactionSourceTrajectory p hM hT U (t + s) := by
  unfold wholeLineCauchyReactionSourceTrajectory
  rw [wholeLineBUCTrajectoryExtend_shift_eq ht hh hth hT U hs]

/-- The gradient Duhamel history of a shifted trajectory is the translated
recent gradient history of the original trajectory. -/
theorem wholeLineCauchyGradientDuhamelBUC_shift_eq
    (p : CMParams) {M T t h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r ∈ Set.Icc (0 : ℝ) h) :
    wholeLineCauchyGradientDuhamelBUC p hM hh
        (wholeLineBUCTrajectoryShift ht hh hth U) r =
      ∫ s in t..(t + r),
        wholeLineCauchyGradientBUCIntegrand p hM hT U (t + r) s := by
  unfold wholeLineCauchyGradientDuhamelBUC
  have htranslate :
      (∫ s in (0 : ℝ)..r,
          wholeLineCauchyGradientBUCIntegrand p hM hT U (t + r) (t + s)) =
        ∫ s in t..(t + r),
          wholeLineCauchyGradientBUCIntegrand p hM hT U (t + r) s := by
    simpa using intervalIntegral.integral_comp_add_left
      (a := (0 : ℝ)) (b := r)
      (wholeLineCauchyGradientBUCIntegrand p hM hT U (t + r)) t
  rw [← htranslate]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hr.1] at hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) h :=
    ⟨hs.1, hs.2.trans hr.2⟩
  unfold wholeLineCauchyGradientBUCIntegrand
  rw [wholeLineCauchyFluxSourceTrajectory_shift_eq
    p hM hT ht hh hth U hsIcc]
  rw [show r - s = (t + r) - (t + s) by ring]

/-- The value Duhamel history of a shifted trajectory is the translated
recent value history of the original trajectory. -/
theorem wholeLineCauchyValueDuhamelBUC_shift_eq
    (p : CMParams) {M T t h r : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ T)
    (U : WholeLineBUCTrajectory T) (hr : r ∈ Set.Icc (0 : ℝ) h) :
    wholeLineCauchyValueDuhamelBUC p hM hh
        (wholeLineBUCTrajectoryShift ht hh hth U) r =
      ∫ s in t..(t + r),
        wholeLineCauchyValueBUCIntegrand p hM hT U (t + r) s := by
  unfold wholeLineCauchyValueDuhamelBUC
  have htranslate :
      (∫ s in (0 : ℝ)..r,
          wholeLineCauchyValueBUCIntegrand p hM hT U (t + r) (t + s)) =
        ∫ s in t..(t + r),
          wholeLineCauchyValueBUCIntegrand p hM hT U (t + r) s := by
    simpa using intervalIntegral.integral_comp_add_left
      (a := (0 : ℝ)) (b := r)
      (wholeLineCauchyValueBUCIntegrand p hM hT U (t + r)) t
  rw [← htranslate]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hr.1] at hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) h :=
    ⟨hs.1, hs.2.trans hr.2⟩
  unfold wholeLineCauchyValueBUCIntegrand
  rw [wholeLineCauchyReactionSourceTrajectory_shift_eq
    p hM hT ht hh hth U hsIcc]
  rw [show r - s = (t + r) - (t + s) by ring]

/-- A positive-time subwindow of a physical canonical fixed point is exactly
the canonical fixed point restarted from its initial slice. -/
theorem wholeLineCauchyBUCMildFixedPoint_shift_eq
    (p : CMParams) {M T t h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmallT : wholeLineCauchyBUCMildRate p M T < 1)
    (ht : 0 < t) (hh : 0 < h) (hth : t + h ≤ T)
    (hsmallh : wholeLineCauchyBUCMildRate p M h < 1)
    (hstrip : ∀ z : Set.Icc (0 : ℝ) T, ∀ x,
      (wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT z).1 x ∈
        Set.Icc (0 : ℝ) M) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT
    let zt : Set.Icc (0 : ℝ) T :=
      ⟨t, ht.le, (le_add_of_nonneg_right hh.le).trans hth⟩
    wholeLineBUCTrajectoryShift ht.le hh.le hth U =
      wholeLineCauchyBUCMildFixedPoint p hM hh.le (U zt) hsmallh := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT
  let zt : Set.Icc (0 : ℝ) T :=
    ⟨t, ht.le, (le_add_of_nonneg_right hh.le).trans hth⟩
  let V : WholeLineBUCTrajectory h :=
    wholeLineBUCTrajectoryShift ht.le hh.le hth U
  have hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hh.le (U zt)) V := by
    apply ContinuousMap.ext
    intro z
    let r : ℝ := z.1
    have hr : r ∈ Set.Icc (0 : ℝ) h := z.2
    by_cases hr0 : r = 0
    · subst r
      have hz0 : z = ⟨0, ⟨le_rfl, hh.le⟩⟩ := Subtype.ext hr0
      subst z
      simp [V, zt, wholeLineCauchyBUCMildMap,
        wholeLineCauchyGradientDuhamelBUC,
        wholeLineCauchyValueDuhamelBUC,
        wholeLineCauchyHeatBUCTotal]
    have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
    let ztr : Set.Icc (0 : ℝ) T :=
      ⟨t + r, add_nonneg ht.le hr.1, by linarith [hr.2, hth]⟩
    have hUt : U zt =
        wholeLineCauchyHeatBUCTotal t u₀ +
          (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U t +
          wholeLineCauchyValueDuhamelBUC p hM hT U t := by
      have hfix := congrArg (fun W : WholeLineBUCTrajectory T => W zt)
        (wholeLineCauchyBUCMildFixedPoint_eq_mildMap
          p hM hT u₀ hsmallT)
      simpa [U, zt, wholeLineCauchyBUCMildMap] using hfix
    have hUtr : U ztr =
        wholeLineCauchyHeatBUCTotal (t + r) u₀ +
          (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U (t + r) +
          wholeLineCauchyValueDuhamelBUC p hM hT U (t + r) := by
      have hfix := congrArg (fun W : WholeLineBUCTrajectory T => W ztr)
        (wholeLineCauchyBUCMildFixedPoint_eq_mildMap
          p hM hT u₀ hsmallT)
      simpa [U, ztr, wholeLineCauchyBUCMildMap] using hfix
    have hGrestart := wholeLineCauchyGradientDuhamelBUC_restart_fixedPoint
      p hM hT u₀ hsmallT ht (by linarith [hh, hth]) hrpos
      (theta := (1 / 2 : ℝ)) (eta := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hstrip
    have hRrestart := wholeLineCauchyValueDuhamelBUC_restart
      p hM hT U ht hrpos
    have hGshift := wholeLineCauchyGradientDuhamelBUC_shift_eq
      p hM hT ht.le hh.le hth U hr
    have hRshift := wholeLineCauchyValueDuhamelBUC_shift_eq
      p hM hT ht.le hh.le hth U hr
    have heat_add (a b : WholeLineBUC) :
        wholeLineCauchyHeatBUCTotal r (a + b) =
          wholeLineCauchyHeatBUCTotal r a +
            wholeLineCauchyHeatBUCTotal r b := by
      simp only [wholeLineCauchyHeatBUCTotal, dif_pos hrpos]
      change wholeLineCauchyHeatBUCCLM r hrpos (a + b) =
        wholeLineCauchyHeatBUCCLM r hrpos a +
          wholeLineCauchyHeatBUCCLM r hrpos b
      exact map_add (wholeLineCauchyHeatBUCCLM r hrpos) a b
    have heat_smul (c : ℝ) (a : WholeLineBUC) :
        wholeLineCauchyHeatBUCTotal r (c • a) =
          c • wholeLineCauchyHeatBUCTotal r a := by
      simp only [wholeLineCauchyHeatBUCTotal, dif_pos hrpos]
      change wholeLineCauchyHeatBUCCLM r hrpos (c • a) =
        c • wholeLineCauchyHeatBUCCLM r hrpos a
      exact map_smul (wholeLineCauchyHeatBUCCLM r hrpos) c a
    have hheatUt :
        wholeLineCauchyHeatBUCTotal r (U zt) =
          wholeLineCauchyHeatBUCTotal (t + r) u₀ +
            (-p.χ) • wholeLineCauchyHeatBUCTotal r
              (wholeLineCauchyGradientDuhamelBUC p hM hT U t) +
            wholeLineCauchyHeatBUCTotal r
              (wholeLineCauchyValueDuhamelBUC p hM hT U t) := by
      rw [hUt]
      rw [heat_add, heat_add, heat_smul]
      rw [wholeLineCauchyHeatBUCTotal_add_time hrpos ht]
      simpa [add_comm]
    change wholeLineCauchyBUCMildMap p hM hh.le (U zt) V z = V z
    change
      wholeLineCauchyHeatBUCTotal r (U zt) +
        (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hh.le V r +
        wholeLineCauchyValueDuhamelBUC p hM hh.le V r = U ztr
    symm
    rw [hUtr, hGrestart, hRrestart, hGshift, hRshift, hheatUt]
    simp only [U]
    module
  have hcontract := wholeLineCauchyBUCMildMap_contracting
    p hM hh.le (U zt) hsmallh
  have huniq := hcontract.fixedPoint_unique hfixed
  simpa [U, V, zt, wholeLineCauchyBUCMildFixedPoint] using huniq

/-- Restricting a canonical fixed point to a shorter initial horizon gives
the canonical fixed point constructed directly on that horizon. -/
theorem wholeLineCauchyBUCMildFixedPoint_restrict_eq
    (p : CMParams) {M T h : ℝ}
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (u₀ : WholeLineBUC)
    (hsmallT : wholeLineCauchyBUCMildRate p M T < 1)
    (hh : 0 ≤ h) (hhT : h ≤ T)
    (hsmallh : wholeLineCauchyBUCMildRate p M h < 1) :
    let U := wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT
    wholeLineBUCTrajectoryShift le_rfl hh (by simpa using hhT) U =
      wholeLineCauchyBUCMildFixedPoint p hM hh u₀ hsmallh := by
  dsimp only
  let U : WholeLineBUCTrajectory T :=
    wholeLineCauchyBUCMildFixedPoint p hM hT u₀ hsmallT
  let V : WholeLineBUCTrajectory h :=
    wholeLineBUCTrajectoryShift le_rfl hh (by simpa using hhT) U
  have hzeroT : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hU0 : U ⟨0, hzeroT⟩ = u₀ := by
    simpa [U] using wholeLineCauchyBUCMildFixedPoint_initial
      p hM hT u₀ hsmallT hzeroT
  have hfixed : IsFixedPt (wholeLineCauchyBUCMildMap p hM hh u₀) V := by
    apply ContinuousMap.ext
    intro z
    let r : ℝ := z.1
    have hr : r ∈ Set.Icc (0 : ℝ) h := z.2
    let zr : Set.Icc (0 : ℝ) T :=
      ⟨r, hr.1, hr.2.trans hhT⟩
    have hUr : U zr =
        wholeLineCauchyHeatBUCTotal r u₀ +
          (-p.χ) • wholeLineCauchyGradientDuhamelBUC p hM hT U r +
          wholeLineCauchyValueDuhamelBUC p hM hT U r := by
      have hfix := congrArg (fun W : WholeLineBUCTrajectory T => W zr)
        (wholeLineCauchyBUCMildFixedPoint_eq_mildMap
          p hM hT u₀ hsmallT)
      simpa [U, zr, wholeLineCauchyBUCMildMap] using hfix
    have hGshift := wholeLineCauchyGradientDuhamelBUC_shift_eq
      p hM hT le_rfl hh (by simpa using hhT) U hr
    have hRshift := wholeLineCauchyValueDuhamelBUC_shift_eq
      p hM hT le_rfl hh (by simpa using hhT) U hr
    have hG : wholeLineCauchyGradientDuhamelBUC p hM hh V r =
        wholeLineCauchyGradientDuhamelBUC p hM hT U r := by
      simpa [V, wholeLineCauchyGradientDuhamelBUC] using hGshift
    have hR : wholeLineCauchyValueDuhamelBUC p hM hh V r =
        wholeLineCauchyValueDuhamelBUC p hM hT U r := by
      simpa [V, wholeLineCauchyValueDuhamelBUC] using hRshift
    rw [wholeLineCauchyBUCMildMap_apply, hG, hR, ← hUr]
    simp [V, zr, r, wholeLineBUCTrajectoryShift]
  have hcontract := wholeLineCauchyBUCMildMap_contracting
    p hM hh u₀ hsmallh
  have huniq := hcontract.fixedPoint_unique hfixed
  simpa [U, V, wholeLineCauchyBUCMildFixedPoint] using huniq

section WholeLineCauchyCanonicalRestartAxiomAudit

#print axioms wholeLineBUCTrajectoryShift
#print axioms wholeLineBUCTrajectoryExtend_shift_eq
#print axioms wholeLineCauchyGradientDuhamelBUC_shift_eq
#print axioms wholeLineCauchyValueDuhamelBUC_shift_eq
#print axioms wholeLineCauchyBUCMildFixedPoint_shift_eq
#print axioms wholeLineCauchyBUCMildFixedPoint_restrict_eq

end WholeLineCauchyCanonicalRestartAxiomAudit

end ShenWork.Paper1
