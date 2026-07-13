/-
  Direct target-time derivative of the faithful logistic Duhamel leg.

  The source is replaced outside the physical interval by its constant spatial
  extension and outside the active time horizon by zero.  This representative
  is globally continuous on every spatial slice, agrees with the true source
  wherever the Neumann semigroup integrates, and has the same uniform positive-
  time trace and Holder control as the faithful mild solution.
-/
import ShenWork.Paper2.IntervalFullDuhamelTimeDerivativeHolder
import ShenWork.Paper2.IntervalJointContinuityUniformTrace
import ShenWork.Paper2.IntervalDomainMConjugateMildJointValue
import ShenWork.Paper2.IntervalDomainMConjugateMildInteriorC2
import ShenWork.PDE.IntervalDomainContinuousExtension

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure
    intervalDomainConstExtend constExtend_continuous
    constExtend_eq_lift_on_Icc semigroupOperator_constExtend_eq_lift)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)

/-- Constant spatial extension of the logistic source, cut off outside the
time interval on which the packaged mild solution is defined. -/
def conjugateMildMLogisticConstCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) : ℝ → ℝ → ℝ :=
  fun s y =>
    if 0 < s ∧ s ≤ D.T then
      intervalDomainConstExtend (intervalLogisticSource p (D.u s)) y
    else 0

private theorem constExtend_eq_apply_unitClip
    (f : intervalDomainPoint → ℝ) (y : ℝ) :
    intervalDomainConstExtend f y = f (unitClip y) := by
  unfold intervalDomainConstExtend unitClip
  by_cases h0 : y ≤ 0
  · simp only [dif_pos h0]
    congr 1
    apply Subtype.ext
    simp [min_eq_left (h0.trans zero_le_one), max_eq_left h0]
  · simp only [dif_neg h0]
    by_cases h1 : 1 ≤ y
    · simp only [dif_pos h1]
      congr 1
      apply Subtype.ext
      simp [min_eq_right h1]
    · simp only [dif_neg h1]
      congr 1
      apply Subtype.ext
      simp [min_eq_left (le_of_not_ge h1), max_eq_right (le_of_not_ge h0)]

/-- The actual lifted logistic source is jointly continuous on the faithful
strict-positive-time closed spatial slab. -/
theorem conjugateMildM_logisticLifted_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry (fun t : ℝ => logisticLifted p (D.u t)))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  have hu := conjugateMildM_jointValue_u D hu₀_bound hu₀_meas
  have hpoly : ContinuousOn
      (fun q : ℝ × ℝ =>
        intervalDomainLift (D.u q.1) q.2 *
          (p.a - p.b * intervalDomainLift (D.u q.1) q.2 ^ p.α))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) :=
    hu.mul (continuousOn_const.sub
      (continuousOn_const.mul
        (hu.rpow_const (fun _ _ => Or.inr p.hα.le))))
  refine hpoly.congr ?_
  intro q hq
  have hx := (Set.mem_prod.mp hq).2
  simp [Function.uncurry, logisticLifted, intervalLogisticSource,
    intervalDomainLift, hx]

/-- The cutoff constant-extension source is jointly measurable on all of
space-time. -/
theorem conjugateMildMLogisticConstCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    Measurable (Function.uncurry (conjugateMildMLogisticConstCutoff D)) := by
  have hsource : Measurable
      (fun q : ℝ × ℝ => logisticLifted p (D.u q.1) q.2) :=
    logisticLifted_joint_measurable_of_hasJoint D.hmeas
  have hclipMap : Continuous
      (fun q : ℝ × ℝ => (q.1, (unitClip q.2).1)) :=
    continuous_fst.prodMk
      (continuous_subtype_val.comp (unitClip_continuous.comp continuous_snd))
  have hcomp : Measurable
      (fun q : ℝ × ℝ => logisticLifted p (D.u q.1) (unitClip q.2).1) :=
    hsource.comp hclipMap.measurable
  have htime : MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ D.T} :=
    (isOpen_Ioi.preimage continuous_fst).measurableSet.inter
      (isClosed_Iic.preimage continuous_fst).measurableSet
  have hite : Measurable
      (fun q : ℝ × ℝ =>
        if 0 < q.1 ∧ q.1 ≤ D.T then
          logisticLifted p (D.u q.1) (unitClip q.2).1 else 0) :=
    Measurable.ite htime hcomp measurable_const
  convert hite using 1
  funext q
  by_cases hwin : 0 < q.1 ∧ q.1 ≤ D.T
  · change
      (if 0 < q.1 ∧ q.1 ≤ D.T then
        intervalDomainConstExtend (intervalLogisticSource p (D.u q.1)) q.2
       else 0) =
      (if 0 < q.1 ∧ q.1 ≤ D.T then
        logisticLifted p (D.u q.1) (unitClip q.2).1 else 0)
    rw [if_pos hwin, if_pos hwin, constExtend_eq_apply_unitClip]
    simp [logisticLifted, intervalDomainLift, (unitClip q.2).2]
  · change
      (if 0 < q.1 ∧ q.1 ≤ D.T then
        intervalDomainConstExtend (intervalLogisticSource p (D.u q.1)) q.2
       else 0) =
      (if 0 < q.1 ∧ q.1 ≤ D.T then
        logisticLifted p (D.u q.1) (unitClip q.2).1 else 0)
    simp [hwin]

/-- Every spatial slice of the cutoff representative is globally continuous. -/
theorem conjugateMildMLogisticConstCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s, Continuous (conjugateMildMLogisticConstCutoff D s) := by
  intro s
  by_cases hwin : 0 < s ∧ s ≤ D.T
  · change Continuous (fun y =>
      if 0 < s ∧ s ≤ D.T then
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) y else 0)
    simp only [hwin, if_true]
    apply constExtend_continuous
    have hu : Continuous (D.u s) := D.hcont s hwin.1 hwin.2
    unfold intervalLogisticSource
    exact hu.mul (continuous_const.sub
      (continuous_const.mul (hu.rpow_const (fun _ => Or.inr p.hα.le))))
  · change Continuous (fun y =>
      if 0 < s ∧ s ≤ D.T then
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) y else 0)
    simpa only [hwin, if_false] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

/-- Global uniform bound for the cutoff representative. -/
theorem conjugateMildMLogisticConstCutoff_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s y, |conjugateMildMLogisticConstCutoff D s y| ≤
      D.M * (p.a + p.b * D.M ^ p.α) := by
  intro s y
  by_cases hwin : 0 < s ∧ s ≤ D.T
  · change
      |if 0 < s ∧ s ≤ D.T then
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) y else 0| ≤ _
    rw [if_pos hwin, constExtend_eq_apply_unitClip]
    have hbound := ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
      p D.hM (fun z => D.hbound s hwin.1 hwin.2 z) (unitClip y).1
    simpa [logisticLifted, intervalDomainLift, (unitClip y).2] using hbound
  · change
      |if 0 < s ∧ s ≤ D.T then
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) y else 0| ≤ _
    rw [if_neg hwin, abs_zero]
    exact logisticCutoffSource_boundConst_nonneg (p := p) D.hM

/-- Integrability of every cutoff representative slice against the physical
interval measure. -/
theorem conjugateMildMLogisticConstCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s, Integrable (conjugateMildMLogisticConstCutoff D s)
      (intervalMeasure 1) := by
  intro s
  simpa [intervalMeasure, ShenWork.IntervalDomain.intervalSet] using
    (conjugateMildMLogisticConstCutoff_continuous D s).continuousOn.integrableOn_Icc

/-- At an interior target time, the cutoff representative converges uniformly
in the physical spatial variable to its target slice. -/
theorem conjugateMildMLogisticConstCutoff_uniformTrace
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t : ℝ} (ht : 0 < t) (htT : t < D.T) :
    TendstoUniformlyOn (conjugateMildMLogisticConstCutoff D)
      (conjugateMildMLogisticConstCutoff D t) (𝓝 t)
      (Set.Icc (0 : ℝ) 1) := by
  have hactual := jointContinuousOn_Ioo_prod_Icc_tendstoUniformlyOn
    (conjugateMildM_logisticLifted_jointContinuousOn D hu₀_bound hu₀_meas)
    ⟨ht, htT⟩
  have hevent : ∀ᶠ s in 𝓝 t,
      Set.EqOn (fun x => logisticLifted p (D.u s) x)
        (conjugateMildMLogisticConstCutoff D s) (Set.Icc (0 : ℝ) 1) := by
    filter_upwards [Ioo_mem_nhds ht htT] with s hs x hx
    rw [conjugateMildMLogisticConstCutoff, if_pos ⟨hs.1, hs.2.le⟩,
      constExtend_eq_lift_on_Icc hx]
    rfl
  have hleft := hactual.congr hevent
  apply hleft.congr_right
  intro x hx
  rw [conjugateMildMLogisticConstCutoff, if_pos ⟨ht, htT.le⟩,
    constExtend_eq_lift_on_Icc hx]
  rfl

/-- Direct target-time derivative of the actual logistic Duhamel leg. -/
theorem conjugateMildM_logisticDuhamel_hasDerivAt_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t < D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s)
          (logisticLifted p (D.u s)) x)
      ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x) +
        logisticLifted p (D.u t) x) t := by
  let H : ℝ → ℝ → ℝ := conjugateMildMLogisticConstCutoff D
  let CQ : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact logisticCutoffSource_boundConst_nonneg (p := p) D.hM
  obtain ⟨HQ, hHQ, hholder⟩ :=
    conjugateMildM_logisticLifted_positiveTime_holder_uniform
      D hu₀_bound hu₀_meas (show 0 < t / 2 by linarith)
  have hmain := intervalFullDuhamel_hasDerivAt_time_of_uniform_trace_late_holder
    ht (show 0 < (1 : ℝ) / 4 by norm_num)
      (show (1 : ℝ) / 4 < 1 by norm_num) hCQ hHQ
      (show Measurable (Function.uncurry H) by
        simpa [H] using conjugateMildMLogisticConstCutoff_measurable D)
      (show ∀ s, Continuous (H s) by
        simpa [H] using conjugateMildMLogisticConstCutoff_continuous D)
      (show ∀ s, Integrable (H s) (intervalMeasure 1) by
        simpa [H] using conjugateMildMLogisticConstCutoff_integrable D)
      (show ∀ s y, |H s y| ≤ CQ by
        simpa [H, CQ] using conjugateMildMLogisticConstCutoff_bound D)
      (show TendstoUniformlyOn H (H t) (𝓝 t) (Set.Icc (0 : ℝ) 1) by
        simpa [H] using conjugateMildMLogisticConstCutoff_uniformTrace
          D hu₀_bound hu₀_meas ht htT)
      (fun s hts hst a ha b hb => by
        have hsT : s ≤ D.T := (hst.trans htT).le
        have hae : H s a = logisticLifted p (D.u s) a := by
          dsimp [H, conjugateMildMLogisticConstCutoff]
          rw [if_pos ⟨by linarith [hts, ht], hsT⟩,
            constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self ha)]
          rfl
        have hbe : H s b = logisticLifted p (D.u s) b := by
          dsimp [H, conjugateMildMLogisticConstCutoff]
          rw [if_pos ⟨by linarith [hts, ht], hsT⟩,
            constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hb)]
          rfl
        rw [hae, hbe]
        exact hholder s hts.le hsT a ha b hb)
      hx
  have hvalue_eq : ∀ tau, 0 < tau → tau ≤ D.T →
      (∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s) (H s) x) =
      ∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s)
          (logisticLifted p (D.u s)) x := by
    intro tau htau htauT
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le htau.le]
    filter_upwards with s hs
    have hHs : H s =
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) := by
      funext y
      dsimp [H, conjugateMildMLogisticConstCutoff]
      rw [if_pos ⟨hs.1, hs.2.trans htauT⟩]
    rw [hHs]
    exact semigroupOperator_constExtend_eq_lift
  have hevent :
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s) (H s) x) =ᶠ[𝓝 t]
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s)
          (logisticLifted p (D.u s)) x) := by
    filter_upwards [Ioo_mem_nhds ht htT] with tau htau
    exact hvalue_eq tau htau.1 htau.2.le
  have hderiv_eq :
      (∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (H s) z) y) x) =
      ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z) y) x := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le ht.le]
    filter_upwards with s hs
    have hspace :
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (H s) z) =
        fun z : ℝ => intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) z := by
      funext z
      have hHs : H s =
          intervalDomainConstExtend (intervalLogisticSource p (D.u s)) := by
        funext y
        dsimp [H, conjugateMildMLogisticConstCutoff]
        rw [if_pos ⟨hs.1, hs.2.trans htT.le⟩]
      rw [hHs]
      exact semigroupOperator_constExtend_eq_lift
    rw [hspace]
  have htrace_eq : H t x = logisticLifted p (D.u t) x := by
    dsimp [H, conjugateMildMLogisticConstCutoff]
    rw [if_pos ⟨ht, htT.le⟩,
      constExtend_eq_lift_on_Icc hx]
    rfl
  rw [hderiv_eq, htrace_eq] at hmain
  exact hmain.congr_of_eventuallyEq hevent.symm

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_logisticLifted_jointContinuousOn
#print axioms ShenWork.Paper2.conjugateMildMLogisticConstCutoff_uniformTrace
#print axioms ShenWork.Paper2.conjugateMildM_logisticDuhamel_hasDerivAt_time
