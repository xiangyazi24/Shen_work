import ShenWork.Paper2.IntervalDomainMEllipticResolverAgreement
import ShenWork.Paper2.IntervalDomainMConjugateConePreserved

/-!
# Pointwise B-form restart for faithful general-`m` classical solutions

The spectral restart identity is already available almost everywhere.  Here it
is identified with the general-`m` conjugate mild map on a clamped relative-time
trajectory and upgraded to pointwise equality by spatial continuity.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted intervalConjugateDuhamelMapM
   chemFluxMLifted_uncurry_measurable)

/-- Globally clamped relative-time trajectory of a classical solution. -/
def classicalRestartTrajectoryM
    (a h : ℝ) (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  fun r x => u (a + restartTimeClamp h r) x

theorem classicalRestartTrajectoryM_eq
    {a h r : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Icc (0 : ℝ) h) :
    classicalRestartTrajectoryM a h u r = u (a + r) := by
  funext x
  simp [classicalRestartTrajectoryM, restartTimeClamp_eq_self hr]

theorem classicalRestartTrajectoryM_hasContinuousSlices
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    HasContinuousSlices h (classicalRestartTrajectoryM a h u) := by
  intro r _ _
  have hfield := restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  have hcomp : Continuous (fun x : intervalDomainPoint =>
      restartField a h u r x.1) :=
    hfield.comp (continuous_const.prodMk continuous_subtype_val)
  have heq : (fun x : intervalDomainPoint => restartField a h u r x.1) =
      classicalRestartTrajectoryM a h u r := by
    funext x
    simp [restartField, classicalRestartTrajectoryM, clamp01_eq_self x.2,
      intervalDomainLift]
  rwa [heq] at hcomp

theorem classicalRestartTrajectoryM_hasJointMeasurability
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    HasJointMeasurability (classicalRestartTrajectoryM a h u) := by
  have hfield := (restartField_continuous hsol ha hh hahT
    u (Or.inl rfl)).measurable
  have heq : (fun q : ℝ × ℝ =>
      intervalDomainLift (classicalRestartTrajectoryM a h u q.1) q.2) =
      fun q : ℝ × ℝ =>
        if q.2 ∈ Icc (0 : ℝ) 1 then restartField a h u q.1 q.2 else 0 := by
    funext q
    by_cases hq : q.2 ∈ Icc (0 : ℝ) 1
    · simp [intervalDomainLift, hq, classicalRestartTrajectoryM,
        restartField, clamp01_eq_self hq]
    · simp [intervalDomainLift, hq]
  unfold HasJointMeasurability
  rw [heq]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
    hfield measurable_const

/-- On the physical restart rectangle, the classical general-`m` flux is the
resolver-based flux used by the faithful conjugate mild map. -/
theorem restartFluxM_eq_chemFluxMLifted_restartTrajectoryM
    {p : CM2Params} {T a h r y : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : r ∈ Icc (0 : ℝ) h) (hy : y ∈ Icc (0 : ℝ) 1) :
    restartFluxM p a h u v r y =
      chemFluxMLifted p (classicalRestartTrajectoryM a h u r) y := by
  have ht : a + r ∈ Ioo (0 : ℝ) T := by
    constructor
    · linarith [hr.1]
    · exact lt_of_le_of_lt
        (by simpa [add_comm] using add_le_add_left hr.2 a) hahT
  have hgrad := solution_lift_v_deriv_eq_resolverGrad_IccM hsol ht hy
  have htraj : classicalRestartTrajectoryM a h u r = u (a + r) :=
    classicalRestartTrajectoryM_eq hr
  rcases eq_or_lt_of_le hy.1 with rfl | hy0
  · have hzero := ShenWork.Paper2.resolverGradReal_zero p (u (a + r))
    unfold restartFluxM chemFluxMLifted
    rw [restartField_eq_physical hr (by constructor <;> norm_num),
      restartChemGrad_eq_deriv hsol ha hh hahT hr (by constructor <;> norm_num),
      hgrad, htraj, hzero]
    simp
  · rcases eq_or_lt_of_le hy.2 with rfl | hy1
    · have hzero := ShenWork.Paper2.resolverGradReal_one p (u (a + r))
      unfold restartFluxM chemFluxMLifted
      rw [restartField_eq_physical hr (by constructor <;> norm_num),
        restartChemGrad_eq_deriv hsol ha hh hahT hr (by constructor <;> norm_num),
        hgrad, htraj, hzero]
      simp
    · have hyIoo : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
      have hvalue := solution_v_eq_resolver_pointwiseM hsol ht hyIoo
      unfold restartFluxM chemFluxMLifted
      rw [restartField_eq_physical hr hy, restartField_eq_physical hr hy,
        restartChemGrad_eq_deriv hsol ha hh hahT hr hy, hgrad, htraj]
      simp only [intervalDomainLift, hy, dif_pos]
      rw [hvalue]
      simp [intervalDomainLift, hy]

theorem restartLogisticM_eq_logisticLifted_restartTrajectoryM
    {p : CM2Params} {a h r y : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Icc (0 : ℝ) h) (hy : y ∈ Icc (0 : ℝ) 1) :
    restartLogisticM p a h u r y =
      logisticLifted p (classicalRestartTrajectoryM a h u r) y := by
  rw [restartLogisticM_eq_physical hr hy,
    classicalRestartTrajectoryM_eq hr]
  simp [logisticLifted, logisticLiftedM,
    ShenWork.IntervalDomainExistence.intervalLogisticSource,
    intervalDomainLift, hy]

private theorem intervalConjugateKernelOperator_congr_on_IccM
    {t x : ℝ} {f g : ℝ → ℝ} (hfg : EqOn f g (Icc (0 : ℝ) 1)) :
    intervalConjugateKernelOperator t f x =
      intervalConjugateKernelOperator t g x := by
  unfold intervalConjugateKernelOperator
  congr 1
  apply integral_congr_ae
  filter_upwards
    [(ae_restrict_mem measurableSet_Icc :
      ∀ᵐ y : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), y ∈ Icc (0 : ℝ) 1)]
    with y hy
  rw [hfg hy]

private theorem intervalFullSemigroupOperator_congr_on_IccM
    {t x : ℝ} {f g : ℝ → ℝ} (hfg : EqOn f g (Icc (0 : ℝ) 1)) :
    intervalFullSemigroupOperator t f x = intervalFullSemigroupOperator t g x := by
  unfold intervalFullSemigroupOperator
  apply integral_congr_ae
  filter_upwards
    [(ae_restrict_mem measurableSet_Icc :
      ∀ᵐ y : ℝ ∂volume.restrict (Icc (0 : ℝ) 1), y ∈ Icc (0 : ℝ) 1)]
    with y hy
  rw [hfg hy]

/-- The physical restart candidate is the faithful general-`m` conjugate map
evaluated on the clamped relative-time trajectory. -/
theorem faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMapM
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : r ∈ Icc (0 : ℝ) h) (x : intervalDomainPoint) :
    faithfulRestartDuhamelM p a h u v r x.1 =
      intervalConjugateDuhamelMapM p (u a)
        (classicalRestartTrajectoryM a h u) r x := by
  unfold faithfulRestartDuhamelM restartChemDuhamelM
    restartLogisticDuhamelM intervalConjugateDuhamelMapM
  have hchem :
      (∫ s in (0 : ℝ)..r,
        intervalConjugateKernelOperator (r - s)
          (restartFluxM p a h u v s) x.1) =
      ∫ s in (0 : ℝ)..r,
        intervalConjugateKernelOperator (r - s)
          (chemFluxMLifted p (classicalRestartTrajectoryM a h u s)) x.1 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hr.1] at hs
    apply intervalConjugateKernelOperator_congr_on_IccM
    intro y hy
    exact restartFluxM_eq_chemFluxMLifted_restartTrajectoryM
      hsol ha hh hahT ⟨hs.1, hs.2.trans hr.2⟩ hy
  have hlog :
      (∫ s in (0 : ℝ)..r,
        intervalFullSemigroupOperator (r - s)
          (restartLogisticM p a h u s) x.1) =
      ∫ s in (0 : ℝ)..r,
        intervalFullSemigroupOperator (r - s)
          (logisticLifted p (classicalRestartTrajectoryM a h u s)) x.1 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hr.1] at hs
    apply intervalFullSemigroupOperator_congr_on_IccM
    intro y hy
    exact restartLogisticM_eq_logisticLifted_restartTrajectoryM
      ⟨hs.1, hs.2.trans hr.2⟩ hy
  rw [hchem, hlog]
  ring

private theorem faithfulRestartDuhamelM_continuousOn_IccM
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr0 : 0 < r) (hrh : r ≤ h) :
    ContinuousOn (faithfulRestartDuhamelM p a h u v r) (Icc (0 : ℝ) 1) := by
  let w := classicalRestartTrajectoryM a h u
  obtain ⟨M₀, hM₀, hu₀⟩ := exists_solutionLift_abs_bound hsol
    (t := a) ⟨ha, by linarith [hahT, hh]⟩
  obtain ⟨CQ, hCQ, hq⟩ := exists_restartFluxM_bound hsol ha hh hahT
  obtain ⟨CL, hCL, hell⟩ := exists_restartLogisticM_bound hsol ha hh hahT
  have huaCont : Continuous (u a) :=
    solutionSlice_continuous hsol ⟨ha, by linarith [hahT, hh]⟩
  have hLiftMeas : Measurable (intervalDomainLift (u a)) :=
    ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      huaCont
  have hwMeas : HasJointMeasurability w := by
    simpa [w] using classicalRestartTrajectoryM_hasJointMeasurability
      hsol ha hh hahT
  have hQMeas : Measurable
      (Function.uncurry (fun s y => chemFluxMLifted p (w s) y)) :=
    chemFluxMLifted_uncurry_measurable hwMeas
  have hLMeas : Measurable
      (Function.uncurry (fun s y => logisticLifted p (w s) y)) :=
    ShenWork.Paper2.logisticLifted_uncurry_measurable hwMeas
  have hQBound : ∀ s, 0 < s → s ≤ h → ∀ y,
      |chemFluxMLifted p (w s) y| ≤ CQ := by
    intro s hs0 hsh y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · rw [← restartFluxM_eq_chemFluxMLifted_restartTrajectoryM
          hsol ha hh hahT ⟨hs0.le, hsh⟩ hy]
      exact hq s y
    · simp [chemFluxMLifted, intervalDomainLift, hy,
        Real.zero_rpow p.hm.ne']
      exact hCQ
  have hLBound : ∀ s, 0 < s → s ≤ h → ∀ y,
      |logisticLifted p (w s) y| ≤ CL := by
    intro s hs0 hsh y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · rw [← restartLogisticM_eq_logisticLifted_restartTrajectoryM
          (p := p) (a := a) ⟨hs0.le, hsh⟩ hy]
      exact hell s y
    · simp [logisticLifted, intervalDomainLift, hy]
      exact hCL
  have hQInt : ∀ s, 0 < s → s ≤ h →
      Integrable (chemFluxMLifted p (w s)) (intervalMeasure 1) := by
    intro s hs hsh
    have hsmeas : Measurable (chemFluxMLifted p (w s)) := by
      simpa [Function.uncurry] using
        hQMeas.comp (measurable_const.prodMk measurable_id)
    exact intervalMeasure_integrable_of_abs_bound
      hsmeas.aestronglyMeasurable (hQBound s hs hsh)
  have hLslice : ∀ s, AEStronglyMeasurable
      (logisticLifted p (w s)) (intervalMeasure 1) := by
    intro s
    exact (hLMeas.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hmapCont : Continuous (fun x : intervalDomainPoint =>
      intervalConjugateDuhamelMapM p (u a) w r x) :=
    ShenWork.IntervalDomainMConjugateConePreserved.intervalConjugateDuhamelMapM_hasContinuousSlices_of_ball
      hM₀ hCL hu₀ hLiftMeas hQMeas hLMeas hQInt hLslice hQBound hLBound
      r hr0 hrh
  rw [continuousOn_iff_continuous_restrict]
  let e : Icc (0 : ℝ) 1 → intervalDomainPoint := fun x => ⟨x.1, x.2⟩
  have he : Continuous e := by fun_prop
  have heq : Set.restrict (Icc (0 : ℝ) 1)
      (faithfulRestartDuhamelM p a h u v r) =
      (fun x => intervalConjugateDuhamelMapM p (u a) w r (e x)) := by
    funext x
    exact faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMapM
      hsol ha hh hahT ⟨hr0.le, hrh⟩ (e x)
  rw [heq]
  exact hmapCont.comp he

/-- The a.e. physical restart identity upgrades to pointwise equality on the
closed interval. -/
theorem intervalDomainM_classical_bform_restart_pointwise
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr0 : 0 < r) (hrh : r ≤ h) :
    ∀ x : intervalDomainPoint,
      u (a + r) x =
        intervalConjugateDuhamelMapM p (u a)
          (classicalRestartTrajectoryM a h u) r x := by
  have hae := faithfulRestartDuhamelM_ae_eq_solution
    hsol ha hh hahT hr0 hrh
  rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at hae
  have hcand := faithfulRestartDuhamelM_continuousOn_IccM
    hsol ha hh hahT hr0 hrh
  have ht : a + r ∈ Ioo (0 : ℝ) T := by
    constructor
    · linarith
    · exact lt_of_le_of_lt (by linarith [hrh]) hahT
  have huslice : ContinuousOn (intervalDomainLift (u (a + r)))
      (Icc (0 : ℝ) 1) :=
    (hsol.regularity.2.2.2.2.1 (a + r) ht).1.1.continuousOn
  have heqOn : EqOn (faithfulRestartDuhamelM p a h u v r)
      (intervalDomainLift (u (a + r))) (Icc (0 : ℝ) 1) := by
    refine MeasureTheory.Measure.eqOn_of_ae_eq hae hcand huslice ?_
    rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  intro x
  have hx := heqOn x.2
  have hmap := faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMapM
    hsol ha hh hahT ⟨hr0.le, hrh⟩ x
  rw [hmap] at hx
  simpa [intervalDomainLift, x.2] using hx.symm

#print axioms classicalRestartTrajectoryM_hasJointMeasurability
#print axioms restartFluxM_eq_chemFluxMLifted_restartTrajectoryM
#print axioms faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMapM
#print axioms intervalDomainM_classical_bform_restart_pointwise

end ShenWork.Paper2.IntervalDomainM
