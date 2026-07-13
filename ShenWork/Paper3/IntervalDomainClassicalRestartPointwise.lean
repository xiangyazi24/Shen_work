/- Pointwise B-form restart for arbitrary positive classical interval orbits. -/
import ShenWork.Paper2.IntervalDomainMPhysicalRestart
import ShenWork.Paper2.IntervalConjugateConePreserved
import ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer
import ShenWork.Paper2.IntervalDomainL2UEnergyCombine
import ShenWork.Paper3.IntervalDomainModelLinearizationAudit

namespace ShenWork.Paper3

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain
open ShenWork.Paper2

noncomputable section

local instance : TopologicalSpace intervalDomain.Point :=
  inferInstanceAs (TopologicalSpace intervalDomainPoint)

open ShenWork.IntervalGradientDuhamelMap
  (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateDuhamelMap intervalConjugateKernelOperator)
open ShenWork.IntervalMildPicard
  (HasContinuousSlices HasJointMeasurability)
open ShenWork.Paper2.IntervalDomainM

/-- The globally clamped relative-time trajectory attached to a positive
classical restart window. -/
def intervalDomainRestartTrajectory
    (a h : ℝ) (u : ℝ → intervalDomainPoint → ℝ) :
    ℝ → intervalDomainPoint → ℝ :=
  fun r x ↦ u (a + restartTimeClamp h r) x

theorem intervalDomainRestartTrajectory_eq
    {a h r : ℝ} {u : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) h) :
    intervalDomainRestartTrajectory a h u r = u (a + r) := by
  funext x
  simp [intervalDomainRestartTrajectory, restartTimeClamp_eq_self hr]

theorem intervalDomainRestartTrajectory_hasContinuousSlices
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    HasContinuousSlices h (intervalDomainRestartTrajectory a h u) := by
  intro r hr _hrh
  have hfield := restartField_continuous hsol ha hh hahT u (Or.inl rfl)
  have hcomp : Continuous (fun x : intervalDomainPoint ↦
      restartField a h u r x.1) :=
    hfield.comp (continuous_const.prodMk continuous_subtype_val)
  have heq : (fun x : intervalDomainPoint ↦ restartField a h u r x.1) =
      intervalDomainRestartTrajectory a h u r := by
    funext x
    simp [restartField, intervalDomainRestartTrajectory, clamp01_eq_self x.2,
      intervalDomainLift]
  rwa [heq] at hcomp

theorem intervalDomainRestartTrajectory_hasJointMeasurability
    {p : CM2Params} {T a h : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T) :
    HasJointMeasurability (intervalDomainRestartTrajectory a h u) := by
  have hfield := (restartField_continuous hsol ha hh hahT u (Or.inl rfl)).measurable
  have heq : (fun q : ℝ × ℝ ↦
      intervalDomainLift (intervalDomainRestartTrajectory a h u q.1) q.2) =
      fun q : ℝ × ℝ ↦
        if q.2 ∈ Set.Icc (0 : ℝ) 1 then restartField a h u q.1 q.2 else 0 := by
    funext q
    by_cases hq : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, hq, intervalDomainRestartTrajectory,
        restartField, clamp01_eq_self hq]
    · simp [intervalDomainLift, hq]
  unfold HasJointMeasurability
  rw [heq]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
    hfield measurable_const

/-- On the physical restart rectangle, the faithful `m=1` flux is exactly the
resolver-based flux used by the weak B-form map. -/
theorem restartFluxM_eq_chemFluxLifted_restartTrajectory
    {p : CM2Params} {T a h r y : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hahT : a + h < T)
    (hr : r ∈ Set.Icc (0 : ℝ) h) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    restartFluxM p a h u v r y =
      chemFluxLifted p (intervalDomainRestartTrajectory a h u r) y := by
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  have ht : a + r ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith [hr.1]
    · exact lt_of_le_of_lt
        (by simpa [add_comm] using add_le_add_left hr.2 a) hahT
  have hgrad := solution_lift_v_deriv_eq_resolverGrad_Icc hsol ht hy
  have hvalue :=
    ShenWork.Paper2.IntervalChiNegH1PhysicalResolverSupProducer.solution_v_eq_resolver_pointwise_Icc
      hsol ht hy
  have htraj : intervalDomainRestartTrajectory a h u r = u (a + r) :=
    intervalDomainRestartTrajectory_eq hr
  unfold restartFluxM chemFluxLifted
  rw [restartField_eq_physical hr hy, restartField_eq_physical hr hy,
    restartChemGrad_eq_deriv hsolM ha hh hahT hr hy, hm, Real.rpow_one,
    hgrad, htraj]
  simp only [intervalDomainLift, hy, dif_pos]
  rw [hvalue]
  simp [intervalDomainLift, hy]

/-- The clamped logistic restart source agrees with the standard weak-map
source on the same physical rectangle. -/
theorem restartLogisticM_eq_logisticLifted_restartTrajectory
    {p : CM2Params} {a h r y : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) h) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    restartLogisticM p a h u r y =
      logisticLifted p (intervalDomainRestartTrajectory a h u r) y := by
  rw [restartLogisticM_eq_physical hr hy,
    intervalDomainRestartTrajectory_eq hr]
  simp [logisticLifted, logisticLiftedM,
    ShenWork.IntervalDomainExistence.intervalLogisticSource,
    intervalDomainLift, hy]

private theorem intervalConjugateKernelOperator_congr_on_Icc
    {t x : ℝ} {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g (Set.Icc (0 : ℝ) 1)) :
    intervalConjugateKernelOperator t f x =
      intervalConjugateKernelOperator t g x := by
  unfold intervalConjugateKernelOperator
  congr 1
  apply integral_congr_ae
  filter_upwards
    [(ae_restrict_mem measurableSet_Icc :
      ∀ᵐ y : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        y ∈ Set.Icc (0 : ℝ) 1)] with y hy
  rw [hfg hy]

private theorem intervalFullSemigroupOperator_congr_on_Icc
    {t x : ℝ} {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g (Set.Icc (0 : ℝ) 1)) :
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t f x =
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator t g x := by
  unfold ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator
  apply integral_congr_ae
  filter_upwards
    [(ae_restrict_mem measurableSet_Icc :
      ∀ᵐ y : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        y ∈ Set.Icc (0 : ℝ) 1)] with y hy
  rw [hfg hy]

/-- The physical faithful restart candidate is the standard conjugate weak
map evaluated on the clamped relative trajectory. -/
theorem faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMap
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hahT : a + h < T) (hr : r ∈ Set.Icc (0 : ℝ) h)
    (x : intervalDomainPoint) :
    faithfulRestartDuhamelM p a h u v r x.1 =
      intervalConjugateDuhamelMap p (u a)
        (intervalDomainRestartTrajectory a h u) r x := by
  unfold faithfulRestartDuhamelM restartChemDuhamelM
    restartLogisticDuhamelM intervalConjugateDuhamelMap
  have hchem :
      (∫ s in (0 : ℝ)..r,
        intervalConjugateKernelOperator (r - s)
          (restartFluxM p a h u v s) x.1) =
      ∫ s in (0 : ℝ)..r,
        intervalConjugateKernelOperator (r - s)
          (chemFluxLifted p (intervalDomainRestartTrajectory a h u s)) x.1 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hr.1] at hs
    apply intervalConjugateKernelOperator_congr_on_Icc
    intro y hy
    exact restartFluxM_eq_chemFluxLifted_restartTrajectory
      hsol hm ha hh hahT ⟨hs.1, hs.2.trans hr.2⟩ hy
  have hlog :
      (∫ s in (0 : ℝ)..r,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (r - s)
          (restartLogisticM p a h u s) x.1) =
      ∫ s in (0 : ℝ)..r,
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator (r - s)
          (logisticLifted p (intervalDomainRestartTrajectory a h u s)) x.1 := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hr.1] at hs
    apply intervalFullSemigroupOperator_congr_on_Icc
    intro y hy
    exact restartLogisticM_eq_logisticLifted_restartTrajectory
      ⟨hs.1, hs.2.trans hr.2⟩ hy
  rw [hchem, hlog]
  ring

private theorem faithfulRestartDuhamelM_continuousOn_Icc
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hahT : a + h < T) (hr0 : 0 < r) (hrh : r ≤ h) :
    ContinuousOn (faithfulRestartDuhamelM p a h u v r)
      (Set.Icc (0 : ℝ) 1) := by
  let w := intervalDomainRestartTrajectory a h u
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  obtain ⟨M₀, hM₀, hu₀⟩ := exists_solutionLift_abs_bound hsolM
    (t := a) ⟨ha, by linarith [hahT, hh]⟩
  obtain ⟨CQ, hCQ, hq⟩ := exists_restartFluxM_bound hsolM ha hh hahT
  obtain ⟨CL, hCL, hell⟩ := exists_restartLogisticM_bound hsolM ha hh hahT
  have huaCont : Continuous (u a) := solutionSlice_continuous hsolM
    ⟨ha, by linarith [hahT, hh]⟩
  have hLiftMeas : Measurable (intervalDomainLift (u a)) :=
    ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      huaCont
  have hwCont : HasContinuousSlices h w := by
    simpa [w] using intervalDomainRestartTrajectory_hasContinuousSlices
      hsolM ha hh hahT
  have hwMeas : HasJointMeasurability w := by
    simpa [w] using intervalDomainRestartTrajectory_hasJointMeasurability
      hsolM ha hh hahT
  have hQMeas : Measurable
      (Function.uncurry (fun s y ↦ chemFluxLifted p (w s) y)) :=
    ShenWork.Paper2.chemFluxLifted_uncurry_measurable hwMeas
  have hLMeas : Measurable
      (Function.uncurry (fun s y ↦ logisticLifted p (w s) y)) :=
    ShenWork.Paper2.logisticLifted_uncurry_measurable hwMeas
  have hQBound : ∀ s, 0 < s → s ≤ h → ∀ y,
      |chemFluxLifted p (w s) y| ≤ CQ := by
    intro s hs0 hsh y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · rw [← restartFluxM_eq_chemFluxLifted_restartTrajectory
          hsol hm ha hh hahT ⟨hs0.le, hsh⟩ hy]
      exact hq s y
    · simp [chemFluxLifted, intervalDomainLift, hy]
      exact hCQ
  have hLBound : ∀ s, 0 < s → s ≤ h → ∀ y,
      |logisticLifted p (w s) y| ≤ CL := by
    intro s hs0 hsh y
    by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
    · rw [← restartLogisticM_eq_logisticLifted_restartTrajectory
          (p := p) (a := a) ⟨hs0.le, hsh⟩ hy]
      exact hell s y
    · simp [logisticLifted, intervalDomainLift, hy]
      exact hCL
  have hQInt : ∀ s, 0 < s → s ≤ h →
      Integrable (chemFluxLifted p (w s)) (intervalMeasure 1) := by
    intro s hs hsh
    have hsmeas : Measurable (chemFluxLifted p (w s)) := by
      simpa [Function.uncurry] using
        hQMeas.comp
          ((measurable_const.prodMk measurable_id) :
            Measurable (fun y : ℝ ↦ (s, y)))
    exact intervalMeasure_integrable_of_abs_bound
      hsmeas.aestronglyMeasurable (hQBound s hs hsh)
  have hLslice : ∀ s, AEStronglyMeasurable
      (logisticLifted p (w s)) (intervalMeasure 1) := by
    intro s
    exact (hLMeas.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hmapCont : Continuous (fun x : intervalDomainPoint ↦
      intervalConjugateDuhamelMap p (u a) w r x) :=
    ShenWork.IntervalConjugateConePreserved.intervalConjugateDuhamelMap_hasContinuousSlices_of_ball
      hM₀ hCQ hCL hu₀ hLiftMeas hQMeas hLMeas hQInt hLslice hQBound hLBound
      r hr0 hrh
  rw [continuousOn_iff_continuous_restrict]
  let e : Set.Icc (0 : ℝ) 1 → intervalDomainPoint := fun x ↦ ⟨x.1, x.2⟩
  have he : Continuous e := by fun_prop
  have heq : Set.restrict (Set.Icc (0 : ℝ) 1)
      (faithfulRestartDuhamelM p a h u v r) =
      (fun x ↦ intervalConjugateDuhamelMap p (u a) w r (e x)) := by
    funext x
    exact faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMap
      hsol hm ha hh hahT ⟨hr0.le, hrh⟩ (e x)
  rw [heq]
  exact hmapCont.comp he

/-- The existing a.e. physical restart identity upgrades to equality at every
point of the closed interval.  No zero-time regularity is used. -/
theorem intervalDomain_classical_bform_restart_pointwise
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomain p T u v)
    (hm : p.m = 1) (ha : 0 < a) (hh : 0 ≤ h)
    (hahT : a + h < T) (hr0 : 0 < r) (hrh : r ≤ h) :
    ∀ x : intervalDomainPoint,
      u (a + r) x =
        intervalConjugateDuhamelMap p (u a)
          (intervalDomainRestartTrajectory a h u) r x := by
  have hsolM := isPaper2ClassicalSolution_intervalDomainM_of_m_eq_one p hm hsol
  have hae := faithfulRestartDuhamelM_ae_eq_solution
    hsolM ha hh hahT hr0 hrh
  rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at hae
  have hcand := faithfulRestartDuhamelM_continuousOn_Icc
    hsol hm ha hh hahT hr0 hrh
  have ht : a + r ∈ Set.Ioo (0 : ℝ) T := by
    constructor
    · linarith
    · exact lt_of_le_of_lt (by linarith [hrh]) hahT
  have huslice : ContinuousOn (intervalDomainLift (u (a + r)))
      (Set.Icc (0 : ℝ) 1) :=
    ((hsol.regularity.2.2.2.2.1 (a + r) ht).1.1).continuousOn
  have heqOn : Set.EqOn (faithfulRestartDuhamelM p a h u v r)
      (intervalDomainLift (u (a + r))) (Set.Icc (0 : ℝ) 1) := by
    refine MeasureTheory.Measure.eqOn_of_ae_eq hae hcand huslice ?_
    rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  intro x
  have hx := heqOn x.2
  have hmap := faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMap
    hsol hm ha hh hahT ⟨hr0.le, hrh⟩ x
  rw [hmap] at hx
  simpa [intervalDomainLift, x.2] using hx.symm

#print axioms intervalDomainRestartTrajectory_hasJointMeasurability
#print axioms restartFluxM_eq_chemFluxLifted_restartTrajectory
#print axioms faithfulRestartDuhamelM_eq_intervalConjugateDuhamelMap
#print axioms intervalDomain_classical_bform_restart_pointwise

end

end ShenWork.Paper3
