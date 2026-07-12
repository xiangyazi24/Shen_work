import ShenWork.Paper2.IntervalDomainMRestartSources
import ShenWork.Paper2.IntervalChiNegHmdC
import ShenWork.Paper2.IntervalConjugateSemigroupComposition
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalGradientCoeffDuhamel
import ShenWork.PDE.IntervalSpectralSubtypeAdapter
import ShenWork.PDE.CosineParsevalBridge

/-!
# Physical Duhamel restart for the faithful general-m interval equation

The coefficient restart from `IntervalDomainMClassicalRestart` is reconstructed
as an actual divergence-form heat-semigroup identity.  The semigroup convention
at zero has a null diagonal discontinuity, so the natural conclusion is first an
almost-everywhere identity; this is exactly what the subsequent sup-bound
argument needs.
-/

open MeasureTheory Set Filter Topology
open scoped Topology Interval
open ShenWork.IntervalDomain

noncomputable section

namespace ShenWork.Paper2.IntervalDomainM

open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateCosineSeries
  (intervalSineInner)

/-- The faithful chemotaxis Duhamel leg on one relative restart window. -/
def restartChemDuhamelM (p : CM2Params) (a h : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r,
    intervalConjugateKernelOperator (r - s) (restartFluxM p a h u v s) x

/-- The faithful logistic Duhamel leg on one relative restart window. -/
def restartLogisticDuhamelM (p : CM2Params) (a h : ℝ)
    (u : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..r,
    intervalFullSemigroupOperator (r - s) (restartLogisticM p a h u s) x

/-- Three-term physical restart candidate. -/
def faithfulRestartDuhamelM (p : CM2Params) (a h : ℝ)
    (u v : ℝ → intervalDomainPoint → ℝ) (r x : ℝ) : ℝ :=
  intervalFullSemigroupOperator r (intervalDomainLift (u a)) x -
    p.χ₀ * restartChemDuhamelM p a h u v r x +
      restartLogisticDuhamelM p a h u r x

/-- A bounded measurable real field is interval-integrable on `[0,1]`. -/
lemma intervalIntegrable_zero_one_of_measurable_bounded
    {f : ℝ → ℝ} {C : ℝ} (hf : Measurable f)
    (hC : ∀ x, |f x| ≤ C) : IntervalIntegrable f volume 0 1 := by
  have hint : Integrable f (intervalMeasure 1) :=
    intervalMeasure_integrable_of_abs_bound hf.aestronglyMeasurable hC
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change Integrable f (volume.restrict (Ioc (0 : ℝ) 1))
  rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  simpa [intervalMeasure, intervalSet] using hint

/-- Cosine totality in a bounded-measurable form. -/
theorem ae_eq_on_unitInterval_of_cosineCoeffs_eq_of_measurable_bounded
    {f g : ℝ → ℝ} {Cf Cg : ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf_bound : ∀ x, |f x| ≤ Cf) (hg_bound : ∀ x, |g x| ≤ Cg)
    (hcoeff : ∀ k, cosineCoeffs f k = cosineCoeffs g k) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
  let d : ℝ → ℝ := fun x => f x - g x
  have hdmeas : Measurable d := hf.sub hg
  have hdbound : ∀ x, |d x| ≤ Cf + Cg := by
    intro x
    exact (abs_sub _ _).trans (add_le_add (hf_bound x) (hg_bound x))
  have hdmem : MemLp d (2 : ENNReal) (intervalMeasure 1) := by
    refine MemLp.of_bound hdmeas.aestronglyMeasurable (Cf + Cg) ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using hdbound x)
  have hfint := intervalIntegrable_zero_one_of_measurable_bounded hf hf_bound
  have hgint := intervalIntegrable_zero_one_of_measurable_bounded hg hg_bound
  have hraw : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1,
        Real.cos ((n : ℝ) * Real.pi * x) * d x) = 0 := by
    intro n
    let c : ℝ → ℝ := fun x => Real.cos ((n : ℝ) * Real.pi * x)
    have hccont : Continuous c := by unfold c; fun_prop
    have hfprod : IntervalIntegrable (fun x => c x * f x) volume 0 1 :=
      hfint.continuousOn_mul hccont.continuousOn
    have hgprod : IntervalIntegrable (fun x => c x * g x) volume 0 1 :=
      hgint.continuousOn_mul hccont.continuousOn
    have hcoef := hcoeff n
    rw [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
      ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral]
      at hcoef
    have heq : (∫ x in (0 : ℝ)..1, c x * f x) =
        ∫ x in (0 : ℝ)..1, c x * g x := by
      by_cases hn : n = 0
      · simpa [hn, c] using hcoef
      · have htwo : (2 : ℝ) ≠ 0 := by norm_num
        exact mul_left_cancel₀ htwo (by simpa [hn, c] using hcoef)
    calc
      (∫ x in (0 : ℝ)..1,
          Real.cos ((n : ℝ) * Real.pi * x) * d x) =
          ∫ x in (0 : ℝ)..1, c x * f x - c x * g x := by
            refine intervalIntegral.integral_congr (fun x _ => ?_)
            simp [d, c]
            ring
      _ = (∫ x in (0 : ℝ)..1, c x * f x) -
            ∫ x in (0 : ℝ)..1, c x * g x := by
              rw [intervalIntegral.integral_sub hfprod hgprod]
      _ = 0 := sub_eq_zero.mpr heq
  have hdcomplex :
      (fun x : ℝ => ((d x : ℝ) : ℂ))
        =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] 0 := by
    apply ShenWork.CosineParsevalBridge.unitIntervalCosine_nat_total_ae_zero
    · exact
        ShenWork.HeatKernelGradientEstimates.unitInterval_memLp_two_intervalIntegrable
          hdmem.ofReal
    · exact
        ShenWork.HeatKernelGradientEstimates.unitIntervalEvenReflection_memLp_two
          hdmem.ofReal
    · exact
        ShenWork.HeatKernelGradientEstimates.unitInterval_memLp_two_norm_sq_intervalIntegrable
          hdmem.ofReal
    · intro n
      have hcast := congrArg (fun z : ℝ => (z : ℂ)) (hraw n)
      calc
        (∫ x in (0 : ℝ)..1,
            (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) * (d x : ℂ)) =
            ∫ x in (0 : ℝ)..1,
              ((Real.cos ((n : ℝ) * Real.pi * x) * d x : ℝ) : ℂ) := by
                refine intervalIntegral.integral_congr (fun x _ => ?_)
                simp
        _ = ((∫ x in (0 : ℝ)..1,
              Real.cos ((n : ℝ) * Real.pi * x) * d x : ℝ) : ℂ) :=
              intervalIntegral.integral_ofReal
        _ = 0 := hcast
  filter_upwards [hdcomplex] with x hx
  have hre := congrArg Complex.re hx
  simpa [d] using sub_eq_zero.mp hre

/-- Every positive classical slice has a finite global bound after zero
extension. -/
theorem exists_solutionLift_abs_bound
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ C ≥ 0, ∀ x, |intervalDomainLift (u t) x| ≤ C := by
  have hc := solution_lift_continuousOn_Icc hsol ht
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hc.abs
  refine ⟨|intervalDomainLift (u t) z|, abs_nonneg _, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact hmax hx
  · simp [intervalDomainLift, hx]

theorem solutionSlice_continuous
    {p : CM2Params} {T t : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ht : t ∈ Ioo (0 : ℝ) T) : Continuous (u t) := by
  have hc := solution_lift_continuousOn_Icc hsol ht
  have hr := hc.restrict
  have heq : (Icc (0 : ℝ) 1).restrict (intervalDomainLift (u t)) = u t := by
    funext x
    simp [Set.restrict, intervalDomainLift, x.property]
  rw [← heq]
  exact hr

/-- Cosine coefficient of the homogeneous restart leg, using the subtype-
continuous spectral adapter (the zero extension itself is not continuous). -/
theorem cosineCoeff_restartHomM
    {p : CM2Params} {T a r M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : a ∈ Ioo (0 : ℝ) T) (hr : 0 < r)
    (hM : 0 ≤ M) (huM : ∀ x, |intervalDomainLift (u a) x| ≤ M)
    (k : ℕ) :
    cosineCoeffs
        (fun x => intervalFullSemigroupOperator r (intervalDomainLift (u a)) x) k =
      Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k := by
  have hucont : Continuous (u a) := solutionSlice_continuous hsol ha
  have hliftcont := solution_lift_continuousOn_Icc hsol ha
  have hcoef : ∀ n,
      |cosineCoeffs (intervalDomainLift (u a)) n| ≤ 2 * M := by
    intro n
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hliftcont hM (fun x _ => huM x) n
  have heq : Set.EqOn
      (fun x => intervalFullSemigroupOperator r (intervalDomainLift (u a)) x)
      (fun x => unitIntervalCosineHeatValue r
        (cosineCoeffs (intervalDomainLift (u a))) x)
      (Icc (0 : ℝ) 1) := by
    intro x hx
    exact ShenWork.IntervalSpectralSubtypeAdapter.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
      hr hucont hcoef hx
  rw [ShenWork.Paper2.cosineCoeffs_congr_on_Icc heq k]
  simpa [solutionCoeffM] using
    ShenWork.IntervalSemigroupComposition.cosineCoeffs_unitIntervalCosineHeatValue
      hr hcoef k

lemma intervalSineInner_restartFluxM_eq_physical
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : r ∈ Icc (0 : ℝ) h) (k : ℕ) :
    intervalSineInner (restartFluxM p a h u v r) k =
      intervalSineInner (intervalFluxM p (u (a + r)) (v (a + r))) k := by
  unfold intervalSineInner
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    congr 1
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    rw [restartFluxM_eq_physical hsol ha hh hahT hr hx]

lemma cosineCoeffs_restartLogisticM_eq_physical
    {p : CM2Params} {a h r : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hr : r ∈ Icc (0 : ℝ) h) (k : ℕ) :
    cosineCoeffs (restartLogisticM p a h u r) k =
      cosineCoeffs (logisticLiftedM p (u (a + r))) k := by
  exact ShenWork.Paper2.cosineCoeffs_congr_on_Icc
    (fun x hx => restartLogisticM_eq_physical hr hx) k

/-- The two clamped source coefficients combine to the physical B-form source
coefficient at absolute time `a+r`. -/
theorem restartSourceCoeffM_eq_physical
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr : r ∈ Icc (0 : ℝ) h) (k : ℕ) :
    cosineCoeffs (restartLogisticM p a h u r) k -
        p.χ₀ * (((k : ℝ) * Real.pi) *
          intervalSineInner (restartFluxM p a h u v r) k) =
      sourceCoeffM p u v (a + r) k := by
  rw [cosineCoeffs_restartLogisticM_eq_physical hr k,
    intervalSineInner_restartFluxM_eq_physical hsol ha hh hahT hr k]
  rfl

theorem integrableOn_Ioc_sub_rpow_neg_half_const
    (t K : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => K * (t - s) ^ (-(1 / 2) : ℝ))
      (Ioc (0 : ℝ) t) volume := by
  have h :=
    (ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul K
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at h
  simpa [mul_comm] using h

theorem restartChemDuhamelM_measurable
    {p : CM2Params} {a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hq : Measurable (Function.uncurry (restartFluxM p a h u v))) :
    Measurable (restartChemDuhamelM p a h u v r) := by
  have hbase :=
    ShenWork.IntervalConjugateKernelJointMeas.intervalConjugateKernelOperator_s_param_joint_measurable
      hq
  have hv :=
    ShenWork.IntervalMildPicardThreshold.variable_interval_integral_measurable'
      hbase
  simpa [restartChemDuhamelM] using
    hv.comp (measurable_const.prodMk measurable_id)

theorem restartLogisticDuhamelM_measurable
    {p : CM2Params} {a h r : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hell : Measurable (Function.uncurry (restartLogisticM p a h u))) :
    Measurable (restartLogisticDuhamelM p a h u r) := by
  have hbase :=
    ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
      hell
  have hv :=
    ShenWork.IntervalMildPicardThreshold.variable_interval_integral_measurable'
      hbase
  simpa [restartLogisticDuhamelM] using
    hv.comp (measurable_const.prodMk measurable_id)

set_option maxHeartbeats 1000000 in
theorem restartChemDuhamelM_abs_le
    {p : CM2Params} {a h r Cq : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hr : 0 < r) (hCq : 0 ≤ Cq)
    (hq_meas : Measurable (Function.uncurry (restartFluxM p a h u v)))
    (hq_bound : ∀ s y, |restartFluxM p a h u v s y| ≤ Cq) (x : ℝ) :
    |restartChemDuhamelM p a h u v r x| ≤
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt r) * Cq := by
  have hq_int : ∀ s, Integrable (restartFluxM p a h u v s)
      (intervalMeasure 1) := by
    intro s
    have hmap : Measurable (fun y : ℝ => ((s, y) : ℝ × ℝ)) :=
      measurable_const.prodMk measurable_id
    have hsmeas : Measurable (restartFluxM p a h u v s) :=
      hq_meas.comp hmap
    exact intervalMeasure_integrable_of_abs_bound
      hsmeas.aestronglyMeasurable (hq_bound s)
  have hII : IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (r - s)
        (restartFluxM p a h u v s) x) volume 0 r :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hr hCq hq_meas hq_int hq_bound
  simpa [restartChemDuhamelM] using
    ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
      hr le_rfl (fun s _ _ => hq_int s) hCq
        (fun s _ _ => hq_bound s) x hII

theorem restartLogisticDuhamelM_abs_le
    {p : CM2Params} {a h r Cell : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    (hr : 0 < r) (hCell : 0 ≤ Cell)
    (hell_bound : ∀ s y, |restartLogisticM p a h u s y| ≤ Cell) (x : ℝ) :
    |restartLogisticDuhamelM p a h u r x| ≤ r * Cell := by
  simpa [restartLogisticDuhamelM] using
    ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      hr le_rfl hCell hell_bound x

theorem faithfulRestartDuhamelM_measurable
    {p : CM2Params} {T a h r M : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : a ∈ Ioo (0 : ℝ) T) (hr : 0 < r)
    (hM : 0 ≤ M) (huM : ∀ x, |intervalDomainLift (u a) x| ≤ M)
    (hq : Measurable (Function.uncurry (restartFluxM p a h u v)))
    (hell : Measurable (Function.uncurry (restartLogisticM p a h u))) :
    Measurable (faithfulRestartDuhamelM p a h u v r) := by
  have hua_meas : AEStronglyMeasurable (intervalDomainLift (u a))
      (intervalMeasure 1) :=
    (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      (solutionSlice_continuous hsol ha)).aestronglyMeasurable
  have hhom : Continuous
      (fun x => intervalFullSemigroupOperator r (intervalDomainLift (u a)) x) :=
    ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      hr hM huM hua_meas
  exact (hhom.measurable.sub
      (measurable_const.mul (restartChemDuhamelM_measurable hq))).add
        (restartLogisticDuhamelM_measurable hell)

theorem faithfulRestartDuhamelM_abs_le
    {p : CM2Params} {a h r M Cq Cell : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (huM : ∀ x, |intervalDomainLift (u a) x| ≤ M)
    (hCq : 0 ≤ Cq)
    (hq_meas : Measurable (Function.uncurry (restartFluxM p a h u v)))
    (hq_bound : ∀ s y, |restartFluxM p a h u v s y| ≤ Cq)
    (hCell : 0 ≤ Cell)
    (hell_bound : ∀ s y, |restartLogisticM p a h u s y| ≤ Cell)
    (x : ℝ) :
    |faithfulRestartDuhamelM p a h u v r x| ≤
      M + |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt r) * Cq) + r * Cell := by
  have hhom :=
    ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      hr hM huM x
  have hchem := restartChemDuhamelM_abs_le hr hCq hq_meas hq_bound x
  have hlog := restartLogisticDuhamelM_abs_le hr hCell hell_bound x
  calc
    |faithfulRestartDuhamelM p a h u v r x| ≤
        |intervalFullSemigroupOperator r (intervalDomainLift (u a)) x| +
          |p.χ₀ * restartChemDuhamelM p a h u v r x| +
            |restartLogisticDuhamelM p a h u r x| := by
              unfold faithfulRestartDuhamelM
              simpa [sub_eq_add_neg] using abs_add_three
                (intervalFullSemigroupOperator r (intervalDomainLift (u a)) x)
                (-p.χ₀ * restartChemDuhamelM p a h u v r x)
                (restartLogisticDuhamelM p a h u r x)
    _ ≤ M + |p.χ₀| *
          (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
            (2 * Real.sqrt r) * Cq) + r * Cell := by
      rw [abs_mul]
      gcongr

set_option maxHeartbeats 1000000 in
theorem cosineCoeff_restartChemDuhamelM
    {p : CM2Params} {T a h r Cq : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr0 : 0 < r)
    (hCq : 0 ≤ Cq)
    (hq_bound : ∀ s y, |restartFluxM p a h u v s y| ≤ Cq)
    (k : ℕ) :
    cosineCoeffs (restartChemDuhamelM p a h u v r) k =
      ∫ s in (0 : ℝ)..r,
        Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
          (((k : ℝ) * Real.pi) *
            intervalSineInner (restartFluxM p a h u v s) k) := by
  let q : ℝ → ℝ → ℝ := restartFluxM p a h u v
  let G : ℝ → ℝ → ℝ := fun s x =>
    intervalConjugateKernelOperator (r - s) (q s) x
  let Cg :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  let K : ℝ := Cg * Cq
  let μs : ℝ → ℝ := fun s =>
    K * (max 0 (r - s)) ^ (-(1 / 2) : ℝ)
  have hqcont : Continuous (Function.uncurry q) := by
    simpa [q] using restartFluxM_continuous hsol ha hh hahT
  have hqmeas : Measurable (Function.uncurry q) := hqcont.measurable
  have hqint : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s
    have hsmeas : Measurable (q s) :=
      hqmeas.comp (measurable_const.prodMk measurable_id)
    exact intervalMeasure_integrable_of_abs_bound
      hsmeas.aestronglyMeasurable (hq_bound s)
  have hbase :=
    ShenWork.IntervalConjugateKernelJointMeas.intervalConjugateKernelOperator_s_param_joint_measurable
      hqmeas
  have hmap : Measurable (fun z : ℝ × ℝ =>
      (((r, z.2), z.1) : (ℝ × ℝ) × ℝ)) :=
    (measurable_const.prodMk measurable_snd).prodMk measurable_fst
  have hGmeas : Measurable (Function.uncurry G) := by
    simpa [G] using hbase.comp hmap
  have hK : 0 ≤ K := mul_nonneg
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg hCq
  have hμint : IntegrableOn μs (Ioc (0 : ℝ) r) volume := by
    refine (integrableOn_Ioc_sub_rpow_neg_half_const r K hr0.le).congr_fun ?_
      measurableSet_Ioc
    intro s hs
    simp [μs, max_eq_right (sub_nonneg.mpr hs.2)]
  have hGbnd : ∀ s x, |G s x| ≤ μs s := by
    intro s x
    by_cases hlag : 0 < r - s
    · have hop :=
        ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_abs_le
          hlag (hqint s) (hq_bound s) x
      calc
        |G s x| ≤ Cg * (r - s) ^ (-(1 / 2) : ℝ) * Cq := by
          simpa [G, Cg, q] using hop
        _ = μs s := by
          simp [μs, max_eq_right hlag.le, K, Cg]
          ring
    · have hzero :=
        ShenWork.Paper2.IntervalConjugateSourceBridge.intervalConjugateKernelOperator_nonpos
          (le_of_not_gt hlag) (q s) x
      rw [show G s x = 0 by simpa [G] using hzero, abs_zero]
      exact mul_nonneg hK (Real.rpow_nonneg (le_max_left 0 (r - s)) _)
  have hswap :=
    ShenWork.Paper2.IntervalChiNegHmdC.cosineCoeffs_integral_swap_ae_L1
      hr0.le G hGmeas hμint hGbnd k
  rw [show restartChemDuhamelM p a h u v r = fun x => ∫ s in (0 : ℝ)..r, G s x
      by funext x; rfl, hswap]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume r] with s hsr hs
  rw [Set.uIoc_of_le hr0.le] at hs
  have hsrlt : s < r := lt_of_le_of_ne hs.2 hsr
  have hnative := ShenWork.Paper2.intervalConjugateKernelOperator_cosineCoeff_native
    (sub_pos.mpr hsrlt) (hqcont.uncurry_left s) k
  simpa [G, q, sub_mul] using hnative

set_option maxHeartbeats 1000000 in
theorem cosineCoeff_restartLogisticDuhamelM
    {p : CM2Params} {T a h r Cell : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr0 : 0 < r) (hCell : 0 ≤ Cell)
    (hell_bound : ∀ s y, |restartLogisticM p a h u s y| ≤ Cell)
    (k : ℕ) :
    cosineCoeffs (restartLogisticDuhamelM p a h u r) k =
      ∫ s in (0 : ℝ)..r,
        Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
          cosineCoeffs (restartLogisticM p a h u s) k := by
  let ell : ℝ → ℝ → ℝ := restartLogisticM p a h u
  let G : ℝ → ℝ → ℝ := fun s x =>
    intervalFullSemigroupOperator (r - s) (ell s) x
  have hellcont : Continuous (Function.uncurry ell) := by
    simpa [ell] using restartLogisticM_continuous hsol ha hh hahT
  have hellmeas : Measurable (Function.uncurry ell) := hellcont.measurable
  have hbase :=
    ShenWork.IntervalMildPicardThreshold.intervalFullSemigroupOperator_s_param_joint_measurable'
      hellmeas
  have hmap : Measurable (fun z : ℝ × ℝ =>
      (((r, z.2), z.1) : (ℝ × ℝ) × ℝ)) :=
    (measurable_const.prodMk measurable_snd).prodMk measurable_fst
  have hGmeas : Measurable (Function.uncurry G) := by
    simpa [G] using hbase.comp hmap
  have hGbnd : ∀ s x, |G s x| ≤ Cell := by
    intro s x
    by_cases hlag : 0 < r - s
    · simpa [G, ell] using
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
          hlag hCell (hell_bound s) x
    · have hzero :=
        ShenWork.Paper2.IntervalConjugateSourceBridge.intervalFullSemigroupOperator_nonpos
          (le_of_not_gt hlag) (ell s) x
      rw [show G s x = 0 by simpa [G] using hzero, abs_zero]
      exact hCell
  have hswap :=
    ShenWork.Paper2.IntervalChiNegHmdC.cosineCoeffs_integral_swap_ae
      hr0.le G hGmeas hGbnd k
  rw [show restartLogisticDuhamelM p a h u r =
      fun x => ∫ s in (0 : ℝ)..r, G s x by funext x; rfl, hswap]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume r] with s hsr hs
  rw [Set.uIoc_of_le hr0.le] at hs
  have hsrlt : s < r := lt_of_le_of_ne hs.2 hsr
  have hscont : Continuous (ell s) := hellcont.uncurry_left s
  have hscoef : ∀ n, |cosineCoeffs (ell s) n| ≤ 2 * Cell := by
    intro n
    exact ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      hscont.continuousOn hCell (fun y _ => hell_bound s y) n
  have hdiag :=
    ShenWork.Paper2.IntervalGradientCoeffDuhamel.cosineCoeffs_intervalFullSemigroupOperator_diag
      (sub_pos.mpr hsrlt) hscont hscoef k
  simpa [G, ell, sub_mul] using hdiag

theorem cosineCoeffs_family_continuous
    {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (k : ℕ) :
    Continuous (fun s => cosineCoeffs (F s) k) := by
  let G : ℝ → ℝ → ℝ := fun s x =>
    Real.cos ((k : ℝ) * Real.pi * x) * F s x
  have hG : Continuous (Function.uncurry G) := by
    have hcos : Continuous (fun z : ℝ × ℝ =>
        Real.cos ((k : ℝ) * Real.pi * z.2)) := by fun_prop
    exact hcos.mul hF
  have hint : Continuous (fun s => ∫ x in (0 : ℝ)..1, G s x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hG 0 1
  have hmul : Continuous (fun s =>
      (if k = 0 then (1 : ℝ) else 2) * ∫ x in (0 : ℝ)..1, G s x) :=
    continuous_const.mul hint
  simpa [ShenWork.IntervalMildPicardRegularity.cosineCoeffs_eq_factor_mul_integral,
    G] using hmul

theorem intervalSineInner_family_continuous
    {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (k : ℕ) :
    Continuous (fun s => intervalSineInner (F s) k) := by
  by_cases hk : k = 0
  · subst k
    simpa [intervalSineInner] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · let G : ℝ → ℝ → ℝ := fun s x =>
      Real.sin ((k : ℝ) * Real.pi * x) * F s x
    have hG : Continuous (Function.uncurry G) := by
      have hsin : Continuous (fun z : ℝ × ℝ =>
          Real.sin ((k : ℝ) * Real.pi * z.2)) := by fun_prop
      exact hsin.mul hF
    have hint : Continuous (fun s => ∫ x in (0 : ℝ)..1, G s x) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        hG 0 1
    have hmul : Continuous (fun s => 2 * ∫ x in (0 : ℝ)..1, G s x) :=
      continuous_const.mul hint
    simpa [intervalSineInner, hk, G] using hmul

set_option maxHeartbeats 1500000 in
theorem cosineCoeff_faithfulRestartDuhamelM_eq_solution
    {p : CM2Params} {T a h r M Cq Cell : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr0 : 0 < r) (hrh : r ≤ h)
    (hM : 0 ≤ M) (huM : ∀ x, |intervalDomainLift (u a) x| ≤ M)
    (hCq : 0 ≤ Cq)
    (hq_bound : ∀ s y, |restartFluxM p a h u v s y| ≤ Cq)
    (hCell : 0 ≤ Cell)
    (hell_bound : ∀ s y, |restartLogisticM p a h u s y| ≤ Cell)
    (k : ℕ) :
    cosineCoeffs (faithfulRestartDuhamelM p a h u v r) k =
      solutionCoeffM u (a + r) k := by
  have harT : a + r < T :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrh a) hahT
  have haT : a < T := lt_of_lt_of_le (by linarith : a < a + r) harT.le
  have haq : Continuous (Function.uncurry (restartFluxM p a h u v)) :=
    restartFluxM_continuous hsol ha hh hahT
  have hal : Continuous (Function.uncurry (restartLogisticM p a h u)) :=
    restartLogisticM_continuous hsol ha hh hahT
  have hhomCoeff := cosineCoeff_restartHomM hsol ⟨ha, haT⟩ hr0 hM huM k
  have hchemCoeff := cosineCoeff_restartChemDuhamelM
    hsol ha hh hahT hr0 hCq hq_bound k
  have hlogCoeff := cosineCoeff_restartLogisticDuhamelM
    hsol ha hh hahT hr0 hCell hell_bound k
  let H : ℝ → ℝ := fun x =>
    intervalFullSemigroupOperator r (intervalDomainLift (u a)) x
  let B : ℝ → ℝ := restartChemDuhamelM p a h u v r
  let L : ℝ → ℝ := restartLogisticDuhamelM p a h u r
  let CB : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
      (2 * Real.sqrt r) * Cq
  have hHmeas : Measurable H := by
    have hua_meas : AEStronglyMeasurable (intervalDomainLift (u a))
        (intervalMeasure 1) :=
      (ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
        (solutionSlice_continuous hsol ⟨ha, haT⟩)).aestronglyMeasurable
    exact (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
      hr0 hM huM hua_meas).measurable
  have hHbound : ∀ x, |H x| ≤ M := fun x => by
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
      hr0 hM huM x
  have hBmeas : Measurable B := by
    simpa [B] using restartChemDuhamelM_measurable haq.measurable
  have hBbound : ∀ x, |B x| ≤ CB := by
    intro x
    simpa [B, CB] using restartChemDuhamelM_abs_le
      hr0 hCq haq.measurable hq_bound x
  have hLmeas : Measurable L := by
    simpa [L] using restartLogisticDuhamelM_measurable hal.measurable
  have hLbound : ∀ x, |L x| ≤ r * Cell := by
    intro x
    simpa [L] using restartLogisticDuhamelM_abs_le hr0 hCell hell_bound x
  have hHint := intervalIntegrable_zero_one_of_measurable_bounded hHmeas hHbound
  have hBint := intervalIntegrable_zero_one_of_measurable_bounded hBmeas hBbound
  have hLint := intervalIntegrable_zero_one_of_measurable_bounded hLmeas hLbound
  have hsplit := cosineCoeffs_sub_const_mul_add_of_intervalIntegrable
    p.χ₀ k hHint hBint hLint
  have hAcont : Continuous (fun s =>
      Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
        (((k : ℝ) * Real.pi) * intervalSineInner
          (restartFluxM p a h u v s) k)) := by
    have hexp : Continuous (fun s : ℝ =>
        Real.exp (-(r - s) * unitIntervalCosineEigenvalue k)) := by
      fun_prop
    exact hexp.mul (continuous_const.mul
      (intervalSineInner_family_continuous haq k))
  have hLccont : Continuous (fun s =>
      Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (restartLogisticM p a h u s) k) := by
    have hexp : Continuous (fun s : ℝ =>
        Real.exp (-(r - s) * unitIntervalCosineEigenvalue k)) := by
      fun_prop
    exact hexp.mul (cosineCoeffs_family_continuous hal k)
  let A : ℝ → ℝ := fun s =>
    Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
      (((k : ℝ) * Real.pi) * intervalSineInner
        (restartFluxM p a h u v s) k)
  let LC : ℝ → ℝ := fun s =>
    Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (restartLogisticM p a h u s) k
  have hAint : IntervalIntegrable A volume 0 r := by
    simpa [A] using hAcont.intervalIntegrable (μ := volume) 0 r
  have hLCint : IntervalIntegrable LC volume 0 r := by
    simpa [LC] using hLccont.intervalIntegrable (μ := volume) 0 r
  have hcombine :
      (-p.χ₀) * (∫ s in (0 : ℝ)..r, A s) + ∫ s in (0 : ℝ)..r, LC s =
        ∫ s in (0 : ℝ)..r, (LC s - p.χ₀ * A s) := by
    calc
      (-p.χ₀) * (∫ s in (0 : ℝ)..r, A s) + ∫ s in (0 : ℝ)..r, LC s =
          (∫ s in (0 : ℝ)..r, LC s) -
            p.χ₀ * (∫ s in (0 : ℝ)..r, A s) := by ring
      _ = (∫ s in (0 : ℝ)..r, LC s) -
            ∫ s in (0 : ℝ)..r, p.χ₀ * A s := by
              rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (0 : ℝ)..r, (LC s - p.χ₀ * A s) := by
              rw [intervalIntegral.integral_sub hLCint (hAint.const_mul p.χ₀)]
  have hsourceRel :
      (∫ s in (0 : ℝ)..r, (LC s - p.χ₀ * A s)) =
        ∫ s in (0 : ℝ)..r,
          Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
            sourceCoeffM p u v (a + s) k := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le hr0.le] at hs
    have hsrc := restartSourceCoeffM_eq_physical
      hsol ha hh hahT ⟨hs.1, hs.2.trans hrh⟩ k
    dsimp [LC, A]
    rw [← hsrc]
    ring
  have hshift :
      (∫ s in (0 : ℝ)..r,
          Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
            sourceCoeffM p u v (a + s) k) =
        ∫ s in a..(a + r),
          Real.exp (-((a + r) - s) * unitIntervalCosineEigenvalue k) *
            sourceCoeffM p u v s k := by
    have hraw := intervalIntegral.integral_comp_add_left
      (fun s => Real.exp (-((a + r) - s) * unitIntervalCosineEigenvalue k) *
        sourceCoeffM p u v s k) a (a := (0 : ℝ)) (b := r)
    calc
      (∫ s in (0 : ℝ)..r,
          Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
            sourceCoeffM p u v (a + s) k) =
          ∫ s in (0 : ℝ)..r,
            Real.exp (-((a + r) - (a + s)) * unitIntervalCosineEigenvalue k) *
              sourceCoeffM p u v (a + s) k := by
                refine intervalIntegral.integral_congr (fun s _ => ?_)
                congr 2
                ring
      _ = ∫ s in (a + 0)..(a + r),
          Real.exp (-((a + r) - s) * unitIntervalCosineEigenvalue k) *
            sourceCoeffM p u v s k := hraw
      _ = _ := by rw [add_zero]
  have hrestart := solutionCoeffM_restart hsol ha (by linarith) harT k
  rw [show cosineCoeffs (faithfulRestartDuhamelM p a h u v r) k =
      cosineCoeffs H k - p.χ₀ * cosineCoeffs B k + cosineCoeffs L k by
        simpa [faithfulRestartDuhamelM, H, B, L] using hsplit,
    show cosineCoeffs H k =
      Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k by
        simpa [H] using hhomCoeff,
    show cosineCoeffs B k = ∫ s in (0 : ℝ)..r, A s by
      simpa [B, A] using hchemCoeff,
    show cosineCoeffs L k = ∫ s in (0 : ℝ)..r, LC s by
      simpa [L, LC] using hlogCoeff]
  calc
    (Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k -
          p.χ₀ * (∫ s in (0 : ℝ)..r, A s)) +
        ∫ s in (0 : ℝ)..r, LC s =
        Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k +
          ((-p.χ₀) * (∫ s in (0 : ℝ)..r, A s) +
            ∫ s in (0 : ℝ)..r, LC s) := by ring
    _ = Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k +
          ∫ s in (0 : ℝ)..r, (LC s - p.χ₀ * A s) := by rw [hcombine]
    _ = Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k +
          ∫ s in (0 : ℝ)..r,
            Real.exp (-(r - s) * unitIntervalCosineEigenvalue k) *
              sourceCoeffM p u v (a + s) k := by rw [hsourceRel]
    _ = Real.exp (-r * unitIntervalCosineEigenvalue k) * solutionCoeffM u a k +
          ∫ s in a..(a + r),
            Real.exp (-((a + r) - s) * unitIntervalCosineEigenvalue k) *
              sourceCoeffM p u v s k := by rw [hshift]
    _ = solutionCoeffM u (a + r) k := by
      simpa [show a + r - a = r by ring] using hrestart.symm

set_option maxHeartbeats 1500000 in
/-- Physical divergence-form restart identity, first in its natural a.e. form.
The only exceptional set comes from the semigroup convention at zero lag and
cosine `L²` totality. -/
theorem faithfulRestartDuhamelM_ae_eq_solution
    {p : CM2Params} {T a h r : ℝ}
    {u v : ℝ → intervalDomainPoint → ℝ}
    (hsol : IsPaper2ClassicalSolution intervalDomainM p T u v)
    (ha : 0 < a) (hh : 0 ≤ h) (hahT : a + h < T)
    (hr0 : 0 < r) (hrh : r ≤ h) :
    faithfulRestartDuhamelM p a h u v r
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        intervalDomainLift (u (a + r)) := by
  have harT : a + r < T :=
    lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hrh a) hahT
  have haT : a < T := lt_of_lt_of_le (by linarith : a < a + r) harT.le
  obtain ⟨M, hM, huM⟩ :=
    exists_solutionLift_abs_bound hsol ⟨ha, haT⟩
  obtain ⟨Cq, hCq, hq_bound⟩ :=
    exists_restartFluxM_bound hsol ha hh hahT
  obtain ⟨Cell, hCell, hell_bound⟩ :=
    exists_restartLogisticM_bound hsol ha hh hahT
  obtain ⟨Mu, hMu, hu_bound⟩ :=
    exists_solutionLift_abs_bound hsol ⟨by linarith, harT⟩
  have hqcont := restartFluxM_continuous hsol ha hh hahT
  have hellcont := restartLogisticM_continuous hsol ha hh hahT
  have hcand_meas : Measurable (faithfulRestartDuhamelM p a h u v r) :=
    faithfulRestartDuhamelM_measurable hsol ⟨ha, haT⟩ hr0 hM huM
      hqcont.measurable hellcont.measurable
  let Ccand : ℝ := M + |p.χ₀| *
      (ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
        (2 * Real.sqrt r) * Cq) + r * Cell
  have hcand_bound : ∀ x,
      |faithfulRestartDuhamelM p a h u v r x| ≤ Ccand := by
    intro x
    simpa [Ccand] using faithfulRestartDuhamelM_abs_le
      hr0 hM huM hCq hqcont.measurable hq_bound hCell hell_bound x
  have huslice_cont : Continuous (u (a + r)) :=
    solutionSlice_continuous hsol ⟨by linarith, harT⟩
  have hu_meas : Measurable (intervalDomainLift (u (a + r))) :=
    ShenWork.IntervalMildPicardThreshold.intervalDomainLift_measurable_of_continuous'
      huslice_cont
  apply ae_eq_on_unitInterval_of_cosineCoeffs_eq_of_measurable_bounded
    hcand_meas hu_meas hcand_bound hu_bound
  intro k
  exact cosineCoeff_faithfulRestartDuhamelM_eq_solution
    hsol ha hh hahT hr0 hrh hM huM hCq hq_bound hCell hell_bound k

#print axioms ae_eq_on_unitInterval_of_cosineCoeffs_eq_of_measurable_bounded
#print axioms cosineCoeff_faithfulRestartDuhamelM_eq_solution
#print axioms faithfulRestartDuhamelM_ae_eq_solution

end ShenWork.Paper2.IntervalDomainM
