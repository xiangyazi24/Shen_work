/-
  Positive-time continuity of the faithful conjugate mild trajectory at every
  fixed spatial point.

  The source is only jointly measurable in time and space.  Consequently the
  proof does not rescale the Volterra integrals (which would make the source
  move with the target time).  At a target time `t0 > 0` it instead cuts the
  integrals at a fixed `c < t0`.  On `[0,c]` the source at each integration time
  is frozen, so fixed-source kernel continuity and dominated convergence apply.
  The remaining tails are bounded by `O(sqrt (t-c))` for the conjugate kernel
  and `O(t-c)` for the value kernel.
-/
import ShenWork.Paper2.IntervalChiNegTrajBanachFinal
import ShenWork.Paper2.IntervalChiNegValueOpCont
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalConjugateDuhamelSupLocalized
import ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
import ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
import ShenWork.PDE.IntervalSemigroupAtZero

open MeasureTheory Filter Topology Set intervalIntegral
open scoped Topology Interval

open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted intervalConjugateDuhamelMapM
   chemFluxMLifted_abs_le_of_pos_slice
   chemFluxMLifted_uncurry_measurable chemFluxMLifted_integrable_of_pos_slice)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_s_param_joint_measurable)
open ShenWork.IntervalMildPicardThreshold
  (intervalFullSemigroupOperator_s_param_joint_measurable'
   logisticLifted_joint_measurable')
open ShenWork.IntervalConjugateChemFluxIntegrable
  (conjugateDuhamel_intervalIntegrable_of_measurable_bound)
open ShenWork.IntervalDuhamelIntegrability
  (valueDuhamel_sup_bound_universal
   valueDuhamel_intervalIntegrable_of_joint_measurable)

noncomputable section

namespace ShenWork.Paper2

/-! ## Fixed-source continuity atoms -/

/-- A bounded integrable fixed source gives a jointly continuous Neumann heat
profile on every compact positive-time slab.  Unlike `valueOp_src_jointCont`,
no continuity of the source itself is needed because it does not move with the
time parameter. -/
theorem fullSemigroup_fixedSource_jointContinuousOnM
    {tau0 T : ℝ} (htau0 : 0 < tau0) (htau0T : tau0 ≤ T)
    {f : ℝ → ℝ} {Cf : ℝ}
    (hf_int : Integrable f (intervalMeasure 1))
    (hf_bound : ∀ y, |f y| ≤ Cf) :
    ContinuousOn
      (fun q : ℝ × ℝ => intervalFullSemigroupOperator q.1 f q.2)
      (Set.Icc tau0 T ×ˢ Set.Icc (0 : ℝ) 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  have hCf : 0 ≤ Cf := le_trans (abs_nonneg (f 0)) (hf_bound 0)
  open ShenWork.Paper2.IntervalChiNegValueOpCont in
    apply MeasureTheory.continuousOn_of_dominated
      (bound := fun _ : ℝ => valueKernelBound tau0 T * Cf)
    · intro q _hq
      have hm : Measurable
          (fun y : ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel
              q.1 q.2 y) :=
        fullKernel_joint_measurable.comp
          (f := fun y : ℝ => ((q.1, q.2), y))
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)
      exact hm.aestronglyMeasurable.mul hf_int.aestronglyMeasurable
    · intro q hq
      rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
        MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hqpos : 0 < q.1 := lt_of_lt_of_le htau0 hq.1.1
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg
          (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg
            hqpos _ _)]
      exact mul_le_mul
        (fullKernel_le htau0 htau0T hq.1 hq.2 hy)
        (hf_bound y) (abs_nonneg _)
        (valueKernelBound_nonneg htau0)
    · exact integrable_const _
    · show ∀ᵐ y ∂(intervalMeasure 1), ContinuousOn
          (fun q : ℝ × ℝ =>
            ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel
              q.1 q.2 y * f y)
          (Set.Icc tau0 T ×ˢ Set.Icc (0 : ℝ) 1)
      rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
        MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy => ?_
      exact (fullKernel_jointCont htau0 htau0T y hy).mul continuousOn_const

/-! ## Fixed-upper-limit early pieces -/

/-- On a target-time window lying strictly to the right of the fixed integration
upper bound `c`, the conjugate Duhamel early piece is continuous.  For each
integration time the source is fixed; only the positive lag varies. -/
theorem conjugateEarly_continuousOnM
    {c lo hi : ℝ} (hc0 : 0 ≤ c) (hclo : c < lo) (hlohi : lo ≤ hi)
    {Q : ℝ → ℝ → ℝ} {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ_meas : Measurable (Function.uncurry Q))
    (hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQ_bound : ∀ s y, |Q s y| ≤ CQ)
    (x : intervalDomainPoint) :
    ContinuousOn
      (fun t : ℝ => ∫ s in (0 : ℝ)..c,
        intervalConjugateKernelOperator (t - s) (Q s) x.1)
      (Set.Icc lo hi) := by
  rw [continuousOn_iff_continuous_restrict]
  set Cg : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hCg0 : 0 ≤ Cg :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  have hgap : 0 < lo - c := sub_pos.mpr hclo
  have hgap_hi : lo - c ≤ hi := by linarith
  have hjoint : Measurable
      (fun r : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator (r.1.1 - r.2) (Q r.2) r.1.2) :=
    intervalConjugateKernelOperator_s_param_joint_measurable hQ_meas
  refine intervalIntegral.continuous_of_dominated_interval
    (μ := volume)
    (F := fun t : ↥(Set.Icc lo hi) => fun s : ℝ =>
      intervalConjugateKernelOperator (t.1 - s) (Q s) x.1)
    (bound := fun _ : ℝ => Cg * CQ * (lo - c) ^ (-(1 / 2) : ℝ))
    ?_ ?_ intervalIntegral.intervalIntegrable_const ?_
  · intro t
    have hmap : Measurable
        (fun s : ℝ => (((t.1, x.1), s) : (ℝ × ℝ) × ℝ)) :=
      measurable_const.prodMk measurable_id
    exact (hjoint.comp hmap).aestronglyMeasurable
  · intro t
    filter_upwards [] with s hs
    rw [Set.uIoc_of_le hc0] at hs
    have hlower : lo - c ≤ t.1 - s := by linarith [t.2.1, hs.2]
    have hlag : 0 < t.1 - s := lt_of_lt_of_le hgap hlower
    have hpow :
        (t.1 - s) ^ (-(1 / 2) : ℝ) ≤
          (lo - c) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hgap hlower (by norm_num)
    rw [Real.norm_eq_abs]
    have hraw :=
      ShenWork.IntervalConjugateDuhamelMap.intervalConjugateKernelOperator_abs_le
        hlag (hQ_int s) (hQ_bound s) x.1
    calc
      |intervalConjugateKernelOperator (t.1 - s) (Q s) x.1|
          ≤ Cg * (t.1 - s) ^ (-(1 / 2) : ℝ) * CQ := by
              simpa [Cg] using hraw
      _ ≤ Cg * (lo - c) ^ (-(1 / 2) : ℝ) * CQ := by
            gcongr
      _ = Cg * CQ * (lo - c) ^ (-(1 / 2) : ℝ) := by ring
  · filter_upwards [] with s hs
    rw [Set.uIoc_of_le hc0] at hs
    have hbase :=
      ShenWork.Paper2.IntervalChiNegTrajBanachFinal.kernelOp_jointCont
        hgap hgap_hi (hQ_int s) (hQ_bound s)
    have hmap : Continuous
        (fun t : ↥(Set.Icc lo hi) => ((t.1 - s, x.1) : ℝ × ℝ)) := by
      fun_prop
    exact hbase.comp_continuous hmap (fun t => by
      refine ⟨⟨?_, ?_⟩, x.2⟩
      · linarith [t.2.1, hs.2]
      · linarith [t.2.2, hs.1])

/-- The analogous early-piece continuity for the value semigroup. -/
theorem valueEarly_continuousOnM
    {c lo hi : ℝ} (hc0 : 0 ≤ c) (hclo : c < lo) (hlohi : lo ≤ hi)
    {F : ℝ → ℝ → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_meas : Measurable (Function.uncurry F))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF)
    (x : intervalDomainPoint) :
    ContinuousOn
      (fun t : ℝ => ∫ s in (0 : ℝ)..c,
        intervalFullSemigroupOperator (t - s) (F s) x.1)
      (Set.Icc lo hi) := by
  rw [continuousOn_iff_continuous_restrict]
  have hgap : 0 < lo - c := sub_pos.mpr hclo
  have hgap_hi : lo - c ≤ hi := by linarith
  have hjoint : Measurable
      (fun r : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator (r.1.1 - r.2) (F r.2) r.1.2) :=
    intervalFullSemigroupOperator_s_param_joint_measurable' hF_meas
  refine intervalIntegral.continuous_of_dominated_interval
    (μ := volume)
    (F := fun t : ↥(Set.Icc lo hi) => fun s : ℝ =>
      intervalFullSemigroupOperator (t.1 - s) (F s) x.1)
    (bound := fun _ : ℝ => CF)
    ?_ ?_ intervalIntegral.intervalIntegrable_const ?_
  · intro t
    have hmap : Measurable
        (fun s : ℝ => (((t.1, x.1), s) : (ℝ × ℝ) × ℝ)) :=
      measurable_const.prodMk measurable_id
    exact (hjoint.comp hmap).aestronglyMeasurable
  · intro t
    filter_upwards [] with s hs
    rw [Set.uIoc_of_le hc0] at hs
    have hlag : 0 < t.1 - s := by linarith [t.2.1, hs.2]
    rw [Real.norm_eq_abs]
    exact
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        hlag hCF (hF_bound s) x.1
  · filter_upwards [] with s hs
    rw [Set.uIoc_of_le hc0] at hs
    have hbase := fullSemigroup_fixedSource_jointContinuousOnM
      hgap hgap_hi (hF_int s) (hF_bound s)
    have hmap : Continuous
        (fun t : ↥(Set.Icc lo hi) => ((t.1 - s, x.1) : ℝ × ℝ)) := by
      fun_prop
    exact hbase.comp_continuous hmap (fun t => by
      refine ⟨⟨?_, ?_⟩, x.2⟩
      · linarith [t.2.1, hs.2]
      · linarith [t.2.2, hs.1])

/-! ## Short-tail estimates -/

/-- A translated conjugate Duhamel tail has the expected square-root bound. -/
theorem conjugateTail_abs_leM
    {c t : ℝ} (hct : c < t)
    {Q : ℝ → ℝ → ℝ} {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ_meas : Measurable (Function.uncurry Q))
    (hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1))
    (hQ_bound : ∀ s y, |Q s y| ≤ CQ)
    (x : ℝ) :
    |∫ s in c..t, intervalConjugateKernelOperator (t - s) (Q s) x|
      ≤ ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant *
          (2 * Real.sqrt (t - c)) * CQ := by
  let Qshift : ℝ → ℝ → ℝ := fun r => Q (r + c)
  have hshift_meas : Measurable (Function.uncurry Qshift) := by
    exact hQ_meas.comp ((measurable_fst.add measurable_const).prodMk measurable_snd)
  have hshift_int : ∀ r, Integrable (Qshift r) (intervalMeasure 1) :=
    fun r => hQ_int (r + c)
  have hshift_bound : ∀ r y, |Qshift r y| ≤ CQ :=
    fun r y => hQ_bound (r + c) y
  have hlen : 0 < t - c := sub_pos.mpr hct
  have hint :=
    conjugateDuhamel_intervalIntegrable_of_measurable_bound
      hlen hCQ hshift_meas hshift_int hshift_bound (x := x)
  have hbd :=
    ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
      hlen (le_refl (t - c))
      (fun r _hr _hrT => hshift_int r) hCQ
      (fun r _hr _hrT => hshift_bound r) x hint
  have hshift :
      (∫ r in (0 : ℝ)..(t - c),
        intervalConjugateKernelOperator ((t - c) - r) (Qshift r) x) =
        (∫ s in c..t,
          intervalConjugateKernelOperator (t - s) (Q s) x) := by
    have hintegrand_shift :
        (fun r : ℝ =>
          intervalConjugateKernelOperator ((t - c) - r) (Qshift r) x) =
        fun r : ℝ =>
          intervalConjugateKernelOperator (t - (r + c)) (Q (r + c)) x := by
      funext r
      dsimp [Qshift]
      rw [show (t - c) - r = t - (r + c) by ring]
    rw [hintegrand_shift]
    have h := intervalIntegral.integral_comp_add_right
      (f := fun s : ℝ => intervalConjugateKernelOperator (t - s) (Q s) x)
      (a := (0 : ℝ)) (b := t - c) c
    simpa using h
  rwa [hshift] at hbd

/-- A translated value-Duhamel tail has the linear bound. -/
theorem valueTail_abs_leM
    {c t : ℝ} (hct : c < t)
    {F : ℝ → ℝ → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_bound : ∀ s y, |F s y| ≤ CF)
    (x : ℝ) :
    |∫ s in c..t, intervalFullSemigroupOperator (t - s) (F s) x|
      ≤ (t - c) * CF := by
  let Fshift : ℝ → ℝ → ℝ := fun r => F (r + c)
  have hlen : 0 < t - c := sub_pos.mpr hct
  have hbd :=
    valueDuhamel_sup_bound_universal hlen (le_refl (t - c)) hCF
      (fun r y => hF_bound (r + c) y) x
  have hshift :
      (∫ r in (0 : ℝ)..(t - c),
        intervalFullSemigroupOperator ((t - c) - r) (Fshift r) x) =
        (∫ s in c..t,
          intervalFullSemigroupOperator (t - s) (F s) x) := by
    have hintegrand_shift :
        (fun r : ℝ =>
          intervalFullSemigroupOperator ((t - c) - r) (Fshift r) x) =
        fun r : ℝ =>
          intervalFullSemigroupOperator (t - (r + c)) (F (r + c)) x := by
      funext r
      dsimp [Fshift]
      rw [show (t - c) - r = t - (r + c) by ring]
    rw [hintegrand_shift]
    have h := intervalIntegral.integral_comp_add_right
      (f := fun s : ℝ => intervalFullSemigroupOperator (t - s) (F s) x)
      (a := (0 : ℝ)) (b := t - c) c
    simpa using h
  rwa [hshift] at hbd

/-! ## Faithful mild time-slice continuity -/

/-- Every fixed spatial point of the faithful conjugate mild trajectory is
continuous on positive times, including one-sided continuity at the terminal
time.  The only initial-datum inputs are the same boundedness and measurability
assumptions used by the faithful positive-time spatial regularity chain. -/
theorem conjugateMildM_timeSlice_continuousOn_Ioc
    {p : CM2Params} {u0 : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u0)
    (hu0_bound : ∀ y, |intervalDomainLift u0 y| ≤ D.M)
    (hu0_meas : AEStronglyMeasurable
      (intervalDomainLift u0) (intervalMeasure 1))
    (x : intervalDomainPoint) :
    ContinuousOn (fun t : ℝ => D.u t x) (Set.Ioc (0 : ℝ) D.T) := by
  -- Globally cut off the two source families.  On every mild integration
  -- window `(0,t]`, `t ≤ D.T`, they agree with the faithful sources.
  let Q : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) y else 0
  let L : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then logisticLifted p (D.u s) y else 0
  have hcM : D.c ≤ D.M := D.floor_le_bound
  let CQ : ℝ := D.M ^ p.m *
    (Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * D.M ^ p.γ)))
  let CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
  have hCQ : 0 ≤ CQ := by
    dsimp [CQ]
    exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (by norm_num)
          (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))
  have hCL : 0 ≤ CL := by
    dsimp [CL]
    exact mul_nonneg D.hM.le
      (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))
  have hQ_meas : Measurable (Function.uncurry Q) := by
    have hbase := chemFluxMLifted_uncurry_measurable
      (p := p) (u := D.u) D.hmeas
    simp only [Q]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hL_meas : Measurable (Function.uncurry L) := by
    have hbase :=
      logisticLifted_joint_measurable' (p := p) (u := D.u) D.hmeas
    simp only [L]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hQ_bound : ∀ s y, |Q s y| ≤ CQ := by
    intro s y
    simp only [Q]
    split_ifs with hs
    · dsimp [CQ]
      exact chemFluxMLifted_abs_le_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2) y
    · simpa using hCQ
  have hL_bound : ∀ s y, |L s y| ≤ CL := by
    intro s y
    simp only [L]
    split_ifs with hs
    · dsimp [CL]
      exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p D.hM (D.hbound s hs.1 hs.2) y
    · simpa using hCL
  have hQ_int : ∀ s, Integrable (Q s) (intervalMeasure 1) := by
    intro s
    simp only [Q]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p D.hc hcM
        (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
          (D.hcont s hs.1 hs.2)
    · simp
  have hL_int : ∀ s, Integrable (L s) (intervalMeasure 1) := by
    intro s
    simp only [L]
    split_ifs with hs
    · exact
        ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
          p (D.hbound s hs.1 hs.2) D.hM.le (D.hcont s hs.1 hs.2)
    · simp
  have hu0_int : Integrable (intervalDomainLift u0) (intervalMeasure 1) :=
    ShenWork.IntervalDomain.intervalMeasure_integrable_of_abs_bound
      hu0_meas hu0_bound

  intro t0 ht0
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  set Cg : ℝ :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  let tailBound : ℝ → ℝ := fun r =>
    |p.χ₀| * (Cg * (2 * Real.sqrt r) * CQ) + r * CL
  have htail_cont : ContinuousAt tailBound 0 := by
    dsimp [tailBound]
    fun_prop
  have htail_zero : tailBound 0 = 0 := by
    simp [tailBound]
  have heps3 : 0 < eps / 3 := by positivity
  obtain ⟨dtail, hdtail, htail_close⟩ :=
    (Metric.continuousAt_iff.mp htail_cont) (eps / 3) heps3
  let rho : ℝ := min (t0 / 4) (dtail / 4)
  have hrho : 0 < rho := by
    exact lt_min (by linarith [ht0.1]) (by linarith)
  have hrho_t : rho ≤ t0 / 4 := min_le_left _ _
  have hrho_d : rho ≤ dtail / 4 := min_le_right _ _
  let c : ℝ := t0 - rho
  let lo : ℝ := t0 - rho / 2
  let hi : ℝ := t0 + rho / 2
  have hc0 : 0 ≤ c := by dsimp [c]; linarith
  have hclo : c < lo := by dsimp [c, lo]; linarith
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hlo0 : 0 < lo := by dsimp [lo]; linarith
  have ht0mem : t0 ∈ Set.Icc lo hi := by
    constructor <;> dsimp [lo, hi] <;> linarith
  have hbox_nhds : Set.Icc lo hi ∈ nhds t0 :=
    Icc_mem_nhds (by dsimp [lo]; linarith) (by dsimp [hi]; linarith)

  let Hom : ℝ → ℝ := fun t =>
    intervalFullSemigroupOperator t (intervalDomainLift u0) x.1
  let BEarly : ℝ → ℝ := fun t =>
    ∫ s in (0 : ℝ)..c,
      intervalConjugateKernelOperator (t - s) (Q s) x.1
  let LEarly : ℝ → ℝ := fun t =>
    ∫ s in (0 : ℝ)..c,
      intervalFullSemigroupOperator (t - s) (L s) x.1
  let Core : ℝ → ℝ := fun t =>
    Hom t + (-p.χ₀) * BEarly t + LEarly t

  have hHom_on : ContinuousOn Hom (Set.Icc lo hi) := by
    have hjoint := fullSemigroup_fixedSource_jointContinuousOnM
      hlo0 hlohi hu0_int hu0_bound
    have hpair : ContinuousOn (fun t : ℝ => ((t, x.1) : ℝ × ℝ))
        (Set.Icc lo hi) := continuousOn_id.prodMk continuousOn_const
    exact hjoint.comp hpair (fun t ht => ⟨ht, x.2⟩)
  have hBEarly_on : ContinuousOn BEarly (Set.Icc lo hi) := by
    exact conjugateEarly_continuousOnM hc0 hclo hlohi hCQ
      hQ_meas hQ_int hQ_bound x
  have hLEarly_on : ContinuousOn LEarly (Set.Icc lo hi) := by
    exact valueEarly_continuousOnM hc0 hclo hlohi hCL
      hL_meas hL_int hL_bound x
  have hCore_on : ContinuousOn Core (Set.Icc lo hi) := by
    exact (hHom_on.add (continuousOn_const.mul hBEarly_on)).add hLEarly_on
  have hCore_at : ContinuousAt Core t0 := hCore_on.continuousAt hbox_nhds
  obtain ⟨dcore, hdcore, hcore_close⟩ :=
    (Metric.continuousAt_iff.mp hCore_at) (eps / 3) heps3
  refine ⟨min dcore (rho / 2), lt_min hdcore (by linarith), ?_⟩
  intro t ht htdist
  have htcore : dist t t0 < dcore :=
    lt_of_lt_of_le htdist (min_le_left _ _)
  have htnear : dist t t0 < rho / 2 :=
    lt_of_lt_of_le htdist (min_le_right _ _)
  have htnear_abs : |t - t0| < rho / 2 := by
    simpa [Real.dist_eq] using htnear
  have hct : c < t := by
    have hlow := (abs_lt.mp htnear_abs).1
    dsimp [c]
    linarith
  have htlocal : t ∈ Set.Icc lo hi := by
    dsimp [lo, hi]
    constructor <;> linarith [abs_lt.mp htnear_abs]
  have hgap0 : 0 ≤ t - c := sub_nonneg.mpr hct.le
  have hgap_lt : t - c < dtail := by
    dsimp [c]
    have : t - t0 < rho / 2 := (abs_lt.mp htnear_abs).2
    have h2rho : 2 * rho ≤ dtail / 2 := by linarith [hrho_d]
    linarith
  have hrho_lt : rho < dtail := by linarith [hrho_d, hdtail]
  have htail_nonneg : ∀ {r : ℝ}, 0 ≤ r → 0 ≤ tailBound r := by
    intro r hr
    dsimp [tailBound]
    have hCg0 : 0 ≤ Cg :=
      ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
    positivity
  have htail_t : tailBound (t - c) < eps / 3 := by
    have hd : dist (t - c) 0 < dtail := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hgap0]
      exact hgap_lt
    have h := htail_close hd
    rw [htail_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg (htail_nonneg hgap0)] at h
    exact h
  have htail_t0 : tailBound rho < eps / 3 := by
    have hd : dist rho 0 < dtail := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hrho]
      exact hrho_lt
    have h := htail_close hd
    rw [htail_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg (htail_nonneg hrho.le)] at h
    exact h

  let BTail : ℝ → ℝ := fun r =>
    ∫ s in c..r,
      intervalConjugateKernelOperator (r - s) (Q s) x.1
  let LTail : ℝ → ℝ := fun r =>
    ∫ s in c..r,
      intervalFullSemigroupOperator (r - s) (L s) x.1

  have hmild_cutoff : ∀ r, 0 < r → r ≤ D.T →
      D.u r x = Hom r + (-p.χ₀) *
          (∫ s in (0 : ℝ)..r,
            intervalConjugateKernelOperator (r - s) (Q s) x.1) +
        (∫ s in (0 : ℝ)..r,
          intervalFullSemigroupOperator (r - s) (L s) x.1) := by
    intro r hr hrT
    have hm := D.hmild r hr hrT x
    rw [hm]
    unfold intervalConjugateDuhamelMapM
    dsimp [Hom]
    have hBeq :
        (∫ s in (0 : ℝ)..r,
          intervalConjugateKernelOperator (r - s)
            (chemFluxMLifted p (D.u s)) x.1) =
        (∫ s in (0 : ℝ)..r,
          intervalConjugateKernelOperator (r - s) (Q s) x.1) := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le hr.le] at hs
      have hsT : s ≤ D.T := hs.2.trans hrT
      simp [Q, hs.1, hsT]
    have hLeq :
        (∫ s in (0 : ℝ)..r,
          intervalFullSemigroupOperator (r - s)
            (logisticLifted p (D.u s)) x.1) =
        (∫ s in (0 : ℝ)..r,
          intervalFullSemigroupOperator (r - s) (L s) x.1) := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le hr.le] at hs
      have hsT : s ≤ D.T := hs.2.trans hrT
      simp [L, hs.1, hsT]
    rw [hBeq, hLeq]
  have hsplit : ∀ r, 0 < r → r ≤ D.T → c < r →
      D.u r x = Core r + (-p.χ₀) * BTail r + LTail r := by
    intro r hr hrT hcr
    rw [hmild_cutoff r hr hrT]
    have hBfull :=
      conjugateDuhamel_intervalIntegrable_of_measurable_bound
        hr hCQ hQ_meas hQ_int hQ_bound (x := x.1)
    have hLfull :=
      valueDuhamel_intervalIntegrable_of_joint_measurable
        hr hL_meas hCL hL_bound x.1
    have hc_mem : c ∈ Set.uIcc (0 : ℝ) r := by
      rw [Set.uIcc_of_le hr.le]
      exact ⟨hc0, hcr.le⟩
    have hB0c := hBfull.mono_set
      (Set.uIcc_subset_uIcc_left hc_mem)
    have hBcR := hBfull.mono_set
      (Set.uIcc_subset_uIcc_right hc_mem)
    have hL0c := hLfull.mono_set
      (Set.uIcc_subset_uIcc_left hc_mem)
    have hLcR := hLfull.mono_set
      (Set.uIcc_subset_uIcc_right hc_mem)
    have hBsplit :=
      intervalIntegral.integral_add_adjacent_intervals hB0c hBcR
    have hLsplit :=
      intervalIntegral.integral_add_adjacent_intervals hL0c hLcR
    rw [← hBsplit, ← hLsplit]
    dsimp [Core, BEarly, LEarly, BTail, LTail]
    ring
  have hsplit_t := hsplit t ht.1 ht.2 hct
  have hct0 : c < t0 := by dsimp [c]; linarith
  have hsplit_t0 := hsplit t0 ht0.1 ht0.2 hct0
  have hBtail_t := conjugateTail_abs_leM hct hCQ hQ_meas hQ_int hQ_bound x.1
  have hLtail_t := valueTail_abs_leM hct hCL hL_bound x.1
  have hBtail_t0 := conjugateTail_abs_leM hct0 hCQ hQ_meas hQ_int hQ_bound x.1
  have hLtail_t0 := valueTail_abs_leM hct0 hCL hL_bound x.1
  have htail_pair_t : |(-p.χ₀) * BTail t + LTail t| < eps / 3 := by
    calc
      |(-p.χ₀) * BTail t + LTail t|
          ≤ |p.χ₀| * |BTail t| + |LTail t| := by
              calc
                |(-p.χ₀) * BTail t + LTail t|
                    ≤ |(-p.χ₀) * BTail t| + |LTail t| := abs_add_le _ _
                _ = |p.χ₀| * |BTail t| + |LTail t| := by
                  rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| *
            (Cg * (2 * Real.sqrt (t - c)) * CQ) + (t - c) * CL := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hBtail_t (abs_nonneg _)) hLtail_t
      _ = tailBound (t - c) := by rfl
      _ < eps / 3 := htail_t
  have htail_pair_t0 : |(-p.χ₀) * BTail t0 + LTail t0| < eps / 3 := by
    have ht0c : t0 - c = rho := by dsimp [c]; ring
    calc
      |(-p.χ₀) * BTail t0 + LTail t0|
          ≤ |p.χ₀| * |BTail t0| + |LTail t0| := by
              calc
                |(-p.χ₀) * BTail t0 + LTail t0|
                    ≤ |(-p.χ₀) * BTail t0| + |LTail t0| := abs_add_le _ _
                _ = |p.χ₀| * |BTail t0| + |LTail t0| := by
                  rw [abs_mul, abs_neg]
      _ ≤ |p.χ₀| *
            (Cg * (2 * Real.sqrt (t0 - c)) * CQ) + (t0 - c) * CL := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hBtail_t0 (abs_nonneg _)) hLtail_t0
      _ = tailBound rho := by rw [ht0c]
      _ < eps / 3 := htail_t0
  have hcore : dist (Core t) (Core t0) < eps / 3 := hcore_close htcore
  rw [hsplit_t, hsplit_t0, Real.dist_eq]
  have htail_sub :
      |((-p.χ₀) * BTail t + LTail t) -
          ((-p.χ₀) * BTail t0 + LTail t0)| ≤
        |(-p.χ₀) * BTail t + LTail t| +
          |(-p.χ₀) * BTail t0 + LTail t0| := by
    calc
      |((-p.χ₀) * BTail t + LTail t) -
          ((-p.χ₀) * BTail t0 + LTail t0)| =
          |((-p.χ₀) * BTail t + LTail t) +
            (-((-p.χ₀) * BTail t0 + LTail t0))| := by
              congr 1
      _ ≤ |(-p.χ₀) * BTail t + LTail t| +
          |-((-p.χ₀) * BTail t0 + LTail t0)| := abs_add_le _ _
      _ = |(-p.χ₀) * BTail t + LTail t| +
          |(-p.χ₀) * BTail t0 + LTail t0| := by rw [abs_neg]
  calc
    |(Core t + (-p.χ₀) * BTail t + LTail t) -
        (Core t0 + (-p.χ₀) * BTail t0 + LTail t0)|
        ≤ |Core t - Core t0| +
            |(-p.χ₀) * BTail t + LTail t| +
            |(-p.χ₀) * BTail t0 + LTail t0| := by
          calc
            |(Core t + (-p.χ₀) * BTail t + LTail t) -
                (Core t0 + (-p.χ₀) * BTail t0 + LTail t0)| =
                |(Core t - Core t0) +
                  (((-p.χ₀) * BTail t + LTail t) -
                    ((-p.χ₀) * BTail t0 + LTail t0))| := by
                      congr 1
                      ring
            _ ≤ |Core t - Core t0| +
                |((-p.χ₀) * BTail t + LTail t) -
                  ((-p.χ₀) * BTail t0 + LTail t0)| := abs_add_le _ _
            _ ≤ |Core t - Core t0| +
                (|(-p.χ₀) * BTail t + LTail t| +
                  |(-p.χ₀) * BTail t0 + LTail t0|) :=
                    add_le_add (le_refl _) htail_sub
            _ = |Core t - Core t0| +
                |(-p.χ₀) * BTail t + LTail t| +
                |(-p.χ₀) * BTail t0 + LTail t0| := by ring
    _ < eps / 3 + eps / 3 + eps / 3 := by
      rw [Real.dist_eq] at hcore
      exact add_lt_add (add_lt_add hcore htail_pair_t) htail_pair_t0
    _ = eps := by ring

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_timeSlice_continuousOn_Ioc
