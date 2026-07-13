/-
  Joint positive-time continuity of the faithful interior time derivative.

  The proof first establishes the only nonsingular kernel fact not already
  exposed by the positive-time C2 files: away from zero lag, the literal
  Hessians of both the full and conjugate Neumann operators are jointly
  continuous in lag and space.  The conjugate statement uses a fixed
  positive half-step and the committed full-semigroup second-value series.
-/
import ShenWork.Paper2.IntervalConjugateMildJointTimeDerivativeInterior
import ShenWork.Paper2.IntervalDomainMConjugateMildTimeDerivativeClosed
import ShenWork.Paper2.IntervalDomainMConjugateMildChemDivJointContinuity
import ShenWork.Paper2.IntervalDomainMConjugateMildLogisticTimeDerivative
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeFluxC1eta

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (constExtend_eq_lift_on_Icc intervalDomainConstExtend intervalDomainLift
    intervalDomainPoint intervalMeasure semigroupOperator_constExtend_eq_lift)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted chemFluxMLifted_abs_le_of_pos_slice
    chemFluxMLifted_uncurry_measurable chemFluxMLifted_continuous_of_pos_slice)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalDomainRegularityBootstrap
  (unitIntervalCosineHeatSecondValue)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)

/-! ## Faithful chemotaxis Hessian -/

private def jointChemFluxBoundConst
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) : ℝ :=
  D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)))

private theorem jointChemFluxBoundConst_nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    0 ≤ jointChemFluxBoundConst D := by
  unfold jointChemFluxBoundConst
  exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))

private def jointChemFluxWindowCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) : ℝ → ℝ → ℝ :=
  fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) y else 0

private theorem jointChemFluxWindowCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    Measurable (Function.uncurry (jointChemFluxWindowCutoff D)) := by
  have hbase := chemFluxMLifted_uncurry_measurable
    (p := p) (u := D.u) D.hmeas
  unfold jointChemFluxWindowCutoff
  refine Measurable.ite ?_ hbase measurable_const
  exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
    ((isClosed_Iic.preimage continuous_fst).measurableSet)

private theorem jointChemFluxWindowCutoff_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s y, |jointChemFluxWindowCutoff D s y| ≤ jointChemFluxBoundConst D := by
  intro s y
  unfold jointChemFluxWindowCutoff
  split_ifs with hs
  · exact chemFluxMLifted_abs_le_of_pos_slice p D.hc D.floor_le_bound
      (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
        (D.hcont s hs.1 hs.2) y
  · simpa using jointChemFluxBoundConst_nonneg D

private theorem jointChemFluxWindowCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s, Continuous (jointChemFluxWindowCutoff D s) := by
  intro s
  unfold jointChemFluxWindowCutoff
  split_ifs with hs
  · exact chemFluxMLifted_continuous_of_pos_slice p D.hc D.floor_le_bound
      (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
        (D.hcont s hs.1 hs.2)
  · exact continuous_const

private theorem jointChemFluxWindowCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s, Integrable (jointChemFluxWindowCutoff D s) (intervalMeasure 1) := by
  intro s
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (jointChemFluxWindowCutoff_continuous D s).continuousOn.integrableOn_Icc

private theorem jointIntervalFullSemigroupOperator_congr_on_Ioo
    {f g : ℝ → ℝ} (hfg : Set.EqOn f g (Set.Ioo (0 : ℝ) 1))
    (r x : ℝ) :
    intervalFullSemigroupOperator r f x =
      intervalFullSemigroupOperator r g x := by
  unfold intervalFullSemigroupOperator
  apply MeasureTheory.integral_congr_ae
  have hmem : ∀ᵐ y : ℝ ∂(intervalMeasure 1),
      y ∈ Set.Ioo (0 : ℝ) 1 := by
    simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
    refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
    have hne0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    have hne1 : ∀ᵐ y : ℝ ∂volume, y ≠ 1 := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne0, hne1] with y hy0 hy1 hy
    exact ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0),
      lt_of_le_of_ne hy.2 hy1⟩
  filter_upwards [hmem] with y hy
  rw [hfg hy]

private theorem jointConstExtend_eq_apply_unitClip
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

/-- A continuous constant extension of the physical flux-divergence
representative, switched on only after the fixed positive cutoff `a`. -/
private def jointChemDivLateConstCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) (a : ℝ) : ℝ → ℝ → ℝ :=
  fun s y =>
    if a < s ∧ s < D.T then
      intervalDomainConstExtend
        (fun x : intervalDomainPoint =>
          conjugateMildMChemDivJointRep p D.u s x.1) y
    else 0

private theorem jointChemDivLateConstCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    Measurable (Function.uncurry (jointChemDivLateConstCutoff D a)) := by
  let A : Set (ℝ × ℝ) := {q | a < q.1 ∧ q.1 < D.T}
  let R : ℝ × ℝ → ℝ := fun q =>
    conjugateMildMChemDivJointRep p D.u q.1 (unitClip q.2).1
  have hmap : Continuous
      (fun q : ℝ × ℝ => (q.1, (unitClip q.2).1)) :=
    continuous_fst.prodMk
      (continuous_subtype_val.comp (unitClip_continuous.comp continuous_snd))
  have hR : ContinuousOn R A := by
    apply (conjugateMildMChemDivJointRep_jointContinuousOn
      D hu₀_bound hu₀_meas).comp hmap.continuousOn
    intro q hq
    exact Set.mem_prod.mpr
      ⟨⟨ha.trans_lt hq.1, hq.2⟩, (unitClip q.2).2⟩
  have hA : MeasurableSet A :=
    ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isOpen_Iio.preimage continuous_fst).measurableSet)
  have hpiece : Function.uncurry (jointChemDivLateConstCutoff D a) =
      A.piecewise R (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ A
    · rw [Set.piecewise_eq_of_mem _ _ _ hq]
      have hq' : a < q.1 ∧ q.1 < D.T := by simpa [A] using hq
      change (if a < q.1 ∧ q.1 < D.T then
          intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              conjugateMildMChemDivJointRep p D.u q.1 x.1) q.2 else 0) = _
      rw [if_pos hq', jointConstExtend_eq_apply_unitClip]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq]
      have hq' : ¬ (a < q.1 ∧ q.1 < D.T) := by simpa [A] using hq
      change (if a < q.1 ∧ q.1 < D.T then
          intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              conjugateMildMChemDivJointRep p D.u q.1 x.1) q.2 else 0) = 0
      rw [if_neg hq']
  rw [hpiece]
  exact ContinuousOn.measurable_piecewise hR continuousOn_const hA

private theorem jointChemDivLateConstCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ s, Continuous (jointChemDivLateConstCutoff D a s) := by
  intro s
  by_cases hs : a < s ∧ s < D.T
  · rw [show jointChemDivLateConstCutoff D a s =
        intervalDomainConstExtend
          (fun x : intervalDomainPoint =>
            conjugateMildMChemDivJointRep p D.u s x.1) by
      funext y
      simp [jointChemDivLateConstCutoff, hs]]
    apply ShenWork.IntervalDomain.constExtend_continuous
    have hslice : ContinuousOn
        (fun x : intervalDomainPoint =>
          conjugateMildMChemDivJointRep p D.u s x.1) Set.univ := by
      apply (conjugateMildMChemDivJointRep_jointContinuousOn
        D hu₀_bound hu₀_meas).comp
        (continuous_const.prodMk continuous_subtype_val).continuousOn
      intro x _hx
      exact Set.mem_prod.mpr ⟨⟨ha.trans_lt hs.1, hs.2⟩, x.2⟩
    simpa only [continuousOn_univ] using hslice
  · rw [show jointChemDivLateConstCutoff D a s = fun _ : ℝ => 0 by
      funext y
      simp [jointChemDivLateConstCutoff, hs]]
    exact continuous_const

private theorem jointChemDivLateConstCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ s, Integrable (jointChemDivLateConstCutoff D a s) (intervalMeasure 1) := by
  intro s
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (jointChemDivLateConstCutoff_continuous
    D hu₀_bound hu₀_meas ha s).continuousOn.integrableOn_Icc

private theorem jointChemDivLateConstCutoff_bounded
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s y, |jointChemDivLateConstCutoff D a s y| ≤ C := by
  obtain ⟨C, hC, hraw⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀_bound hu₀_meas ha
  refine ⟨C, hC, ?_⟩
  intro s y
  by_cases hs : a < s ∧ s < D.T
  · rw [jointChemDivLateConstCutoff, if_pos hs,
      jointConstExtend_eq_apply_unitClip]
    let R : ℝ → ℝ := conjugateMildMChemDivJointRep p D.u s
    have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
      apply (conjugateMildMChemDivJointRep_jointContinuousOn
        D hu₀_bound hu₀_meas).comp
        (continuous_const.prodMk continuous_id).continuousOn
      intro z hz
      exact Set.mem_prod.mpr ⟨⟨ha.trans hs.1, hs.2⟩, hz⟩
    have hRIoo : ∀ z ∈ Set.Ioo (0 : ℝ) 1, |R z| ≤ C := by
      intro z hz
      rw [show R z = deriv (chemFluxMLifted p (D.u s)) z by
        symm
        exact deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
          D hu₀_bound hu₀_meas (ha.trans hs.1) hs.2.le hz]
      exact hraw s hs.1.le hs.2.le z hz
    have hcl : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 :=
      closure_Ioo (by norm_num)
    have hzcl : (unitClip y).1 ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [hcl]
      exact (unitClip y).2
    exact le_on_closure (s := Set.Ioo (0 : ℝ) 1)
      (f := fun z => |R z|) (g := fun _ => C) hRIoo
      (by simpa [hcl] using hRcont.abs) continuousOn_const hzcl
  · rw [jointChemDivLateConstCutoff, if_neg hs, abs_zero]
    exact hC

private theorem jointChemDivLateConstCutoff_positiveStripHolder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    (a : ℝ) :
    ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ D.T →
          ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |jointChemDivLateConstCutoff D a s x -
              jointChemDivLateConstCutoff D a s y| ≤
                HQ * |x - y| ^ theta := by
  intro tau htau
  obtain ⟨theta, HQ, htheta0, htheta1, hHQ, hraw⟩ :=
    conjugateMildMChemDivJointRep_positiveTime_holder_uniform
      D hu₀_bound hu₀_meas htau
  refine ⟨theta, HQ, htheta0, htheta1, hHQ, ?_⟩
  intro s htaus hsT x hx y hy
  by_cases hs : a < s ∧ s < D.T
  · have hLx : jointChemDivLateConstCutoff D a s x =
        conjugateMildMChemDivJointRep p D.u s x := by
      rw [jointChemDivLateConstCutoff, if_pos hs,
        constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hx)]
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hx]
    have hLy : jointChemDivLateConstCutoff D a s y =
        conjugateMildMChemDivJointRep p D.u s y := by
      rw [jointChemDivLateConstCutoff, if_pos hs,
        constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hy)]
      simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
    rw [hLx, hLy]
    exact hraw s htaus hsT x hx y hy
  · simp only [jointChemDivLateConstCutoff, if_neg hs, sub_self, abs_zero]
    exact mul_nonneg hHQ (Real.rpow_nonneg (abs_nonneg _) _)

/-- On a time window lying strictly after `a`, the actual conjugate-kernel
Hessian splits into a nonsingular old conjugate history and a full-semigroup
history of the continuous physical divergence representative.  Every
adjacent-interval split below carries explicit integrability evidence. -/
private theorem conjugateMildM_chemHessian_decomposition_after
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a t x : ℝ} (ha : 0 < a) (hat : a < t) (htT : t < D.T)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (t - s)
          (jointChemFluxWindowCutoff D s) z) y) x) +
      ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (t - s)
          (jointChemDivLateConstCutoff D a s) z) y) x =
    ∫ s in (0 : ℝ)..t, deriv (fun y : ℝ ↦ deriv
      (fun z : ℝ ↦ intervalConjugateKernelOperator (t - s)
        (chemFluxMLifted p (D.u s)) z) y) x := by
  let Qc : ℝ → ℝ → ℝ := jointChemFluxWindowCutoff D
  let L : ℝ → ℝ → ℝ := jointChemDivLateConstCutoff D a
  let A : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) y) x
  let AO : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (t - s) (Qc s) z) y) x
  let AL : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) y) x
  have ht : 0 < t := ha.trans hat
  have hActualInt : IntervalIntegrable A volume 0 t := by
    simpa [A] using
      (conjugateMildM_chemDuhamel_secondDeriv_intervalIntegrable_Icc
        D hu₀_bound hu₀_meas ht htT.le hx)
  have hActualOld : IntervalIntegrable A volume 0 a :=
    hActualInt.mono_set (by
      rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc le_rfl hat.le)
  have hActualLate : IntervalIntegrable A volume a t :=
    hActualInt.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc ha.le le_rfl)
  have hOldEq : (∫ s in (0 : ℝ)..a, AO s) = ∫ s in (0 : ℝ)..a, A s := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le ha.le]
    filter_upwards with s hs
    have hsT : s ≤ D.T := hs.2.trans (hat.le.trans htT.le)
    have hQeq : Qc s = chemFluxMLifted p (D.u s) := by
      funext y
      simp [Qc, jointChemFluxWindowCutoff, hs.1, hsT]
    dsimp [AO, A]
    rw [hQeq]
  have hALearly : IntervalIntegrable AL volume 0 a := by
    have hzeroInt : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 a :=
      intervalIntegrable_const
    refine hzeroInt.congr_ae ?_
    rw [Set.uIoc_of_le ha.le]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro s hs
    symm
    have hsa : ¬ a < s := not_lt_of_ge hs.2
    have hLs : L s = fun _ : ℝ => 0 := by
      change jointChemDivLateConstCutoff D a s = fun _ : ℝ => 0
      funext y
      simp [jointChemDivLateConstCutoff, hsa]
    dsimp [AL]
    rw [hLs]
    simp [intervalFullSemigroupOperator]
  have hALeq : A =ᵐ[volume.restrict (Set.uIoc a t)] AL := by
    rw [Set.uIoc_of_le hat.le]
    change ∀ᵐ s ∂volume.restrict (Set.Ioc a t), A s = AL s
    refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne] with s hst_ne hs
    have hst : s < t := lt_of_le_of_ne hs.2 hst_ne
    have hs0 : 0 < s := ha.trans hs.1
    have hsT : s ≤ D.T := (hst.trans htT).le
    have hlag : 0 < t - s := sub_pos.mpr hst
    have hLrep : Set.EqOn (L s)
        (conjugateMildMChemDivJointRep p D.u s) (Set.Icc (0 : ℝ) 1) := by
      intro z hz
      change jointChemDivLateConstCutoff D a s z = _
      rw [jointChemDivLateConstCutoff,
        if_pos ⟨hs.1, hst.trans htT⟩, constExtend_eq_lift_on_Icc hz]
      simp [intervalDomainLift, hz]
    have hspace :
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) =
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) := by
      funext z
      have hSLrep :=
        ShenWork.Paper2.intervalFullSemigroupOperator_congr_on_Icc
          (t := t - s) hLrep z
      have hrawrep := jointIntervalFullSemigroupOperator_congr_on_Ioo
        (fun w hw => deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
          D hu₀_bound hu₀_meas hs0 hsT hw) (t - s) z
      have hIBP := conjugateMildM_intervalConjugateKernelOperator_eq_semigroup_fluxDeriv
        D hu₀_bound hu₀_meas hs0 hsT hlag (x := z)
      exact hSLrep.trans (hrawrep.symm.trans hIBP.symm)
    dsimp [A, AL]
    rw [hspace]
  have hALlate : IntervalIntegrable AL volume a t :=
    hActualLate.congr_ae hALeq
  have hLateEq : (∫ s in (0 : ℝ)..t, AL s) = ∫ s in a..t, A s := by
    rw [(intervalIntegral.integral_add_adjacent_intervals hALearly hALlate).symm]
    have hzero : (∫ s in (0 : ℝ)..a, AL s) = 0 := by
      calc
        _ = ∫ _s in (0 : ℝ)..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ha.le] at hs
          have hsa : ¬ a < s := not_lt_of_ge hs.2
          have hLs : L s = fun _ : ℝ => 0 := by
            change jointChemDivLateConstCutoff D a s = fun _ : ℝ => 0
            funext y
            simp [jointChemDivLateConstCutoff, hsa]
          dsimp [AL]
          rw [hLs]
          simp [intervalFullSemigroupOperator]
        _ = 0 := by simp
    rw [hzero, zero_add]
    apply intervalIntegral.integral_congr_ae
    rw [← ae_restrict_iff' measurableSet_uIoc]
    exact hALeq.symm
  have hActualSplit :
      (∫ s in (0 : ℝ)..a, A s) + ∫ s in a..t, A s =
        ∫ s in (0 : ℝ)..t, A s :=
    intervalIntegral.integral_add_adjacent_intervals hActualOld hActualLate
  change (∫ s in (0 : ℝ)..a, AO s) + ∫ s in (0 : ℝ)..t, AL s =
    ∫ s in (0 : ℝ)..t, A s
  rw [hOldEq, hLateEq]
  exact hActualSplit

/-- Joint continuity of the actual chemotaxis Hessian on any strip whose
lower endpoint is strictly positive. -/
private theorem conjugateMildM_chemDuhamel_secondDeriv_jointContinuousOn_after
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s)
          (chemFluxMLifted p (D.u s)) z) y) q.2)
      (Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let Qc : ℝ → ℝ → ℝ := jointChemFluxWindowCutoff D
  let L : ℝ → ℝ → ℝ := jointChemDivLateConstCutoff D a
  let S : Set (ℝ × ℝ) := Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1
  have hQc_meas : Measurable (Function.uncurry Qc) := by
    simpa [Qc] using jointChemFluxWindowCutoff_measurable D
  have hQc_cont : ∀ s, Continuous (Qc s) := by
    simpa [Qc] using jointChemFluxWindowCutoff_continuous D
  have hQc_int : ∀ s, Integrable (Qc s) (intervalMeasure 1) := by
    simpa [Qc] using jointChemFluxWindowCutoff_integrable D
  have hQc_bound : ∀ s y, |Qc s y| ≤ jointChemFluxBoundConst D := by
    simpa [Qc] using jointChemFluxWindowCutoff_bound D
  have hOldCont : ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s) (Qc s) z) y) q.2)
      S := by
    intro q hq
    have hbase :=
      intervalConjugateDuhamel_fixedHistory_secondDeriv_continuousWithinAt_joint
        ha.le hq.1.1 hQc_meas hQc_cont hQc_int hQc_bound hq.2
    exact hbase.mono (by
      intro z hz
      exact Set.mem_prod.mpr ⟨ha.trans hz.1.1, hz.2⟩)
  obtain ⟨CL, hCL, hLbound⟩ :=
    jointChemDivLateConstCutoff_bounded D hu₀_bound hu₀_meas ha
  have hLmeas : Measurable (Function.uncurry L) := by
    simpa [L] using jointChemDivLateConstCutoff_measurable
      D hu₀_bound hu₀_meas ha.le
  have hLcont : ∀ s, Continuous (L s) := by
    simpa [L] using jointChemDivLateConstCutoff_continuous
      D hu₀_bound hu₀_meas ha.le
  have hLint : ∀ s, Integrable (L s) (intervalMeasure 1) := by
    simpa [L] using jointChemDivLateConstCutoff_integrable
      D hu₀_bound hu₀_meas ha.le
  have hLholder : ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ D.T →
          ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |L s x - L s y| ≤ HQ * |x - y| ^ theta := by
    simpa [L] using
      (jointChemDivLateConstCutoff_positiveStripHolder
        D hu₀_bound hu₀_meas a)
  have hLateBase :=
    intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
      D.hT hLmeas hLcont hLint hLbound hLholder
  have hLateCont : ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (L s) z) y) q.2)
      S :=
    hLateBase.mono (by
      intro q hq
      exact Set.mem_prod.mpr ⟨⟨ha.trans hq.1.1, hq.1.2⟩, hq.2⟩)
  have hsum := hOldCont.add hLateCont
  refine hsum.congr ?_
  intro q hq
  simpa [Qc, L, S] using
    (conjugateMildM_chemHessian_decomposition_after
      D hu₀_bound hu₀_meas ha hq.1.1 hq.1.2 hq.2).symm

/-- The Hessian history of the faithful chemotaxis Duhamel leg is jointly
continuous at strict positive times, including both physical endpoints. -/
theorem conjugateMildM_chemDuhamel_secondDeriv_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalConjugateKernelOperator (q.1 - s)
          (chemFluxMLifted p (D.u s)) z) y) q.2)
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1
  intro q hq
  let a : ℝ := q.1 / 2
  have ha : 0 < a := by dsimp [a]; linarith [hq.1.1]
  have haq : a < q.1 := by dsimp [a]; linarith [hq.1.1]
  have hstrip := conjugateMildM_chemDuhamel_secondDeriv_jointContinuousOn_after
    D hu₀_bound hu₀_meas ha
  have hqstrip : q ∈ Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.mem_prod.mpr ⟨⟨haq, hq.1.2⟩, hq.2⟩
  have hwithin := hstrip q hqstrip
  have hnear0 : Set.Ioi a ×ˢ Set.univ ∈ nhds q :=
    prod_mem_nhds (Ioi_mem_nhds haq) univ_mem
  have hlocal : Set.Ioo a D.T ×ˢ Set.Icc (0 : ℝ) 1 ∈
      nhdsWithin q S := by
    have hinter := Filter.inter_mem (Filter.mem_inf_of_left hnear0)
      (self_mem_nhdsWithin (a := q) (s := S))
    refine Filter.mem_of_superset hinter ?_
    intro z hz
    exact Set.mem_prod.mpr ⟨⟨hz.1.1, hz.2.1.2⟩, hz.2.2⟩
  exact hwithin.mono_of_mem_nhdsWithin hlocal

/-! ## Faithful logistic Hessian -/

/-- The Hessian history of the faithful logistic Duhamel leg is jointly
continuous at strict positive times, including both physical endpoints. -/
theorem conjugateMildM_logisticDuhamel_secondDeriv_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (fun q : ℝ × ℝ ↦ ∫ s in (0 : ℝ)..q.1, deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s)
          (logisticLifted p (D.u s)) z) y) q.2)
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let F : ℝ → ℝ → ℝ := conjugateMildMLogisticConstCutoff D
  let CL : ℝ := D.M * (p.a + p.b * D.M ^ p.α)
  have hF_meas : Measurable (Function.uncurry F) := by
    simpa [F] using conjugateMildMLogisticConstCutoff_measurable D
  have hF_cont : ∀ s, Continuous (F s) := by
    simpa [F] using conjugateMildMLogisticConstCutoff_continuous D
  have hF_int : ∀ s, Integrable (F s) (intervalMeasure 1) := by
    simpa [F] using conjugateMildMLogisticConstCutoff_integrable D
  have hF_bound : ∀ s y, |F s y| ≤ CL := by
    simpa [F, CL] using conjugateMildMLogisticConstCutoff_bound D
  have hF_holder : ∀ tau, 0 < tau →
      ∃ theta HQ : ℝ, 0 < theta ∧ theta < 1 ∧ 0 ≤ HQ ∧
        ∀ s, tau ≤ s → s ≤ D.T →
          ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |F s x - F s y| ≤ HQ * |x - y| ^ theta := by
    intro tau htau
    obtain ⟨HQ, hHQ, hraw⟩ :=
      conjugateMildM_logisticLifted_positiveTime_holder_uniform
        D hu₀_bound hu₀_meas htau
    refine ⟨(1 / 4 : ℝ), HQ, by norm_num, by norm_num, hHQ, ?_⟩
    intro s htaus hsT x hx y hy
    have hs0 : 0 < s := htau.trans_le htaus
    have hxIcc := Set.Ioo_subset_Icc_self hx
    have hyIcc := Set.Ioo_subset_Icc_self hy
    have hFx : F s x = logisticLifted p (D.u s) x := by
      dsimp [F, conjugateMildMLogisticConstCutoff]
      rw [if_pos ⟨hs0, hsT⟩, constExtend_eq_lift_on_Icc hxIcc]
      rfl
    have hFy : F s y = logisticLifted p (D.u s) y := by
      dsimp [F, conjugateMildMLogisticConstCutoff]
      rw [if_pos ⟨hs0, hsT⟩, constExtend_eq_lift_on_Icc hyIcc]
      rfl
    rw [hFx, hFy]
    exact hraw s htaus hsT x hx y hy
  have hbase :=
    intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
      D.hT hF_meas hF_cont hF_int hF_bound hF_holder
  refine hbase.congr ?_
  intro q hq
  apply intervalIntegral.integral_congr_ae
  rw [Set.uIoc_of_le hq.1.1.le]
  filter_upwards with s hs
  have hsT : s ≤ D.T := hs.2.trans hq.1.2.le
  have hspace :
      (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s) (F s) z) =
      (fun z : ℝ ↦ intervalFullSemigroupOperator (q.1 - s)
        (logisticLifted p (D.u s)) z) := by
    funext z
    have hFs : F s =
        intervalDomainConstExtend (intervalLogisticSource p (D.u s)) := by
      funext y
      dsimp [F, conjugateMildMLogisticConstCutoff]
      rw [if_pos ⟨hs.1, hsT⟩]
    rw [hFs]
    exact semigroupOperator_constExtend_eq_lift
  rw [hspace]

/-! ## Closed-slab joint time derivative -/

/-- The faithful positive-time derivative representative is jointly
continuous in time and closed physical space.  Its construction uses only
the mild-solution data and the original datum's continuity, bound, and
measurability. -/
theorem conjugateMildMTimeDerivJointRep_jointContinuousOn
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry (conjugateMildMTimeDerivJointRep D))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) :=
    Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1
  have hinit : ContinuousOn
      (fun q : ℝ × ℝ ↦ deriv (fun y : ℝ ↦ deriv
        (fun z : ℝ ↦ intervalFullSemigroupOperator q.1
          (intervalDomainLift u₀) z) y) q.2) S := by
    apply (intervalFullSemigroupOperator_lift_secondDeriv_jointContinuousOn_Ioi_Icc
      hu₀_cont).mono
    intro q hq
    exact Set.mem_prod.mpr ⟨hq.1.1, hq.2⟩
  have hchemH :=
    conjugateMildM_chemDuhamel_secondDeriv_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hchemTrace :=
    conjugateMildMChemDivJointRep_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hlogH :=
    conjugateMildM_logisticDuhamel_secondDeriv_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hlogTrace :=
    conjugateMildM_logisticLifted_jointContinuousOn
      D hu₀_bound hu₀_meas
  have hchi : ContinuousOn (fun _ : ℝ × ℝ ↦ (-p.χ₀)) S :=
    continuousOn_const
  have hsum :=
    (hinit.add (hchi.mul (hchemH.add hchemTrace))).add
      (hlogH.add hlogTrace)
  simpa [S, conjugateMildMTimeDerivJointRep, Function.uncurry] using hsum

/-- The literal target-time derivative of the lifted faithful solution is
jointly continuous on the same closed spatial slab. -/
theorem conjugateMildM_intervalDomainLift_timeDeriv_jointContinuousOn_Icc
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1)) :
    ContinuousOn
      (Function.uncurry (fun t x ↦
        deriv (fun s : ℝ ↦ intervalDomainLift (D.u s) x) t))
      (Set.Ioo (0 : ℝ) D.T ×ˢ Set.Icc (0 : ℝ) 1) := by
  refine (conjugateMildMTimeDerivJointRep_jointContinuousOn
    D hu₀_cont hu₀_bound hu₀_meas).congr ?_
  intro q hq
  simpa [Function.uncurry] using
    (conjugateMildM_intervalDomainLift_hasDerivAt_time_Icc
      D hu₀_cont hu₀_bound hu₀_meas hq.1.1 hq.1.2 hq.2).deriv

section AxiomAudit

#print axioms intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Icc
#print axioms intervalFullSemigroupOperator_secondDeriv_jointContinuousOn_Ioi_Ioo
#print axioms intervalConjugateKernelOperator_secondDeriv_jointContinuousOn_Ioi_Ioo
#print axioms intervalFullDuhamel_secondDeriv_jointContinuousOn_of_positiveStripHolder
#print axioms conjugateMildM_chemDuhamel_secondDeriv_jointContinuousOn
#print axioms conjugateMildM_logisticDuhamel_secondDeriv_jointContinuousOn
#print axioms conjugateMildMTimeDerivJointRep_jointContinuousOn
#print axioms conjugateMildM_intervalDomainLift_timeDeriv_jointContinuousOn_Icc

end AxiomAudit

end ShenWork.Paper2
