/-
  Direct target-time differentiation of the faithful chemotaxis Duhamel leg.

  The old history is kept in the original conjugate-kernel form, where the
  flux itself has a uniform bound.  Only a strictly positive late-time window
  is integrated by parts into the continuous representative of the physical
  flux derivative.  This avoids asserting a false bound for `Q_x` as time
  tends to zero.
-/
import ShenWork.Paper2.IntervalFullDuhamelTimeDerivativeHolder
import ShenWork.Paper2.IntervalDomainMConjugateMildChemDivJointContinuity
import ShenWork.Paper2.IntervalDomainMConjugateMildChemFluxC1
import ShenWork.Paper2.IntervalDomainMConjugateMildPositiveTimeC2
import ShenWork.Paper2.IntervalConjugateSemigroupTimeDerivative
import ShenWork.PDE.IntervalDomainContinuousExtension

open MeasureTheory Filter Set Topology
open scoped Topology

noncomputable section

namespace ShenWork.Paper2

open ShenWork.IntervalDomain
  (intervalDomainConstExtend intervalDomainLift intervalDomainPoint intervalMeasure
    constExtend_continuous constExtend_eq_lift_on_Icc)
open ShenWork.Paper2.IntervalDomainMConjugatePicardFloorInhabit
  (ConjugateMildSolutionDataM)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
  (chemFluxMLifted chemFluxMLifted_abs_le_of_pos_slice
   chemFluxMLifted_uncurry_measurable chemFluxMLifted_continuous_of_pos_slice)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicardThreshold
  (unitClip unitClip_continuous unitClip_of_mem)

private def chemFluxBoundConst
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) : ℝ :=
  D.M ^ p.m * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * D.M ^ p.γ)))

private theorem chemFluxBoundConst_nonneg
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    0 ≤ chemFluxBoundConst D := by
  unfold chemFluxBoundConst
  exact mul_nonneg (Real.rpow_nonneg D.hM.le _)
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))

private def chemFluxWindowCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) : ℝ → ℝ → ℝ :=
  fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxMLifted p (D.u s) y else 0

private theorem chemFluxWindowCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    Measurable (Function.uncurry (chemFluxWindowCutoff D)) := by
  have hbase := chemFluxMLifted_uncurry_measurable
    (p := p) (u := D.u) D.hmeas
  unfold chemFluxWindowCutoff
  refine Measurable.ite ?_ hbase measurable_const
  exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
    ((isClosed_Iic.preimage continuous_fst).measurableSet)

private theorem chemFluxWindowCutoff_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s y, |chemFluxWindowCutoff D s y| ≤ chemFluxBoundConst D := by
  intro s y
  unfold chemFluxWindowCutoff
  split_ifs with hs
  · exact chemFluxMLifted_abs_le_of_pos_slice p D.hc D.floor_le_bound
      (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
        (D.hcont s hs.1 hs.2) y
  · simpa using chemFluxBoundConst_nonneg D

private theorem chemFluxWindowCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s, Continuous (chemFluxWindowCutoff D s) := by
  intro s
  unfold chemFluxWindowCutoff
  split_ifs with hs
  · exact chemFluxMLifted_continuous_of_pos_slice p D.hc D.floor_le_bound
      (D.hbound s hs.1 hs.2) (D.hfloor s hs.1 hs.2)
        (D.hcont s hs.1 hs.2)
  · exact continuous_const

private theorem chemFluxWindowCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) :
    ∀ s, Integrable (chemFluxWindowCutoff D s) (intervalMeasure 1) := by
  intro s
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (chemFluxWindowCutoff_continuous D s).continuousOn.integrableOn_Icc

/-- The Neumann semigroup is insensitive to changing a source at the two
spatial endpoints. -/
private theorem intervalFullSemigroupOperator_congr_on_Ioo
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

/-- Constant spatial extension of the continuous physical `Q_x`
representative, used only after the strictly positive cutoff `a`. -/
private def chemDivLateConstCutoff
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀) (a : ℝ) : ℝ → ℝ → ℝ :=
  fun s y =>
    if a < s ∧ s < D.T then
      intervalDomainConstExtend
        (fun x : intervalDomainPoint =>
          conjugateMildMChemDivJointRep p D.u s x.1) y
    else 0

private theorem chemDivLateConstCutoff_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    Measurable (Function.uncurry (chemDivLateConstCutoff D a)) := by
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
  have hpiece : Function.uncurry (chemDivLateConstCutoff D a) =
      A.piecewise R (fun _ => 0) := by
    funext q
    by_cases hq : q ∈ A
    · rw [Set.piecewise_eq_of_mem _ _ _ hq]
      have hq' : a < q.1 ∧ q.1 < D.T := by simpa [A] using hq
      change (if a < q.1 ∧ q.1 < D.T then
          intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              conjugateMildMChemDivJointRep p D.u q.1 x.1) q.2 else 0) = _
      rw [if_pos hq', constExtend_eq_apply_unitClip]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hq]
      have hq' : ¬ (a < q.1 ∧ q.1 < D.T) := by simpa [A] using hq
      change (if a < q.1 ∧ q.1 < D.T then
          intervalDomainConstExtend
            (fun x : intervalDomainPoint =>
              conjugateMildMChemDivJointRep p D.u q.1 x.1) q.2 else 0) = 0
      rw [if_neg hq']
  rw [hpiece]
  exact ContinuousOn.measurable_piecewise hR continuousOn_const hA

private theorem chemDivLateConstCutoff_continuous
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ s, Continuous (chemDivLateConstCutoff D a s) := by
  intro s
  by_cases hs : a < s ∧ s < D.T
  · rw [show chemDivLateConstCutoff D a s =
        intervalDomainConstExtend
          (fun x : intervalDomainPoint =>
            conjugateMildMChemDivJointRep p D.u s x.1) by
      funext y
      simp [chemDivLateConstCutoff, hs]]
    apply constExtend_continuous
    have hslice : ContinuousOn
        (fun x : intervalDomainPoint =>
          conjugateMildMChemDivJointRep p D.u s x.1) Set.univ := by
      apply (conjugateMildMChemDivJointRep_jointContinuousOn
        D hu₀_bound hu₀_meas).comp
        (continuous_const.prodMk continuous_subtype_val).continuousOn
      intro x _hx
      exact Set.mem_prod.mpr ⟨⟨ha.trans_lt hs.1, hs.2⟩, x.2⟩
    simpa only [continuousOn_univ] using hslice
  · rw [show chemDivLateConstCutoff D a s = fun _ : ℝ => 0 by
      funext y
      simp [chemDivLateConstCutoff, hs]]
    exact continuous_const

private theorem chemDivLateConstCutoff_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ s, Integrable (chemDivLateConstCutoff D a s) (intervalMeasure 1) := by
  intro s
  simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
  exact (chemDivLateConstCutoff_continuous
    D hu₀_bound hu₀_meas ha s).continuousOn.integrableOn_Icc

private theorem chemDivLateConstCutoff_bounded
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s y, |chemDivLateConstCutoff D a s y| ≤ C := by
  obtain ⟨C, hC, hraw⟩ :=
    conjugateMildM_chemFlux_deriv_positiveTime_uniformBound
      D hu₀_bound hu₀_meas ha
  refine ⟨C, hC, ?_⟩
  intro s y
  by_cases hs : a < s ∧ s < D.T
  · rw [chemDivLateConstCutoff, if_pos hs, constExtend_eq_apply_unitClip]
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
  · rw [chemDivLateConstCutoff, if_neg hs, abs_zero]
    exact hC

private theorem chemDivLateConstCutoff_uniformTrace
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a t : ℝ} (hat : a < t) (ht : 0 < t) (htT : t < D.T) :
    TendstoUniformlyOn (chemDivLateConstCutoff D a)
      (chemDivLateConstCutoff D a t) (nhds t) (Set.Icc (0 : ℝ) 1) := by
  have hactual := conjugateMildMChemDivJointRep_uniformTrace
    D hu₀_bound hu₀_meas ht htT
  have hevent : ∀ᶠ s in nhds t,
      Set.EqOn (conjugateMildMChemDivJointRep p D.u s)
        (chemDivLateConstCutoff D a s) (Set.Icc (0 : ℝ) 1) := by
    filter_upwards [Ioo_mem_nhds hat htT] with s hs x hx
    have hcut : chemDivLateConstCutoff D a s x =
        conjugateMildMChemDivJointRep p D.u s x := by
      have hs' : a < s ∧ s < D.T := hs
      change (if a < s ∧ s < D.T then
        intervalDomainConstExtend
          (fun z : intervalDomainPoint =>
            conjugateMildMChemDivJointRep p D.u s z.1) x else 0) = _
      rw [if_pos hs', constExtend_eq_lift_on_Icc hx]
      simp [intervalDomainLift, hx]
    exact hcut.symm
  have hleft := hactual.congr hevent
  apply hleft.congr_right
  intro x hx
  have hcut : chemDivLateConstCutoff D a t x =
      conjugateMildMChemDivJointRep p D.u t x := by
    change (if a < t ∧ t < D.T then
      intervalDomainConstExtend
        (fun z : intervalDomainPoint =>
          conjugateMildMChemDivJointRep p D.u t z.1) x else 0) = _
    rw [if_pos ⟨hat, htT⟩, constExtend_eq_lift_on_Icc hx]
    simp [intervalDomainLift, hx]
  exact hcut.symm

private theorem chemDivLateConstCutoff_holder
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {a t eta H : ℝ} (ha : 0 < a) (hat2 : a < t / 2) (htT : t < D.T)
    (hholder : ∀ s, a ≤ s → s ≤ D.T →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |conjugateMildMChemDivJointRep p D.u s x -
          conjugateMildMChemDivJointRep p D.u s y| ≤
            H * |x - y| ^ eta) :
    ∀ s, t / 2 < s → s < t →
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ y ∈ Set.Ioo (0 : ℝ) 1,
        |chemDivLateConstCutoff D a s x -
          chemDivLateConstCutoff D a s y| ≤ H * |x - y| ^ eta := by
  intro s hts hst x hx y hy
  have has : a < s := hat2.trans hts
  have hsT : s < D.T := hst.trans htT
  have hcutx : chemDivLateConstCutoff D a s x =
      conjugateMildMChemDivJointRep p D.u s x := by
    rw [chemDivLateConstCutoff, if_pos ⟨has, hsT⟩,
      constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hx)]
    simp [intervalDomainLift, Set.Ioo_subset_Icc_self hx]
  have hcuty : chemDivLateConstCutoff D a s y =
      conjugateMildMChemDivJointRep p D.u s y := by
    rw [chemDivLateConstCutoff, if_pos ⟨has, hsT⟩,
      constExtend_eq_lift_on_Icc (Set.Ioo_subset_Icc_self hy)]
    simp [intervalDomainLift, Set.Ioo_subset_Icc_self hy]
  rw [hcutx, hcuty]
  exact hholder s has.le hsT.le x hx y hy

/-- Direct target-time derivative of the actual conjugate-kernel chemotaxis
Duhamel leg.  The source trace is the literal interior derivative of the
faithful chemotaxis flux. -/
theorem conjugateMildM_chemDuhamel_hasDerivAt_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildSolutionDataM p u₀)
    (hu₀_bound : ∀ y, |intervalDomainLift u₀ y| ≤ D.M)
    (hu₀_meas : AEStronglyMeasurable
      (intervalDomainLift u₀) (intervalMeasure 1))
    {t x : ℝ} (ht : 0 < t) (htT : t < D.T)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x)
      ((∫ s in (0 : ℝ)..t, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x) +
        deriv (chemFluxMLifted p (D.u t)) x) t := by
  let a : ℝ := t / 4
  let Qc : ℝ → ℝ → ℝ := chemFluxWindowCutoff D
  let L : ℝ → ℝ → ℝ := chemDivLateConstCutoff D a
  have ha : 0 < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  have hat2 : a < t / 2 := by dsimp [a]; linarith
  have haT : a ≤ D.T := (hat.le.trans htT.le)
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hQc_meas : Measurable (Function.uncurry Qc) := by
    simpa [Qc] using chemFluxWindowCutoff_measurable D
  have hQc_cont : ∀ s, Continuous (Qc s) := by
    simpa [Qc] using chemFluxWindowCutoff_continuous D
  have hQc_int : ∀ s, Integrable (Qc s) (intervalMeasure 1) := by
    simpa [Qc] using chemFluxWindowCutoff_integrable D
  have hQc_bound : ∀ s y, |Qc s y| ≤ chemFluxBoundConst D := by
    simpa [Qc] using chemFluxWindowCutoff_bound D
  have hOldBase := intervalConjugateDuhamel_fixedHistory_hasDerivAt_time
    (a := a) (t := t) ha.le hat (chemFluxBoundConst_nonneg D)
      hQc_meas hQc_cont hQc_int hQc_bound hxIcc
  have hOldEvent :
      (fun tau : ℝ => ∫ s in (0 : ℝ)..a,
        intervalConjugateKernelOperator (tau - s) (Qc s) x) =ᶠ[nhds t]
      (fun tau : ℝ => ∫ s in (0 : ℝ)..a,
        intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x) := by
    apply Filter.Eventually.of_forall
    intro tau
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le ha.le]
    filter_upwards with s hs
    have hsT : s ≤ D.T := hs.2.trans haT
    have hQeq : Qc s = chemFluxMLifted p (D.u s) := by
      funext y
      simp [Qc, chemFluxWindowCutoff, hs.1, hsT]
    rw [hQeq]
  have hOld := hOldBase.congr_of_eventuallyEq hOldEvent.symm
  have hIold :
      (∫ s in (0 : ℝ)..a, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s) (Qc s) z) y) x) =
      ∫ s in (0 : ℝ)..a, deriv (fun y : ℝ => deriv
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) y) x := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le ha.le]
    filter_upwards with s hs
    have hsT : s ≤ D.T := hs.2.trans haT
    have hQeq : Qc s = chemFluxMLifted p (D.u s) := by
      funext y
      simp [Qc, chemFluxWindowCutoff, hs.1, hsT]
    rw [hQeq]
  rw [hIold] at hOld
  obtain ⟨eta, H, heta0, heta1, hH, hrepHolder⟩ :=
    conjugateMildMChemDivJointRep_positiveTime_holder_uniform
      D hu₀_bound hu₀_meas ha
  obtain ⟨C, hC, hLbound⟩ :=
    chemDivLateConstCutoff_bounded D hu₀_bound hu₀_meas ha
  have hLmeas : Measurable (Function.uncurry L) := by
    simpa [L] using chemDivLateConstCutoff_measurable
      D hu₀_bound hu₀_meas ha.le
  have hLcont : ∀ s, Continuous (L s) := by
    simpa [L] using chemDivLateConstCutoff_continuous
      D hu₀_bound hu₀_meas ha.le
  have hLint : ∀ s, Integrable (L s) (intervalMeasure 1) := by
    simpa [L] using chemDivLateConstCutoff_integrable
      D hu₀_bound hu₀_meas ha.le
  have hLtrace : TendstoUniformlyOn L (L t) (nhds t)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [L] using chemDivLateConstCutoff_uniformTrace
      D hu₀_bound hu₀_meas hat ht htT
  have hLholder : ∀ s, t / 2 < s → s < t →
      ∀ z ∈ Set.Ioo (0 : ℝ) 1, ∀ w ∈ Set.Ioo (0 : ℝ) 1,
        |L s z - L s w| ≤ H * |z - w| ^ eta := by
    simpa [L] using chemDivLateConstCutoff_holder
      D hu₀_bound hu₀_meas ha hat2 htT hrepHolder
  have hLateBase := intervalFullDuhamel_hasDerivAt_time_of_uniform_trace_late_holder
    ht heta0 heta1 hC hH hLmeas hLcont hLint hLbound hLtrace hLholder hxIcc
  have hLateEvent :
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalFullSemigroupOperator (tau - s) (L s) x) =ᶠ[nhds t]
      (fun tau : ℝ => ∫ s in a..tau,
        intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x) := by
    filter_upwards [Ioo_mem_nhds hat htT] with tau htau
    have htau0 : 0 < tau := ha.trans htau.1
    have hV :=
      ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
        htau0 hLmeas hC hLbound x
    have hV0a := hV.mono_set (by
      rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le htau0.le]
      exact Set.Icc_subset_Icc le_rfl htau.1.le)
    have hVa := hV.mono_set (by
      rw [Set.uIcc_of_le htau.1.le, Set.uIcc_of_le htau0.le]
      exact Set.Icc_subset_Icc ha.le le_rfl)
    rw [(intervalIntegral.integral_add_adjacent_intervals hV0a hVa).symm]
    have hzero : (∫ s in (0 : ℝ)..a,
        intervalFullSemigroupOperator (tau - s) (L s) x) = 0 := by
      calc
        _ = ∫ _s in (0 : ℝ)..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ha.le] at hs
          have hsa : ¬ a < s := not_lt_of_ge hs.2
          have hLs : L s = fun _ : ℝ => 0 := by
            change chemDivLateConstCutoff D a s = fun _ : ℝ => 0
            funext y
            simp [chemDivLateConstCutoff, hsa]
          change intervalFullSemigroupOperator (tau - s) (L s) x = 0
          rw [hLs]
          simp [intervalFullSemigroupOperator]
        _ = 0 := by simp
    rw [hzero, zero_add]
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le htau.1.le]
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ tau := by
      rw [ae_iff]
      simp only [not_not, Set.setOf_eq_eq_singleton]
      exact Real.volume_singleton
    filter_upwards [hne] with s hstau hs
    have hst : s < tau := lt_of_le_of_ne hs.2 hstau
    have hs0 : 0 < s := ha.trans hs.1
    have hsT : s ≤ D.T := (hst.trans htau.2).le
    have hlag : 0 < tau - s := sub_pos.mpr hst
    have hLrep : Set.EqOn (L s)
        (conjugateMildMChemDivJointRep p D.u s) (Set.Icc (0 : ℝ) 1) := by
      intro z hz
      change chemDivLateConstCutoff D a s z = _
      rw [chemDivLateConstCutoff, if_pos ⟨hs.1, hst.trans htau.2⟩,
        constExtend_eq_lift_on_Icc hz]
      simp [intervalDomainLift, hz]
    have hSLrep :=
      ShenWork.Paper2.intervalFullSemigroupOperator_congr_on_Icc
        (t := tau - s) hLrep x
    have hrawrep := intervalFullSemigroupOperator_congr_on_Ioo
      (fun z hz => deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
        D hu₀_bound hu₀_meas hs0 hsT hz) (tau - s) x
    have hIBP := conjugateMildM_intervalConjugateKernelOperator_eq_semigroup_fluxDeriv
      D hu₀_bound hu₀_meas hs0 hsT hlag (x := x)
    exact hSLrep.trans (hrawrep.symm.trans hIBP.symm)
  have hLate := hLateBase.congr_of_eventuallyEq hLateEvent.symm
  have hActualInt :=
    conjugateMildM_chemDuhamel_secondDeriv_intervalIntegrable_interior
      D hu₀_bound hu₀_meas ht htT.le hx
  let A : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalConjugateKernelOperator (t - s)
      (chemFluxMLifted p (D.u s)) z) y) x
  let AL : ℝ → ℝ := fun s => deriv (fun y : ℝ => deriv
    (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) y) x
  have hActualInt' : IntervalIntegrable A volume 0 t := by
    simpa [A] using hActualInt
  have hActualOld : IntervalIntegrable A volume 0 a :=
    hActualInt'.mono_set (by
      rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc le_rfl hat.le)
  have hActualLate : IntervalIntegrable A volume a t :=
    hActualInt'.mono_set (by
      rw [Set.uIcc_of_le hat.le, Set.uIcc_of_le ht.le]
      exact Set.Icc_subset_Icc ha.le le_rfl)
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
      change chemDivLateConstCutoff D a s = fun _ : ℝ => 0
      funext y
      simp [chemDivLateConstCutoff, hsa]
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
    filter_upwards [hne] with s hst hs
    have hst' : s < t := lt_of_le_of_ne hs.2 hst
    have hs0 : 0 < s := ha.trans hs.1
    have hsT : s ≤ D.T := (hst'.trans htT).le
    have hlag : 0 < t - s := sub_pos.mpr hst'
    have hLrep : Set.EqOn (L s)
        (conjugateMildMChemDivJointRep p D.u s) (Set.Icc (0 : ℝ) 1) := by
      intro z hz
      change chemDivLateConstCutoff D a s z = _
      rw [chemDivLateConstCutoff,
        if_pos ⟨hs.1, hst'.trans htT⟩, constExtend_eq_lift_on_Icc hz]
      simp [intervalDomainLift, hz]
    have hspace :
        (fun z : ℝ => intervalFullSemigroupOperator (t - s) (L s) z) =
        (fun z : ℝ => intervalConjugateKernelOperator (t - s)
          (chemFluxMLifted p (D.u s)) z) := by
      funext z
      have hSLrep :=
        ShenWork.Paper2.intervalFullSemigroupOperator_congr_on_Icc
          (t := t - s) hLrep z
      have hrawrep := intervalFullSemigroupOperator_congr_on_Ioo
        (fun w hw => deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
          D hu₀_bound hu₀_meas hs0 hsT hw) (t - s) z
      have hIBP := conjugateMildM_intervalConjugateKernelOperator_eq_semigroup_fluxDeriv
        D hu₀_bound hu₀_meas hs0 hsT hlag (x := z)
      exact hSLrep.trans (hrawrep.symm.trans hIBP.symm)
    dsimp [A, AL]
    rw [hspace]
  have hALlate : IntervalIntegrable AL volume a t :=
    hActualLate.congr_ae hALeq
  have hILate : (∫ s in (0 : ℝ)..t, AL s) = ∫ s in a..t, A s := by
    rw [(intervalIntegral.integral_add_adjacent_intervals hALearly hALlate).symm]
    have hzero : (∫ s in (0 : ℝ)..a, AL s) = 0 := by
      calc
        _ = ∫ _s in (0 : ℝ)..a, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [Set.uIcc_of_le ha.le] at hs
          have hsa : ¬ a < s := not_lt_of_ge hs.2
          have hLs : L s = fun _ : ℝ => 0 := by
            change chemDivLateConstCutoff D a s = fun _ : ℝ => 0
            funext y
            simp [chemDivLateConstCutoff, hsa]
          dsimp [AL]
          rw [hLs]
          simp [intervalFullSemigroupOperator]
        _ = 0 := by simp
    rw [hzero, zero_add]
    apply intervalIntegral.integral_congr_ae
    rw [← ae_restrict_iff' measurableSet_uIoc]
    exact hALeq.symm
  have hTrace : L t x = deriv (chemFluxMLifted p (D.u t)) x := by
    change chemDivLateConstCutoff D a t x = _
    rw [chemDivLateConstCutoff, if_pos ⟨hat, htT⟩,
      constExtend_eq_lift_on_Icc hxIcc]
    simpa [intervalDomainLift, hxIcc] using
      (deriv_chemFluxMLifted_eq_conjugateMildMChemDivJointRep_interior
        D hu₀_bound hu₀_meas ht htT.le hx).symm
  change HasDerivAt _ ((∫ s in (0 : ℝ)..t, AL s) + L t x) t at hLate
  rw [hILate, hTrace] at hLate
  have hsum := hOld.add hLate
  have hsplitH :
      (∫ s in (0 : ℝ)..a, A s) + ∫ s in a..t, A s =
        ∫ s in (0 : ℝ)..t, A s :=
    intervalIntegral.integral_add_adjacent_intervals hActualOld hActualLate
  have hderivSum :
      ((∫ s in (0 : ℝ)..a, A s) +
        ((∫ s in a..t, A s) + deriv (chemFluxMLifted p (D.u t)) x)) =
      (∫ s in (0 : ℝ)..t, A s) + deriv (chemFluxMLifted p (D.u t)) x := by
    rw [← hsplitH]
    ring
  change HasDerivAt _
    ((∫ s in (0 : ℝ)..a, A s) +
      ((∫ s in a..t, A s) + deriv (chemFluxMLifted p (D.u t)) x)) t at hsum
  rw [hderivSum] at hsum
  have hsumEvent :
      (fun tau : ℝ =>
        (∫ s in (0 : ℝ)..a, intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x) +
        ∫ s in a..tau, intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x) =ᶠ[nhds t]
      (fun tau : ℝ => ∫ s in (0 : ℝ)..tau,
        intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x) := by
    filter_upwards [Ioo_mem_nhds hat htT] with tau htau
    have htau0 : 0 < tau := ha.trans htau.1
    have hwhole_cut :=
      ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
        htau0 (chemFluxBoundConst_nonneg D) hQc_meas hQc_int hQc_bound (x := x)
    have hwhole : IntervalIntegrable
        (fun s : ℝ => intervalConjugateKernelOperator (tau - s)
          (chemFluxMLifted p (D.u s)) x) volume 0 tau := by
      refine IntervalIntegrable.congr ?_ hwhole_cut
      intro s hs
      rw [Set.uIoc_of_le htau0.le] at hs
      have hsT : s ≤ D.T := hs.2.trans htau.2.le
      have hQeq : Qc s = chemFluxMLifted p (D.u s) := by
        funext y
        simp [Qc, chemFluxWindowCutoff, hs.1, hsT]
      change intervalConjugateKernelOperator (tau - s) (Qc s) x =
        intervalConjugateKernelOperator (tau - s) (chemFluxMLifted p (D.u s)) x
      rw [hQeq]
    have hleft := hwhole.mono_set (by
      rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le htau0.le]
      exact Set.Icc_subset_Icc le_rfl htau.1.le)
    have hright := hwhole.mono_set (by
      rw [Set.uIcc_of_le htau.1.le, Set.uIcc_of_le htau0.le]
      exact Set.Icc_subset_Icc ha.le le_rfl)
    exact intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hfinal := hsum.congr_of_eventuallyEq hsumEvent.symm
  simpa [A] using hfinal

end ShenWork.Paper2

#print axioms ShenWork.Paper2.conjugateMildM_chemDuhamel_hasDerivAt_time
