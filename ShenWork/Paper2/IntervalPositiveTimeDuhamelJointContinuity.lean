import ShenWork.Paper2.IntervalChiNegTrajBanachFinal
import ShenWork.Paper2.IntervalChiNegValueOpCont

open MeasureTheory Set Filter Topology
open scoped Topology Interval

open ShenWork.IntervalDomain
  (intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel
   intervalNeumannFullKernelDerivSeries
   intervalNeumannFullKernelDerivSeries_joint_measurable)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator)
open ShenWork.IntervalConjugateKernelJointMeas
  (intervalConjugateKernelOperator_eq_neg_derivSeries_integral)
open ShenWork.Paper2.IntervalChiNegTrajBanachFinal
  (pref_bound derivSeries_abs_le derivSeries_jointCont)
open ShenWork.Paper2.IntervalChiNegValueOpCont
  (valueKernelBound valueKernelBound_nonneg fullKernel_le fullKernel_jointCont
   fullKernel_joint_measurable)

noncomputable section

namespace ShenWork.Paper2.PositiveTimeDuhamelJointContinuity

/-- Three-parameter conjugate-kernel continuity when the source family is only
jointly continuous at positive source times.  This is the natural interface for
Picard trajectories in this repository: their value at `t = 0` is defined to be
zero, while the positive-time trace approaches the initial datum. -/
theorem kernelOp_src_jointContinuousOn_positive
    {τ₀ T S : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2)
      ((Set.Icc τ₀ T ×ˢ Set.Ioo (0 : ℝ) S) ×ˢ Set.Icc 0 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  obtain ⟨M, hM0, hMbd⟩ := pref_bound (T := T) hτ₀
  have hCF : 0 ≤ CF := le_trans (abs_nonneg (F 0 0)) (hF_bound 0 0)
  set B : ℝ :=
    (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k : ℝ)) ^ 2 / (4 * (4 * T))))
      + (∑' k : ℤ, M * Real.exp (-(0 + 2 * (k : ℝ)) ^ 2 / (4 * (4 * T))))
    with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    refine add_nonneg ?_ ?_ <;>
      exact tsum_nonneg (fun k => mul_nonneg hM0 (Real.exp_pos _).le)
  have hrepr :
      (fun q : (ℝ × ℝ) × ℝ =>
        intervalConjugateKernelOperator q.1.1 (F q.1.2) q.2) =
      fun q : (ℝ × ℝ) × ℝ =>
        -∫ y, intervalNeumannFullKernelDerivSeries q.1.1 y q.2 * F q.1.2 y
          ∂ intervalMeasure 1 := by
    funext q
    exact intervalConjugateKernelOperator_eq_neg_derivSeries_integral
      q.1.1 (F q.1.2) q.2
  rw [hrepr]
  apply ContinuousOn.neg
  apply continuousOn_of_dominated (bound := fun _ : ℝ => B * CF)
  · intro q _hq
    have hm : Measurable
        (fun y : ℝ => intervalNeumannFullKernelDerivSeries q.1.1 y q.2) :=
      intervalNeumannFullKernelDerivSeries_joint_measurable.comp
        ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    exact hm.aestronglyMeasurable.mul (hF_int q.1.2).aestronglyMeasurable
  · intro q hq
    change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), _
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hqbox :
        (q.1.1, q.2) ∈ Set.Icc τ₀ T ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨hq.1.1, hq.2⟩
    have hDS := derivSeries_abs_le hτ₀ hM0 hMbd y hy (q.1.1, q.2) hqbox
    exact mul_le_mul hDS (hF_bound q.1.2 y) (abs_nonneg _) hBnn
  · exact integrable_const _
  · change ∀ᵐ y ∂ intervalMeasure 1,
      ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalNeumannFullKernelDerivSeries q.1.1 y q.2 * F q.1.2 y)
        ((Set.Icc τ₀ T ×ˢ Set.Ioo (0 : ℝ) S) ×ˢ Set.Icc 0 1)
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    apply ContinuousOn.mul
    · have hbase := derivSeries_jointCont hτ₀ hτ₀T y hy
      exact hbase.comp (continuousOn_fst.fst.prodMk continuousOn_snd) (by
        intro q hq
        exact ⟨hq.1.1, hq.2⟩)
    · exact hF_cont.comp
        (continuousOn_fst.snd.prodMk continuousOn_const) (by
          intro q hq
          exact ⟨hq.1.2, hy⟩)

/-- Value-semigroup analogue of
`kernelOp_src_jointContinuousOn_positive`. -/
theorem valueOp_src_jointContinuousOn_positive
    {τ₀ T S : ℝ} (hτ₀ : 0 < τ₀) (hτ₀T : τ₀ ≤ T)
    {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) S ×ˢ Set.Icc (0 : ℝ) 1))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF) :
    ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalFullSemigroupOperator q.1.1 (F q.1.2) q.2)
      ((Set.Icc τ₀ T ×ˢ Set.Ioo (0 : ℝ) S) ×ˢ Set.Icc 0 1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  have hCF : 0 ≤ CF := le_trans (abs_nonneg (F 0 0)) (hF_bound 0 0)
  apply continuousOn_of_dominated
    (bound := fun _ : ℝ => valueKernelBound τ₀ T * CF)
  · intro q _hq
    have hm : Measurable (fun y : ℝ =>
        intervalNeumannFullKernel q.1.1 q.2 y) :=
      fullKernel_joint_measurable.comp
        (f := fun y : ℝ => ((q.1.1, q.2), y))
        ((measurable_const.prodMk measurable_const).prodMk measurable_id)
    exact hm.aestronglyMeasurable.mul (hF_int q.1.2).aestronglyMeasurable
  · intro q hq
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hq1 : 0 < q.1.1 := lt_of_lt_of_le hτ₀ hq.1.1.1
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg
        (ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel_nonneg
          hq1 _ _)]
    exact mul_le_mul (fullKernel_le hτ₀ hτ₀T hq.1.1 hq.2 hy)
      (hF_bound q.1.2 y) (abs_nonneg _) (valueKernelBound_nonneg hτ₀)
  · exact integrable_const _
  · change ∀ᵐ y ∂ intervalMeasure 1,
      ContinuousOn (fun q : (ℝ × ℝ) × ℝ =>
        intervalNeumannFullKernel q.1.1 q.2 y * F q.1.2 y)
        ((Set.Icc τ₀ T ×ˢ Set.Ioo (0 : ℝ) S) ×ˢ Set.Icc 0 1)
    rw [intervalMeasure, ShenWork.IntervalDomain.intervalSet,
      MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    apply ContinuousOn.mul
    · have hbase := fullKernel_jointCont hτ₀ hτ₀T y hy
      exact hbase.comp (continuousOn_fst.fst.prodMk continuousOn_snd) (by
        intro q hq
        exact ⟨hq.1.1, hq.2⟩)
    · exact hF_cont.comp
        (continuousOn_fst.snd.prodMk continuousOn_const) (by
          intro q hq
          exact ⟨hq.1.2, hy⟩)

/-- Topological core of the positive-time Duhamel-leg argument.  At an interior
box point, both the kernel lag `τ(1-r)` and the sampled source time `τr` stay
strictly positive. -/
theorem rescaledLeg_interior_continuousAt_positive
    {t : ℝ} {F : ℝ → ℝ → ℝ}
    {Op : ℝ → (ℝ → ℝ) → ℝ → ℝ}
    (hsrc : ∀ τ₀ : ℝ, 0 < τ₀ → τ₀ ≤ t →
      ContinuousOn
        (fun q : (ℝ × ℝ) × ℝ => Op q.1.1 (F q.1.2) q.2)
        ((Set.Icc τ₀ t ×ˢ Set.Ioo (0 : ℝ) t) ×ˢ Set.Icc 0 1))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (z₀ : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint)
    (hz0 : 0 < z₀.1.1) :
    ContinuousAt
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * Op (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1) z₀ := by
  set τ₀ : ℝ := (z₀.1.1 / 4) * (1 - r) with hτ₀def
  have hτ₀pos : 0 < τ₀ := mul_pos (by linarith) (by linarith)
  have hτ₀t : τ₀ ≤ t := by
    calc
      τ₀ = (z₀.1.1 / 4) * (1 - r) := hτ₀def
      _ ≤ z₀.1.1 * 1 := by
        apply mul_le_mul (by linarith) (by linarith) (by linarith) z₀.1.2.1
      _ = z₀.1.1 := mul_one _
      _ ≤ t := z₀.1.2.2
  set g : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint → (ℝ × ℝ) × ℝ :=
    fun z => ((z.1.1 * (1 - r), z.1.1 * r), z.2.1) with hgdef
  have hg_cont : Continuous g := by
    rw [hgdef]
    fun_prop
  set S : Set ((ℝ × ℝ) × ℝ) :=
    (Set.Icc τ₀ t ×ˢ Set.Ioo (0 : ℝ) t) ×ˢ Set.Icc (0 : ℝ) 1 with hSdef
  have hKon : ContinuousOn
      (fun q : (ℝ × ℝ) × ℝ => Op q.1.1 (F q.1.2) q.2) S := by
    simpa [S] using hsrc τ₀ hτ₀pos hτ₀t
  have hsource₀ : z₀.1.1 * r ∈ Set.Ioo (0 : ℝ) t := by
    refine ⟨mul_pos hz0 hr0, ?_⟩
    exact (mul_lt_mul_of_pos_left hr1 hz0).trans_le (by simpa using z₀.1.2.2)
  have hmem₀ : g z₀ ∈ S := by
    refine ⟨⟨⟨?_, ?_⟩, hsource₀⟩, z₀.2.2⟩
    · rw [hτ₀def]
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    · calc
        z₀.1.1 * (1 - r) ≤ z₀.1.1 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) z₀.1.2.1
        _ = z₀.1.1 := mul_one _
        _ ≤ t := z₀.1.2.2
  have hnbhd : g ⁻¹' S ∈ 𝓝 z₀ := by
    have hopen : ∀ᶠ z in 𝓝 z₀, z₀.1.1 / 2 < z.1.1 := by
      have hc : Continuous
          (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint => z.1.1) := by
        fun_prop
      have hm : z₀ ∈ (fun z => z.1.1) ⁻¹' Set.Ioi (z₀.1.1 / 2) := by
        simp only [Set.mem_preimage, Set.mem_Ioi]
        linarith
      exact (hc.isOpen_preimage _ isOpen_Ioi).mem_nhds hm
    filter_upwards [hopen] with z hz
    have hzpos : 0 < z.1.1 := by linarith [hz0]
    have hsource : z.1.1 * r ∈ Set.Ioo (0 : ℝ) t := by
      refine ⟨mul_pos hzpos hr0, ?_⟩
      exact (mul_lt_mul_of_pos_left hr1 hzpos).trans_le (by simpa using z.1.2.2)
    refine ⟨⟨⟨?_, ?_⟩, hsource⟩, z.2.2⟩
    · rw [hτ₀def]
      have h1r : 0 ≤ 1 - r := by linarith
      calc
        z₀.1.1 / 4 * (1 - r) ≤ z₀.1.1 / 2 * (1 - r) :=
          mul_le_mul_of_nonneg_right (by linarith) h1r
        _ ≤ z.1.1 * (1 - r) :=
          mul_le_mul_of_nonneg_right (le_of_lt hz) h1r
    · calc
        z.1.1 * (1 - r) ≤ z.1.1 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) z.1.2.1
        _ = z.1.1 := mul_one _
        _ ≤ t := z.1.2.2
  have hKat : ContinuousAt
      (fun z => Op (g z).1.1 (F (g z).1.2) (g z).2) z₀ := by
    have h1 : ContinuousWithinAt
        (fun q : (ℝ × ℝ) × ℝ => Op q.1.1 (F q.1.2) q.2) S (g z₀) :=
      hKon _ hmem₀
    have h2 : ContinuousWithinAt g (g ⁻¹' S) z₀ := hg_cont.continuousWithinAt
    exact (h1.comp h2 (Set.mapsTo_preimage g S)).continuousAt hnbhd
  have hmul : ContinuousAt
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint => z.1.1) z₀ := by
    fun_prop
  have hfin : ContinuousAt
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * Op (g z).1.1 (F (g z).1.2) (g z).2) z₀ :=
    hmul.mul hKat
  have heq :
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * Op (g z).1.1 (F (g z).1.2) (g z).2) =
      fun z => z.1.1 * Op (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1 := by
    funext z
    rw [hgdef]
    congr 2
    ring
  rw [heq] at hfin
  exact hfin

/-- The rescaled singular conjugate leg is continuous on the whole time box
from source continuity only on the open positive-time slab. -/
theorem conjugateLeg_rescaled_continuous_positive
    {t : ℝ} {F : ℝ → ℝ → ℝ} {CF : ℝ}
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * intervalConjugateKernelOperator
          (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rcases eq_or_lt_of_le z₀.1.2.1 with hz0 | hz0
  · exact ShenWork.Paper2.IntervalChiNegTrajBanachFinal.boundary_contAt
      hF_int hF_bound hr1 z₀ hz0.symm
  · exact rescaledLeg_interior_continuousAt_positive
      (Op := intervalConjugateKernelOperator)
      (fun τ₀ hτ₀ hτ₀t =>
        kernelOp_src_jointContinuousOn_positive hτ₀ hτ₀t
          hF_cont hF_int hF_bound)
      hr0 hr1 z₀ hz0

/-- The singular conjugate Duhamel leg is jointly continuous on `[0,t]` even
when its source is only jointly continuous for positive source times. -/
theorem conjugateLeg_continuous_positive
    {t : ℝ} {F : ℝ → ℝ → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_meas : Measurable (Function.uncurry F))
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF) :
    Continuous
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        ∫ s in (0 : ℝ)..z.1.1,
          intervalConjugateKernelOperator (z.1.1 - s) (F s) z.2.1) :=
  ShenWork.Paper2.IntervalChiNegTrajBanachClose.conjugateLeg_continuous
    hCF hF_meas hF_int hF_bound (by
      have hne0 : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      have hne1 : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      filter_upwards [hne0, hne1] with r hr0 hr1 hr
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
      exact conjugateLeg_rescaled_continuous_positive hF_cont hF_int hF_bound
        hr.1 (lt_of_le_of_ne hr.2 hr1))

/-- The rescaled value leg has the same positive-source-time interface. -/
theorem valueLeg_rescaled_continuous_positive
    {t : ℝ} {F : ℝ → ℝ → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        z.1.1 * intervalFullSemigroupOperator
          (z.1.1 - z.1.1 * r) (F (z.1.1 * r)) z.2.1) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rcases eq_or_lt_of_le z₀.1.2.1 with hz0 | hz0
  · exact ShenWork.Paper2.IntervalChiNegValueOpCont.valueLeg_boundary_contAt
      hCF hF_bound hr1 z₀ hz0.symm
  · exact rescaledLeg_interior_continuousAt_positive
      (Op := intervalFullSemigroupOperator)
      (fun τ₀ hτ₀ hτ₀t =>
        valueOp_src_jointContinuousOn_positive hτ₀ hτ₀t
          hF_cont hF_int hF_bound)
      hr0 hr1 z₀ hz0

/-- The value Duhamel leg is jointly continuous on `[0,t]` from open-positive
source continuity. -/
theorem valueLeg_continuous_positive
    {t : ℝ} (ht0 : 0 ≤ t) {F : ℝ → ℝ → ℝ} {CF : ℝ} (hCF : 0 ≤ CF)
    (hF_meas : Measurable (Function.uncurry F))
    (hF_cont : ContinuousOn (Function.uncurry F)
      (Set.Ioo (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) 1))
    (hF_int : ∀ s, Integrable (F s) (intervalMeasure 1))
    (hF_bound : ∀ s y, |F s y| ≤ CF) :
    Continuous
      (fun z : ↥(Set.Icc (0 : ℝ) t) × intervalDomainPoint =>
        ∫ s in (0 : ℝ)..z.1.1,
          intervalFullSemigroupOperator (z.1.1 - s) (F s) z.2.1) :=
  ShenWork.Paper2.IntervalChiNegLegContinuity.logisticLeg_continuous_reduced
    ht0 hCF hF_meas hF_bound (by
      have hne0 : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      have hne1 : ∀ᵐ r : ℝ ∂volume, r ≠ 1 := by
        rw [MeasureTheory.ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      filter_upwards [hne0, hne1] with r hr0 hr1 hr
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
      exact valueLeg_rescaled_continuous_positive hCF hF_cont hF_int hF_bound
        hr.1 (lt_of_le_of_ne hr.2 hr1))

end ShenWork.Paper2.PositiveTimeDuhamelJointContinuity
