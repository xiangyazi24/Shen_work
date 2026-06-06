/-
  ShenWork/Paper2/IntervalMildPicardThreshold.lean

  **Threshold-uniform Picard existence time** (Q2 / hQuant core).

  `intervalMildSolution_exists_picard` (IntervalMildPicard.lean) chooses
  the Picard horizon `T₀` PER DATUM: the contraction target is
  `min 1 (inf u₀)`, because the crude mild-formulation positivity
  argument needs the Duhamel correction `A·√T + B·T` to stay below
  `inf u₀`.  Hence the horizon degenerates as `inf u₀ → 0` and no
  uniform δ(M) is obtained.

  This file re-runs the same construction with the quantifiers REORDERED:
  on the threshold class `{u₀ : |u₀| ≤ M_in, c ≤ u₀}` the constants
  `A(M), B(M)` and the contraction target `min 1 c` are datum-free, so
  ONE horizon `δ = δ(p, M_in, c) > 0` works for every datum in the
  class.  Output: `MildExistenceData p u₀` (hence
  `GradientMildSolutionData p u₀` via `gradientMildSolutionData_of_data`)
  with `D.T = δ`.

  The construction body is the proof of
  `intervalMildSolution_exists_picard` verbatim, with:
  * the datum bound `B` replaced by the class bound `M_in`
    (ball radius `M = 2·max M_in 1`);
  * `c_u₀ = sInf (range u₀)` replaced by the class threshold `c`
    (`hLift_lower` from `c ≤ u₀`, `hc_le_M` from `c ≤ u₀ x₀ ≤ M/2`);
  * the horizon `T₀` chosen ONCE before the datum is introduced.

  The file-private measurability lemmas of IntervalMildPicard.lean are
  copied verbatim (they are `private`, hence not importable).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildPicard
import ShenWork.PDE.IntervalSemigroupUniform

open MeasureTheory Set Filter
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalChemFluxLipschitz
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.IntervalMildPicardThreshold

/-! ## File-private measurability lemmas (verbatim copies)

These are `private` in IntervalMildPicard.lean and therefore not
importable; they are reproduced verbatim. -/

private theorem logisticLifted_joint_measurable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability u) :
    Measurable (fun q : ℝ × ℝ => logisticLifted p (u q.1) q.2) := by
  have h_rpow : Measurable (fun x : ℝ => x ^ p.α) := by fun_prop
  have hpow :
      Measurable (fun q : ℝ × ℝ =>
        (intervalDomainLift (u q.1) q.2) ^ p.α) :=
    h_rpow.comp hum
  have hpoly :
      Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift (u q.1) q.2 *
          (p.a - p.b * (intervalDomainLift (u q.1) q.2) ^ p.α)) :=
    hum.mul (measurable_const.sub (measurable_const.mul hpow))
  rw [show
      (fun q : ℝ × ℝ => logisticLifted p (u q.1) q.2) =
        fun q : ℝ × ℝ =>
          intervalDomainLift (u q.1) q.2 *
            (p.a - p.b * (intervalDomainLift (u q.1) q.2) ^ p.α) by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [logisticLifted, ShenWork.IntervalDomainExistence.intervalLogisticSource,
        intervalDomainLift, hy]
    · simp [logisticLifted, intervalDomainLift, hy]]
  exact hpoly

private theorem logisticLifted_time_cutoff_measurable
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (hum : HasJointMeasurability u) :
    Measurable
      (fun q : ℝ × ℝ =>
        if 0 < q.1 ∧ q.1 ≤ T then logisticLifted p (u q.1) q.2 else 0) := by
  have hsource : Measurable (fun q : ℝ × ℝ => logisticLifted p (u q.1) q.2) :=
    logisticLifted_joint_measurable hum
  refine Measurable.ite ?_ hsource measurable_const
  have htime :
      MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ T} := by
    exact (isOpen_Ioi.preimage continuous_fst).measurableSet.inter
      (isClosed_Iic.preimage continuous_fst).measurableSet
  exact htime

private theorem intervalDomainLift_measurable_of_continuous
    {f : intervalDomainPoint → ℝ} (hf : Continuous f) :
    Measurable (intervalDomainLift f) := by
  have hcont_on : ContinuousOn (intervalDomainLift f) (Set.Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift f) = f := by
      ext ⟨x, hx⟩
      change intervalDomainLift f x = f ⟨x, hx⟩
      rw [intervalDomainLift, dif_pos hx]
    rw [heq]
    exact hf
  have hpiece :
      (Set.Icc (0 : ℝ) 1).piecewise (intervalDomainLift f) (fun _ : ℝ => 0) =
        intervalDomainLift f := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      simp [intervalDomainLift, hx]
  rw [← hpiece]
  exact ContinuousOn.measurable_piecewise hcont_on continuousOn_const measurableSet_Icc

private theorem intervalNeumannFullKernel_joint_measurable :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      intervalNeumannFullKernel q.1.1 q.1.2 q.2) := by
  open ShenWork.IntervalNeumannFullKernel in
  set g : ℤ → (ℝ × ℝ) × ℝ → ℝ :=
    fun k q =>
      heatKernel q.1.1 (q.1.2 - q.2 + 2 * (k : ℝ)) +
        heatKernel q.1.1 (q.1.2 + q.2 + 2 * (k : ℝ)) with hg_def
  have hg_meas : ∀ k, Measurable (g k) := by
    intro k
    show Measurable (fun q : (ℝ × ℝ) × ℝ =>
      heatKernel q.1.1 (q.1.2 - q.2 + 2 * (k : ℝ)) +
        heatKernel q.1.1 (q.1.2 + q.2 + 2 * (k : ℝ)))
    unfold heatKernel
    fun_prop
  have hg_sum : ∀ q : (ℝ × ℝ) × ℝ, Summable (fun k : ℤ => g k q) := by
    intro q
    rcases lt_or_ge 0 q.1.1 with ht | ht
    · exact (latticeGaussianSummable ht (q.1.2 - q.2)).add
        (latticeGaussianSummable ht (q.1.2 + q.2))
    · have hzero : (fun k : ℤ => g k q) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        simp [hg_def, ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht]
      rw [hzero]
      exact summable_zero
  have hmeas := ShenWork.IntervalNeumannFullKernel.measurable_tsum_int_of_summable
    hg_meas hg_sum
  have hfun :
      (fun q : (ℝ × ℝ) × ℝ => intervalNeumannFullKernel q.1.1 q.1.2 q.2) =
        fun q : (ℝ × ℝ) × ℝ => ∑' k : ℤ, g k q := by
    funext q
    rfl
  rw [hfun]
  exact hmeas

private theorem intervalFullSemigroupOperator_joint_measurable
    {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun q : ℝ × ℝ => intervalFullSemigroupOperator q.1 f q.2) := by
  have hprod : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      intervalNeumannFullKernel q.1.1 q.1.2 q.2 * f q.2) :=
    intervalNeumannFullKernel_joint_measurable.mul (hf.comp measurable_snd)
  have hstrong : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      intervalNeumannFullKernel q.1.1 q.1.2 q.2 * f q.2) :=
    hprod.stronglyMeasurable
  have hI : StronglyMeasurable (fun q : ℝ × ℝ =>
      ∫ y, intervalNeumannFullKernel q.1 q.2 y * f y ∂ intervalMeasure 1) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := intervalMeasure 1) hstrong
  simpa [intervalFullSemigroupOperator] using hI.measurable

private theorem variable_interval_integral_measurable
    {G : (ℝ × ℝ) × ℝ → ℝ} (hG : Measurable G) :
    Measurable (fun q : ℝ × ℝ => ∫ s in (0 : ℝ)..q.1, G (q, s)) := by
  set A : Set ((ℝ × ℝ) × ℝ) := {r | 0 < r.2 ∧ r.2 ≤ r.1.1}
  set B : Set ((ℝ × ℝ) × ℝ) := {r | r.1.1 < r.2 ∧ r.2 ≤ 0}
  have hA : MeasurableSet A := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hB : MeasurableSet B := by
    exact (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  set IA : ℝ × ℝ → ℝ := fun q =>
    ∫ s : ℝ, A.indicator G (q, s) ∂volume
  set IB : ℝ × ℝ → ℝ := fun q =>
    ∫ s : ℝ, B.indicator G (q, s) ∂volume
  have hIA : Measurable IA := by
    have hstrong : StronglyMeasurable (fun r : (ℝ × ℝ) × ℝ => A.indicator G r) :=
      (hG.indicator hA).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := volume) hstrong).measurable
  have hIB : Measurable IB := by
    have hstrong : StronglyMeasurable (fun r : (ℝ × ℝ) × ℝ => B.indicator G r) :=
      (hG.indicator hB).stronglyMeasurable
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := volume) hstrong).measurable
  have h_eq :
      (fun q : ℝ × ℝ => ∫ s in (0 : ℝ)..q.1, G (q, s)) =
        fun q : ℝ × ℝ => if 0 ≤ q.1 then IA q else -IB q := by
    funext q
    by_cases ht : 0 ≤ q.1
    · simp only [if_pos ht]
      rw [intervalIntegral.integral_of_le ht, ← MeasureTheory.integral_indicator measurableSet_Ioc]
      congr
    · simp only [if_neg ht]
      have hqle : q.1 ≤ 0 := (not_le.mp ht).le
      rw [intervalIntegral.integral_of_ge hqle,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      congr
  rw [h_eq]
  exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
    hIA hIB.neg

private theorem intervalFullSemigroupOperator_s_param_joint_measurable
    {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun r : (ℝ × ℝ) × ℝ =>
      intervalFullSemigroupOperator (r.1.1 - r.2) (F r.2) r.1.2) := by
  have hprod : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      intervalNeumannFullKernel (q.1.1.1 - q.1.2) q.1.1.2 q.2 * F q.1.2 q.2) := by
    have hK : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
        intervalNeumannFullKernel (q.1.1.1 - q.1.2) q.1.1.2 q.2) :=
      intervalNeumannFullKernel_joint_measurable.comp
        (((measurable_fst.fst.fst.sub measurable_fst.snd).prodMk measurable_fst.fst.snd).prodMk
          measurable_snd)
    have hsrc : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ => F q.1.2 q.2) :=
      hF.comp (measurable_fst.snd.prodMk measurable_snd)
    exact hK.mul hsrc
  have hI : StronglyMeasurable (fun r : (ℝ × ℝ) × ℝ =>
      ∫ y, intervalNeumannFullKernel (r.1.1 - r.2) r.1.2 y * F r.2 y
        ∂ intervalMeasure 1) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := intervalMeasure 1) hprod.stronglyMeasurable
  simpa [intervalFullSemigroupOperator] using hI.measurable

private theorem intervalFullSemigroupOperator_hasDerivAt_fst_of_integrable
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ}
    (hf_int : Integrable f (intervalMeasure 1)) (x : ℝ) :
    HasDerivAt (fun z : ℝ => intervalFullSemigroupOperator t f z)
      (∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x * f y
        ∂(intervalMeasure 1)) x := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  set M : ℝ := ∑' k : ℤ,
    (ShenWork.IntervalNeumannFullKernel.heatGradWindowBound t x 2 k +
      ShenWork.IntervalNeumannFullKernel.heatGradWindowBound t x 2 k) with hM_def
  have hMnn : 0 ≤ M := by
    rw [hM_def]
    exact tsum_nonneg fun k => by
      unfold ShenWork.IntervalNeumannFullKernel.heatGradWindowBound
        ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
      positivity
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := x)
    (bound := fun y => M * ‖f y‖)
    (F := fun z y => intervalNeumannFullKernel t z y * f y)
    (F' := fun z y => deriv (fun z' : ℝ => intervalNeumannFullKernel t z' y) z * f y)
    (Metric.ball_mem_nhds x one_pos)
    ?hFmeas ?hFint ?hF'meas ?hbound ?hbdint ?hdiff).2
  case hFmeas =>
    exact Filter.Eventually.of_forall fun z => by
      have hcont :=
        ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd ht z
      exact (hcont.aestronglyMeasurable measurableSet_Icc).mul hf_int.aestronglyMeasurable
  case hFint =>
    obtain ⟨CK, hCK⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
        (ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd ht x)
    have hK_bound : ∀ᵐ y ∂(intervalMeasure 1),
        ‖intervalNeumannFullKernel t x y‖ ≤ CK := by
      change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ‖intervalNeumannFullKernel t x y‖ ≤ CK
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun y hy => hCK y hy
    have hcont :=
      ShenWork.IntervalNeumannFullKernel.continuousOn_intervalNeumannFullKernel_snd ht x
    exact hf_int.bdd_mul (hcont.aestronglyMeasurable measurableSet_Icc) hK_bound
  case hF'meas =>
    have hcont :=
      ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_fst ht x
    exact (hcont.aestronglyMeasurable measurableSet_Icc).mul hf_int.aestronglyMeasurable
  case hbound =>
    change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ z ∈ Metric.ball x 1,
        ‖deriv (fun z' : ℝ => intervalNeumannFullKernel t z' y) z * f y‖ ≤ M * ‖f y‖
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    refine Filter.Eventually.of_forall fun y hy z hz => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hz1 : |z - x| ≤ 1 := by
      rw [← Real.dist_eq]
      exact le_of_lt (Metric.mem_ball.mp hz)
    have hy1 : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact mul_le_mul_of_nonneg_right
      (ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalNeumannFullKernel_fst_le_const
        ht x hz1 hy1)
      (norm_nonneg (f y))
  case hbdint =>
    exact hf_int.norm.const_mul M
  case hdiff =>
    refine Filter.Eventually.of_forall fun y z _ => ?_
    have hderiv :=
      ShenWork.IntervalNeumannFullKernel.hasDerivAt_intervalNeumannFullKernel_fst ht z y
    simpa [hderiv.deriv] using hderiv.mul_const (f y)

private theorem continuousOn_deriv_intervalNeumannFullKernel_fst_in_x
    {t : ℝ} (ht : 0 < t) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (fun x : ℝ =>
      deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x)
      (Set.Icc (0 : ℝ) 1) := by
  have hcd := ShenWork.IntervalNeumannFullKernel.continuous_deriv_heatKernel ht
  have hfun :
      (fun x : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x) =
        fun x : ℝ =>
          (∑' k : ℤ,
            deriv (fun z : ℝ => heatKernel t z) (x - y + 2 * (k : ℝ))) +
          (∑' k : ℤ,
            deriv (fun z : ℝ => heatKernel t z) (x + y + 2 * (k : ℝ))) := by
    funext x
    exact (ShenWork.IntervalNeumannFullKernel.hasDerivAt_intervalNeumannFullKernel_fst
      ht x y).deriv
  rw [hfun]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (ShenWork.IntervalNeumannFullKernel.summable_heatGradWindowBound ht 0 1)
      (fun k x hx => ?_)
    rw [Real.norm_eq_abs]
    refine ShenWork.IntervalNeumannFullKernel.abs_deriv_heatKernel_le_windowShift
      ht 0 1 k ?_
    rw [show x - y + 2 * (k : ℝ) - (0 + 2 * (k : ℝ)) = x - y by ring]
    exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  · refine continuousOn_tsum (fun k => (hcd.comp (by fun_prop)).continuousOn)
      (ShenWork.IntervalNeumannFullKernel.summable_heatGradWindowBound ht 0 2)
      (fun k x hx => ?_)
    rw [Real.norm_eq_abs]
    refine ShenWork.IntervalNeumannFullKernel.abs_deriv_heatKernel_le_windowShift
      ht 0 2 k ?_
    rw [show x + y + 2 * (k : ℝ) - (0 + 2 * (k : ℝ)) = x + y by ring]
    exact abs_le.mpr ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩

private theorem intervalFullSemigroupOperator_deriv_continuous_of_bounded
    {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} {C : ℝ}
    (_hC : 0 ≤ C) (hf_bound : ∀ y, |f y| ≤ C)
    (hf_meas : AEStronglyMeasurable f (intervalMeasure 1)) :
    Continuous (fun x : intervalDomainPoint =>
      deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x.1) := by
  haveI : IsFiniteMeasure (intervalMeasure 1) :=
    ⟨ShenWork.IntervalDomain.intervalMeasure_univ_lt_top 1⟩
  set B : ℝ := ∑' k : ℤ,
    (ShenWork.IntervalNeumannFullKernel.heatGradWindowBound t 0 2 k +
      ShenWork.IntervalNeumannFullKernel.heatGradWindowBound t 0 2 k)
  have hB_nn : 0 ≤ B := by
    simp only [B]
    exact tsum_nonneg fun k => by
      unfold ShenWork.IntervalNeumannFullKernel.heatGradWindowBound
        ShenWork.IntervalNeumannFullKernel.heatGradPointwiseBound
      positivity
  have hcont_int :
      Continuous (fun x : intervalDomainPoint =>
        ∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1 * f y
          ∂(intervalMeasure 1)) := by
    refine MeasureTheory.continuous_of_dominated
      (μ := intervalMeasure 1)
      (F := fun x : intervalDomainPoint => fun y : ℝ =>
        deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1 * f y)
      (bound := fun _ : ℝ => B * C) ?hF_meas ?h_bound ?h_bound_int ?h_cont
    · intro x
      exact ((ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_fst
          ht x.1).aestronglyMeasurable measurableSet_Icc).mul hf_meas
    · intro x
      change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ‖deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1 * f y‖ ≤ B * C
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hx_abs : |x.1 - (0 : ℝ)| ≤ 1 :=
        abs_le.mpr ⟨by linarith [x.2.1], by linarith [x.2.2]⟩
      have hy_abs : |y| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hderiv_bound :
          |deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1| ≤ B := by
        simpa [B] using
          (ShenWork.IntervalNeumannFullKernel.abs_deriv_intervalNeumannFullKernel_fst_le_const
            (t := t) ht (0 : ℝ) (z := x.1) (y := y) hx_abs hy_abs)
      exact mul_le_mul hderiv_bound (hf_bound y) (abs_nonneg _) hB_nn
    · exact integrable_const _
    · change ∀ᵐ y ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        Continuous (fun x : intervalDomainPoint =>
          deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1 * f y)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      refine Filter.Eventually.of_forall fun y hy => ?_
      have hcx : Continuous (fun x : intervalDomainPoint =>
          deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1) := by
        change Continuous (Set.restrict (Set.Icc (0 : ℝ) 1)
          (fun x : ℝ => deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x))
        exact continuousOn_iff_continuous_restrict.mp
          (continuousOn_deriv_intervalNeumannFullKernel_fst_in_x ht hy)
      exact hcx.mul continuous_const
  have hrepr :
      (fun x : intervalDomainPoint =>
        deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x.1) =
        fun x : intervalDomainPoint =>
          ∫ y, deriv (fun z : ℝ => intervalNeumannFullKernel t z y) x.1 * f y
            ∂(intervalMeasure 1) := by
    funext x
    exact (ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
      (t := t) ht (f := f) hf_meas (Cf := C) hf_bound x.1).deriv
  rw [hrepr]
  exact hcont_int

private theorem intervalNeumannFullKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) (x y : ℝ) :
    intervalNeumannFullKernel t x y = 0 := by
  unfold intervalNeumannFullKernel
  have hzero : (fun k : ℤ =>
      heatKernel t (x - y + 2 * (k : ℝ)) +
        heatKernel t (x + y + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
    funext k
    rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht,
      ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos ht]
    simp
  rw [hzero, tsum_zero]

private theorem intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    intervalFullSemigroupOperator t f x = 0 := by
  unfold intervalFullSemigroupOperator
  have hzero : (fun y : ℝ => intervalNeumannFullKernel t x y * f y) =
      fun _ : ℝ => (0 : ℝ) := by
    funext y
    rw [intervalNeumannFullKernel_of_nonpos ht x y]
    simp
  rw [hzero]
  simp

private theorem deriv_intervalFullSemigroupOperator_eq_zero_of_nonpos
    {t : ℝ} (ht : t ≤ 0) (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun z : ℝ => intervalFullSemigroupOperator t f z) x = 0 := by
  have hfun : (fun z : ℝ => intervalFullSemigroupOperator t f z) = fun _ : ℝ => 0 := by
    funext z
    exact intervalFullSemigroupOperator_eq_zero_of_nonpos ht f z
  rw [hfun, deriv_const]

private def intervalNeumannFullKernelDerivSeries (τ x y : ℝ) : ℝ :=
  (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (x - y + 2 * (k : ℝ))) +
    (∑' k : ℤ, deriv (fun z : ℝ => heatKernel τ z) (x + y + 2 * (k : ℝ)))

private theorem intervalNeumannFullKernelDerivSeries_joint_measurable :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      intervalNeumannFullKernelDerivSeries q.1.1 q.1.2 q.2) := by
  set g₁ : ℤ → (ℝ × ℝ) × ℝ → ℝ :=
    fun k q => deriv (fun z : ℝ => heatKernel q.1.1 z)
      (q.1.2 - q.2 + 2 * (k : ℝ)) with hg₁_def
  set g₂ : ℤ → (ℝ × ℝ) × ℝ → ℝ :=
    fun k q => deriv (fun z : ℝ => heatKernel q.1.1 z)
      (q.1.2 + q.2 + 2 * (k : ℝ)) with hg₂_def
  have hg₁_meas : ∀ k, Measurable (g₁ k) := by
    intro k
    have heq : g₁ k =
        fun q : (ℝ × ℝ) × ℝ =>
          -((q.1.2 - q.2 + 2 * (k : ℝ)) / (2 * q.1.1)) *
            heatKernel q.1.1 (q.1.2 - q.2 + 2 * (k : ℝ)) := by
      funext q
      simp only [hg₁_def]
      exact ShenWork.IntervalNeumannFullKernel.deriv_heatKernel_global q.1.1
        (q.1.2 - q.2 + 2 * (k : ℝ))
    rw [heq]
    unfold heatKernel
    fun_prop
  have hg₂_meas : ∀ k, Measurable (g₂ k) := by
    intro k
    have heq : g₂ k =
        fun q : (ℝ × ℝ) × ℝ =>
          -((q.1.2 + q.2 + 2 * (k : ℝ)) / (2 * q.1.1)) *
            heatKernel q.1.1 (q.1.2 + q.2 + 2 * (k : ℝ)) := by
      funext q
      simp only [hg₂_def]
      exact ShenWork.IntervalNeumannFullKernel.deriv_heatKernel_global q.1.1
        (q.1.2 + q.2 + 2 * (k : ℝ))
    rw [heq]
    unfold heatKernel
    fun_prop
  have hsum_aux : ∀ (z : ℝ) (q : (ℝ × ℝ) × ℝ),
      Summable (fun k : ℤ => deriv (fun u : ℝ => heatKernel q.1.1 u)
        (z + 2 * (k : ℝ))) := by
    intro z q
    rcases lt_or_ge 0 q.1.1 with hτ | hτ
    · exact ShenWork.IntervalNeumannFullKernel.latticeGaussianGradSummable hτ z
    · have hz : (fun k : ℤ => deriv (fun u : ℝ => heatKernel q.1.1 u)
          (z + 2 * (k : ℝ))) = fun _ : ℤ => (0 : ℝ) := by
        funext k
        have hzero : (fun u : ℝ => heatKernel q.1.1 u) = fun _ : ℝ => (0 : ℝ) := by
          funext u
          exact ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos hτ u
        rw [hzero, deriv_const]
      rw [hz]
      exact summable_zero
  have hg₁_sum : ∀ q, Summable (fun k : ℤ => g₁ k q) :=
    fun q => hsum_aux (q.1.2 - q.2) q
  have hg₂_sum : ∀ q, Summable (fun k : ℤ => g₂ k q) :=
    fun q => hsum_aux (q.1.2 + q.2) q
  have hmeas := (ShenWork.IntervalNeumannFullKernel.measurable_tsum_int_of_summable
      hg₁_meas hg₁_sum).add
    (ShenWork.IntervalNeumannFullKernel.measurable_tsum_int_of_summable
      hg₂_meas hg₂_sum)
  simpa [intervalNeumannFullKernelDerivSeries, g₁, g₂] using hmeas

private theorem intervalFullSemigroupOperator_deriv_s_param_joint_measurable
    {F : ℝ → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun r : (ℝ × ℝ) × ℝ =>
      deriv (fun z : ℝ =>
        intervalFullSemigroupOperator (r.1.1 - r.2) (F r.2) z) r.1.2) := by
  classical
  set Kd : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    intervalNeumannFullKernelDerivSeries q.1.1 q.1.2 q.2
  have hKd : Measurable Kd := by
    simpa [Kd] using intervalNeumannFullKernelDerivSeries_joint_measurable
  set D : (ℝ × ℝ) × ℝ → ℝ := fun r =>
    ∫ y, Kd ((r.1.1 - r.2, r.1.2), y) * F r.2 y ∂(intervalMeasure 1)
  have hD : Measurable D := by
    have hprod : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
        Kd ((q.1.1.1 - q.1.2, q.1.1.2), q.2) * F q.1.2 q.2) := by
      have hK : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
          Kd ((q.1.1.1 - q.1.2, q.1.1.2), q.2)) :=
        hKd.comp
          (((measurable_fst.fst.fst.sub measurable_fst.snd).prodMk measurable_fst.fst.snd).prodMk
            measurable_snd)
      have hsrc : Measurable (fun q : ((ℝ × ℝ) × ℝ) × ℝ => F q.1.2 q.2) :=
        hF.comp (measurable_fst.snd.prodMk measurable_snd)
      exact hK.mul hsrc
    have hI : StronglyMeasurable (fun r : (ℝ × ℝ) × ℝ =>
        ∫ y, Kd ((r.1.1 - r.2, r.1.2), y) * F r.2 y ∂(intervalMeasure 1)) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right'
        (ν := intervalMeasure 1) hprod.stronglyMeasurable
    simpa [D] using hI.measurable
  have hIntSet : MeasurableSet {s : ℝ | Integrable (F s) (intervalMeasure 1)} :=
    measurableSet_integrable (ν := intervalMeasure 1) hF.stronglyMeasurable
  have hBranch : MeasurableSet {r : (ℝ × ℝ) × ℝ |
      0 < r.1.1 - r.2 ∧ Integrable (F r.2) (intervalMeasure 1)} := by
    exact (measurableSet_lt measurable_const (measurable_fst.fst.sub measurable_snd)).inter
      (hIntSet.preimage measurable_snd)
  have h_eq :
      (fun r : (ℝ × ℝ) × ℝ =>
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (r.1.1 - r.2) (F r.2) z) r.1.2) =
        fun r : (ℝ × ℝ) × ℝ =>
          if 0 < r.1.1 - r.2 ∧ Integrable (F r.2) (intervalMeasure 1) then D r else 0 := by
    funext r
    by_cases hτ : 0 < r.1.1 - r.2
    · by_cases hint : Integrable (F r.2) (intervalMeasure 1)
      · simp only [hτ, hint, true_and, if_true]
        have hderiv :=
          intervalFullSemigroupOperator_hasDerivAt_fst_of_integrable hτ hint r.1.2
        rw [hderiv.deriv]
        simp only [D]
        congr
        funext y
        have hKfun :
            deriv (fun z : ℝ => intervalNeumannFullKernel (r.1.1 - r.2) z y) r.1.2 =
              intervalNeumannFullKernelDerivSeries (r.1.1 - r.2) r.1.2 y := by
          simpa [intervalNeumannFullKernelDerivSeries] using
            (ShenWork.IntervalNeumannFullKernel.hasDerivAt_intervalNeumannFullKernel_fst
              hτ r.1.2 y).deriv
        rw [hKfun]
      · simp only [hτ, hint, and_false, if_false]
        exact ShenWork.IntervalDuhamelIntegrability.deriv_intervalFullSemigroupOperator_eq_zero_of_not_integrable
          hτ hint r.1.2
    · simp only [hτ, false_and, if_false]
      exact deriv_intervalFullSemigroupOperator_eq_zero_of_nonpos
        (not_lt.mp hτ) (F r.2) r.1.2
  rw [h_eq]
  exact Measurable.ite hBranch hD measurable_const

private theorem measurable_tsum_nat {α : Type*} [MeasurableSpace α]
    {f : ℕ → α → ℝ} (hf : ∀ n, Measurable (f n)) :
    Measurable (fun a : α => ∑' n : ℕ, f n a) := by
  classical
  let L := SummationFilter.unconditional ℕ
  set S : Finset ℕ → α → ℝ := fun s a => ∑ n ∈ s, f n a with hSdef
  have hS_meas : ∀ s, StronglyMeasurable (S s) := by
    intro s
    exact (Finset.measurable_sum _ (fun n _ => hf n)).stronglyMeasurable
  set C : Set α := {a | ∃ c : ℝ, Tendsto (fun s : Finset ℕ => S s a) L.filter (nhds c)}
    with hCdef
  have hC_meas : MeasurableSet C := by
    simpa [C] using MeasureTheory.StronglyMeasurable.measurableSet_exists_tendsto
      (l := L.filter) (f := S) hS_meas
  have hlim_meas : Measurable (fun a : α =>
      L.filter.limUnder (fun s : Finset ℕ => S s a)) := by
    exact (MeasureTheory.StronglyMeasurable.limUnder (l := L.filter) hS_meas).measurable
  have h_eq : (fun a : α => ∑' n : ℕ, f n a) =
      fun a : α => if a ∈ C then L.filter.limUnder (fun s : Finset ℕ => S s a) else 0 := by
    funext a
    by_cases ha : a ∈ C
    · simp only [ha, if_true]
      rcases ha with ⟨c, hc⟩
      have hsum : Summable (fun n : ℕ => f n a) := ⟨c, hc⟩
      exact hsum.hasSum.limUnder_eq.symm
    · simp only [ha, if_false]
      have hnot : ¬ Summable (fun n : ℕ => f n a) := by
        intro hs
        exact ha ⟨∑' n : ℕ, f n a, hs.hasSum⟩
      exact tsum_eq_zero_of_not_summable hnot
  rw [h_eq]
  exact Measurable.ite hC_meas hlim_meas measurable_const

private theorem intervalNeumannResolverSourceCoeff_time_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) (k : ℕ) :
    Measurable (fun s : ℝ => ShenWork.PDE.intervalNeumannResolverSourceCoeff p (w s) k) := by
  set src : ℝ → ℝ → ℂ :=
    fun s x => ((p.ν * intervalDomainLift (w s) x ^ p.γ : ℝ) : ℂ) with hsrc_def
  have hsrc_meas : Measurable (fun q : ℝ × ℝ => src q.1 q.2) := by
    have h_rpow : Measurable (fun x : ℝ => x ^ p.γ) := by fun_prop
    have hpow : Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift (w q.1) q.2 ^ p.γ) :=
      h_rpow.comp hum
    have hreal : Measurable (fun q : ℝ × ℝ =>
        p.ν * intervalDomainLift (w q.1) q.2 ^ p.γ) :=
      measurable_const.mul hpow
    exact Complex.continuous_ofReal.measurable.comp hreal
  have hraw : ∀ n : ℕ, Measurable (fun s : ℝ =>
      ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff (fun x : ℝ => src s x) n) := by
    intro n
    set F : ℝ × ℝ → ℂ :=
      fun q => (Real.cos ((n : ℝ) * Real.pi * q.2) : ℂ) * src q.1 q.2 with hF_def
    have hF : Measurable F := by
      have hcos : Measurable (fun q : ℝ × ℝ =>
          (Real.cos ((n : ℝ) * Real.pi * q.2) : ℂ)) := by
        fun_prop
      exact hcos.mul hsrc_meas
    have hI : StronglyMeasurable (fun s : ℝ =>
        ∫ x : ℝ, F (s, x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Ioc (0 : ℝ) 1)) hF.stronglyMeasurable
    have hfun : (fun s : ℝ =>
        ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
          (fun x : ℝ => src s x) n) =
        fun s : ℝ => ∫ x : ℝ, F (s, x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      funext s
      rw [ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff,
        intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    rw [hfun]
    exact hI.measurable
  have hcoeff_real : Measurable (fun s : ℝ =>
      ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
        (fun x : ℝ => src s x) k) := by
    by_cases hk : k = 0
    · subst k
      have hre : Measurable (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
            (fun x : ℝ => src s x) 0).re) :=
        Complex.continuous_re.measurable.comp (hraw 0)
      simpa [ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff] using hre
    · have hre : Measurable (fun s : ℝ =>
          (ShenWork.HeatKernelGradientEstimates.unitIntervalCosineRawCoeff
            (fun x : ℝ => src s x) k).re) :=
        Complex.continuous_re.measurable.comp (hraw k)
      simpa [ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff, hk] using
        (measurable_const.mul hre)
  have hcomplex : Measurable (fun s : ℝ =>
      ((ShenWork.HeatKernelGradientEstimates.unitIntervalNeumannCosineCoeff
        (fun x : ℝ => src s x) k : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hcoeff_real
  simpa [ShenWork.PDE.intervalNeumannResolverSourceCoeff, hsrc_def] using hcomplex

private theorem intervalNeumannResolverCoeff_re_time_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) (k : ℕ) :
    Measurable (fun s : ℝ => (ShenWork.PDE.intervalNeumannResolverCoeff p (w s) k).re) := by
  have hsource := intervalNeumannResolverSourceCoeff_time_measurable (p := p) (w := w) hum k
  have hcoeff : Measurable (fun s : ℝ =>
      ShenWork.PDE.intervalNeumannResolverCoeff p (w s) k) := by
    unfold ShenWork.PDE.intervalNeumannResolverCoeff
    unfold ShenWork.PDE.ResolventEstimate.shiftedNeumannResolventCoeff
    exact measurable_const.mul hsource
  exact Complex.continuous_re.measurable.comp hcoeff

private theorem intervalNeumannResolverR_lift_joint_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) :
    Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) := by
  have hseries : Measurable (fun q : ℝ × ℝ =>
      ∑' k : ℕ,
        (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re *
          unitIntervalCosineMode k q.2) := by
    refine measurable_tsum_nat ?_
    intro k
    have hcoeff : Measurable (fun q : ℝ × ℝ =>
        (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re) :=
      (intervalNeumannResolverCoeff_re_time_measurable (p := p) (w := w) hum k).comp
        measurable_fst
    have hmode : Measurable (fun q : ℝ × ℝ => unitIntervalCosineMode k q.2) := by
      unfold unitIntervalCosineMode
      fun_prop
    exact hcoeff.mul hmode
  have hfun : (fun q : ℝ × ℝ =>
      intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) =
      fun q : ℝ × ℝ =>
        if q.2 ∈ Set.Icc (0 : ℝ) 1 then
          ∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re *
              unitIntervalCosineMode k q.2
        else 0 := by
    funext q
    by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
    · simp [intervalDomainLift, ShenWork.PDE.intervalNeumannResolverR, hy]
    · simp [intervalDomainLift, hy]
  rw [hfun]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd) hseries measurable_const

private theorem resolverGradReal_joint_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) :
    Measurable (fun q : ℝ × ℝ => ShenWork.Paper2.resolverGradReal p (w q.1) q.2) := by
  unfold ShenWork.Paper2.resolverGradReal
  refine measurable_tsum_nat ?_
  intro k
  have hcoeff : Measurable (fun q : ℝ × ℝ =>
      (ShenWork.PDE.intervalNeumannResolverCoeff p (w q.1) k).re) :=
    (intervalNeumannResolverCoeff_re_time_measurable (p := p) (w := w) hum k).comp
      measurable_fst
  have hmode : Measurable (fun q : ℝ × ℝ =>
      -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * q.2)) := by
    fun_prop
  exact hcoeff.mul hmode

private theorem chemFluxLifted_joint_measurable
    {p : CM2Params} {w : ℝ → intervalDomainPoint → ℝ}
    (hum : HasJointMeasurability w) :
    Measurable (fun q : ℝ × ℝ => chemFluxLifted p (w q.1) q.2) := by
  have hR := intervalNeumannResolverR_lift_joint_measurable (p := p) (w := w) hum
  have hG := resolverGradReal_joint_measurable (p := p) (w := w) hum
  have hden_base : Measurable (fun q : ℝ × ℝ =>
      1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) :=
    measurable_const.add hR
  have h_rpow : Measurable (fun x : ℝ => x ^ p.β) := by fun_prop
  have hden : Measurable (fun q : ℝ × ℝ =>
      (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p (w q.1)) q.2) ^ p.β) :=
    h_rpow.comp hden_base
  have hnum : Measurable (fun q : ℝ × ℝ =>
      intervalDomainLift (w q.1) q.2 *
        ShenWork.Paper2.resolverGradReal p (w q.1) q.2) :=
    hum.mul hG
  simpa [chemFluxLifted] using hnum.div hden

private theorem chemFluxLifted_bound_of_ball
    (p : CM2Params) {M : ℝ} (hM_nonneg : 0 ≤ M)
    {w : intervalDomainPoint → ℝ}
    (hw_bound : ∀ x, |w x| ≤ M)
    (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_cont : Continuous w) :
    ∀ y : ℝ,
      |chemFluxLifted p w y| ≤
        M * (Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * (p.ν * M ^ p.γ))) := by
  intro y
  set C_RG := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))
  have hC_RG_nn : 0 ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM_nonneg _)))
  unfold chemFluxLifted
  by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
  · have hcont_on : ContinuousOn (intervalDomainLift w) (Set.Icc (0 : ℝ) 1) := by
      rw [continuousOn_iff_continuous_restrict]
      have : Set.restrict (Set.Icc (0 : ℝ) 1) (intervalDomainLift w) = w := by
        ext ⟨x, hx⟩
        simp [Set.restrict, intervalDomainLift, hx]
        rfl
      rw [this]
      exact hw_cont
    have hlb : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ intervalDomainLift w x := by
      intro x hx
      simp [intervalDomainLift, hx]
      exact hw_nonneg ⟨x, hx⟩
    have hub : ∀ x ∈ Set.Icc (0 : ℝ) 1, intervalDomainLift w x ≤ M := by
      intro x hx
      simp [intervalDomainLift, hx]
      exact (abs_le.mp (hw_bound ⟨x, hx⟩)).2
    have hgrad : |ShenWork.Paper2.resolverGradReal p w y| ≤ C_RG := by
      simpa [C_RG] using
        ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
          p hcont_on hlb hub hy
    have hlift : |intervalDomainLift w y| ≤ M := by
      simp [intervalDomainLift, hy]
      exact hw_bound ⟨y, hy⟩
    open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
        ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
        ShenWork.IntervalNeumannFullKernel ShenWork.IntervalResolverPositivity in
    have hR_nonneg_pt : 0 ≤ intervalNeumannResolverR p w ⟨y, hy⟩ := by
      have hcont_src : Continuous
          (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) :=
        continuous_const.mul (hw_cont.rpow_const (fun x ↦ Or.inr p.hγ.le))
      set clip : ℝ → intervalDomainPoint := fun x ↦
        ⟨max 0 (min x 1), le_max_left 0 _,
          max_le (by norm_num) (min_le_right x 1)⟩
      have hclip_cont : Continuous clip :=
        Continuous.subtype_mk
          (continuous_const.max (continuous_id.min continuous_const)) _
      set f : ℝ → ℝ :=
        (fun x : intervalDomainPoint ↦ p.ν * (w x) ^ p.γ) ∘ clip
      have hf_cont : Continuous f := hcont_src.comp hclip_cont
      have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
        mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nonneg _) _)
      have hf_coeff : ∀ k, cosineCoeffs f k =
          (intervalNeumannResolverSourceCoeff p w k).re := by
        intro k
        have hsrc_eq :
            (intervalNeumannResolverSourceCoeff p w k).re =
            cosineCoeffs (fun x ↦ p.ν * intervalDomainLift w x ^ p.γ) k := by
          simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
            Complex.ofReal_re]
        rw [hsrc_eq]
        exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
          simp only [f, Function.comp, clip]
          have hclip_eq : max 0 (min x 1) = x := by
            rw [min_eq_left hx.2, max_eq_right hx.1]
          simp only [hclip_eq, intervalDomainLift,
            dif_pos (Set.mem_Icc.mpr hx)]) k
      have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
        have h := resolverSourceCoeff_re_sq_summable_of_continuousOn p hcont_on
        simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero] at h
        exact h.congr (fun k ↦ by rw [hf_coeff])
      exact intervalNeumannResolverR_nonneg_of_nonneg_source
        hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
    have hR_lift_eq :
        intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y =
          ShenWork.PDE.intervalNeumannResolverR p w ⟨y, hy⟩ := by
      simp [intervalDomainLift, hy]
    have hden_ge_one :
        1 ≤ (1 + intervalDomainLift
          (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β := by
      rw [hR_lift_eq]
      exact Real.one_le_rpow (by linarith [hR_nonneg_pt]) p.hβ
    calc
      |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y /
          (1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β|
          = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| /
            |(1 + intervalDomainLift (ShenWork.PDE.intervalNeumannResolverR p w) y) ^ p.β| :=
            abs_div _ _
      _ ≤ |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          rwa [abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos
            (by rw [hR_lift_eq]; linarith [hR_nonneg_pt]) p.β))]
      _ = |intervalDomainLift w y * ShenWork.Paper2.resolverGradReal p w y| := by
          rw [div_one]
      _ ≤ |intervalDomainLift w y| * |ShenWork.Paper2.resolverGradReal p w y| :=
          le_of_eq (abs_mul _ _)
      _ ≤ M * C_RG := by
          exact mul_le_mul hlift hgrad (abs_nonneg _) hM_nonneg
      _ = M * (Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
              (2 * (p.ν * M ^ p.γ))) := by
          rfl
  · simp [intervalDomainLift, hy, zero_mul, abs_zero]
    exact mul_nonneg hM_nonneg hC_RG_nn


/-! ## The threshold-uniform existence theorem -/

set_option maxHeartbeats 1600000 in
/-- **Threshold-uniform Picard data**: one horizon `δ = δ(p, M_in, c) > 0`
for EVERY continuous datum with `|u₀| ≤ M_in` and `c ≤ u₀`.  The
contraction-rate and positivity constants depend only on the ball radius
`M = 2·max M_in 1` and the threshold `c`, so the
`exists_small_contraction_time_target` choice can be made before the
datum is introduced. -/
theorem thresholdMildExistenceData_exists (p : CM2Params)
    {M_in c : ℝ} (hM_in : 0 < M_in) (hc : 0 < c)
    (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ →
        (∀ x, |u₀ x| ≤ M_in) →
        (∀ x, c ≤ u₀ x) →
        ∃ D : MildExistenceData p u₀, D.T = δ := by
  set M := 2 * max M_in 1 with hMdef
  have hM : 0 < M := by positivity
  -- Extract PDE constants
  have hlog :=
    ShenWork.IntervalLogisticLipschitz.intervalLogisticReaction_lipschitz_on_bounded
      p hα_ge hM
  obtain ⟨C_L, hC_L_pos, hC_L_lip⟩ := hlog
  -- Logistic source sup bound: |L(w)(y)| ≤ C_L_val when |w| ≤ M
  set C_L_val := M * (p.a + p.b * M ^ p.α)
  have hC_L_val_nn : (0 : ℝ) ≤ C_L_val :=
    mul_nonneg hM.le (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  -- Uniform resolver-gradient bound (Atom B3, independent of w):
  -- |∂ₓR(w)(y)| ≤ C_RG := √(∑ₖ weight²) · 2νM^γ  for all w in the nonneg M-ball.
  set C_RG := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ))
  have hC_RG_nn : (0 : ℝ) ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
  -- Uniform flux sup bound: |chemFluxLifted p w y| ≤ C_Q_unif := M · C_RG
  -- Since (1+R)^β ≥ 1 (R ≥ 0) and |lift w| ≤ M, |∂ₓR| ≤ C_RG.
  set C_Q_unif := M * C_RG
  have hC_Q_unif_nn : (0 : ℝ) ≤ C_Q_unif := mul_nonneg hM.le hC_RG_nn
  -- Resolver value weight (for value Lipschitz in Atom B4)
  set C_RV := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
    (2 * (p.ν * (p.γ * M ^ (p.γ - 1))))
  have hC_RV_nn : (0 : ℝ) ≤ C_RV :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_nonneg p.hν.le (mul_nonneg p.hγ.le (Real.rpow_nonneg hM.le _))))
  -- Resolver gradient Lipschitz constant (Atom B4 gradient diff)
  set C_RGL := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * (p.γ * M ^ (p.γ - 1))))
  have hC_RGL_nn : (0 : ℝ) ≤ C_RGL :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_nonneg p.hν.le (mul_nonneg p.hγ.le (Real.rpow_nonneg hM.le _))))
  -- Flux Lipschitz constant from chemFlux_div_lipschitz:
  -- |Q(u)(y) - Q(w)(y)| ≤ C_Q_lip · d where
  -- C_Q_lip = B_G + M·L_G + M·B_G·β·L_R (B_G=C_RG, L_G=C_RGL, L_R=C_RV)
  set C_Q_lip := C_RG + M * C_RGL + M * C_RG * p.β * C_RV
  have hC_Q_lip_nn : (0 : ℝ) ≤ C_Q_lip :=
    add_nonneg (add_nonneg hC_RG_nn (mul_nonneg hM.le hC_RGL_nn))
      (mul_nonneg (mul_nonneg (mul_nonneg hM.le hC_RG_nn) p.hβ) hC_RV_nn)
  -- Heat gradient L∞→L∞ constant
  set C_grad := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hC_grad_nn : (0 : ℝ) ≤ C_grad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  -- Choose T₀: A·√T₀ + B·T₀ < 1. A uses max(C_Q_unif, C_Q_lip) to cover
  -- both mapsTo (sup bound C_Q_unif) and contraction (Lipschitz C_Q_lip).
  set C_Q_max := max C_Q_unif C_Q_lip
  have hC_Q_max_nn : (0 : ℝ) ≤ C_Q_max := le_max_of_le_left hC_Q_unif_nn
  set A_picard := 2 * |p.χ₀| * C_grad * C_Q_max + C_L + 1
  set B_picard := C_L_val + C_L + 1
  have hA_nn : (0 : ℝ) ≤ A_picard := by positivity
  have hB_nn : (0 : ℝ) ≤ B_picard := by positivity
  -- Uniform contraction horizon: A·√T₀ + B·T₀ < min(1, c), datum-free.
  obtain ⟨T₀, hT₀, hK_lt_min⟩ :=
    exists_small_contraction_time_target hA_nn hB_nn (lt_min one_pos hc)
  have hK_lt : A_picard * Real.sqrt T₀ + B_picard * T₀ < 1 :=
    lt_of_lt_of_le hK_lt_min (min_le_left 1 c)
  have hcorr_lt_c : A_picard * Real.sqrt T₀ + B_picard * T₀ < c :=
    lt_of_lt_of_le hK_lt_min (min_le_right 1 c)
  have hM_ge_2 : (2 : ℝ) ≤ M := by
    have : (1 : ℝ) ≤ max M_in 1 := le_max_right M_in 1
    simp only [hMdef]; linarith
  refine ⟨T₀, hT₀, ?_⟩
  intro u₀ hu₀_cont hu₀_bound hu₀_lb
  have hu₀_nonneg : ∀ x, 0 ≤ u₀ x := fun x => le_trans hc.le (hu₀_lb x)
  have hB_le : ∀ x, |u₀ x| ≤ M / 2 := by
    intro x
    calc |u₀ x| ≤ M_in := hu₀_bound x
      _ ≤ max M_in 1 := le_max_left M_in 1
      _ = M / 2 := by rw [hMdef]; ring
  have hbase_ball : ∀ T : ℝ, ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ 0 t x| ≤ M := by
    intro T t ht _htT x
    exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound ht
      (by linarith : (0:ℝ) ≤ M)
      (fun y => by
        calc |intervalDomainLift u₀ y|
            ≤ M / 2 := by
              unfold intervalDomainLift
              split_ifs with hy
              · exact hB_le ⟨y, hy⟩
              · simp; linarith
            _ ≤ M := by linarith) x.1
  -- Step 1b: hbase_nonneg — S(t)u₀ ≥ 0 by semigroup positivity
  have hLift_nonneg : ∀ y, 0 ≤ intervalDomainLift u₀ y := by
    intro y; unfold intervalDomainLift; split_ifs with hy
    · exact hu₀_nonneg ⟨y, hy⟩
    · simp
  have hbase_nonneg : ∀ T : ℝ, ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ 0 t x := by
    intro T t ht _htT x
    exact ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg ht
      hLift_nonneg x.1
  -- The core mapsTo inequality:
  -- |χ₀|·C_grad·2√T₀·C_Q_unif + T₀·C_L_val ≤ A·√T₀ + B·T₀ < 1 ≤ M/2
  -- (C_Q_unif ≤ C_Q_lip since C_Q_lip = C_RG + M·C_RGL + M·C_RG·β·C_RV ≥ C_RG
  --  and C_Q_unif = M·C_RG, so we bound via C_Q_unif ≤ C_Q_lip when possible,
  --  or directly via A_picard which absorbs both)
  have hcorrection_le : |p.χ₀| * C_grad * (2 * Real.sqrt T₀) * C_Q_unif
      + T₀ * C_L_val ≤ M / 2 := by
    have hle : C_Q_unif ≤ C_Q_max := le_max_left _ _
    have h1 : 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀
        ≤ A_picard * Real.sqrt T₀ := by
      gcongr
      calc 2 * |p.χ₀| * C_grad * C_Q_unif
          ≤ 2 * |p.χ₀| * C_grad * C_Q_max := by
            gcongr
        _ ≤ A_picard := by simp only [A_picard]; linarith [hC_L_pos.le]
    have h2 : C_L_val * T₀ ≤ B_picard * T₀ := by
      gcongr; linarith [hC_L_pos.le]
    calc |p.χ₀| * C_grad * (2 * Real.sqrt T₀) * C_Q_unif + T₀ * C_L_val
        = 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀ + C_L_val * T₀ := by ring
      _ ≤ A_picard * Real.sqrt T₀ + B_picard * T₀ := add_le_add h1 h2
      _ ≤ 1 := hK_lt.le
      _ ≤ M / 2 := by linarith
  -- Helper: lift of u₀ bounded and measurable
  have hLift_le : ∀ y, |intervalDomainLift u₀ y| ≤ M / 2 := by
    intro y; unfold intervalDomainLift; split_ifs with hy
    · exact hB_le ⟨y, hy⟩
    · simp; linarith
  have hLift_le_M : ∀ y, |intervalDomainLift u₀ y| ≤ M :=
    fun y => (hLift_le y).trans (by linarith)
  have hLift_meas :=
    ShenWork.IntervalDuhamelIntegrability.intervalDomainLift_aestronglyMeasurable_of_continuous
      hu₀_cont
  -- Helper: semigroup of u₀ continuous (for subtype)
  have hSg_cont : ∀ t, 0 < t → Continuous
      (fun x : intervalDomainPoint =>
        intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1) := by
    intro t ht
    exact (ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
        ht (by linarith : (0:ℝ) ≤ M) hLift_le_M
        hLift_meas).comp continuous_subtype_val
  -- Extract hmapsTo proof so it can be reused in hbase_diff
  have hmapsTo_proof : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T₀ → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T₀ w →
      ∀ t, 0 < t → t ≤ T₀ → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ w t x| ≤ M := by
    /- GOAL: ∀ w bounded nonneg continuous on (0,T₀], |Φ(u₀,w)(t,x)| ≤ M.
       Strategy: |S(t)u₀| ≤ M/2 + correction ≤ M/2.
       The Duhamel universal bounds need source bounds ∀ s y. The trajectory
       w is only bounded for s > 0. We bridge this by replacing the source
       with an extended version (= original for 0 < s ≤ T₀, = 0 otherwise)
       using integral_congr_ae (they agree on the open interval (0,t]). -/
    intro w hw_bound hw_nonneg hw_cont t ht htT x
    unfold intervalGradientDuhamelMap
    have hterm1 :
        |intervalFullSemigroupOperator t
          (intervalDomainLift u₀) x.1| ≤ M / 2 :=
      ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
        ht (by linarith : (0:ℝ) ≤ M / 2) hLift_le x.1
    -- Extended logistic source: agrees with original on (0,T₀], = 0 otherwise
    set r_val : ℝ → ℝ → ℝ := fun s y =>
      if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
    -- r_val is uniformly bounded by C_L_val
    -- r_val is uniformly bounded by C_L_val
    -- For 0 < s ≤ T₀: |w s| ≤ M by hw_bound, so |logistic(w s)(y)| ≤ M·(a+b·M^α).
    -- For other s: r_val = 0 ≤ C_L_val.
    have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L_val := by
      intro s y; simp only [r_val]
      split_ifs with h
      · -- 0 < s ∧ s ≤ T₀: logistic source bounded
        -- Uses: |w s x| ≤ M and |x·(a-b·x^α)| ≤ M·(a+b·M^α) on [-M,M]
        have hws := hw_bound s h.1 h.2
        exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound p hM
          (fun x => hws x) y
      · simp; exact hC_L_val_nn
    -- Integral equality: original = extended (agree on (0,t] ⊃ Ι 0 t)
    have hval_eq : (∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
        = ∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s) (r_val s) x.1 := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro s hs
      -- s ∈ Ι 0 t = Set.uIoc 0 t. Since 0 < t, this is Ioc 0 t, so 0 < s ≤ t.
      rw [Set.uIoc_of_le ht.le] at hs
      simp only [r_val, if_pos (And.intro hs.1 (hs.2.trans htT))]
    -- Extended flux source
    set r_grad : ℝ → ℝ → ℝ := fun s y =>
      if 0 < s ∧ s ≤ T₀ then chemFluxLifted p (w s) y else 0
    -- r_grad is uniformly bounded by C_Q_unif
    -- SORRY: the proof needs (1+R)^β ≥ 1 (from R ≥ 0 via resolver positivity)
    -- and |∂ₓR(w s)| ≤ C_RG (from resolverGrad_sup_le_of_bounded).
    -- Both are available but the resolver positivity setup is ~30 lines.
    have hr_grad_bound : ∀ s y, |r_grad s y| ≤ C_Q_unif := by
      intro s y; simp only [r_grad]
      split_ifs with h
      · -- |chemFluxLifted p (w s) y| ≤ C_Q_unif = M * C_RG
        unfold chemFluxLifted
        by_cases hy : y ∈ Set.Icc (0:ℝ) 1
        · -- y in [0,1]: bound each factor
          have hw_s := hw_bound s h.1 h.2
          have hw_nn_s := hw_nonneg s h.1 h.2
          have hw_cont_s := hw_cont s h.1 h.2
          have hcont_on : ContinuousOn (intervalDomainLift (w s)) (Set.Icc (0:ℝ) 1) := by
            rw [continuousOn_iff_continuous_restrict]
            have : Set.restrict (Set.Icc (0:ℝ) 1) (intervalDomainLift (w s)) = w s := by
              ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
            rw [this]; exact hw_cont_s
          have hlb : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ intervalDomainLift (w s) x := by
            intro x hx; simp [intervalDomainLift, hx]; exact hw_nn_s ⟨x, hx⟩
          have hub : ∀ x ∈ Set.Icc (0:ℝ) 1, intervalDomainLift (w s) x ≤ M := by
            intro x hx; simp [intervalDomainLift, hx]
            exact (abs_le.mp (hw_s ⟨x, hx⟩)).2
          -- |resolverGrad| ≤ C_RG
          have hgrad := ShenWork.IntervalResolverWeakBounds.resolverGrad_sup_le_of_bounded
            p hcont_on hlb hub hy
          -- |lift w| ≤ M
          have hlift : |intervalDomainLift (w s) y| ≤ M := by
            simp [intervalDomainLift, hy]; exact hw_s ⟨y, hy⟩
          -- R ≥ 0 on the subtype (resolver positivity)
          open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
              ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
              ShenWork.IntervalNeumannFullKernel ShenWork.IntervalResolverPositivity in
          have hR_nonneg_pt : 0 ≤ intervalNeumannResolverR p (w s) ⟨y, hy⟩ := by
            have hcont_src : Continuous
                (fun x : intervalDomainPoint ↦ p.ν * (w s x) ^ p.γ) :=
              continuous_const.mul (hw_cont_s.rpow_const (fun x ↦ Or.inr p.hγ.le))
            set clip : ℝ → intervalDomainPoint := fun x ↦
              ⟨max 0 (min x 1), le_max_left 0 _,
                max_le (by norm_num) (min_le_right x 1)⟩
            have hclip_cont : Continuous clip :=
              Continuous.subtype_mk
                (continuous_const.max (continuous_id.min continuous_const)) _
            set f : ℝ → ℝ :=
              (fun x : intervalDomainPoint ↦ p.ν * (w s x) ^ p.γ) ∘ clip
            have hf_cont : Continuous f := hcont_src.comp hclip_cont
            have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
              mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nn_s _) _)
            have hf_coeff : ∀ k, cosineCoeffs f k =
                (intervalNeumannResolverSourceCoeff p (w s) k).re := by
              intro k
              have hsrc_eq :
                  (intervalNeumannResolverSourceCoeff p (w s) k).re =
                  cosineCoeffs (fun x ↦ p.ν * intervalDomainLift (w s) x ^ p.γ) k := by
                simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
                  Complex.ofReal_re]
              rw [hsrc_eq]
              exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
                simp only [f, Function.comp, clip]
                have hclip_eq : max 0 (min x 1) = x := by
                  rw [min_eq_left hx.2, max_eq_right hx.1]
                simp only [hclip_eq, intervalDomainLift,
                  dif_pos (Set.mem_Icc.mpr hx)]) k
            have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
              have h := resolverSourceCoeff_re_sq_summable_of_continuousOn
                p hcont_on
              simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
                at h
              exact h.congr (fun k ↦ by rw [hf_coeff])
            exact intervalNeumannResolverR_nonneg_of_nonneg_source
              hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
          -- intervalDomainLift of R at y ∈ [0,1] = R ⟨y, hy⟩
          have hR_lift_eq : intervalDomainLift (intervalNeumannResolverR p (w s)) y
              = intervalNeumannResolverR p (w s) ⟨y, hy⟩ := by
            simp [intervalDomainLift, hy]
          -- (1 + R)^β ≥ 1
          have hden_ge_one :
              1 ≤ (1 + intervalDomainLift
                (intervalNeumannResolverR p (w s)) y) ^ p.β := by
            rw [hR_lift_eq]
            exact Real.one_le_rpow (by linarith [hR_nonneg_pt]) p.hβ
          -- |a * b / c| ≤ |a| * |b| / |c| ≤ M * C_RG / 1
          calc |intervalDomainLift (w s) y * resolverGradReal p (w s) y /
                (1 + intervalDomainLift (intervalNeumannResolverR p (w s)) y) ^ p.β|
              = |intervalDomainLift (w s) y * resolverGradReal p (w s) y| /
                |(1 + intervalDomainLift (intervalNeumannResolverR p (w s)) y) ^ p.β| :=
                abs_div _ _
            _ ≤ |intervalDomainLift (w s) y * resolverGradReal p (w s) y| / 1 := by
                apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
                rwa [abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos
                  (by rw [hR_lift_eq]; linarith [hR_nonneg_pt]) p.β))]
            _ = |intervalDomainLift (w s) y * resolverGradReal p (w s) y| := by
                rw [div_one]
            _ ≤ |intervalDomainLift (w s) y| * |resolverGradReal p (w s) y| :=
                le_of_eq (abs_mul _ _)
            _ ≤ M * C_RG := by
                exact mul_le_mul hlift (hgrad) (abs_nonneg _) hM.le
        · -- y outside [0,1]: lift = 0
          simp [intervalDomainLift, hy, zero_mul, zero_div, abs_zero]
          exact hC_Q_unif_nn
      · simp; exact hC_Q_unif_nn
    -- Integral equality for gradient term
    have hgrad_eq : (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (w s)) z) x.1)
        = ∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (r_grad s) z) x.1 := by
      apply intervalIntegral.integral_congr_ae
      apply Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le ht.le] at hs
      simp only [r_grad, if_pos (And.intro hs.1 (hs.2.trans htT))]
    -- Bound value Duhamel via universal lemma
    have hterm3 : |(∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (w s)) x.1)| ≤ T₀ * C_L_val := by
      rw [hval_eq]
      exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
        ht htT hC_L_val_nn hr_val_bound x.1
    -- Bound gradient Duhamel via universal lemma
    have hterm2 : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (w s)) z) x.1)|
        ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif) := by
      rw [abs_mul, abs_neg]
      gcongr
      rw [hgrad_eq]
      exact ShenWork.IntervalDuhamelIntegrability.gradDuhamel_sup_bound_universal
        ht htT hC_Q_unif_nn hr_grad_bound x.1
    -- Assemble: |Φ| ≤ M/2 + correction ≤ M/2 + M/2 = M
    -- Triangle inequality: |a+b+c| ≤ |a| + |b| + |c|
    have hab := abs_add_le
      (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1)
      ((-p.χ₀) * (∫ s in (0:ℝ)..t, deriv (fun z =>
        intervalFullSemigroupOperator (t - s) (chemFluxLifted p (w s)) z) x.1))
    have habc := abs_add_le
      (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 +
        (-p.χ₀) * (∫ s in (0:ℝ)..t, deriv (fun z =>
          intervalFullSemigroupOperator (t - s) (chemFluxLifted p (w s)) z) x.1))
      (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
        (logisticLifted p (w s)) x.1)
    linarith
  refine ⟨{
    T := T₀
    M := M
    K := A_picard * Real.sqrt T₀ + B_picard * T₀
    C₀ := 2 * M
    hT := hT₀
    hM := hM
    hK := hK_lt
    hK_nn := by positivity
    hC₀ := by linarith
    hbase_ball := hbase_ball T₀
    hbase_nonneg := hbase_nonneg T₀
    hbase_cont := by
      intro t ht _htT; exact hSg_cont t ht
    hmapsTo := hmapsTo_proof
    hmapsTo_nn := by
      -- Small-T₀ domination: S(t)u₀(x) ≥ inf u₀, |corrections| < inf u₀
      intro w _hw_bound _hw_nonneg _hw_cont t ht _htT x
      haveI : CompactSpace intervalDomainPoint :=
        isCompact_iff_compactSpace.mp isCompact_Icc
      haveI : Nonempty intervalDomainPoint :=
        ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩⟩
      unfold intervalGradientDuhamelMap
      -- Step 1: Lower bound the semigroup term
      have hLift_lower : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → c ≤ intervalDomainLift u₀ y := by
        intro y hy
        simp only [intervalDomainLift, dif_pos hy]
        exact hu₀_lb ⟨y, hy⟩
      have hc_le_M : c ≤ M := by
        have hx₀ := hu₀_lb ⟨0, left_mem_Icc.mpr zero_le_one⟩
        have habs := le_abs_self (u₀ ⟨0, left_mem_Icc.mpr zero_le_one⟩)
        have hhalf := hB_le ⟨0, left_mem_Icc.mpr zero_le_one⟩
        linarith
      have hSg_lower : c ≤ intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
          ht hc.le hc_le_M hLift_meas hLift_lower hLift_le_M x.1
      -- Step 2: Bound the correction terms
      -- Extended logistic source
      set r_val : ℝ → ℝ → ℝ := fun s y =>
        if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
      have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L_val := by
        intro s y; simp only [r_val]
        split_ifs with h
        · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound p hM
            (fun x => _hw_bound s h.1 h.2 x) y
        · simp; exact hC_L_val_nn
      -- Extended flux source
      set r_grad : ℝ → ℝ → ℝ := fun s y =>
        if 0 < s ∧ s ≤ T₀ then chemFluxLifted p (w s) y else 0
      have hr_grad_bound : ∀ s y, |r_grad s y| ≤ C_Q_unif := by
        intro s y; simp only [r_grad]
        split_ifs with h
        · simpa [C_Q_unif, C_RG] using
            chemFluxLifted_bound_of_ball p hM.le
              (_hw_bound s h.1 h.2) (_hw_nonneg s h.1 h.2)
              (_hw_cont s h.1 h.2) y
        · simp; exact hC_Q_unif_nn
      -- Integral equalities
      have hval_eq : (∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
          = ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (r_val s) x.1 := by
        apply intervalIntegral.integral_congr_ae
        apply Eventually.of_forall
        intro s hs
        rw [Set.uIoc_of_le ht.le] at hs
        simp only [r_val, if_pos (And.intro hs.1 (hs.2.trans _htT))]
      have hgrad_eq : (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (w s)) z) x.1)
          = ∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (r_grad s) z) x.1 := by
        apply intervalIntegral.integral_congr_ae
        apply Eventually.of_forall
        intro s hs
        rw [Set.uIoc_of_le ht.le] at hs
        simp only [r_grad, if_pos (And.intro hs.1 (hs.2.trans _htT))]
      -- Value Duhamel bound
      have hterm3 : |(∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1)| ≤ T₀ * C_L_val := by
        rw [hval_eq]
        exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
          ht _htT hC_L_val_nn hr_val_bound x.1
      -- Gradient Duhamel bound
      have hterm2 : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (w s)) z) x.1)|
          ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif) := by
        rw [abs_mul, abs_neg]
        gcongr
        rw [hgrad_eq]
        exact ShenWork.IntervalDuhamelIntegrability.gradDuhamel_sup_bound_universal
          ht _htT hC_Q_unif_nn hr_grad_bound x.1
      -- Step 3: Combine: S(t)u₀ + correction ≥ c - |correction| > 0
      have hcorr_abs : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (w s)) z) x.1)
          + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (w s)) x.1)| ≤
          A_picard * Real.sqrt T₀ + B_picard * T₀ := by
        calc |(-p.χ₀) * (∫ s in (0:ℝ)..t,
              deriv (fun z => intervalFullSemigroupOperator (t - s)
                (chemFluxLifted p (w s)) z) x.1)
            + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
                (logisticLifted p (w s)) x.1)|
            ≤ |(-p.χ₀) * (∫ s in (0:ℝ)..t,
                deriv (fun z => intervalFullSemigroupOperator (t - s)
                  (chemFluxLifted p (w s)) z) x.1)|
              + |(∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
                  (logisticLifted p (w s)) x.1)| := abs_add_le _ _
          _ ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif)
              + T₀ * C_L_val := add_le_add hterm2 hterm3
          _ ≤ A_picard * Real.sqrt T₀ + B_picard * T₀ := by
              have hle_CQ : C_Q_unif ≤ C_Q_max := le_max_left _ _
              have h1 : 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀
                  ≤ A_picard * Real.sqrt T₀ := by
                gcongr
                calc 2 * |p.χ₀| * C_grad * C_Q_unif
                    ≤ 2 * |p.χ₀| * C_grad * C_Q_max := by gcongr
                  _ ≤ A_picard := by simp only [A_picard]; linarith [hC_L_pos.le]
              have h2 : C_L_val * T₀ ≤ B_picard * T₀ := by
                gcongr; linarith [hC_L_pos.le]
              calc |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif) + T₀ * C_L_val
                  = 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀ + C_L_val * T₀ := by ring
                _ ≤ A_picard * Real.sqrt T₀ + B_picard * T₀ := add_le_add h1 h2
      linarith [neg_abs_le ((-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (w s)) z) x.1)
          + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (w s)) x.1))]

    hmapsTo_pos := by
      -- Strict positivity: S(t)u₀(x) ≥ c > |corrections|
      intro w _hw_bound _hw_nonneg _hw_cont t ht _htT x
      haveI : CompactSpace intervalDomainPoint :=
        isCompact_iff_compactSpace.mp isCompact_Icc
      haveI : Nonempty intervalDomainPoint :=
        ⟨⟨0, left_mem_Icc.mpr zero_le_one⟩⟩
      unfold intervalGradientDuhamelMap
      -- Step 1: Lower bound the semigroup term
      have hLift_lower : ∀ y, y ∈ Set.Icc (0 : ℝ) 1 → c ≤ intervalDomainLift u₀ y := by
        intro y hy
        simp only [intervalDomainLift, dif_pos hy]
        exact hu₀_lb ⟨y, hy⟩
      have hc_le_M : c ≤ M := by
        have hx₀ := hu₀_lb ⟨0, left_mem_Icc.mpr zero_le_one⟩
        have habs := le_abs_self (u₀ ⟨0, left_mem_Icc.mpr zero_le_one⟩)
        have hhalf := hB_le ⟨0, left_mem_Icc.mpr zero_le_one⟩
        linarith
      have hSg_lower : c ≤ intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 :=
        ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_lower_bound
          ht hc.le hc_le_M hLift_meas hLift_lower hLift_le_M x.1
      -- Step 2: Bound the correction terms
      set r_val : ℝ → ℝ → ℝ := fun s y =>
        if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
      have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L_val := by
        intro s y; simp only [r_val]
        split_ifs with h
        · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound p hM
            (fun x => _hw_bound s h.1 h.2 x) y
        · simp; exact hC_L_val_nn
      set r_grad : ℝ → ℝ → ℝ := fun s y =>
        if 0 < s ∧ s ≤ T₀ then chemFluxLifted p (w s) y else 0
      have hr_grad_bound : ∀ s y, |r_grad s y| ≤ C_Q_unif := by
        intro s y; simp only [r_grad]
        split_ifs with h
        · simpa [C_Q_unif, C_RG] using
            chemFluxLifted_bound_of_ball p hM.le
              (_hw_bound s h.1 h.2) (_hw_nonneg s h.1 h.2)
              (_hw_cont s h.1 h.2) y
        · simp; exact hC_Q_unif_nn
      have hval_eq : (∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
          = ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (r_val s) x.1 := by
        apply intervalIntegral.integral_congr_ae
        apply Eventually.of_forall
        intro s hs
        rw [Set.uIoc_of_le ht.le] at hs
        simp only [r_val, if_pos (And.intro hs.1 (hs.2.trans _htT))]
      have hgrad_eq : (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (w s)) z) x.1)
          = ∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (r_grad s) z) x.1 := by
        apply intervalIntegral.integral_congr_ae
        apply Eventually.of_forall
        intro s hs
        rw [Set.uIoc_of_le ht.le] at hs
        simp only [r_grad, if_pos (And.intro hs.1 (hs.2.trans _htT))]
      have hterm3 : |(∫ s in (0:ℝ)..t,
          intervalFullSemigroupOperator (t - s)
            (logisticLifted p (w s)) x.1)| ≤ T₀ * C_L_val := by
        rw [hval_eq]
        exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
          ht _htT hC_L_val_nn hr_val_bound x.1
      have hterm2 : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (w s)) z) x.1)|
          ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif) := by
        rw [abs_mul, abs_neg]
        gcongr
        rw [hgrad_eq]
        exact ShenWork.IntervalDuhamelIntegrability.gradDuhamel_sup_bound_universal
          ht _htT hC_Q_unif_nn hr_grad_bound x.1
      -- Step 3: Combine with strict inequality
      have hcorr_abs : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (w s)) z) x.1)
          + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (w s)) x.1)| ≤
          A_picard * Real.sqrt T₀ + B_picard * T₀ := by
        calc |(-p.χ₀) * (∫ s in (0:ℝ)..t,
              deriv (fun z => intervalFullSemigroupOperator (t - s)
                (chemFluxLifted p (w s)) z) x.1)
            + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
                (logisticLifted p (w s)) x.1)|
            ≤ |(-p.χ₀) * (∫ s in (0:ℝ)..t,
                deriv (fun z => intervalFullSemigroupOperator (t - s)
                  (chemFluxLifted p (w s)) z) x.1)|
              + |(∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
                  (logisticLifted p (w s)) x.1)| := abs_add_le _ _
          _ ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif)
              + T₀ * C_L_val := add_le_add hterm2 hterm3
          _ ≤ A_picard * Real.sqrt T₀ + B_picard * T₀ := by
              have hle_CQ : C_Q_unif ≤ C_Q_max := le_max_left _ _
              have h1 : 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀
                  ≤ A_picard * Real.sqrt T₀ := by
                gcongr
                calc 2 * |p.χ₀| * C_grad * C_Q_unif
                    ≤ 2 * |p.χ₀| * C_grad * C_Q_max := by gcongr
                  _ ≤ A_picard := by simp only [A_picard]; linarith [hC_L_pos.le]
              have h2 : C_L_val * T₀ ≤ B_picard * T₀ := by
                gcongr; linarith [hC_L_pos.le]
              calc |p.χ₀| * (C_grad * (2 * Real.sqrt T₀) * C_Q_unif) + T₀ * C_L_val
                  = 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀ + C_L_val * T₀ := by ring
                _ ≤ A_picard * Real.sqrt T₀ + B_picard * T₀ := add_le_add h1 h2
      -- S(t)u₀ ≥ c and |corrections| < c, so Φ > 0
      linarith [neg_abs_le ((-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (w s)) z) x.1)
          + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (w s)) x.1))]
    hcont_preserved := by
      /- Φ preserves continuous slices.
         Route: S(t)u₀ is continuous (hSg_cont). For the Duhamel integrals
         ∫₀ᵗ S(t-s) source(s) x ds, use MeasureTheory.continuous_of_dominated:
         F x s := S(t-s)(source(s))(x) is continuous in x for each s
         (by intervalFullSemigroupOperator_continuous_of_bounded), uniformly
         bounded (by semigroup L∞ bound), and the bound is integrable on [0,t].
         The gradient Duhamel ∫₀ᵗ ∂ₓS(t-s) flux(s) x ds uses the same pattern
         with the heat gradient kernel. Converting intervalIntegral to Bochner
         integral is the main technical step. -/
      intro w hw_bound hw_nonneg hw_cont hwm t ht htT
      -- Φ(w)(t)(x) = S(t)u₀(x.1) + (-χ₀) * ∫₀ᵗ ∂ₓS(t-s) Q(w s) ds + ∫₀ᵗ S(t-s) L(w s) ds
      -- Need: Continuous (Φ(w)(t)) where Φ(w)(t) : intervalDomainPoint → ℝ
      -- Route: continuous_of_dominated_interval for each Duhamel integral,
      -- composed with continuous_subtype_val.
      have hL_bound : ∀ s, 0 < s → s ≤ T₀ → ∀ y : ℝ,
          |logisticLifted p (w s) y| ≤ C_L_val := by
        intro s hs hsT y
        exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound p hM
          (fun x => hw_bound s hs hsT x) y
      have hQ_bound : ∀ s, 0 < s → s ≤ T₀ → ∀ y : ℝ,
          |chemFluxLifted p (w s) y| ≤ C_Q_unif := by
        intro s hs hsT y
        simpa [C_Q_unif, C_RG] using
          chemFluxLifted_bound_of_ball p hM.le
            (hw_bound s hs hsT) (hw_nonneg s hs hsT) (hw_cont s hs hsT) y
      have hL_meas : Measurable (fun q : ℝ × ℝ => logisticLifted p (w q.1) q.2) :=
        logisticLifted_joint_measurable (p := p) (u := w) hwm
      have hQ_meas : Measurable (fun q : ℝ × ℝ => chemFluxLifted p (w q.1) q.2) :=
        chemFluxLifted_joint_measurable (p := p) (w := w) hwm
      have hL_slice_meas : ∀ s,
          AEStronglyMeasurable (logisticLifted p (w s)) (intervalMeasure 1) := by
        intro s
        have hm : Measurable (fun y : ℝ => logisticLifted p (w s) y) :=
          hL_meas.comp (measurable_const.prodMk measurable_id)
        exact hm.aestronglyMeasurable
      have hQ_slice_meas : ∀ s,
          AEStronglyMeasurable (chemFluxLifted p (w s)) (intervalMeasure 1) := by
        intro s
        have hm : Measurable (fun y : ℝ => chemFluxLifted p (w s) y) :=
          hQ_meas.comp (measurable_const.prodMk measurable_id)
        exact hm.aestronglyMeasurable
      have hne_t : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
        rw [ae_iff]
        simp only [not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
      have hL_joint_semigroup :
          Measurable (fun r : (ℝ × ℝ) × ℝ =>
            intervalFullSemigroupOperator (r.1.1 - r.2)
              (logisticLifted p (w r.2)) r.1.2) :=
        intervalFullSemigroupOperator_s_param_joint_measurable
          (F := fun s => logisticLifted p (w s))
          (by simpa [Function.uncurry] using hL_meas)
      set GQ : (ℝ × ℝ) × ℝ → ℝ := fun r =>
        deriv (fun z : ℝ =>
          intervalFullSemigroupOperator (r.1.1 - r.2)
            (chemFluxLifted p (w r.2)) z) r.1.2
      have hQ_joint_grad : Measurable GQ := by
        dsimp only [GQ]
        exact intervalFullSemigroupOperator_deriv_s_param_joint_measurable
          (F := fun s => chemFluxLifted p (w s))
          (by simpa [Function.uncurry] using hQ_meas)
      have hVal_cont : Continuous (fun x : intervalDomainPoint =>
          ∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1) := by
        refine intervalIntegral.continuous_of_dominated_interval
          (μ := volume)
          (F := fun x : intervalDomainPoint => fun s : ℝ =>
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)
          (bound := fun _ : ℝ => C_L_val)
          ?hVal_meas ?hVal_bound intervalIntegrable_const ?hVal_slice_cont
        · intro x
          have hmap : Measurable (fun s : ℝ => (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
            measurable_const.prodMk measurable_id
          have hm : Measurable (fun s : ℝ =>
              intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1) :=
            hL_joint_semigroup.comp hmap
          exact hm.aestronglyMeasurable
        · intro x
          filter_upwards [hne_t] with s hsne hsI
          rw [Set.uIoc_of_le ht.le] at hsI
          have hst : s < t := lt_of_le_of_ne hsI.2 hsne
          have hts : 0 < t - s := sub_pos.mpr hst
          rw [Real.norm_eq_abs]
          exact ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_Linfty_bound
            hts hC_L_val_nn (hL_bound s hsI.1 (hsI.2.trans htT)) x.1
        · filter_upwards [hne_t] with s hsne hsI
          rw [Set.uIoc_of_le ht.le] at hsI
          have hst : s < t := lt_of_le_of_ne hsI.2 hsne
          have hts : 0 < t - s := sub_pos.mpr hst
          have hLs_bound : ∀ y : ℝ, |logisticLifted p (w s) y| ≤ C_L_val :=
            hL_bound s hsI.1 (hsI.2.trans htT)
          have hcont_real : Continuous (fun x : ℝ =>
              intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x) :=
            ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_continuous_of_bounded
              (t := t - s) (f := logisticLifted p (w s)) (M := C_L_val)
              hts hC_L_val_nn hLs_bound (hL_slice_meas s)
          exact hcont_real.comp continuous_subtype_val
      have hGrad_cont_GQ : Continuous (fun x : intervalDomainPoint =>
          ∫ s in (0 : ℝ)..t, GQ ((t, x.1), s)) := by
        refine intervalIntegral.continuous_of_dominated_interval
          (μ := volume)
          (F := fun x : intervalDomainPoint => fun s : ℝ => GQ ((t, x.1), s))
          (bound := fun s : ℝ =>
            C_grad * C_Q_unif * (t - s) ^ (-(1 / 2) : ℝ))
          ?hGrad_meas ?hGrad_bound
          ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
            (C_grad * C_Q_unif))
          ?hGrad_slice_cont
        · intro x
          have hmap : Measurable (fun s : ℝ => (((t, x.1), s) : (ℝ × ℝ) × ℝ)) :=
            measurable_const.prodMk measurable_id
          have hm : Measurable (fun s : ℝ => GQ ((t, x.1), s)) :=
            hQ_joint_grad.comp hmap
          exact hm.aestronglyMeasurable
        · intro x
          filter_upwards [hne_t] with s hsne hsI
          rw [Set.uIoc_of_le ht.le] at hsI
          have hst : s < t := lt_of_le_of_ne hsI.2 hsne
          have hts : 0 < t - s := sub_pos.mpr hst
          dsimp only [GQ]
          rw [Real.norm_eq_abs]
          have hQs_bound : ∀ y : ℝ, |chemFluxLifted p (w s) y| ≤ C_Q_unif :=
            hQ_bound s hsI.1 (hsI.2.trans htT)
          have hderiv_bound :
              |deriv (fun z : ℝ =>
                intervalFullSemigroupOperator (t - s) (chemFluxLifted p (w s)) z) x.1|
                ≤ C_grad * (t - s) ^ (-(1 / 2) : ℝ) * C_Q_unif := by
            simpa [C_grad] using
              ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_deriv_Linfty_pointwise_sqrt_t
                (t := t - s) (f := chemFluxLifted p (w s)) hts
                (hQ_slice_meas s) (Cf := C_Q_unif) hQs_bound x.1
          calc
            |deriv (fun z : ℝ =>
                intervalFullSemigroupOperator (t - s) (chemFluxLifted p (w s)) z) x.1|
                ≤ C_grad * (t - s) ^ (-(1 / 2) : ℝ) * C_Q_unif := hderiv_bound
            _ = C_grad * C_Q_unif * (t - s) ^ (-(1 / 2) : ℝ) := by ring
        · filter_upwards [hne_t] with s hsne hsI
          rw [Set.uIoc_of_le ht.le] at hsI
          have hst : s < t := lt_of_le_of_ne hsI.2 hsne
          have hts : 0 < t - s := sub_pos.mpr hst
          dsimp only [GQ]
          have hQs_bound : ∀ y : ℝ, |chemFluxLifted p (w s) y| ≤ C_Q_unif :=
            hQ_bound s hsI.1 (hsI.2.trans htT)
          exact intervalFullSemigroupOperator_deriv_continuous_of_bounded
            (t := t - s) (f := chemFluxLifted p (w s)) (C := C_Q_unif)
            hts hC_Q_unif_nn hQs_bound (hQ_slice_meas s)
      have hGrad_cont : Continuous (fun x : intervalDomainPoint =>
          ∫ s in (0 : ℝ)..t,
            deriv (fun z : ℝ =>
              intervalFullSemigroupOperator (t - s) (chemFluxLifted p (w s)) z) x.1) := by
        simpa [GQ] using hGrad_cont_GQ
      have hassemble : Continuous (fun x : intervalDomainPoint =>
          intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
            + (-p.χ₀) * (∫ s in (0 : ℝ)..t,
              deriv (fun z : ℝ =>
                intervalFullSemigroupOperator (t - s) (chemFluxLifted p (w s)) z) x.1)
            + ∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1) :=
        ((hSg_cont t ht).add (continuous_const.mul hGrad_cont)).add hVal_cont
      simpa [intervalGradientDuhamelMap] using hassemble
    hcontr := by
      intro u w d hu hu_nn hw hw_nn huc hwc hum hwm hd t ht htT x
      -- Step 1: Unfold Φ and cancel S(t)u₀
      simp only [intervalGradientDuhamelMap]
      set Gu := ∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (u s)) z) x.1
      set Gw := ∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (w s)) z) x.1
      set Vu := ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1
      set Vw := ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1
      have hcancel :
          (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
            + (-p.χ₀) * Gu + Vu)
          - (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
            + (-p.χ₀) * Gw + Vw)
          = (-p.χ₀) * (Gu - Gw) + (Vu - Vw) := by ring
      rw [hcancel]
      -- Step 2: d ≥ 0 (since |u - w| ≥ 0 ≤ d)
      have hd_nn : 0 ≤ d := by
        have := hd t ht htT x
        exact le_trans (abs_nonneg _) this
      -- Step 3: Bound the two Duhamel differences
      have hV : |Vu - Vw| ≤ T₀ * (C_L * d) := by
        -- Extended logistic sources (= original on (0,T₀], = 0 otherwise)
        set r_u : ℝ → ℝ → ℝ := fun s y =>
          if 0 < s ∧ s ≤ T₀ then logisticLifted p (u s) y else 0
        set r_w : ℝ → ℝ → ℝ := fun s y =>
          if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
        -- Integral congr: Vu = ∫ with r_u
        have hVu_eq : Vu = ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (r_u s) x.1 := by
          apply intervalIntegral.integral_congr_ae; apply Eventually.of_forall
          intro s hs; rw [Set.uIoc_of_le ht.le] at hs
          simp only [r_u, if_pos (And.intro hs.1 (hs.2.trans htT))]
        have hVw_eq : Vw = ∫ s in (0:ℝ)..t,
            intervalFullSemigroupOperator (t - s) (r_w s) x.1 := by
          apply intervalIntegral.integral_congr_ae; apply Eventually.of_forall
          intro s hs; rw [Set.uIoc_of_le ht.le] at hs
          simp only [r_w, if_pos (And.intro hs.1 (hs.2.trans htT))]
        rw [hVu_eq, hVw_eq]
        -- Source diff bound: |r_u s y - r_w s y| ≤ C_L · d
        have hr_diff_bound : ∀ s y, |r_u s y - r_w s y| ≤ C_L * d := by
          intro s y; simp only [r_u, r_w]
          split_ifs with h
          · -- s ∈ (0, T₀]: logistic Lipschitz
            unfold logisticLifted intervalDomainLift
              ShenWork.IntervalDomainExistence.intervalLogisticSource
            by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
            · -- y ∈ [0,1]: use hC_L_lip + hd
              simp only [dif_pos hy]
              have hu_s := hu s h.1 h.2 ⟨y, hy⟩
              have hw_s := hw s h.1 h.2 ⟨y, hy⟩
              have hd_s := hd s h.1 h.2 ⟨y, hy⟩
              calc |u s ⟨y, hy⟩ * (p.a - p.b * (u s ⟨y, hy⟩) ^ p.α)
                      - w s ⟨y, hy⟩ * (p.a - p.b * (w s ⟨y, hy⟩) ^ p.α)|
                  ≤ C_L * |u s ⟨y, hy⟩ - w s ⟨y, hy⟩| :=
                    hC_L_lip _ _ hu_s hw_s
                _ ≤ C_L * d := mul_le_mul_of_nonneg_left hd_s hC_L_pos.le
            · -- y ∉ [0,1]: both lifts = 0
              simp only [dif_neg hy, sub_self, abs_zero]
              exact mul_nonneg hC_L_pos.le hd_nn
          · -- s ∉ (0, T₀]: 0 - 0 = 0
            simp; exact mul_nonneg hC_L_pos.le hd_nn
        -- Source spatial integrability (logistic of continuous bounded, or zero)
        have hr_u_int : ∀ s, Integrable (r_u s) (ShenWork.IntervalDomain.intervalMeasure 1) := by
          intro s; simp only [r_u]; split_ifs with h
          · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
              p (hu s h.1 h.2) hM.le (huc s h.1 h.2)
          · exact integrable_zero ℝ ℝ (ShenWork.IntervalDomain.intervalMeasure 1)
        have hr_w_int : ∀ s, Integrable (r_w s) (ShenWork.IntervalDomain.intervalMeasure 1) := by
          intro s; simp only [r_w]; split_ifs with h
          · exact ShenWork.IntervalDuhamelIntegrability.logisticLifted_integrable_of_continuous
              p (hw s h.1 h.2) hM.le (hwc s h.1 h.2)
          · exact integrable_zero ℝ ℝ (ShenWork.IntervalDomain.intervalMeasure 1)
        -- Source sup bounds
        have hr_u_bdd : ∀ s y, |r_u s y| ≤ C_L_val := by
          intro s y; simp only [r_u]; split_ifs with h
          · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
              p hM (hu s h.1 h.2) y
          · simp; exact hC_L_val_nn
        have hr_w_bdd : ∀ s y, |r_w s y| ≤ C_L_val := by
          intro s y; simp only [r_w]; split_ifs with h
          · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
              p hM (hw s h.1 h.2) y
          · simp; exact hC_L_val_nn
        have hCLd_nn : 0 ≤ C_L * d := mul_nonneg hC_L_pos.le hd_nn
        by_cases hint_u : IntervalIntegrable
            (fun s => intervalFullSemigroupOperator (t - s) (r_u s) x.1) volume 0 t
        · by_cases hint_w : IntervalIntegrable
              (fun s => intervalFullSemigroupOperator (t - s) (r_w s) x.1) volume 0 t
          · -- Both integrable: combine + per-slice bound + integrate
            rw [← intervalIntegral.integral_sub hint_u hint_w]
            have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
                |intervalFullSemigroupOperator (t - s) (r_u s) x.1
                  - intervalFullSemigroupOperator (t - s) (r_w s) x.1| ≤ C_L * d := by
              have hne : ∀ᵐ s ∂volume, s ≠ t := by
                rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]
                exact Real.volume_singleton
              refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
              filter_upwards [hne] with s hs hs_mem
              have hst : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs_mem.2 hs)
              exact ShenWork.IntervalDuhamelIntegrability.intervalFullSemigroupOperator_diff_Linfty_of_integrable
                hst (hr_u_int s) (hr_w_int s) hC_L_val_nn (hr_u_bdd s) hC_L_val_nn
                (hr_w_bdd s) hCLd_nn (hr_diff_bound s) x.1
            calc |∫ s in (0:ℝ)..t, (intervalFullSemigroupOperator (t - s) (r_u s) x.1
                    - intervalFullSemigroupOperator (t - s) (r_w s) x.1)|
                ≤ ∫ s in (0:ℝ)..t, |intervalFullSemigroupOperator (t - s) (r_u s) x.1
                    - intervalFullSemigroupOperator (t - s) (r_w s) x.1| :=
                  intervalIntegral.abs_integral_le_integral_abs ht.le
              _ ≤ ∫ s in (0:ℝ)..t, (C_L * d) :=
                  intervalIntegral.integral_mono_ae_restrict ht.le
                    (hint_u.sub hint_w).abs intervalIntegrable_const hptw
              _ = t * (C_L * d) := by
                  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
              _ ≤ T₀ * (C_L * d) := by gcongr
          · -- w not integrable: derive contradiction from joint measurability
            -- r_w s y = if 0 < s ∧ s ≤ T₀ then logisticLifted p (w s) y else 0
            -- Measurability follows from hwm : HasJointMeasurability w
            exfalso; exact hint_w
              (ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
                ht (by
                  show Measurable (fun p : ℝ × ℝ => r_w p.1 p.2)
                  simp only [r_w]
                  exact logisticLifted_time_cutoff_measurable hwm) hC_L_val_nn
                (hr_w_bdd) x.1)
        · exfalso; exact hint_u
            (ShenWork.IntervalDuhamelIntegrability.valueDuhamel_intervalIntegrable_of_joint_measurable
              ht (by
                show Measurable (fun p : ℝ × ℝ => r_u p.1 p.2)
                simp only [r_u]
                exact logisticLifted_time_cutoff_measurable hum) hC_L_val_nn
              (hr_u_bdd) x.1)
      have hG : |Gu - Gw| ≤ C_grad * (2 * Real.sqrt T₀) * (C_Q_lip * d) := by
        -- Extended flux sources (= original on (0,T₀], = 0 otherwise)
        set q_u : ℝ → ℝ → ℝ := fun s y =>
          if 0 < s ∧ s ≤ T₀ then chemFluxLifted p (u s) y else 0
        set q_w : ℝ → ℝ → ℝ := fun s y =>
          if 0 < s ∧ s ≤ T₀ then chemFluxLifted p (w s) y else 0
        -- Integral congr: Gu = ∫ with q_u
        have hGu_eq : Gu = ∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s) (q_u s) z) x.1 := by
          apply intervalIntegral.integral_congr_ae; apply Eventually.of_forall
          intro s hs; rw [Set.uIoc_of_le ht.le] at hs
          simp only [q_u, if_pos (And.intro hs.1 (hs.2.trans htT))]
        have hGw_eq : Gw = ∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s) (q_w s) z) x.1 := by
          apply intervalIntegral.integral_congr_ae; apply Eventually.of_forall
          intro s hs; rw [Set.uIoc_of_le ht.le] at hs
          simp only [q_w, if_pos (And.intro hs.1 (hs.2.trans htT))]
        rw [hGu_eq, hGw_eq]
        -- γ ≥ 1 (needed for resolver Lipschitz — should be a theorem parameter)
        -- hγ_ge is now a theorem hypothesis
        -- Flux source diff bound: |q_u s y - q_w s y| ≤ C_Q_lip · d
        -- Core: chemFlux_div_lipschitz + resolver Atom B bounds.
        have hq_diff_bound : ∀ s y, |q_u s y - q_w s y| ≤ C_Q_lip * d := by
          intro s y; simp only [q_u, q_w]
          split_ifs with h
          · -- 0 < s ∧ s ≤ T₀: chemFlux Lipschitz
            unfold chemFluxLifted
            by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
            · -- y ∈ [0,1]: build resolver bounds, apply chemFlux_div_lipschitz
              have hu_s := hu s h.1 h.2
              have hw_s := hw s h.1 h.2
              have hu_nn_s := hu_nn s h.1 h.2
              have hw_nn_s := hw_nn s h.1 h.2
              have hd_s := hd s h.1 h.2
              have hu_cont_s := huc s h.1 h.2
              have hw_cont_s := hwc s h.1 h.2
              -- ContinuousOn of lifts on [0,1]
              have hcont_u : ContinuousOn (intervalDomainLift (u s))
                  (Set.Icc (0 : ℝ) 1) := by
                rw [continuousOn_iff_continuous_restrict]
                have : Set.restrict (Set.Icc (0:ℝ) 1)
                    (intervalDomainLift (u s)) = u s := by
                  ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
                rw [this]; exact hu_cont_s
              have hcont_w : ContinuousOn (intervalDomainLift (w s))
                  (Set.Icc (0 : ℝ) 1) := by
                rw [continuousOn_iff_continuous_restrict]
                have : Set.restrict (Set.Icc (0:ℝ) 1)
                    (intervalDomainLift (w s)) = w s := by
                  ext ⟨x, hx⟩; simp [Set.restrict, intervalDomainLift, hx]; rfl
                rw [this]; exact hw_cont_s
              -- Membership in [0, M]
              have hmem_u : ∀ x ∈ Set.Icc (0:ℝ) 1,
                  intervalDomainLift (u s) x ∈ Set.Icc (0:ℝ) M := by
                intro x hx; constructor
                · simp [intervalDomainLift, hx]; exact hu_nn_s ⟨x, hx⟩
                · simp [intervalDomainLift, hx]
                  exact (abs_le.mp (hu_s ⟨x, hx⟩)).2
              have hmem_w : ∀ x ∈ Set.Icc (0:ℝ) 1,
                  intervalDomainLift (w s) x ∈ Set.Icc (0:ℝ) M := by
                intro x hx; constructor
                · simp [intervalDomainLift, hx]; exact hw_nn_s ⟨x, hx⟩
                · simp [intervalDomainLift, hx]
                  exact (abs_le.mp (hw_s ⟨x, hx⟩)).2
              -- |lift u - lift w| ≤ d on [0,1]
              have hlift_diff : ∀ x ∈ Set.Icc (0:ℝ) 1,
                  |intervalDomainLift (u s) x - intervalDomainLift (w s) x| ≤ d := by
                intro x hx
                simp [intervalDomainLift, hx]
                exact hd_s ⟨x, hx⟩
              -- |a₂| ≤ M  (w bounded)
              have ha₂ : |intervalDomainLift (w s) y| ≤ M := by
                simp [intervalDomainLift, hy]; exact hw_s ⟨y, hy⟩
              -- |a₁ - a₂| ≤ d  (u-w diff bounded)
              have had : |intervalDomainLift (u s) y
                  - intervalDomainLift (w s) y| ≤ d := hlift_diff y hy
              -- Open namespaces for resolver gradient + positivity proofs
              open ShenWork.PDE ShenWork.IntervalResolverGradientBridge
                  ShenWork.IntervalResolverWeakBounds ShenWork.Paper2
                  ShenWork.IntervalNeumannFullKernel
                  ShenWork.IntervalResolverPositivity in
              -- |g₁| ≤ C_RG  (resolver gradient sup bound for u)
              have hg₁ : |resolverGradReal p (u s) y| ≤ C_RG :=
                resolverGrad_sup_le_of_bounded
                  p hcont_u (fun x hx => (hmem_u x hx).1)
                  (fun x hx => (hmem_u x hx).2) hy
              -- |g₂| ≤ C_RG  (resolver gradient sup bound for w)
              have hg₂ : |resolverGradReal p (w s) y| ≤ C_RG :=
                resolverGrad_sup_le_of_bounded
                  p hcont_w (fun x hx => (hmem_w x hx).1)
                  (fun x hx => (hmem_w x hx).2) hy
              -- |g₁ - g₂| ≤ C_RGL * d  (resolver gradient Lipschitz)
              have hgd : |resolverGradReal p (u s) y
                  - resolverGradReal p (w s) y| ≤ C_RGL * d := by
                have h :=
                  resolverGrad_diff_sup_le_of_bounded
                    p hγ_ge hcont_u hcont_w hmem_u hmem_w hlift_diff hy
                calc |resolverGradReal p (u s) y - resolverGradReal p (w s) y|
                    ≤ Real.sqrt (∑' k : ℕ,
                        (intervalNeumannResolverGradWeight p k) ^ 2) *
                      (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * d)) := h
                  _ = C_RGL * d := by ring
              -- v₁ = R(u s)(y) ≥ 0  (resolver positivity for u)
              have hR_u_nonneg :
                  0 ≤ intervalNeumannResolverR p (u s) ⟨y, hy⟩ := by
                have hcont_src : Continuous
                    (fun x : intervalDomainPoint ↦ p.ν * (u s x) ^ p.γ) :=
                  continuous_const.mul
                    (hu_cont_s.rpow_const (fun x ↦ Or.inr p.hγ.le))
                set clip : ℝ → intervalDomainPoint := fun x ↦
                  ⟨max 0 (min x 1), le_max_left 0 _,
                    max_le (by norm_num) (min_le_right x 1)⟩
                have hclip_cont : Continuous clip :=
                  Continuous.subtype_mk
                    (continuous_const.max (continuous_id.min continuous_const)) _
                set f : ℝ → ℝ :=
                  (fun x : intervalDomainPoint ↦ p.ν * (u s x) ^ p.γ) ∘ clip
                have hf_cont : Continuous f := hcont_src.comp hclip_cont
                have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
                  mul_nonneg p.hν.le (Real.rpow_nonneg (hu_nn_s _) _)
                have hf_coeff : ∀ k, cosineCoeffs f k =
                    (intervalNeumannResolverSourceCoeff p (u s) k).re := by
                  intro k
                  have hsrc_eq :
                      (intervalNeumannResolverSourceCoeff p (u s) k).re =
                      cosineCoeffs
                        (fun x ↦ p.ν * intervalDomainLift (u s) x ^ p.γ)
                        k := by
                    simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
                      Complex.ofReal_re]
                  rw [hsrc_eq]
                  exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
                    simp only [f, Function.comp, clip]
                    have hclip_eq : max 0 (min x 1) = x := by
                      rw [min_eq_left hx.2, max_eq_right hx.1]
                    simp only [hclip_eq, intervalDomainLift,
                      dif_pos (Set.mem_Icc.mpr hx)]) k
                have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
                  have h := resolverSourceCoeff_re_sq_summable_of_continuousOn
                    p hcont_u
                  simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
                    at h
                  exact h.congr (fun k ↦ by rw [hf_coeff])
                exact intervalNeumannResolverR_nonneg_of_nonneg_source
                  hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
              -- v₂ = R(w s)(y) ≥ 0  (resolver positivity for w)
              have hR_w_nonneg :
                  0 ≤ intervalNeumannResolverR p (w s) ⟨y, hy⟩ := by
                have hcont_src : Continuous
                    (fun x : intervalDomainPoint ↦ p.ν * (w s x) ^ p.γ) :=
                  continuous_const.mul
                    (hw_cont_s.rpow_const (fun x ↦ Or.inr p.hγ.le))
                set clip : ℝ → intervalDomainPoint := fun x ↦
                  ⟨max 0 (min x 1), le_max_left 0 _,
                    max_le (by norm_num) (min_le_right x 1)⟩
                have hclip_cont : Continuous clip :=
                  Continuous.subtype_mk
                    (continuous_const.max (continuous_id.min continuous_const)) _
                set f : ℝ → ℝ :=
                  (fun x : intervalDomainPoint ↦ p.ν * (w s x) ^ p.γ) ∘ clip
                have hf_cont : Continuous f := hcont_src.comp hclip_cont
                have hf_nonneg : ∀ z, 0 ≤ f z := fun z ↦
                  mul_nonneg p.hν.le (Real.rpow_nonneg (hw_nn_s _) _)
                have hf_coeff : ∀ k, cosineCoeffs f k =
                    (intervalNeumannResolverSourceCoeff p (w s) k).re := by
                  intro k
                  have hsrc_eq :
                      (intervalNeumannResolverSourceCoeff p (w s) k).re =
                      cosineCoeffs
                        (fun x ↦ p.ν * intervalDomainLift (w s) x ^ p.γ)
                        k := by
                    simp [cosineCoeffs, intervalNeumannResolverSourceCoeff,
                      Complex.ofReal_re]
                  rw [hsrc_eq]
                  exact cosineCoeffs_congr_on_Icc (fun x hx ↦ by
                    simp only [f, Function.comp, clip]
                    have hclip_eq : max 0 (min x 1) = x := by
                      rw [min_eq_left hx.2, max_eq_right hx.1]
                    simp only [hclip_eq, intervalDomainLift,
                      dif_pos (Set.mem_Icc.mpr hx)]) k
                have hâ : Summable (fun k ↦ (cosineCoeffs f k) ^ 2) := by
                  have h := resolverSourceCoeff_re_sq_summable_of_continuousOn
                    p hcont_w
                  simp only [intervalNeumannResolverSourceCoeff_zero, sub_zero]
                    at h
                  exact h.congr (fun k ↦ by rw [hf_coeff])
                exact intervalNeumannResolverR_nonneg_of_nonneg_source
                  hf_cont hf_nonneg hf_coeff hâ ⟨y, hy⟩
              -- v₁ ≥ 0 (lifted resolver value for u)
              have hv₁ : 0 ≤ intervalDomainLift
                  (intervalNeumannResolverR p (u s)) y := by
                simp [intervalDomainLift, hy]; exact hR_u_nonneg
              -- v₂ ≥ 0 (lifted resolver value for w)
              have hv₂ : 0 ≤ intervalDomainLift
                  (intervalNeumannResolverR p (w s)) y := by
                simp [intervalDomainLift, hy]; exact hR_w_nonneg
              -- |v₁ - v₂| ≤ C_RV * d (resolver value Lipschitz)
              have hvd : |intervalDomainLift
                    (intervalNeumannResolverR p (u s)) y
                  - intervalDomainLift
                    (intervalNeumannResolverR p (w s)) y|
                  ≤ C_RV * d := by
                simp [intervalDomainLift, hy]
                have h :=
                  resolverValue_diff_sup_le_of_bounded
                    p hγ_ge hcont_u hcont_w hmem_u hmem_w hlift_diff ⟨y, hy⟩
                calc |intervalNeumannResolverR p (u s) ⟨y, hy⟩
                      - intervalNeumannResolverR p (w s) ⟨y, hy⟩|
                    ≤ Real.sqrt (∑' k : ℕ,
                        (intervalNeumannResolverWeight p k) ^ 2) *
                      (2 * (p.ν * (p.γ * M ^ (p.γ - 1)) * d)) := h
                  _ = C_RV * d := by ring
              -- Apply chemFlux_div_lipschitz
              exact chemFlux_div_lipschitz p.hβ ha₂ hg₁ hg₂ hv₁ hv₂
                had hgd hvd hC_RG_nn
            · -- y ∉ [0,1]: both lifts = 0, fluxes = 0
              simp [intervalDomainLift, hy, zero_mul, zero_div, sub_self, abs_zero]
              exact mul_nonneg hC_Q_lip_nn hd_nn
          · -- s ∉ (0, T₀]: 0 - 0 = 0
            simp; exact mul_nonneg hC_Q_lip_nn hd_nn
        have hq_u_bound : ∀ s y, |q_u s y| ≤ C_Q_unif := by
          intro s y
          simp only [q_u]
          split_ifs with h
          · simpa [C_Q_unif, C_RG] using
              chemFluxLifted_bound_of_ball p hM.le
                (hu s h.1 h.2) (hu_nn s h.1 h.2) (huc s h.1 h.2) y
          · simp
            exact hC_Q_unif_nn
        have hq_w_bound : ∀ s y, |q_w s y| ≤ C_Q_unif := by
          intro s y
          simp only [q_w]
          split_ifs with h
          · simpa [C_Q_unif, C_RG] using
              chemFluxLifted_bound_of_ball p hM.le
                (hw s h.1 h.2) (hw_nn s h.1 h.2) (hwc s h.1 h.2) y
          · simp
            exact hC_Q_unif_nn
        have htime_cutoff :
            MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ q.1 ≤ T₀} := by
          exact (isOpen_Ioi.preimage continuous_fst).measurableSet.inter
            (isClosed_Iic.preimage continuous_fst).measurableSet
        have hq_u_meas : Measurable (Function.uncurry q_u) := by
          show Measurable (fun q : ℝ × ℝ => q_u q.1 q.2)
          simp only [q_u]
          exact Measurable.ite htime_cutoff
            (chemFluxLifted_joint_measurable hum) measurable_const
        have hq_w_meas : Measurable (Function.uncurry q_w) := by
          show Measurable (fun q : ℝ × ℝ => q_w q.1 q.2)
          simp only [q_w]
          exact Measurable.ite htime_cutoff
            (chemFluxLifted_joint_measurable hwm) measurable_const
        -- Gradient Duhamel difference bound
        -- Same by_cases IntervalIntegrable pattern as hV.
        -- Both not-integrable branches discharge via source joint measurability
        -- (same sorry as hV L1003/1008 — trajectory joint measurability).
        by_cases hint_Gu : IntervalIntegrable
            (fun s => deriv (fun z => intervalFullSemigroupOperator (t - s) (q_u s) z) x.1) volume 0 t
        · by_cases hint_Gw : IntervalIntegrable
              (fun s => deriv (fun z => intervalFullSemigroupOperator (t - s) (q_w s) z) x.1) volume 0 t
          · -- Both integrable: combine + per-slice gradient bound + integrate
            -- Per-slice integrability of q_u, q_w
            have hq_u_int : ∀ s, Integrable (q_u s) (intervalMeasure 1) := by
              intro s; simp only [q_u]; split_ifs with h
              · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
                  p (hu s h.1 h.2) hM.le (huc s h.1 h.2) (hu_nn s h.1 h.2)
              · exact integrable_zero ℝ ℝ (intervalMeasure 1)
            have hq_w_int : ∀ s, Integrable (q_w s) (intervalMeasure 1) := by
              intro s; simp only [q_w]; split_ifs with h
              · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
                  p (hw s h.1 h.2) hM.le (hwc s h.1 h.2) (hw_nn s h.1 h.2)
              · exact integrable_zero ℝ ℝ (intervalMeasure 1)
            -- Combine integrals
            rw [← intervalIntegral.integral_sub hint_Gu hint_Gw]
            -- Per-slice gradient difference bound via linearity + singular bound
            set Cg := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
            have hCQLd_nn : 0 ≤ C_Q_lip * d := mul_nonneg hC_Q_lip_nn hd_nn
            have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 t)),
                |deriv (fun z => intervalFullSemigroupOperator (t - s) (q_u s) z) x.1
                  - deriv (fun z => intervalFullSemigroupOperator (t - s) (q_w s) z) x.1|
                  ≤ Cg * (C_Q_lip * d) * (t - s) ^ (-(1/2) : ℝ) := by
              have hne : ∀ᵐ s ∂volume, s ≠ t := by
                rw [ae_iff]; simp only [not_not, Set.setOf_eq_eq_singleton]
                exact Real.volume_singleton
              refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
              filter_upwards [hne] with s hs hs_mem
              have hst : s < t := lt_of_le_of_ne hs_mem.2 hs
              have htms : 0 < t - s := sub_pos.mpr hst
              -- Linearize: deriv(S(τ)(f-g)) = deriv(S(τ)f) - deriv(S(τ)g)
              have hq_u_bdd : ∀ y, |q_u s y| ≤ C_Q_unif := hq_u_bound s
              have hq_w_bdd : ∀ y, |q_w s y| ≤ C_Q_unif := hq_w_bound s
              have hKu : ∀ z, Integrable
                  (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel
                    (t - s) z y * q_u s y) (intervalMeasure 1) :=
                fun z => ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
                  htms z (hq_u_int s) hC_Q_unif_nn hq_u_bdd
              have hKw : ∀ z, Integrable
                  (fun y => ShenWork.IntervalNeumannFullKernel.intervalNeumannFullKernel
                    (t - s) z y * q_w s y) (intervalMeasure 1) :=
                fun z => ShenWork.IntervalDuhamelIntegrability.kernel_mul_integrable_of_source_integrable
                  htms z (hq_w_int s) hC_Q_unif_nn hq_w_bdd
              have hdu := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
                htms (hq_u_int s).aestronglyMeasurable hq_u_bdd x.1
              have hdw := ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator_hasDerivAt_fst
                htms (hq_w_int s).aestronglyMeasurable hq_w_bdd x.1
              have hq_diff_int : Integrable (fun y => q_u s y - q_w s y) (intervalMeasure 1) :=
                (hq_u_int s).sub (hq_w_int s)
              have hlin := ShenWork.IntervalGradDuhamelBound.intervalFullSemigroupOperator_deriv_sub
                hKu hKw hdu.differentiableAt hdw.differentiableAt
              rw [← hlin]
              have h := ShenWork.IntervalNeumannFullKernel.intervalFullCoupledDuhamel_grad_integrand_pointwise_bound
                hs_mem.1 hst hq_diff_int hCQLd_nn (hq_diff_bound s) x.1
              linarith [mul_comm (Cg * (t - s) ^ (-(1/2) : ℝ)) (C_Q_lip * d)]
            -- Integrate the singular bound
            calc |∫ s in (0:ℝ)..t, (deriv (fun z => intervalFullSemigroupOperator (t - s) (q_u s) z) x.1
                    - deriv (fun z => intervalFullSemigroupOperator (t - s) (q_w s) z) x.1)|
                ≤ ∫ s in (0:ℝ)..t, |deriv (fun z => intervalFullSemigroupOperator (t - s) (q_u s) z) x.1
                    - deriv (fun z => intervalFullSemigroupOperator (t - s) (q_w s) z) x.1| :=
                  intervalIntegral.abs_integral_le_integral_abs ht.le
              _ ≤ ∫ s in (0:ℝ)..t, Cg * (C_Q_lip * d) * (t - s) ^ (-(1/2) : ℝ) :=
                  intervalIntegral.integral_mono_ae_restrict ht.le
                    (hint_Gu.sub hint_Gw).abs
                    ((ShenWork.IntervalGradDuhamelBound.intervalIntegrable_sub_rpow_neg_half t).const_mul
                      (Cg * (C_Q_lip * d)))
                    hptw
              _ = Cg * (C_Q_lip * d) * (2 * Real.sqrt t) := by
                  rw [intervalIntegral.integral_const_mul,
                    ShenWork.IntervalGradDuhamelBound.integral_sub_rpow_neg_half ht.le]
              _ ≤ Cg * (2 * Real.sqrt T₀) * (C_Q_lip * d) := by
                  have hsqrt : Real.sqrt t ≤ Real.sqrt T₀ := Real.sqrt_le_sqrt htT
                  have hCg_nn := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
                  have hsqT_nn := Real.sqrt_nonneg T₀
                  nlinarith [mul_nonneg hCg_nn hCQLd_nn, mul_nonneg hsqT_nn hCQLd_nn]
          · exfalso
            exact hint_Gw
              (ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
                ht hq_w_meas hC_Q_unif_nn hq_w_bound x.1)
        · exfalso
          exact hint_Gu
            (ShenWork.IntervalDuhamelIntegrability.gradDuhamel_intervalIntegrable_of_joint_measurable
              ht hq_u_meas hC_Q_unif_nn hq_u_bound x.1)
      -- Step 4: Assemble via gradientDuhamel_contraction_pointwise
      calc |(-p.χ₀) * (Gu - Gw) + (Vu - Vw)|
          ≤ (2 * |p.χ₀| * C_grad * C_Q_lip * Real.sqrt T₀ + C_L * T₀) * d :=
            gradientDuhamel_contraction_pointwise hG hV
        _ ≤ (A_picard * Real.sqrt T₀ + B_picard * T₀) * d := by
            have hA_ge : 2 * |p.χ₀| * C_grad * C_Q_lip ≤ A_picard := by
              calc 2 * |p.χ₀| * C_grad * C_Q_lip
                  ≤ 2 * |p.χ₀| * C_grad * C_Q_max := by
                    gcongr; exact le_max_right _ _
                _ ≤ A_picard := by simp only [A_picard]; linarith [hC_L_pos.le]
            have hB_ge : C_L ≤ B_picard := by
              simp only [B_picard]; linarith [hC_L_val_nn]
            have h1 : 2 * |p.χ₀| * C_grad * C_Q_lip * Real.sqrt T₀
                ≤ A_picard * Real.sqrt T₀ :=
              mul_le_mul_of_nonneg_right hA_ge (Real.sqrt_nonneg _)
            have h2 : C_L * T₀ ≤ B_picard * T₀ :=
              mul_le_mul_of_nonneg_right hB_ge hT₀.le
            nlinarith [hd_nn, Real.sqrt_nonneg T₀, hA_nn, hB_nn]
    hbase_diff := by
      intro t ht htT x
      have hu0 : |picardIter p u₀ 0 t x| ≤ M :=
        hbase_ball T₀ t ht htT x
      have hu1 : |picardIter p u₀ 1 t x| ≤ M :=
        hmapsTo_proof (picardIter p u₀ 0)
          (hbase_ball T₀) (hbase_nonneg T₀)
          (fun t' ht' htT' => hSg_cont t' ht') t ht htT x
      have htri : |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x|
          ≤ |picardIter p u₀ 1 t x| + |picardIter p u₀ 0 t x| := by
        calc |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x|
            = |picardIter p u₀ 1 t x + (-(picardIter p u₀ 0 t x))| := by ring_nf
          _ ≤ |picardIter p u₀ 1 t x| + |-(picardIter p u₀ 0 t x)| :=
              abs_add_le _ _
          _ = |picardIter p u₀ 1 t x| + |picardIter p u₀ 0 t x| := by
              rw [abs_neg]
      linarith
    hbase_meas := by
      have hSg_meas : Measurable (fun q : ℝ × ℝ =>
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
        intervalFullSemigroupOperator_joint_measurable
          (intervalDomainLift_measurable_of_continuous hu₀_cont)
      have hfield :
          (fun q : ℝ × ℝ => intervalDomainLift (picardIter p u₀ 0 q.1) q.2) =
            fun q : ℝ × ℝ =>
              if q.2 ∈ Set.Icc (0 : ℝ) 1 then
                intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
              else 0 := by
        funext q
        by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
        · simp [picardIter, intervalDomainLift, hy]
        · simp [picardIter, intervalDomainLift, hy]
      change Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift (picardIter p u₀ 0 q.1) q.2)
      rw [hfield]
      exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
        hSg_meas measurable_const
    hmeas_preserved := by
      intro w hum
      have hSg_meas : Measurable (fun q : ℝ × ℝ =>
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2) :=
        intervalFullSemigroupOperator_joint_measurable
          (intervalDomainLift_measurable_of_continuous hu₀_cont)
      have hQ_meas :
          Measurable (Function.uncurry (fun s y => chemFluxLifted p (w s) y)) := by
        simpa [Function.uncurry] using chemFluxLifted_joint_measurable hum
      have hGrad_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
          deriv (fun z : ℝ =>
            intervalFullSemigroupOperator (r.1.1 - r.2)
              (chemFluxLifted p (w r.2)) z) r.1.2) :=
        intervalFullSemigroupOperator_deriv_s_param_joint_measurable hQ_meas
      have hGrad : Measurable (fun q : ℝ × ℝ =>
          ∫ s in (0 : ℝ)..q.1,
            deriv (fun z : ℝ =>
              intervalFullSemigroupOperator (q.1 - s)
                (chemFluxLifted p (w s)) z) q.2) :=
        variable_interval_integral_measurable hGrad_integrand
      have hL_meas :
          Measurable (Function.uncurry (fun s y => logisticLifted p (w s) y)) := by
        simpa [Function.uncurry] using logisticLifted_joint_measurable hum
      have hVal_integrand : Measurable (fun r : (ℝ × ℝ) × ℝ =>
          intervalFullSemigroupOperator (r.1.1 - r.2)
            (logisticLifted p (w r.2)) r.1.2) :=
        intervalFullSemigroupOperator_s_param_joint_measurable hL_meas
      have hVal : Measurable (fun q : ℝ × ℝ =>
          ∫ s in (0 : ℝ)..q.1,
            intervalFullSemigroupOperator (q.1 - s)
              (logisticLifted p (w s)) q.2) :=
        variable_interval_integral_measurable hVal_integrand
      have hinside : Measurable (fun q : ℝ × ℝ =>
          intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
            + (-p.χ₀) * (∫ s in (0 : ℝ)..q.1,
              deriv (fun z : ℝ =>
                intervalFullSemigroupOperator (q.1 - s)
                  (chemFluxLifted p (w s)) z) q.2)
            + ∫ s in (0 : ℝ)..q.1,
              intervalFullSemigroupOperator (q.1 - s)
                (logisticLifted p (w s)) q.2) :=
        (hSg_meas.add (measurable_const.mul hGrad)).add hVal
      have hfield :
          (fun q : ℝ × ℝ =>
            intervalDomainLift
              (fun x : intervalDomainPoint => intervalGradientDuhamelMap p u₀ w q.1 x)
              q.2) =
            fun q : ℝ × ℝ =>
              if q.2 ∈ Set.Icc (0 : ℝ) 1 then
                intervalFullSemigroupOperator q.1 (intervalDomainLift u₀) q.2
                  + (-p.χ₀) * (∫ s in (0 : ℝ)..q.1,
                    deriv (fun z : ℝ =>
                      intervalFullSemigroupOperator (q.1 - s)
                        (chemFluxLifted p (w s)) z) q.2)
                  + ∫ s in (0 : ℝ)..q.1,
                    intervalFullSemigroupOperator (q.1 - s)
                      (logisticLifted p (w s)) q.2
              else 0 := by
        funext q
        by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
        · simp [intervalDomainLift, intervalGradientDuhamelMap, hy]
        · simp [intervalDomainLift, hy]
      change Measurable (fun q : ℝ × ℝ =>
        intervalDomainLift
          (fun x : intervalDomainPoint => intervalGradientDuhamelMap p u₀ w q.1 x)
          q.2)
      rw [hfield]
      exact Measurable.ite (measurableSet_Icc.preimage measurable_snd)
        hinside measurable_const
  }, rfl⟩

/-! ## Gradient mild solution data at the uniform horizon -/

/-- `gradientMildSolutionData_of_data` preserves the horizon (the `T`
field of the packaged record is definitionally `E.T`). -/
theorem gradientMildSolutionData_of_data_T {p : CM2Params}
    {u₀ : intervalDomainPoint → ℝ} (E : MildExistenceData p u₀) :
    (gradientMildSolutionData_of_data E).T = E.T := rfl

/-- **Threshold-uniform Picard solution data**: one horizon
`δ = δ(p, M_in, c) > 0` such that every continuous datum with
`|u₀| ≤ M_in` and `c ≤ u₀` has a packaged Picard mild solution
(`GradientMildSolutionData`) on exactly `[0, δ]`. -/
theorem thresholdGradientMildSolutionData_exists (p : CM2Params)
    {M_in c : ℝ} (hM_in : 0 < M_in) (hc : 0 < c)
    (hα_ge : 1 ≤ p.α) (hγ_ge : 1 ≤ p.γ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u₀ : intervalDomainPoint → ℝ,
        Continuous u₀ →
        (∀ x, |u₀ x| ≤ M_in) →
        (∀ x, c ≤ u₀ x) →
        ∃ D : GradientMildSolutionData p u₀, D.T = δ := by
  obtain ⟨δ, hδ, h⟩ :=
    thresholdMildExistenceData_exists p hM_in hc hα_ge hγ_ge
  refine ⟨δ, hδ, ?_⟩
  intro u₀ hcont hbound hlb
  obtain ⟨E, hET⟩ := h u₀ hcont hbound hlb
  exact ⟨gradientMildSolutionData_of_data E,
    by rw [gradientMildSolutionData_of_data_T, hET]⟩

/-! ## Initial approach for any packaged mild solution (G5 + O(√t) corrections)

This discharges the `hInitialApproach` component of the per-datum
frontier interfaces (`PerDatumSpectralFrontier`,
`IntervalDomainGradientMildHalfStep*FrontierCoreLocalData`,
`PicardRestartFrontier`) for every continuous positive datum: it holds
GENERICALLY for any `GradientMildSolutionData`, with no reference to
how the data was constructed. -/

/-- Clamp a real to the unit-interval subtype. -/
private def unitClip (y : ℝ) : intervalDomainPoint :=
  ⟨max 0 (min y 1), le_max_left 0 _,
    max_le (by norm_num) (min_le_right y 1)⟩

private theorem unitClip_continuous :
    Continuous fun y : ℝ => unitClip y := by
  unfold unitClip
  exact Continuous.subtype_mk
    (continuous_const.max (continuous_id.min continuous_const)) _

private theorem unitClip_of_mem {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    unitClip y = ⟨y, hy⟩ := by
  apply Subtype.ext
  simp only [unitClip]
  rw [min_eq_left hy.2, max_eq_right hy.1]

set_option maxHeartbeats 800000 in
/-- **Initial approach of the gradient mild map, generically.**  For ANY
packaged mild solution `D : GradientMildSolutionData p u₀` with
continuous datum, `Φ(u₀, D.u)(t, ·) → u₀` uniformly as `t → 0⁺`:

* the semigroup part converges uniformly by G5
  (`intervalFullSemigroup_tendstoUniformlyOn`, applied to the clipped
  continuous extension of `u₀`, which agrees with the lift on `[0,1]`);
* the Duhamel corrections are `≤ A·√t + B·t` with constants depending
  only on `D.M`, by the universal Duhamel bounds instantiated at the
  horizon `t` itself. -/
theorem gradientMildSolutionData_initialApproach (p : CM2Params)
    {u₀ : intervalDomainPoint → ℝ} (hu₀_cont : Continuous u₀)
    (D : GradientMildSolutionData p u₀) :
    ∀ ε, 0 < ε → ∃ δ > 0, ∀ t, 0 < t → t < δ →
      ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ D.u t x - u₀ x| < ε := by
  intro ε hε
  -- Constants from the ball radius D.M.
  set M := D.M with hMdef
  have hM : 0 < M := D.hM
  set C_L_val := M * (p.a + p.b * M ^ p.α) with hCLval
  have hC_L_val_nn : (0 : ℝ) ≤ C_L_val :=
    mul_nonneg hM.le (add_nonneg p.ha
      (mul_nonneg p.hb (Real.rpow_nonneg hM.le _)))
  set C_RG := Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
    (2 * (p.ν * M ^ p.γ)) with hCRG
  have hC_RG_nn : (0 : ℝ) ≤ C_RG :=
    mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM.le _)))
  set C_Q_unif := M * C_RG with hCQunif
  have hC_Q_unif_nn : (0 : ℝ) ≤ C_Q_unif := mul_nonneg hM.le hC_RG_nn
  set C_grad := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
    with hCgrad
  have hC_grad_nn : (0 : ℝ) ≤ C_grad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  set A_corr := 2 * |p.χ₀| * C_grad * C_Q_unif with hAcorr
  set B_corr := C_L_val with hBcorr
  have hA_nn : (0 : ℝ) ≤ A_corr := by positivity
  have hB_nn : (0 : ℝ) ≤ B_corr := hC_L_val_nn
  -- δ₂: correction horizon with A√t + Bt < ε/2.
  obtain ⟨δ₂, hδ₂, hδ₂small⟩ :=
    exists_small_contraction_time_target hA_nn hB_nn
      (show (0:ℝ) < ε / 2 by linarith)
  -- δ₁: G5 horizon for the clipped extension.
  set f : ℝ → ℝ := fun y => u₀ (unitClip y) with hfdef
  have hf_cont : Continuous f := hu₀_cont.comp unitClip_continuous
  have hG5 :=
    ShenWork.IntervalSemigroupUniform.intervalFullSemigroup_tendstoUniformlyOn
      f hf_cont
  rw [Metric.tendstoUniformlyOn_iff] at hG5
  have hev := hG5 (ε / 2) (by linarith)
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  obtain ⟨δ₁, hδ₁mem, hδ₁sub⟩ := hev
  have hδ₁ : 0 < δ₁ := hδ₁mem
  -- The combined horizon.
  refine ⟨min (min δ₁ δ₂) D.T, lt_min (lt_min hδ₁ hδ₂) D.hT, ?_⟩
  intro t ht htδ x
  have htδ₁ : t < δ₁ := lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_left _ _))
  have htδ₂ : t < δ₂ := lt_of_lt_of_le htδ ((min_le_left _ _).trans (min_le_right _ _))
  have htT : t ≤ D.T := le_of_lt (lt_of_lt_of_le htδ (min_le_right _ _))
  -- Semigroup part: S(t)(lift u₀) = S(t)f on the subtype, and G5 bounds it.
  have hlift_eq_f : ∀ y ∈ Set.Icc (0:ℝ) 1, intervalDomainLift u₀ y = f y := by
    intro y hy
    simp only [intervalDomainLift, dif_pos hy, hfdef, unitClip_of_mem hy]
  have hSg_eq : intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
      = intervalFullSemigroupOperator t f x.1 := by
    unfold intervalFullSemigroupOperator
    apply MeasureTheory.integral_congr_ae
    have : ∀ᵐ y ∂(ShenWork.IntervalDomain.intervalMeasure 1),
        y ∈ Set.Icc (0:ℝ) 1 := by
      simp only [ShenWork.IntervalDomain.intervalMeasure,
        ShenWork.IntervalDomain.intervalSet]
      exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
        (Filter.Eventually.of_forall fun y hy => hy)
    filter_upwards [this] with y hy
    rw [hlift_eq_f y hy]
  have hSg_close : |intervalFullSemigroupOperator t
      (intervalDomainLift u₀) x.1 - u₀ x| < ε / 2 := by
    rw [hSg_eq]
    have hfx : f x.1 = u₀ x := by
      simp only [hfdef, unitClip_of_mem x.2]
      rfl
    have hdist := hδ₁sub ⟨ht, htδ₁⟩ x.1 x.2
    rw [Real.dist_eq] at hdist
    calc |intervalFullSemigroupOperator t f x.1 - u₀ x|
        = |f x.1 - intervalFullSemigroupOperator t f x.1| := by
          rw [hfx, abs_sub_comm]
      _ < ε / 2 := hdist
  -- Correction part: extended sources bounded for ALL (s, y).
  set r_val : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then logisticLifted p (D.u s) y else 0 with hrval
  have hr_val_bound : ∀ s y, |r_val s y| ≤ C_L_val := by
    intro s y; simp only [hrval]
    split_ifs with h
    · exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
        p hM (fun z => D.hbound s h.1 h.2 z) y
    · simp; exact hC_L_val_nn
  set r_grad : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ D.T then chemFluxLifted p (D.u s) y else 0 with hrgrad
  have hr_grad_bound : ∀ s y, |r_grad s y| ≤ C_Q_unif := by
    intro s y; simp only [hrgrad]
    split_ifs with h
    · simpa [C_Q_unif, C_RG] using
        chemFluxLifted_bound_of_ball p hM.le
          (D.hbound s h.1 h.2) (D.hnonneg s h.1 h.2)
          (D.hcont s h.1 h.2) y
    · simp; exact hC_Q_unif_nn
  have hval_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (D.u s)) x.1)
      = ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (r_val s) x.1 := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    simp only [hrval, if_pos (And.intro hs.1 (hs.2.trans htT))]
  have hgrad_eq : (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (D.u s)) z) x.1)
      = ∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (r_grad s) z) x.1 := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    simp only [hrgrad, if_pos (And.intro hs.1 (hs.2.trans htT))]
  -- Universal bounds at the horizon t itself.
  have hterm3 : |(∫ s in (0:ℝ)..t,
      intervalFullSemigroupOperator (t - s)
        (logisticLifted p (D.u s)) x.1)| ≤ t * C_L_val := by
    rw [hval_eq]
    exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
      ht le_rfl hC_L_val_nn hr_val_bound x.1
  have hterm2 : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
      deriv (fun z => intervalFullSemigroupOperator (t - s)
        (chemFluxLifted p (D.u s)) z) x.1)|
      ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt t) * C_Q_unif) := by
    rw [abs_mul, abs_neg]
    gcongr
    rw [hgrad_eq]
    exact ShenWork.IntervalDuhamelIntegrability.gradDuhamel_sup_bound_universal
      ht le_rfl hC_Q_unif_nn hr_grad_bound x.1
  -- The corrections are at most A√t + Bt < ε/2.
  have hcorr : |(-p.χ₀) * (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (D.u s)) z) x.1)
      + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) x.1)| < ε / 2 := by
    have hsqrt_le : Real.sqrt t ≤ Real.sqrt δ₂ := Real.sqrt_le_sqrt htδ₂.le
    have hAB : A_corr * Real.sqrt t + B_corr * t
        ≤ A_corr * Real.sqrt δ₂ + B_corr * δ₂ :=
      add_le_add (mul_le_mul_of_nonneg_left hsqrt_le hA_nn)
        (mul_le_mul_of_nonneg_left htδ₂.le hB_nn)
    calc |(-p.χ₀) * (∫ s in (0:ℝ)..t,
          deriv (fun z => intervalFullSemigroupOperator (t - s)
            (chemFluxLifted p (D.u s)) z) x.1)
        + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1)|
        ≤ |(-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x.1)|
          + |(∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) x.1)| := abs_add_le _ _
      _ ≤ |p.χ₀| * (C_grad * (2 * Real.sqrt t) * C_Q_unif)
          + t * C_L_val := add_le_add hterm2 hterm3
      _ = A_corr * Real.sqrt t + B_corr * t := by
          simp only [hAcorr, hBcorr]; ring
      _ ≤ A_corr * Real.sqrt δ₂ + B_corr * δ₂ := hAB
      _ < ε / 2 := hδ₂small
  -- Assemble.
  unfold intervalGradientDuhamelMap
  have habs := abs_add_le
    (intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x)
    ((-p.χ₀) * (∫ s in (0:ℝ)..t,
        deriv (fun z => intervalFullSemigroupOperator (t - s)
          (chemFluxLifted p (D.u s)) z) x.1)
      + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
          (logisticLifted p (D.u s)) x.1))
  calc |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
        + (-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x.1)
        + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
            (logisticLifted p (D.u s)) x.1) - u₀ x|
      = |(intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x)
        + ((-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x.1)
          + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) x.1))| := by congr 1; ring
    _ ≤ |intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1 - u₀ x|
        + |(-p.χ₀) * (∫ s in (0:ℝ)..t,
            deriv (fun z => intervalFullSemigroupOperator (t - s)
              (chemFluxLifted p (D.u s)) z) x.1)
          + (∫ s in (0:ℝ)..t, intervalFullSemigroupOperator (t - s)
              (logisticLifted p (D.u s)) x.1)| := habs
    _ < ε / 2 + ε / 2 := add_lt_add hSg_close hcorr
    _ = ε := by ring

end ShenWork.IntervalMildPicardThreshold
