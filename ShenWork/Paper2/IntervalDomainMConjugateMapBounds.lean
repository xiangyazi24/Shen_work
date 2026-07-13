import ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalConjugateLogisticDiffBall

/-!
# Positive-strip bounds for the faithful general-`m` mild map

This file supplies the B-form Duhamel integrability and contraction estimates
for the published flux `u^m v_x / (1+v)^β`.  The constants depend only on the
fixed positive strip `c ≤ u ≤ M`, so the result is suitable for the generic
positive-floor Picard construction.
-/

open MeasureTheory Set
open scoped Topology Interval

noncomputable section

namespace ShenWork.Paper2.IntervalDomainMConjugateMapBounds

open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalNeumannFullKernel
  (intervalFullSemigroupOperator intervalNeumannFullKernel)
open ShenWork.IntervalConjugateDuhamelMap
  (intervalConjugateKernelOperator conjugateDuhamel_sup_bound
   conjugateDuhamel_diff_sup_bound)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalPositiveFloorNonlinearLipschitz
  (powerLip powerLip_nonneg)
open ShenWork.Paper2.IntervalDomainMConjugateDuhamelMap
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant heatGradientLinftyLinftyConstant_nonneg)

/-- Uniform size of the faithful general-`m` flux on `0 < c ≤ u ≤ M`. -/
def chemFluxMSupConstant (p : CM2Params) (M : ℝ) : ℝ :=
  M ^ p.m *
    (Real.sqrt (∑' k : ℕ, (intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * (p.ν * M ^ p.γ)))

/-- Lipschitz constant of the faithful general-`m` flux on `c ≤ u ≤ M`. -/
def chemFluxMLipschitzConstant (p : CM2Params) (c M : ℝ) : ℝ :=
  powerLip p.m c M *
      (Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ))) +
    M ^ p.m *
      (Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M))) +
    M ^ p.m *
      (Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * (p.ν * M ^ p.γ))) * p.β *
      (Real.sqrt (∑' k : ℕ,
        (intervalNeumannResolverWeight p k) ^ 2) *
          (2 * (p.ν * powerLip p.γ c M)))

theorem chemFluxMSupConstant_nonneg
    (p : CM2Params) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ chemFluxMSupConstant p M := by
  unfold chemFluxMSupConstant
  exact mul_nonneg (Real.rpow_nonneg hM _)
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _))))

theorem chemFluxMLipschitzConstant_nonneg
    (p : CM2Params) {c M : ℝ} (hc : 0 < c) (hcM : c ≤ M) :
    0 ≤ chemFluxMLipschitzConstant p c M := by
  have hM : 0 ≤ M := hc.le.trans hcM
  have hLm : 0 ≤ powerLip p.m c M := powerLip_nonneg p.hm hc hcM
  have hLγ : 0 ≤ powerLip p.γ c M := powerLip_nonneg p.hγ hc hcM
  unfold chemFluxMLipschitzConstant
  have hBG : 0 ≤ Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * M ^ p.γ)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num)
        (mul_nonneg p.hν.le (Real.rpow_nonneg hM _)))
  have hLG : 0 ≤ Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLγ))
  have hLR : 0 ≤ Real.sqrt (∑' k : ℕ,
      (intervalNeumannResolverWeight p k) ^ 2) *
        (2 * (p.ν * powerLip p.γ c M)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le hLγ))
  exact add_nonneg
    (add_nonneg (mul_nonneg hLm hBG)
      (mul_nonneg (Real.rpow_nonneg hM _) hLG))
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg hM _) hBG) p.hβ) hLR)

/-- The faithful general-`m` B-form leg is time-integrable on the active
window.  The zero extension is used only to feed the global measurable-bound
theorem; on `(0,t]` it agrees with the actual flux. -/
theorem chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
    (p : CM2Params) {T M c CQ : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hCQ : 0 ≤ CQ)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ s, 0 < s → s ≤ T → ∀ x, |w s x| ≤ M)
    (hfloor : ∀ s, 0 < s → s ≤ T → ∀ x, c ≤ w s x)
    (hcont : HasContinuousSlices T w) (hmeas : HasJointMeasurability w)
    (hQbound : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxMLifted p (w s) y| ≤ CQ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (chemFluxMLifted p (w s)) x.1) volume 0 t := by
  let q : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ T then chemFluxMLifted p (w s) y else 0
  have hq_meas : Measurable (fun z : ℝ × ℝ => q z.1 z.2) := by
    have hbase := chemFluxMLifted_uncurry_measurable (p := p) (u := w) hmeas
    exact Measurable.ite
      (((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
        ((isClosed_Iic.preimage continuous_fst).measurableSet))
      hbase measurable_const
  have hq_int : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s
    simp only [q]
    split_ifs with hs
    · exact chemFluxMLifted_integrable_of_pos_slice p hc hcM
        (hbound s hs.1 hs.2) (hfloor s hs.1 hs.2) (hcont s hs.1 hs.2)
    · exact integrable_zero ℝ ℝ (intervalMeasure 1)
  have hq_sup : ∀ s y, |q s y| ≤ CQ := by
    intro s y
    simp only [q]
    split_ifs with hs
    · exact hQbound s hs.1 hs.2 y
    · simpa using hCQ
  have hcut :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      ht hCQ hq_meas hq_int hq_sup (x := x.1)
  have heq : Set.EqOn
      (fun s => intervalConjugateKernelOperator (t - s) (q s) x.1)
      (fun s => intervalConjugateKernelOperator (t - s)
        (chemFluxMLifted p (w s)) x.1) (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hqs : q s = chemFluxMLifted p (w s) := by
      funext y
      simp only [q, if_pos (And.intro hs.1 (hs.2.trans htT))]
    change intervalConjugateKernelOperator (t - s) (q s) x.1 =
      intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1
    rw [hqs]
  exact hcut.congr heq

/-- Time-integrability of the faithful flux difference on the active window. -/
theorem chemFluxMLifted_diff_duhamel_intervalIntegrable_of_positive_cone
    (p : CM2Params) {T M c D : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hD : 0 ≤ D)
    {u w : ℝ → intervalDomainPoint → ℝ}
    (hub : ∀ s, 0 < s → s ≤ T → ∀ x, |u s x| ≤ M)
    (huf : ∀ s, 0 < s → s ≤ T → ∀ x, c ≤ u s x)
    (hwb : ∀ s, 0 < s → s ≤ T → ∀ x, |w s x| ≤ M)
    (hwf : ∀ s, 0 < s → s ≤ T → ∀ x, c ≤ w s x)
    (huc : HasContinuousSlices T u) (hwc : HasContinuousSlices T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hQdiff : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y| ≤ D)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y) x.1)
      volume 0 t := by
  let q : ℝ → ℝ → ℝ := fun s y =>
    if 0 < s ∧ s ≤ T then
      chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y else 0
  have hq_meas : Measurable (fun z : ℝ × ℝ => q z.1 z.2) := by
    have hu := chemFluxMLifted_uncurry_measurable (p := p) (u := u) hum
    have hw := chemFluxMLifted_uncurry_measurable (p := p) (u := w) hwm
    exact Measurable.ite
      (((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
        ((isClosed_Iic.preimage continuous_fst).measurableSet))
      (hu.sub hw) measurable_const
  have hq_int : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s
    simp only [q]
    split_ifs with hs
    · exact (chemFluxMLifted_integrable_of_pos_slice p hc hcM
        (hub s hs.1 hs.2) (huf s hs.1 hs.2) (huc s hs.1 hs.2)).sub
        (chemFluxMLifted_integrable_of_pos_slice p hc hcM
          (hwb s hs.1 hs.2) (hwf s hs.1 hs.2) (hwc s hs.1 hs.2))
    · exact integrable_zero ℝ ℝ (intervalMeasure 1)
  have hq_sup : ∀ s y, |q s y| ≤ D := by
    intro s y
    simp only [q]
    split_ifs with hs
    · exact hQdiff s hs.1 hs.2 y
    · simpa using hD
  have hcut :=
    ShenWork.IntervalConjugateChemFluxIntegrable.conjugateDuhamel_intervalIntegrable_of_measurable_bound
      ht hD hq_meas hq_int hq_sup (x := x.1)
  have heq : Set.EqOn
      (fun s => intervalConjugateKernelOperator (t - s) (q s) x.1)
      (fun s => intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y) x.1)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hqs : q s =
        fun y => chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y := by
      funext y
      simp only [q, if_pos (And.intro hs.1 (hs.2.trans htT))]
    change intervalConjugateKernelOperator (t - s) (q s) x.1 =
      intervalConjugateKernelOperator (t - s)
        (fun y => chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y) x.1
    rw [hqs]
  exact hcut.congr heq

/-- Uniform B-form Duhamel bound for the faithful general-`m` flux. -/
theorem conjugateMDuhamel_sup_bound_of_positive_cone
    (p : CM2Params) {T M c CQ : ℝ}
    (hc : 0 < c) (hcM : c ≤ M) (hCQ : 0 ≤ CQ)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ s, 0 < s → s ≤ T → ∀ x, |w s x| ≤ M)
    (hfloor : ∀ s, 0 < s → s ≤ T → ∀ x, c ≤ w s x)
    (hcont : HasContinuousSlices T w) (hmeas : HasJointMeasurability w)
    (hQbound : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxMLifted p (w s) y| ≤ CQ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ := by
  exact conjugateDuhamel_sup_bound ht htT
    (fun s hs hsT => chemFluxMLifted_integrable_of_pos_slice p hc hcM
      (hbound s hs hsT) (hfloor s hs hsT) (hcont s hs hsT))
    hCQ hQbound x.1
    (chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
      p hc hcM hCQ hbound hfloor hcont hmeas hQbound ht htT x)

private def endpointZero : intervalDomainPoint :=
  ⟨0, by constructor <;> norm_num⟩

/-- The faithful general-`m` B-form map is contractive on a fixed positive
strip.  No lower bound on `m`, `α`, or `γ` beyond the parameter assumptions is
used. -/
theorem intervalConjugateDuhamelMapM_diff_bound_of_positive_cone
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {T M c CL d : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hcM : c ≤ M)
    (hCL : 0 ≤ CL)
    (hCL_lip : ∀ r s : ℝ, |r| ≤ M → |s| ≤ M →
      |r * (p.a - p.b * r ^ p.α) - s * (p.a - p.b * s ^ p.α)| ≤
        CL * |r - s|)
    {u w : ℝ → intervalDomainPoint → ℝ}
    (hub : ∀ s, 0 < s → s ≤ T → ∀ x, |u s x| ≤ M)
    (huf : ∀ s, 0 < s → s ≤ T → ∀ x, c ≤ u s x)
    (hwb : ∀ s, 0 < s → s ≤ T → ∀ x, |w s x| ≤ M)
    (hwf : ∀ s, 0 < s → s ≤ T → ∀ x, c ≤ w s x)
    (huc : HasContinuousSlices T u) (hwc : HasContinuousSlices T w)
    (hum : HasJointMeasurability u) (hwm : HasJointMeasurability w)
    (hd : ∀ s, 0 < s → s ≤ T → ∀ x, |u s x - w s x| ≤ d)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |intervalConjugateDuhamelMapM p u₀ u t x -
        intervalConjugateDuhamelMapM p u₀ w t x| ≤
      (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) *
          chemFluxMLipschitzConstant p c M) + T * CL) * d := by
  have hM : 0 < M := hc.trans_le hcM
  have hd_nn : 0 ≤ d :=
    (abs_nonneg _).trans (hd T hT le_rfl endpointZero)
  have hCQ_nn : 0 ≤ chemFluxMLipschitzConstant p c M :=
    chemFluxMLipschitzConstant_nonneg p hc hcM
  have hCQsup_nn : 0 ≤ chemFluxMSupConstant p M :=
    chemFluxMSupConstant_nonneg p hM.le
  have hq_diff : ∀ s, 0 < s → s ≤ T → ∀ y,
      |chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y| ≤
        chemFluxMLipschitzConstant p c M * d := by
    intro s hs hsT y
    simpa [chemFluxMLipschitzConstant] using
      chemFluxMLifted_diff_bound_of_pos_slice p hc hcM hd_nn
        (hub s hs hsT) (huf s hs hsT) (huc s hs hsT)
        (hwb s hs hsT) (hwf s hs hsT) (hwc s hs hsT)
        (hd s hs hsT) y
  have hq_int_diff : ∀ s, 0 < s → s ≤ T → Integrable
      (fun y => chemFluxMLifted p (u s) y - chemFluxMLifted p (w s) y)
      (intervalMeasure 1) := by
    intro s hs hsT
    exact (chemFluxMLifted_integrable_of_pos_slice p hc hcM
      (hub s hs hsT) (huf s hs hsT) (huc s hs hsT)).sub
      (chemFluxMLifted_integrable_of_pos_slice p hc hcM
        (hwb s hs hsT) (hwf s hs hsT) (hwc s hs hsT))
  have hQsup : ∀ (z : ℝ → intervalDomainPoint → ℝ),
      (∀ s, 0 < s → s ≤ T → ∀ y, |z s y| ≤ M) →
      (∀ s, 0 < s → s ≤ T → ∀ y, c ≤ z s y) →
      HasContinuousSlices T z →
      ∀ s, 0 < s → s ≤ T → ∀ y,
        |chemFluxMLifted p (z s) y| ≤ chemFluxMSupConstant p M := by
    intro z hzb hzf hzc s hs hsT y
    simpa [chemFluxMSupConstant] using
      chemFluxMLifted_abs_le_of_pos_slice p hc hcM
        (hzb s hs hsT) (hzf s hs hsT) (hzc s hs hsT) y
  have hkernel : ∀ (z : ℝ → intervalDomainPoint → ℝ),
      (∀ s, 0 < s → s ≤ T → ∀ y, |z s y| ≤ M) →
      (∀ s, 0 < s → s ≤ T → ∀ y, c ≤ z s y) →
      HasContinuousSlices T z →
      ∀ s, 0 < s → s ≤ T → Integrable
        (fun y => deriv (fun y' => intervalNeumannFullKernel (t - s) x.1 y') y *
          chemFluxMLifted p (z s) y) (intervalMeasure 1) := by
    intro z hzb hzf hzc s hs hsT
    have hKint : Integrable
        (fun y => deriv (fun y' => intervalNeumannFullKernel (t - s) x.1 y') y)
        (intervalMeasure 1) := by
      by_cases hts : 0 < t - s
      · simp only [intervalMeasure, ShenWork.IntervalDomain.intervalSet]
        exact (ShenWork.IntervalNeumannFullKernel.continuousOn_deriv_intervalNeumannFullKernel_snd
          hts x.1).integrableOn_Icc
      · have hk : (fun y' : ℝ => intervalNeumannFullKernel (t - s) x.1 y') =
            fun _ : ℝ => 0 := by
          funext y'
          simp only [intervalNeumannFullKernel]
          have hseries : (fun k : ℤ =>
              heatKernel (t - s) (x.1 - y' + 2 * (k : ℝ)) +
                heatKernel (t - s) (x.1 + y' + 2 * (k : ℝ))) =
              fun _ : ℤ => 0 := by
            funext k
            rw [ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
              ShenWork.IntervalNeumannFullKernel.heatKernel_of_nonpos (not_lt.mp hts),
              add_zero]
          rw [hseries]
          exact tsum_zero
        simp [hk]
    have hQint := chemFluxMLifted_integrable_of_pos_slice p hc hcM
      (hzb s hs hsT) (hzf s hs hsT) (hzc s hs hsT)
    exact hKint.mul_bdd hQint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using hQsup z hzb hzf hzc s hs hsT y)
  have hBu := chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
    p hc hcM hCQsup_nn hub huf huc hum (hQsup u hub huf huc) ht htT x
  have hBw := chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
    p hc hcM hCQsup_nn hwb hwf hwc hwm (hQsup w hwb hwf hwc) ht htT x
  have hBdiff := chemFluxMLifted_diff_duhamel_intervalIntegrable_of_positive_cone
    p hc hcM (mul_nonneg hCQ_nn hd_nn)
      hub huf hwb hwf huc hwc hum hwm hq_diff ht htT x
  have hchem :
      |(∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (u s)) x.1) -
        (∫ s in (0 : ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxMLifted p (w s)) x.1)| ≤
        heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) *
          (chemFluxMLipschitzConstant p c M * d) := by
    rw [← intervalIntegral.integral_sub hBu hBw]
    exact conjugateDuhamel_diff_sup_bound ht htT
      (mul_nonneg hCQ_nn hd_nn) hq_diff hq_int_diff x.1
      (hkernel u hub huf huc) (hkernel w hwb hwf hwc) hBdiff
  have hnonneg_u : ∀ s, 0 < s → s ≤ T → ∀ y, 0 ≤ u s y := by
    intro s hs hsT y
    exact hc.le.trans (huf s hs hsT y)
  have hnonneg_w : ∀ s, 0 < s → s ≤ T → ∀ y, 0 ≤ w s y := by
    intro s hs hsT y
    exact hc.le.trans (hwf s hs hsT y)
  have hlog :=
    ShenWork.IntervalConjugateLogisticDiffBall.logistic_duhamel_diff_bound_of_ball
      p hT hM hCL hd_nn hCL_lip hub hnonneg_u hwb hnonneg_w
      huc hwc hum hwm hd ht htT x
  have hcancel :
      intervalConjugateDuhamelMapM p u₀ u t x -
          intervalConjugateDuhamelMapM p u₀ w t x =
        (-p.χ₀) *
          ((∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (u s)) x.1) -
            (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (w s)) x.1)) +
          ((∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1) -
            (∫ s in (0 : ℝ)..t,
              intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1)) := by
    simp only [intervalConjugateDuhamelMapM]
    ring
  rw [hcancel]
  calc
    |(-p.χ₀) *
          ((∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (u s)) x.1) -
            (∫ s in (0 : ℝ)..t,
              intervalConjugateKernelOperator (t - s)
                (chemFluxMLifted p (w s)) x.1)) +
        ((∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (u s)) x.1) -
          (∫ s in (0 : ℝ)..t,
            intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1))|
        ≤ |p.χ₀| *
            (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) *
              (chemFluxMLipschitzConstant p c M * d)) + T * (CL * d) := by
          calc
            _ ≤ |(-p.χ₀) *
                  ((∫ s in (0 : ℝ)..t,
                      intervalConjugateKernelOperator (t - s)
                        (chemFluxMLifted p (u s)) x.1) -
                    (∫ s in (0 : ℝ)..t,
                      intervalConjugateKernelOperator (t - s)
                        (chemFluxMLifted p (w s)) x.1))| +
                |(∫ s in (0 : ℝ)..t,
                    intervalFullSemigroupOperator (t - s)
                      (logisticLifted p (u s)) x.1) -
                  (∫ s in (0 : ℝ)..t,
                    intervalFullSemigroupOperator (t - s)
                      (logisticLifted p (w s)) x.1)| := abs_add_le _ _
            _ ≤ _ := add_le_add
              (by simpa [abs_mul] using
                mul_le_mul_of_nonneg_left hchem (abs_nonneg p.χ₀)) hlog
    _ = (|p.χ₀| * (heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) *
          chemFluxMLipschitzConstant p c M) + T * CL) * d := by ring

#print axioms chemFluxMLifted_duhamel_intervalIntegrable_of_positive_cone
#print axioms chemFluxMLifted_diff_duhamel_intervalIntegrable_of_positive_cone
#print axioms conjugateMDuhamel_sup_bound_of_positive_cone
#print axioms intervalConjugateDuhamelMapM_diff_bound_of_positive_cone

end ShenWork.Paper2.IntervalDomainMConjugateMapBounds
