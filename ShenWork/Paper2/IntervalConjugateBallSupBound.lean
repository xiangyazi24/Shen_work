/-
  ShenWork/Paper2/IntervalConjugateBallSupBound.lean

  Ball-conditional sup bounds for the two correction Duhamel legs of the
  conjugate map: the hypotheses on the source are required only on the active
  window `(0,T]` (as the ball trajectory provides), via a `0`-extension cutoff
  that leaves the `(0,t]`-supported time integrals unchanged.

    |∫₀ᵗ B_N(t−s) Q(w s) x| ≤ Cg·(2√T)·CQ,
    |∫₀ᵗ S(t−s) L(w s) x|  ≤ T·CL,

  for a `(0,T]`-bounded nonnegative continuous-slice jointly-measurable `w`.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace ShenWork.IntervalConjugateBallSupBound

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.HeatKernelGradientEstimates (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (conjugateChemFlux_duhamel_intervalIntegrable_of_ball)

/-- **Ball-conditional conjugate chemotaxis Duhamel sup bound.** -/
theorem conjugateDuhamel_sup_bound_of_ball
    (p : CM2Params) {T M CQ : ℝ} (hM : 0 ≤ M) (hCQ : 0 ≤ CQ)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M)
    (hnonneg : ∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x)
    (hcont : HasContinuousSlices T w) (hmeas : HasJointMeasurability w)
    (hQbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y, |chemFluxLifted p (w τ) y| ≤ CQ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ := by
  -- cutoff source `q`: raw flux on `(0,T]`, else 0
  set q : ℝ → ℝ → ℝ :=
    fun s yy => if 0 < s ∧ s ≤ T then chemFluxLifted p (w s) yy else 0 with hq
  have hq_sup : ∀ s y, |q s y| ≤ CQ := by
    intro s yy; simp only [hq]; split_ifs with h
    · exact hQbound s h.1 h.2 yy
    · simpa using hCQ
  have hq_meas : Measurable (fun z : ℝ × ℝ => q z.1 z.2) := by
    have hbase := ShenWork.Paper2.chemFluxLifted_uncurry_measurable (p := p) (u := w) hmeas
    simp only [hq]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hq_int : ∀ s, Integrable (q s) (intervalMeasure 1) := by
    intro s; simp only [hq]; split_ifs with h
    · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
        p (hbound s h.1 h.2) hM (hcont s h.1 h.2) (hnonneg s h.1 h.2)
    · simp
  -- time-integrable on (0,t) for the cutoff source
  have hB_int_q : IntervalIntegrable
      (fun s : ℝ => intervalConjugateKernelOperator (t - s) (q s) x.1) volume 0 t := by
    have hcongr : Set.EqOn
        (fun s => intervalConjugateKernelOperator (t - s) (q s) x.1)
        (fun s => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
        (Set.uIoc 0 t) := by
      intro s hs; rw [Set.uIoc_of_le ht.le] at hs
      simp only [hq, if_pos (And.intro hs.1 (le_trans hs.2 htT))]
    exact (conjugateChemFlux_duhamel_intervalIntegrable_of_ball
      p hM hCQ hbound hnonneg hcont hmeas hQbound ht htT x).congr hcongr.symm
  -- the integral over (0,t] sees q = raw flux
  have hint_eq : (∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s) (q s) x.1)
      = ∫ s in (0:ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1 := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs; rw [Set.uIoc_of_le ht.le] at hs
    simp only [hq, if_pos (And.intro hs.1 (le_trans hs.2 htT))]
  rw [← hint_eq]
  exact ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
    ht htT hq_int hCQ hq_sup x.1 hB_int_q

/-- **Ball-conditional logistic value Duhamel sup bound** (uses the universal
value bound on the `0`-extended cutoff source). -/
theorem valueDuhamel_sup_bound_of_ball
    (p : CM2Params) {T M CL : ℝ} (hM : 0 < M) (hCL : 0 ≤ CL)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M)
    (hLbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y, |logisticLifted p (w τ) y| ≤ CL)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |∫ s in (0 : ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1|
      ≤ T * CL := by
  set r : ℝ → ℝ → ℝ :=
    fun s yy => if 0 < s ∧ s ≤ T then logisticLifted p (w s) yy else 0 with hr
  have hr_sup : ∀ s y, |r s y| ≤ CL := by
    intro s yy; simp only [hr]; split_ifs with h
    · exact hLbound s h.1 h.2 yy
    · simpa using hCL
  have hint_eq : (∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (r s) x.1)
      = ∫ s in (0:ℝ)..t,
        intervalFullSemigroupOperator (t - s) (logisticLifted p (w s)) x.1 := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro s hs; rw [Set.uIoc_of_le ht.le] at hs
    simp only [hr, if_pos (And.intro hs.1 (le_trans hs.2 htT))]
  rw [← hint_eq]
  exact ShenWork.IntervalDuhamelIntegrability.valueDuhamel_sup_bound_universal
    ht htT hCL hr_sup x.1

/-- **Universal (integrability-free) conjugate chemotaxis Duhamel sup bound.**
Uses only continuous-slice + sup data; the time-integral is `0` when the
integrand fails to be interval-integrable. -/
theorem conjugateDuhamel_sup_bound_of_ball_univ
    (p : CM2Params) {T M CQ : ℝ} (hM : 0 ≤ M) (hCQ : 0 ≤ CQ)
    {w : ℝ → intervalDomainPoint → ℝ}
    (hbound : ∀ τ, 0 < τ → τ ≤ T → ∀ x, |w τ x| ≤ M)
    (hnonneg : ∀ τ, 0 < τ → τ ≤ T → ∀ x, 0 ≤ w τ x)
    (hcont : HasContinuousSlices T w)
    (hQbound : ∀ τ, 0 < τ → τ ≤ T → ∀ y, |chemFluxLifted p (w τ) y| ≤ CQ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) :
    |∫ s in (0 : ℝ)..t,
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1|
      ≤ heatGradientLinftyLinftyConstant * (2 * Real.sqrt T) * CQ := by
  by_cases hint : IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1) volume 0 t
  · -- integrable: reuse the proven bound via the cutoff source
    set q : ℝ → ℝ → ℝ :=
      fun s yy => if 0 < s ∧ s ≤ T then chemFluxLifted p (w s) yy else 0 with hq
    have hq_sup : ∀ s y, |q s y| ≤ CQ := by
      intro s yy; simp only [hq]; split_ifs with h
      · exact hQbound s h.1 h.2 yy
      · simpa using hCQ
    have hq_int : ∀ s, Integrable (q s) (intervalMeasure 1) := by
      intro s; simp only [hq]; split_ifs with h
      · exact ShenWork.IntervalDuhamelIntegrability.chemFluxLifted_integrable_of_continuous
          p (hbound s h.1 h.2) hM (hcont s h.1 h.2) (hnonneg s h.1 h.2)
      · simp
    have hcongr : Set.EqOn
        (fun s => intervalConjugateKernelOperator (t - s) (q s) x.1)
        (fun s => intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1)
        (Set.uIoc 0 t) := by
      intro s hs; rw [Set.uIoc_of_le ht.le] at hs
      simp only [hq, if_pos (And.intro hs.1 (le_trans hs.2 htT))]
    have hint_eq : (∫ s in (0:ℝ)..t,
          intervalConjugateKernelOperator (t - s) (q s) x.1)
        = ∫ s in (0:ℝ)..t,
          intervalConjugateKernelOperator (t - s) (chemFluxLifted p (w s)) x.1 := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s hs; rw [Set.uIoc_of_le ht.le] at hs
      simp only [hq, if_pos (And.intro hs.1 (le_trans hs.2 htT))]
    rw [← hint_eq]
    exact ShenWork.IntervalConjugateDuhamelMap.conjugateDuhamel_sup_bound
      ht htT hq_int hCQ hq_sup x.1 (hint.congr hcongr.symm)
  · rw [intervalIntegral.integral_undef hint, abs_zero]
    exact mul_nonneg (mul_nonneg ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg T))) hCQ

end ShenWork.IntervalConjugateBallSupBound
