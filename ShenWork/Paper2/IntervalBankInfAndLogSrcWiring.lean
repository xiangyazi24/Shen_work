/-
  ShenWork/Paper2/IntervalBankInfAndLogSrcWiring.lean

  Wiring bricks for two `BFormBankedInputs` fields
  (`ShenWork/Paper2/IntervalBFormDirectClassical.lean:62`):

    * field 2  `Hinf   : ConjugatePicardInfThresholdData p u₀ DB.T`
    * field 6  `hlogSrc : DuhamelSourceTimeC1
                  (coupledLogisticSourceCoeffs p (conjugatePicardLimit p u₀ DB.T))`

  This file lands the genuinely-dischargeable, axiom-clean *windowed* source
  control over the conjugate Picard iterates that field 2's producer
  `conjugatePicardInfThresholdData_of_picard_bounds`
  (`ShenWork/Paper2/IntervalConjugatePicardInfThresholdDischarge.lean:21`) needs:

    - `iterChemFlux_windowBound`  : windowed uniform chemotaxis-flux sup bound
    - `iterLogistic_windowBound`  : windowed uniform logistic sup bound
    - `iterChemFlux_integrable`   : per-slice spatial integrability of the flux
    - `iterLogistic_duhamel_intervalIntegrable` : `hL_int` over the iterates
    - `iterChemFlux_duhamel_intervalIntegrable` : `hB_int` over the iterates

  All inputs are extracted from the keystone `ConjugateMildExistenceData` via the
  landed `conjugatePicardIter_ball` ball/continuity/measurability replay and the
  landed `*_of_ball` integrability atoms.

  IMPORTANT — field 2's producer
  `conjugatePicardInfThresholdData_of_picard_bounds` now accepts WINDOWED bounds
  (`hQ_bound/hL_bound : ∀ n, ∀ s, 0 < s → s ≤ T → …`), so the bricks below
  are a COMPLETE match for field 2.  Field 6 still needs a restart-cosine
  representation + time-`C¹` coefficient data for `conjugatePicardLimit` that is
  not landed anywhere in the tree.

  No `sorry`/`admit`/`native_decide`/custom `axiom`.  New names only.
-/
import ShenWork.Paper2.IntervalConjugatePicardInfThresholdDischarge
import ShenWork.Paper2.IntervalConjugateChemFluxIntegrable
import ShenWork.Paper2.IntervalDuhamelIntegrability

open MeasureTheory Set
open scoped Topology

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)
open ShenWork.IntervalConjugateDuhamelMap (intervalConjugateKernelOperator)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard (HasContinuousSlices HasJointMeasurability)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter ConjugateMildExistenceData)
open ShenWork.IntervalConjugateChemFluxIntegrable
  (chemFluxLifted_sup_bound_of_ball
   conjugateChemFlux_duhamel_intervalIntegrable_of_ball)
open ShenWork.IntervalDuhamelIntegrability
  (chemFluxLifted_integrable_of_continuous
   valueDuhamel_intervalIntegrable_of_joint_measurable)
open ShenWork.IntervalMildPicardThreshold (logisticLifted_joint_measurable')

noncomputable section

namespace ShenWork.IntervalBankInfAndLogSrcWiring

/-- The conjugate Picard iterates satisfy the ball / nonneg / continuous-slice /
joint-measurability package on the window `(0, D.T]`, replayed from the keystone
`ConjugateMildExistenceData`. -/
theorem iter_ball_package
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        |conjugatePicardIter p u₀ n t x| ≤ D.M) ∧
    (∀ t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
        0 ≤ conjugatePicardIter p u₀ n t x) ∧
    HasContinuousSlices D.T (conjugatePicardIter p u₀ n) ∧
    HasJointMeasurability (conjugatePicardIter p u₀ n) := by
  have hball :=
    ShenWork.IntervalConjugatePicard.conjugatePicardIter_ball p u₀
      D.hbase_ball D.hbase_nonneg D.hbase_cont D.hmapsTo D.hmapsTo_nn
      D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hmeas : ∀ m, HasJointMeasurability (conjugatePicardIter p u₀ m) := by
    intro m
    induction m with
    | zero => exact D.hbase_meas
    | succ m ih => exact D.hmeas_preserved _ ih
  exact ⟨hball.1, hball.2.1, hball.2.2, hmeas n⟩

/-- The uniform chemotaxis-flux sup constant supplied by the ball radius `D.M`. -/
def iterCQ {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : ℝ :=
  D.M * (Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * (p.ν * D.M ^ p.γ)))

theorem iterCQ_nonneg {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : 0 ≤ iterCQ D := by
  unfold iterCQ
  exact mul_nonneg D.hM.le
    (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (mul_nonneg p.hν.le (Real.rpow_nonneg D.hM.le _))))

/-- The uniform logistic sup constant supplied by the ball radius `D.M`. -/
def iterCL {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : ℝ :=
  D.M * (p.a + p.b * D.M ^ p.α)

theorem iterCL_nonneg {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : 0 ≤ iterCL D :=
  mul_nonneg D.hM.le (add_nonneg p.ha (mul_nonneg p.hb (Real.rpow_nonneg D.hM.le _)))

/-- **Windowed chemotaxis-flux sup bound over the iterates** (`hQ_bound` on the
window `(0, D.T]`). -/
theorem iterChemFlux_windowBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |chemFluxLifted p (conjugatePicardIter p u₀ n s) y| ≤ iterCQ D := by
  intro s hs hsT y
  obtain ⟨hball, hnn, hcont, _⟩ := iter_ball_package D n
  have := chemFluxLifted_sup_bound_of_ball p D.hM.le (hball s hs hsT) (hnn s hs hsT)
    (hcont s hs hsT) y
  simpa [iterCQ] using this

/-- **Windowed logistic sup bound over the iterates** (`hL_bound` on the
window `(0, D.T]`). -/
theorem iterLogistic_windowBound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T → ∀ y,
      |logisticLifted p (conjugatePicardIter p u₀ n s) y| ≤ iterCL D := by
  intro s hs hsT y
  obtain ⟨hball, _, _, _⟩ := iter_ball_package D n
  exact ShenWork.IntervalDomainExistence.intervalLogisticSource_lift_abs_bound
    p D.hM (hball s hs hsT) y

/-- **`hQ_int`: per-slice spatial integrability of the chemotaxis flux over the
iterates** (windowed). -/
theorem iterChemFlux_integrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ) :
    ∀ s, 0 < s → s ≤ D.T →
      Integrable (chemFluxLifted p (conjugatePicardIter p u₀ n s)) (intervalMeasure 1) := by
  intro s hs hsT
  obtain ⟨hball, hnn, hcont, _⟩ := iter_ball_package D n
  exact chemFluxLifted_integrable_of_continuous p (hball s hs hsT) D.hM.le
    (hcont s hs hsT) (hnn s hs hsT)

/-- **`hB_int`: time-interval-integrability of the conjugate B-form chemotaxis
Duhamel leg over the iterates.** -/
theorem iterChemFlux_duhamel_intervalIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s : ℝ =>
        intervalConjugateKernelOperator (t - s)
          (chemFluxLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t := by
  obtain ⟨hball, hnn, hcont, hmeas⟩ := iter_ball_package D n
  exact conjugateChemFlux_duhamel_intervalIntegrable_of_ball
    p D.hM.le (iterCQ_nonneg D) hball hnn hcont hmeas
    (iterChemFlux_windowBound D n) ht htT x

/-- **`hL_int`: time-interval-integrability of the logistic Duhamel leg over the
iterates.**  The full-semigroup integrand of the cutoff logistic source is
`IntervalIntegrable` via the landed `valueDuhamel` atom; the cutoff agrees with
the raw integrand on `(0,t]`. -/
theorem iterLogistic_duhamel_intervalIntegrable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) (n : ℕ)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    IntervalIntegrable
      (fun s : ℝ =>
        intervalFullSemigroupOperator (t - s)
          (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
      volume 0 t := by
  obtain ⟨_, _, _, hmeas⟩ := iter_ball_package D n
  -- cutoff source: logistic on-window, 0 off-window; bounded everywhere by iterCL.
  set q : ℝ → ℝ → ℝ :=
    fun s yy => if 0 < s ∧ s ≤ D.T then logisticLifted p (conjugatePicardIter p u₀ n s) yy
      else 0 with hq
  have hq_meas : Measurable (Function.uncurry q) := by
    have hbase : Measurable
        (fun z : ℝ × ℝ => logisticLifted p (conjugatePicardIter p u₀ n z.1) z.2) :=
      logisticLifted_joint_measurable' hmeas
    simp only [hq]
    refine Measurable.ite ?_ hbase measurable_const
    exact ((isOpen_Ioi.preimage continuous_fst).measurableSet).inter
      ((isClosed_Iic.preimage continuous_fst).measurableSet)
  have hq_sup : ∀ s yy, |q s yy| ≤ iterCL D := by
    intro s yy; simp only [hq]; split_ifs with h
    · exact iterLogistic_windowBound D n s h.1 h.2 yy
    · simpa using iterCL_nonneg D
  have hbase_int :=
    valueDuhamel_intervalIntegrable_of_joint_measurable ht hq_meas (iterCL_nonneg D)
      hq_sup x.1
  have hcongr : Set.EqOn
      (fun s : ℝ => intervalFullSemigroupOperator (t - s) (q s) x.1)
      (fun s : ℝ => intervalFullSemigroupOperator (t - s)
        (logisticLifted p (conjugatePicardIter p u₀ n s)) x.1)
      (Set.uIoc 0 t) := by
    intro s hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hmem : 0 < s ∧ s ≤ D.T := ⟨hs.1, le_trans hs.2 htT⟩
    simp only [hq, if_pos hmem]
  exact hbase_int.congr hcongr

#print axioms iter_ball_package
#print axioms iterChemFlux_windowBound
#print axioms iterLogistic_windowBound
#print axioms iterChemFlux_integrable
#print axioms iterChemFlux_duhamel_intervalIntegrable
#print axioms iterLogistic_duhamel_intervalIntegrable

end ShenWork.IntervalBankInfAndLogSrcWiring
