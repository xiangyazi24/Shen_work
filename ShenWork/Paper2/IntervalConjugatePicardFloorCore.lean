import ShenWork.Paper2.IntervalConjugatePicard

/-!
# Positive-floor conjugate Picard core

The ordinary conjugate Picard record asks the nonlinear map to be Lipschitz on
the whole nonnegative ball, including zero.  That is unnecessarily strong for
paper-positive data and fails for powers in `(0,1)`.  This file records the
faithful closed cone `c ≤ u ≤ M`, proves geometric convergence there, and
packages the limit as the existing `ConjugateMildSolutionData`.
-/

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- Picard data on a closed positive cone. -/
structure ConjugateMildExistenceFloorData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M : ℝ
  c : ℝ
  K : ℝ
  C₀ : ℝ
  hT : 0 < T
  hM : 0 < M
  hc : 0 < c
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x, |conjugatePicardIter p u₀ 0 t x| ≤ M
  hbase_floor : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ conjugatePicardIter p u₀ 0 t x
  hbase_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0)
  hmapsTo : ∀ w,
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x, |intervalConjugateDuhamelMap p u₀ w t x| ≤ M
  hmapsTo_floor : ∀ w,
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ intervalConjugateDuhamelMap p u₀ w t x
  hcont_preserved : ∀ w,
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T w → HasJointMeasurability w →
    HasContinuousSlices T (fun t x ↦ intervalConjugateDuhamelMap p u₀ w t x)
  hcontract : ∀ u w d,
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T u → HasContinuousSlices T w →
    HasJointMeasurability u → HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x,
      |intervalConjugateDuhamelMap p u₀ u t x -
        intervalConjugateDuhamelMap p u₀ w t x| ≤ K * d
  hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x,
    |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x| ≤ C₀
  hbase_meas : HasJointMeasurability (conjugatePicardIter p u₀ 0)
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability (fun t x ↦ intervalConjugateDuhamelMap p u₀ w t x)

theorem conjugatePicardIter_floor_ball
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceFloorData p u₀) :
    ∀ n,
      (∀ t, 0 < t → t ≤ D.T → ∀ x, |conjugatePicardIter p u₀ n t x| ≤ D.M) ∧
      (∀ t, 0 < t → t ≤ D.T → ∀ x, D.c ≤ conjugatePicardIter p u₀ n t x) ∧
      HasContinuousSlices D.T (conjugatePicardIter p u₀ n) := by
  intro n
  induction n with
  | zero => exact ⟨D.hbase_ball, D.hbase_floor, D.hbase_cont⟩
  | succ n ih =>
      have hmeas : ∀ k, HasJointMeasurability (conjugatePicardIter p u₀ k) := by
        intro k
        induction k with
        | zero => exact D.hbase_meas
        | succ j hj => exact D.hmeas_preserved _ hj
      exact ⟨D.hmapsTo _ ih.1 ih.2.1 ih.2.2,
        D.hmapsTo_floor _ ih.1 ih.2.1 ih.2.2,
        D.hcont_preserved _ ih.1 ih.2.1 ih.2.2 (hmeas n)⟩

theorem conjugatePicardIter_geometric_floor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceFloorData p u₀) :
    ∀ n t, 0 < t → t ≤ D.T → ∀ x,
      |conjugatePicardIter p u₀ (n + 1) t x - conjugatePicardIter p u₀ n t x|
        ≤ D.K ^ n * D.C₀ := by
  intro n
  induction n with
  | zero => simpa using D.hbase_diff
  | succ n ih =>
      intro t ht htT x
      have hdata := conjugatePicardIter_floor_ball D
      have hmeas : ∀ k, HasJointMeasurability (conjugatePicardIter p u₀ k) := by
        intro k
        induction k with
        | zero => exact D.hbase_meas
        | succ j hj => exact D.hmeas_preserved _ hj
      calc
        |conjugatePicardIter p u₀ (n + 2) t x - conjugatePicardIter p u₀ (n + 1) t x|
            = |intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ (n + 1)) t x -
                intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x| := rfl
        _ ≤ D.K * (D.K ^ n * D.C₀) :=
          D.hcontract _ _ _ (hdata (n + 1)).1 (hdata (n + 1)).2.1
            (hdata n).1 (hdata n).2.1 (hdata (n + 1)).2.2 (hdata n).2.2
            (hmeas (n + 1)) (hmeas n) ih t ht htT x
        _ = D.K ^ (n + 1) * D.C₀ := by ring

theorem conjugatePicardLimit_floor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceFloorData p u₀) :
    ∀ t, 0 < t → t ≤ D.T → ∀ x, D.c ≤ conjugatePicardLimit p u₀ D.T t x := by
  intro t ht htT x
  unfold conjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  let a := fun n ↦ conjugatePicardIter p u₀ n t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound D.hK D.hK_nn D.hC₀
      (fun n ↦ conjugatePicardIter_geometric_floor D n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact ge_of_tendsto hL (Eventually.of_forall
    (fun n ↦ (conjugatePicardIter_floor_ball D n).2.1 t ht htT x))

private theorem conjugatePicardLimit_floor_measurable
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceFloorData p u₀)
    (hmeas : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n)) :
    HasJointMeasurability (conjugatePicardLimit p u₀ D.T) := by
  let f : ℕ → ℝ × ℝ → ℝ := fun n q ↦
    if 0 < q.1 ∧ q.1 ≤ D.T then intervalDomainLift (conjugatePicardIter p u₀ n q.1) q.2 else 0
  let g : ℝ × ℝ → ℝ := fun q ↦ intervalDomainLift (conjugatePicardLimit p u₀ D.T q.1) q.2
  have hf : ∀ n, Measurable (f n) := fun n ↦
    Measurable.ite (measurableSet_Ioc.preimage measurable_fst) (hmeas n) measurable_const
  have hlim : Tendsto f atTop (nhds g) := by
    rw [tendsto_pi_nhds]
    intro q
    by_cases hq : 0 < q.1 ∧ q.1 ≤ D.T
    · simp only [f, if_pos hq, g]
      unfold conjugatePicardLimit
      simp only [if_pos hq]
      unfold intervalDomainLift
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp only [dif_pos hy]
        exact tendsto_nhds_limUnder
          (conjugatePicardIter_pointwise_convergent p u₀ D.hK D.hK_nn D.hC₀
            (conjugatePicardIter_geometric_floor D) q.1 hq.1 hq.2 ⟨q.2, hy⟩)
      · simp only [dif_neg hy]
        exact tendsto_const_nhds
    · simp only [f, if_neg hq]
      have : g q = 0 := by
        simp only [g, conjugatePicardLimit, if_neg hq, intervalDomainLift]
        split_ifs <;> rfl
      rw [this]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hf hlim

theorem conjugatePicardLimit_is_mildSolution_floor
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceFloorData p u₀) :
    IntervalConjugateMildSolution p D.T u₀ (conjugatePicardLimit p u₀ D.T) := by
  let hdata := conjugatePicardIter_floor_ball D
  let hball := fun n ↦ (hdata n).1
  let hfloor := fun n ↦ (hdata n).2.1
  let hcont := fun n ↦ (hdata n).2.2
  have hmeas : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ j hj => exact D.hmeas_preserved _ hj
  let hgeom := conjugatePicardIter_geometric_floor D
  have hcontlim := conjugatePicardLimit_hasContinuousSlices p u₀ D.hT D.hK D.hK_nn D.hC₀ hgeom hcont
  have hmeaslim := conjugatePicardLimit_floor_measurable D hmeas
  intro t ht htT x
  have h1K : 0 < 1 - D.K := sub_pos.mpr D.hK
  let tail := fun n ↦ D.K ^ n * D.C₀ / (1 - D.K)
  let ulim := conjugatePicardLimit p u₀ D.T
  have hub := conjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀ hgeom hball
  have hufloor := conjugatePicardLimit_floor D
  have htail : ∀ n s, 0 < s → s ≤ D.T → ∀ y,
      |conjugatePicardIter p u₀ n s y - ulim s y| ≤ tail n :=
    fun n s hs hsT y ↦ conjugatePicardIter_pointwise_tail_bound
      p u₀ D.hK D.hK_nn D.hC₀ hgeom s hs hsT y n
  have hconv := conjugatePicardIter_pointwise_convergent
    p u₀ D.hK D.hK_nn D.hC₀ hgeom t ht htT x
  obtain ⟨L, hL⟩ := hconv
  have hkey : ∀ n, |intervalConjugateDuhamelMap p u₀ ulim t x - L| ≤
      D.K * tail n + tail (n + 1) := by
    intro n
    calc
      |intervalConjugateDuhamelMap p u₀ ulim t x - L| ≤
          |intervalConjugateDuhamelMap p u₀ ulim t x -
            intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x| +
          |intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x - L| := abs_sub_le _ _ _
      _ = |intervalConjugateDuhamelMap p u₀ ulim t x -
            intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x| +
          |conjugatePicardIter p u₀ (n + 1) t x - L| := by rfl
      _ ≤ D.K * tail n + tail (n + 1) := by
        gcongr
        · exact D.hcontract ulim (conjugatePicardIter p u₀ n) (tail n)
            hub hufloor (hball n) (hfloor n) hcontlim (hcont n)
            hmeaslim (hmeas n) (fun s hs hsT y ↦ by
              rw [abs_sub_comm]
              exact htail n s hs hsT y) t ht htT x
        · have heq : L = ulim t x := by
            unfold ulim conjugatePicardLimit
            simp only [ht, htT, and_self, ite_true]
            exact hL.limUnder_eq.symm
          rw [heq]
          exact conjugatePicardIter_pointwise_tail_bound
            p u₀ D.hK D.hK_nn D.hC₀ hgeom t ht htT x (n + 1)
  have htail0 : Tendsto tail atTop (nhds 0) := by
    dsimp [tail]
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one D.hK_nn D.hK
    simpa using (hp.mul_const D.C₀).div_const (1 - D.K)
  have hvanish : Tendsto (fun n ↦ D.K * tail n + tail (n + 1)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (htail0.const_mul D.K).add (htail0.comp (tendsto_add_atTop_nat 1))
  have hz : |intervalConjugateDuhamelMap p u₀ ulim t x - L| ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε ↦ by
      rw [zero_add]
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hvanish) ε hε
      have hNN := hN N le_rfl
      have hnonneg : 0 ≤ D.K * tail N + tail (N + 1) := by
        have ht_nonneg : ∀ n, 0 ≤ tail n := fun n ↦
          div_nonneg (mul_nonneg (pow_nonneg D.hK_nn n) D.hC₀) h1K.le
        exact add_nonneg (mul_nonneg D.hK_nn (ht_nonneg N)) (ht_nonneg (N + 1))
      simp only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at hNN
      exact (hkey N).trans hNN.le)
  unfold conjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  rw [hL.limUnder_eq]
  exact (eq_of_abs_sub_nonpos hz).symm

/-- Package the positive-floor fixed point in the repository's standard mild
solution record. -/
def conjugateMildSolutionData_of_floorData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceFloorData p u₀) : ConjugateMildSolutionData p u₀ := by
  let hdata := conjugatePicardIter_floor_ball D
  let hball := fun n ↦ (hdata n).1
  let hcont := fun n ↦ (hdata n).2.2
  let hgeom := conjugatePicardIter_geometric_floor D
  have hmeas : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ j hj => exact D.hmeas_preserved _ hj
  have hcontlim := conjugatePicardLimit_hasContinuousSlices p u₀ D.hT D.hK D.hK_nn D.hC₀ hgeom hcont
  have hmeaslim := conjugatePicardLimit_floor_measurable D hmeas
  exact {
    T := D.T, hT := D.hT, M := D.M, hM := D.hM
    u := conjugatePicardLimit p u₀ D.T
    hmild := conjugatePicardLimit_is_mildSolution_floor D
    hbound := conjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀ hgeom hball
    hnonneg := fun t ht htT x ↦ le_trans D.hc.le (conjugatePicardLimit_floor D t ht htT x)
    hpos := fun t ht htT x ↦ lt_of_lt_of_le D.hc (conjugatePicardLimit_floor D t ht htT x)
    hcont := hcontlim
    hmeas := hmeaslim }

#print axioms conjugatePicardIter_geometric_floor
#print axioms conjugatePicardLimit_is_mildSolution_floor
#print axioms conjugateMildSolutionData_of_floorData

end ShenWork.IntervalConjugatePicard

end
