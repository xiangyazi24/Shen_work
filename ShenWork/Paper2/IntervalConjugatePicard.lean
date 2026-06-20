/-
  B-form Picard fixed point.

  This file is the B-form analogue of the pointwise Picard core in
  `IntervalMildPicard`: the iterates are built from
  `intervalConjugateDuhamelMap`, and the limit is proved to satisfy
  `IntervalConjugateMildSolution` from the usual ball/contraction/regularity
  data.  The analytic estimates that supply those fields are deliberately kept
  as named hypotheses; no fixed-point equation or spectral agreement is assumed.
-/
import ShenWork.Paper2.IntervalBFormPdeUProducer
import ShenWork.Paper2.IntervalMildPicard

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalConjugateDuhamelMap
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.IntervalConjugatePicard

/-- B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᴮ(u_n)`. -/
def conjugatePicardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x

/-- Pointwise limit of the B-form Picard iterates on `(0,T]`; zero outside. -/
def conjugatePicardLimit (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  if 0 < t ∧ t ≤ T then
    atTop.limUnder (fun n => conjugatePicardIter p u₀ n t x)
  else 0

theorem conjugatePicardIter_pointwise_convergent (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      ∃ L : ℝ, Tendsto (fun n => conjugatePicardIter p u₀ n t x)
        atTop (nhds L) := by
  intro t ht htT x
  exact real_cauchySeq_convergent
    (real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x))

private theorem conjugate_geometric_tail_tendsto_zero {K C₀ : ℝ}
    (hK : K < 1) (hK_nn : 0 ≤ K) :
    Tendsto (fun n => K ^ n * C₀ / (1 - K)) atTop (nhds 0) := by
  have h1K : (0 : ℝ) < 1 - K := by linarith
  rw [show (0 : ℝ) = 0 / (1 - K) from by simp]
  apply Tendsto.div_const
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hK_nn hK
  simpa [zero_mul] using hpow.mul_const C₀

theorem conjugatePicardIter_pointwise_tail_bound (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (_hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) (n : ℕ) :
    |conjugatePicardIter p u₀ n t x - conjugatePicardLimit p u₀ T t x|
      ≤ K ^ n * C₀ / (1 - K) := by
  set a := fun m => conjugatePicardIter p u₀ m t x
  set d := fun m => K ^ m * C₀
  have hdist : ∀ m, dist (a m) (a m.succ) ≤ d m := by
    intro m
    rw [Real.dist_eq, abs_sub_comm]
    exact hbound m t ht htT x
  have hd_sum : Summable d :=
    Summable.mul_right C₀ (summable_geometric_of_lt_one hK_nn hK)
  have hcauchy : CauchySeq a := cauchySeq_of_dist_le_of_summable d hdist hd_sum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim_eq : conjugatePicardLimit p u₀ T t x = L := by
    unfold conjugatePicardLimit
    simp only [ht, htT, and_self, ite_true]
    exact hL.limUnder_eq
  rw [hlim_eq, ← Real.dist_eq]
  calc dist (a n) L ≤ ∑' m, d (n + m) :=
        dist_le_tsum_of_dist_le_of_tendsto d hdist hd_sum hL n
    _ = K ^ n * C₀ / (1 - K) := by
        simp_rw [d, pow_add, mul_assoc]
        rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hK_nn hK]
        ring

theorem conjugatePicardIter_uniform_convergence (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (_hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ t, 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |conjugatePicardIter p u₀ n t x
          - conjugatePicardLimit p u₀ T t x| < ε := by
  intro ε hε
  have htend := conjugate_geometric_tail_tendsto_zero hK hK_nn (C₀ := C₀)
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  exact ⟨N, fun n hn t ht htT x => by
    calc |conjugatePicardIter p u₀ n t x - conjugatePicardLimit p u₀ T t x|
        ≤ K ^ n * C₀ / (1 - K) :=
          conjugatePicardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀
            hbound t ht htT x n
      _ < ε := by
          have h1K : (0 : ℝ) < 1 - K := by linarith
          have hnn : 0 ≤ K ^ n * C₀ / (1 - K) :=
            div_nonneg (mul_nonneg (pow_nonneg hK_nn n) hC₀) h1K.le
          have := hN n hn
          rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn] at this⟩

theorem conjugatePicardLimit_bounded (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ n t x| ≤ M) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardLimit p u₀ T t x| ≤ M := by
  intro t ht htT x
  unfold conjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => conjugatePicardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact le_of_tendsto (hL.abs) (Eventually.of_forall (fun n => hball n t ht htT x))

theorem conjugatePicardLimit_nonneg (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hnn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardIter p u₀ n t x) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardLimit p u₀ T t x := by
  intro t ht htT x
  unfold conjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => conjugatePicardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact ge_of_tendsto hL (Eventually.of_forall (fun n => hnn n t ht htT x))

theorem conjugatePicardLimit_hasContinuousSlices (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hcont_iterates : ∀ n, HasContinuousSlices T (conjugatePicardIter p u₀ n)) :
    HasContinuousSlices T (conjugatePicardLimit p u₀ T) := by
  intro t ht htT
  have hunif :
      TendstoUniformly (fun n => conjugatePicardIter p u₀ n t)
        (conjugatePicardLimit p u₀ T t) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      conjugatePicardIter_uniform_convergence p u₀ hT hK hK_nn hC₀ hbound ε hε
    apply Filter.eventually_atTop.mpr
    exact ⟨N, fun n hn x => by
      rw [Real.dist_eq, abs_sub_comm]
      exact hN n hn t ht htT x⟩
  exact hunif.continuous
    (Eventually.of_forall (fun n => hcont_iterates n t ht htT) |>.frequently)

theorem conjugatePicardLimit_is_mildSolution (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (_hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀) (_hM : 0 < M)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ n t x| ≤ M)
    (hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardIter p u₀ n t x)
    (hcont_iterates : ∀ n, HasContinuousSlices T (conjugatePicardIter p u₀ n))
    (hcont_limit : HasContinuousSlices T (conjugatePicardLimit p u₀ T))
    (hmeas_iterates : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n))
    (hmeas_limit : HasJointMeasurability (conjugatePicardLimit p u₀ T))
    (hcontract : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀ u t x
          - intervalConjugateDuhamelMap p u₀ w t x| ≤ K * d) :
    IntervalConjugateMildSolution p T u₀ (conjugatePicardLimit p u₀ T) := by
  intro t ht htT x
  unfold conjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => conjugatePicardIter p u₀ m t x
  set u := conjugatePicardLimit p u₀ T
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  change atTop.limUnder a = _
  rw [hL.limUnder_eq]
  have h1K : (0 : ℝ) < 1 - K := by linarith
  set tail := fun n => K ^ n * C₀ / (1 - K)
  have hu_ball : ∀ s, 0 < s → s ≤ T → ∀ y, |u s y| ≤ M :=
    conjugatePicardLimit_bounded p u₀ hK hK_nn hC₀ hbound hball
  have hu_nn : ∀ s, 0 < s → s ≤ T → ∀ y, 0 ≤ u s y :=
    conjugatePicardLimit_nonneg p u₀ hK hK_nn hC₀ hbound hball_nn
  have htail : ∀ n s, 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |conjugatePicardIter p u₀ n s y - u s y| ≤ tail n :=
    fun n s hs hsT y =>
      conjugatePicardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀
        hbound s hs hsT y n
  have hkey : ∀ n,
      |intervalConjugateDuhamelMap p u₀ u t x - L|
        ≤ K * tail n + tail (n + 1) := by
    intro n
    calc |intervalConjugateDuhamelMap p u₀ u t x - L|
        ≤ |intervalConjugateDuhamelMap p u₀ u t x
            - intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x|
          + |intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x - L| :=
        abs_sub_le _ _ _
      _ = |intervalConjugateDuhamelMap p u₀ u t x
            - intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x|
          + |conjugatePicardIter p u₀ (n + 1) t x - L| := by rfl
      _ ≤ K * tail n + tail (n + 1) := by
          gcongr
          · exact hcontract u (conjugatePicardIter p u₀ n) (tail n)
              hu_ball hu_nn (fun s hs hsT y => hball n s hs hsT y)
              (fun s hs hsT y => hball_nn n s hs hsT y)
              hcont_limit (hcont_iterates n) hmeas_limit (hmeas_iterates n)
              (fun s hs hsT y => by
                rw [abs_sub_comm]
                exact htail n s hs hsT y)
              t ht htT x
          · have hconv : L = conjugatePicardLimit p u₀ T t x := by
              unfold conjugatePicardLimit
              simp only [ht, htT, and_self, ite_true]
              exact hL.limUnder_eq.symm
            rw [hconv]
            exact conjugatePicardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀
              hbound t ht htT x (n + 1)
  have hvanish : Tendsto (fun n => K * tail n + tail (n + 1)) atTop (nhds 0) := by
    have htail0 := conjugate_geometric_tail_tendsto_zero hK hK_nn (C₀ := C₀)
    have htail1 := htail0.comp (tendsto_add_atTop_nat 1)
    simpa [add_comm] using (htail0.const_mul K).add htail1
  have habs_le_zero : |intervalConjugateDuhamelMap p u₀ u t x - L| ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε => by
      rw [zero_add]
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hvanish) ε hε
      have hN' := hN N le_rfl
      have hnn : 0 ≤ K * tail N + tail (N + 1) := by
        apply add_nonneg
        · exact mul_nonneg hK_nn
            (div_nonneg (mul_nonneg (pow_nonneg hK_nn N) hC₀) h1K.le)
        · exact div_nonneg (mul_nonneg (pow_nonneg hK_nn (N + 1)) hC₀) h1K.le
      simp only [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hN'
      exact (hkey N).trans hN'.le)
  exact (eq_of_abs_sub_nonpos habs_le_zero).symm

/-- Ball membership, nonnegativity, and continuity of B-form Picard iterates. -/
theorem conjugatePicardIter_ball (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T M : ℝ}
    (hbase : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ 0 t x| ≤ M)
    (hbase_nn : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardIter p u₀ 0 t x)
    (hbase_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0))
    (hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀ w t x| ≤ M)
    (hmapsTo_nn : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        0 ≤ intervalConjugateDuhamelMap p u₀ w t x)
    (hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      HasJointMeasurability w →
      HasContinuousSlices T (fun t x => intervalConjugateDuhamelMap p u₀ w t x))
    (hbase_meas : HasJointMeasurability (conjugatePicardIter p u₀ 0))
    (hmeas_preserved : ∀ w, HasJointMeasurability w →
      HasJointMeasurability (fun t x => intervalConjugateDuhamelMap p u₀ w t x))
    (n : ℕ) :
    (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ n t x| ≤ M) ∧
    (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ conjugatePicardIter p u₀ n t x) ∧
    HasContinuousSlices T (conjugatePicardIter p u₀ n) := by
  induction n with
  | zero => exact ⟨hbase, hbase_nn, hbase_cont⟩
  | succ n ih =>
    have hmeas_iterates : ∀ k, HasJointMeasurability (conjugatePicardIter p u₀ k) := by
      intro k
      induction k with
      | zero => exact hbase_meas
      | succ j ihj => exact hmeas_preserved _ ihj
    exact ⟨fun t ht htT x => hmapsTo _ ih.1 ih.2.1 ih.2.2 t ht htT x,
      fun t ht htT x => hmapsTo_nn _ ih.1 ih.2.1 ih.2.2 t ht htT x,
      hcont_preserved _ ih.1 ih.2.1 ih.2.2 (hmeas_iterates n)⟩

theorem conjugatePicardIter_geometric (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K M : ℝ} (_hK_nn : 0 ≤ K)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ n t x| ≤ M)
    (hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint, 0 ≤ conjugatePicardIter p u₀ n t x)
    (hcont_iterates : ∀ n, HasContinuousSlices T (conjugatePicardIter p u₀ n))
    (hmeas_iterates : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n))
    (hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalConjugateDuhamelMap p u₀ u t x
          - intervalConjugateDuhamelMap p u₀ w t x| ≤ K * d)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x| ≤ C₀)
    (n : ℕ) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀ := by
  induction n with
  | zero => simpa using hbase_diff
  | succ n ih =>
    intro t ht htT x
    calc |conjugatePicardIter p u₀ (n + 2) t x
          - conjugatePicardIter p u₀ (n + 1) t x|
        = |intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ (n + 1)) t x
            - intervalConjugateDuhamelMap p u₀ (conjugatePicardIter p u₀ n) t x| := rfl
      _ ≤ K * (K ^ n * C₀) :=
          hcontr _ _ _ (hball (n + 1)) (hball_nn (n + 1))
            (hball n) (hball_nn n)
            (hcont_iterates (n + 1)) (hcont_iterates n)
            (hmeas_iterates (n + 1)) (hmeas_iterates n) ih t ht htT x
      _ = K ^ (n + 1) * C₀ := by ring

/-- Data sufficient for the B-form Picard construction. -/
structure ConjugateMildExistenceData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M : ℝ
  K : ℝ
  C₀ : ℝ
  hT : 0 < T
  hM : 0 < M
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ 0 t x| ≤ M
  hbase_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ conjugatePicardIter p u₀ 0 t x
  hbase_cont : HasContinuousSlices T (conjugatePicardIter p u₀ 0)
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalConjugateDuhamelMap p u₀ w t x| ≤ M
  hmapsTo_nn : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ intervalConjugateDuhamelMap p u₀ w t x
  hmapsTo_pos : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 < intervalConjugateDuhamelMap p u₀ w t x
  hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    HasJointMeasurability w →
    HasContinuousSlices T (fun t x => intervalConjugateDuhamelMap p u₀ w t x)
  hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalConjugateDuhamelMap p u₀ u t x
        - intervalConjugateDuhamelMap p u₀ w t x| ≤ K * d
  hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |conjugatePicardIter p u₀ 1 t x - conjugatePicardIter p u₀ 0 t x| ≤ C₀
  hbase_meas : HasJointMeasurability (conjugatePicardIter p u₀ 0)
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability (fun t x => intervalConjugateDuhamelMap p u₀ w t x)

private theorem conjugatePicardLimit_measurable_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (hgeom : ∀ n t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      |conjugatePicardIter p u₀ (n + 1) t x
        - conjugatePicardIter p u₀ n t x| ≤ D.K ^ n * D.C₀)
    (hmeas_iterates : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n)) :
    HasJointMeasurability (conjugatePicardLimit p u₀ D.T) := by
  set f_n : ℕ → ℝ × ℝ → ℝ := fun n q =>
    if 0 < q.1 ∧ q.1 ≤ D.T then
      intervalDomainLift (conjugatePicardIter p u₀ n q.1) q.2
    else 0
  set g : ℝ × ℝ → ℝ := fun q =>
    intervalDomainLift (conjugatePicardLimit p u₀ D.T q.1) q.2
  have hf_meas : ∀ n, Measurable (f_n n) := fun n => by
    apply Measurable.ite
    · exact measurableSet_Ioc.preimage measurable_fst
    · exact hmeas_iterates n
    · exact measurable_const
  have hlim : Filter.Tendsto f_n Filter.atTop (nhds g) := by
    rw [tendsto_pi_nhds]
    intro q
    by_cases hq : 0 < q.1 ∧ q.1 ≤ D.T
    · simp only [f_n, if_pos hq, g]
      unfold conjugatePicardLimit
      simp only [if_pos hq]
      unfold intervalDomainLift
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp only [dif_pos hy]
        exact tendsto_nhds_limUnder
          (conjugatePicardIter_pointwise_convergent p u₀ D.hK D.hK_nn D.hC₀
            hgeom q.1 hq.1 hq.2 ⟨q.2, hy⟩)
      · simp only [dif_neg hy]
        exact tendsto_const_nhds
    · simp only [f_n, if_neg hq]
      have hg0 : g q = 0 := by
        simp only [g, conjugatePicardLimit, if_neg hq, intervalDomainLift]
        split_ifs <;> rfl
      rw [hg0]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hf_meas hlim

/-- The B-form Picard construction produces a fixed point from honest
mapsTo/contraction data. -/
theorem intervalConjugateMildSolution_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalConjugateMildSolution p T u₀ u := by
  have hball_cont := fun n =>
    conjugatePicardIter_ball p u₀ D.hbase_ball D.hbase_nonneg D.hbase_cont
      D.hmapsTo D.hmapsTo_nn D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hball_nn := fun n => (hball_cont n).2.1
  have hcont_iterates := fun n => (hball_cont n).2.2
  have hmeas_iterates : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom := conjugatePicardIter_geometric p u₀ D.hK_nn hball hball_nn
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
  have hcont_limit := conjugatePicardLimit_hasContinuousSlices p u₀ D.hT D.hK
    D.hK_nn D.hC₀ (fun n => hgeom n) hcont_iterates
  have hmeas_limit :=
    conjugatePicardLimit_measurable_of_data D (fun n => hgeom n) hmeas_iterates
  exact ⟨D.T, D.hT, conjugatePicardLimit p u₀ D.T,
    conjugatePicardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn D.hC₀ D.hM
      (fun n => hgeom n) hball hball_nn hcont_iterates hcont_limit
      hmeas_iterates hmeas_limit D.hcontr⟩

/-- Packaged B-form fixed point and cone bounds. -/
structure ConjugateMildSolutionData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  hT : 0 < T
  M : ℝ
  hM : 0 < M
  u : ℝ → intervalDomainPoint → ℝ
  hmild : IntervalConjugateMildSolution p T u₀ u
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hnonneg : ∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x
  hpos : ∀ t, 0 < t → t ≤ T → ∀ x, 0 < u t x
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u

/-- Build the packaged B-form fixed point from Picard data. -/
def conjugateMildSolutionData_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) : ConjugateMildSolutionData p u₀ := by
  have hball_cont := fun n =>
    conjugatePicardIter_ball p u₀ D.hbase_ball D.hbase_nonneg D.hbase_cont
      D.hmapsTo D.hmapsTo_nn D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hball_nn := fun n => (hball_cont n).2.1
  have hcont_iterates := fun n => (hball_cont n).2.2
  have hmeas_iterates : ∀ n, HasJointMeasurability (conjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom := conjugatePicardIter_geometric p u₀ D.hK_nn hball hball_nn
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
  have hcont_limit := conjugatePicardLimit_hasContinuousSlices p u₀ D.hT D.hK
    D.hK_nn D.hC₀ (fun n => hgeom n) hcont_iterates
  have hmeas_limit :=
    conjugatePicardLimit_measurable_of_data D (fun n => hgeom n) hmeas_iterates
  exact {
    T := D.T
    hT := D.hT
    M := D.M
    hM := D.hM
    u := conjugatePicardLimit p u₀ D.T
    hmild := conjugatePicardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn D.hC₀ D.hM
      (fun n => hgeom n) hball hball_nn hcont_iterates hcont_limit
      hmeas_iterates hmeas_limit D.hcontr
    hbound := conjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀
      (fun n => hgeom n) hball
    hnonneg := conjugatePicardLimit_nonneg p u₀ D.hK D.hK_nn D.hC₀
      (fun n => hgeom n) hball_nn
    hpos := by
      intro t ht htT x
      have hmild_eq := conjugatePicardLimit_is_mildSolution p u₀ D.hT D.hK
        D.hK_nn D.hC₀ D.hM (fun n => hgeom n) hball hball_nn
        hcont_iterates hcont_limit hmeas_iterates hmeas_limit D.hcontr
        t ht htT x
      rw [hmild_eq]
      exact D.hmapsTo_pos _ (conjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀
        (fun n => hgeom n) hball)
        (conjugatePicardLimit_nonneg p u₀ D.hK D.hK_nn D.hC₀
          (fun n => hgeom n) hball_nn) hcont_limit t ht htT x
    hcont := hcont_limit
    hmeas := hmeas_limit
  }

/-- Existence projection with cone bounds exposed. -/
theorem intervalConjugateMildSolution_exists_from_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalConjugateMildSolution p T u₀ u ∧
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ (conjugateMildSolutionData_of_data D).M) ∧
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) := by
  let C := conjugateMildSolutionData_of_data D
  exact ⟨C.T, C.hT, C.u, C.hmild, C.hbound, C.hnonneg⟩

/-- B-form interior PDE for the B-form Picard fixed point, once the independent
spectral-agreement data have been supplied.  The spectral hypothesis is not
hidden inside the Picard data. -/
theorem intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : ConjugateMildExistenceData p u₀)
    (Hpde : ShenWork.IntervalBFormSpectral.HasBFormSpectralPdeAgreement
      p D.T (conjugatePicardLimit p u₀ D.T)) :
    ∀ t x, 0 < t → t < D.T → x ∈ ShenWork.IntervalDomain.intervalDomain.inside →
      ShenWork.IntervalDomain.intervalDomain.timeDeriv
          (conjugatePicardLimit p u₀ D.T) t x =
        ShenWork.IntervalDomain.intervalDomain.laplacian
            ((conjugatePicardLimit p u₀ D.T) t) x
          - p.χ₀ * ShenWork.IntervalDomain.intervalDomain.chemotaxisDiv p
              ((conjugatePicardLimit p u₀ D.T) t)
              (ShenWork.IntervalMildToClassical.mildChemicalConcentration p
                (conjugatePicardLimit p u₀ D.T) t) x
          + (conjugatePicardLimit p u₀ D.T) t x
            * (p.a - p.b * ((conjugatePicardLimit p u₀ D.T) t x) ^ p.α) := by
  have hB : IntervalConjugateMildSolution p D.T u₀
      (conjugatePicardLimit p u₀ D.T) :=
    (conjugateMildSolutionData_of_data D).hmild
  exact ShenWork.IntervalBFormSpectral.intervalConjugateMildSolution_pde_u_of_spectral
    p hB Hpde

#print axioms intervalConjugateMildSolution_of_data
#print axioms intervalConjugateMildSolution_exists_from_data
#print axioms intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral

end ShenWork.IntervalConjugatePicard
