/-
  Truncated B-form Picard fixed point for the cron2 negative-part route.

  This file is additive.  It builds the Picard iteration for
  `truncatedConjugateDuhamelMap` and proves the standard fixed-point theorem
  from explicit maps-to/contraction data, mirroring
  `IntervalConjugatePicard.conjugatePicardLimit_is_mildSolution`.
-/
import ShenWork.Paper2.IntervalBFormNegativePartCron2

open Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

/-- Truncated B-form Picard iteration:
`u₀(t,x) = S(t)u₀(x)`, `u_{n+1} = Φᵀ(u_n)`. -/
def truncatedConjugatePicardIter (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) :
    ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x =>
      truncatedConjugateDuhamelMap p u₀ (truncatedConjugatePicardIter p u₀ n) t x

/-- Pointwise limit of the truncated B-form Picard iterates on `(0,T]`; zero
outside. -/
def truncatedConjugatePicardLimit (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) (T : ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  if 0 < t ∧ t ≤ T then
    atTop.limUnder (fun n => truncatedConjugatePicardIter p u₀ n t x)
  else 0

theorem truncatedConjugatePicardIter_pointwise_convergent
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      ∃ L : ℝ, Tendsto (fun n => truncatedConjugatePicardIter p u₀ n t x)
        atTop (nhds L) := by
  intro t ht htT x
  exact real_cauchySeq_convergent
    (real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x))

private theorem truncated_geometric_tail_tendsto_zero {K C₀ : ℝ}
    (hK : K < 1) (hK_nn : 0 ≤ K) :
    Tendsto (fun n => K ^ n * C₀ / (1 - K)) atTop (nhds 0) := by
  have h1K : (0 : ℝ) < 1 - K := by linarith
  rw [show (0 : ℝ) = 0 / (1 - K) from by simp]
  apply Tendsto.div_const
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hK_nn hK
  simpa [zero_mul] using hpow.mul_const C₀

theorem truncatedConjugatePicardIter_pointwise_tail_bound
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (_hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T)
    (x : intervalDomainPoint) (n : ℕ) :
    |truncatedConjugatePicardIter p u₀ n t x
        - truncatedConjugatePicardLimit p u₀ T t x|
      ≤ K ^ n * C₀ / (1 - K) := by
  set a := fun m => truncatedConjugatePicardIter p u₀ m t x
  set d := fun m => K ^ m * C₀
  have hdist : ∀ m, dist (a m) (a m.succ) ≤ d m := by
    intro m
    rw [Real.dist_eq, abs_sub_comm]
    exact hbound m t ht htT x
  have hd_sum : Summable d :=
    Summable.mul_right C₀ (summable_geometric_of_lt_one hK_nn hK)
  have hcauchy : CauchySeq a := cauchySeq_of_dist_le_of_summable d hdist hd_sum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim_eq : truncatedConjugatePicardLimit p u₀ T t x = L := by
    unfold truncatedConjugatePicardLimit
    simp only [ht, htT, and_self, ite_true]
    exact hL.limUnder_eq
  rw [hlim_eq, ← Real.dist_eq]
  calc dist (a n) L ≤ ∑' m, d (n + m) :=
        dist_le_tsum_of_dist_le_of_tendsto d hdist hd_sum hL n
    _ = K ^ n * C₀ / (1 - K) := by
        simp_rw [d, pow_add, mul_assoc]
        rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hK_nn hK]
        ring

theorem truncatedConjugatePicardIter_uniform_convergence
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (_hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ t, 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ n t x
          - truncatedConjugatePicardLimit p u₀ T t x| < ε := by
  intro ε hε
  have htend := truncated_geometric_tail_tendsto_zero hK hK_nn (C₀ := C₀)
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  exact ⟨N, fun n hn t ht htT x => by
    calc |truncatedConjugatePicardIter p u₀ n t x
          - truncatedConjugatePicardLimit p u₀ T t x|
        ≤ K ^ n * C₀ / (1 - K) :=
          truncatedConjugatePicardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀
            hbound t ht htT x n
      _ < ε := by
          have h1K : (0 : ℝ) < 1 - K := by linarith
          have hnn : 0 ≤ K ^ n * C₀ / (1 - K) :=
            div_nonneg (mul_nonneg (pow_nonneg hK_nn n) hC₀) h1K.le
          have := hN n hn
          rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn] at this⟩

theorem truncatedConjugatePicardLimit_bounded
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint, |truncatedConjugatePicardIter p u₀ n t x| ≤ M) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardLimit p u₀ T t x| ≤ M := by
  intro t ht htT x
  unfold truncatedConjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => truncatedConjugatePicardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact le_of_tendsto (hL.abs) (Eventually.of_forall (fun n => hball n t ht htT x))

theorem truncatedConjugatePicardLimit_hasContinuousSlices
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hcont_iterates : ∀ n, HasContinuousSlices T (truncatedConjugatePicardIter p u₀ n)) :
    HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T) := by
  intro t ht htT
  have hunif :
      TendstoUniformly (fun n => truncatedConjugatePicardIter p u₀ n t)
        (truncatedConjugatePicardLimit p u₀ T t) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ :=
      truncatedConjugatePicardIter_uniform_convergence p u₀ hT hK hK_nn hC₀
        hbound ε hε
    apply Filter.eventually_atTop.mpr
    exact ⟨N, fun n hn x => by
      rw [Real.dist_eq, abs_sub_comm]
      exact hN n hn t ht htT x⟩
  exact hunif.continuous
    (Eventually.of_forall (fun n => hcont_iterates n t ht htT) |>.frequently)

theorem truncatedConjugatePicardLimit_is_mildSolution
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (_hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K)
    (hC₀ : 0 ≤ C₀) (_hM : 0 < M)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint,
        |truncatedConjugatePicardIter p u₀ (n + 1) t x
          - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint, |truncatedConjugatePicardIter p u₀ n t x| ≤ M)
    (hcont_iterates : ∀ n, HasContinuousSlices T (truncatedConjugatePicardIter p u₀ n))
    (hcont_limit : HasContinuousSlices T (truncatedConjugatePicardLimit p u₀ T))
    (hmeas_iterates : ∀ n, HasJointMeasurability (truncatedConjugatePicardIter p u₀ n))
    (hmeas_limit : HasJointMeasurability (truncatedConjugatePicardLimit p u₀ T))
    (hcontract : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |truncatedConjugateDuhamelMap p u₀ u t x
          - truncatedConjugateDuhamelMap p u₀ w t x| ≤ K * d) :
    TruncatedConjugateMildSolution p T u₀
      (truncatedConjugatePicardLimit p u₀ T) := by
  intro t ht htT x
  unfold truncatedConjugatePicardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => truncatedConjugatePicardIter p u₀ m t x
  set u := truncatedConjugatePicardLimit p u₀ T
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀
      (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  change atTop.limUnder a = _
  rw [hL.limUnder_eq]
  have h1K : (0 : ℝ) < 1 - K := by linarith
  set tail := fun n => K ^ n * C₀ / (1 - K)
  have hu_ball : ∀ s, 0 < s → s ≤ T → ∀ y, |u s y| ≤ M :=
    truncatedConjugatePicardLimit_bounded p u₀ hK hK_nn hC₀ hbound hball
  have htail : ∀ n s, 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ n s y - u s y| ≤ tail n :=
    fun n s hs hsT y =>
      truncatedConjugatePicardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀
        hbound s hs hsT y n
  have hkey : ∀ n,
      |truncatedConjugateDuhamelMap p u₀ u t x - L|
        ≤ K * tail n + tail (n + 1) := by
    intro n
    calc |truncatedConjugateDuhamelMap p u₀ u t x - L|
        ≤ |truncatedConjugateDuhamelMap p u₀ u t x
            - truncatedConjugateDuhamelMap p u₀ (truncatedConjugatePicardIter p u₀ n) t x|
          + |truncatedConjugateDuhamelMap p u₀
              (truncatedConjugatePicardIter p u₀ n) t x - L| :=
        abs_sub_le _ _ _
      _ = |truncatedConjugateDuhamelMap p u₀ u t x
            - truncatedConjugateDuhamelMap p u₀ (truncatedConjugatePicardIter p u₀ n) t x|
          + |truncatedConjugatePicardIter p u₀ (n + 1) t x - L| := by rfl
      _ ≤ K * tail n + tail (n + 1) := by
          gcongr
          · exact hcontract u (truncatedConjugatePicardIter p u₀ n) (tail n)
              hu_ball (fun s hs hsT y => hball n s hs hsT y)
              hcont_limit (hcont_iterates n) hmeas_limit (hmeas_iterates n)
              (fun s hs hsT y => by
                rw [abs_sub_comm]
                exact htail n s hs hsT y)
              t ht htT x
          · have hconv : L = truncatedConjugatePicardLimit p u₀ T t x := by
              unfold truncatedConjugatePicardLimit
              simp only [ht, htT, and_self, ite_true]
              exact hL.limUnder_eq.symm
            rw [hconv]
            exact truncatedConjugatePicardIter_pointwise_tail_bound p u₀ hK hK_nn
              hC₀ hbound t ht htT x (n + 1)
  have hvanish : Tendsto (fun n => K * tail n + tail (n + 1)) atTop (nhds 0) := by
    have htail0 := truncated_geometric_tail_tendsto_zero hK hK_nn (C₀ := C₀)
    have htail1 := htail0.comp (tendsto_add_atTop_nat 1)
    simpa [add_comm] using (htail0.const_mul K).add htail1
  have habs_le_zero : |truncatedConjugateDuhamelMap p u₀ u t x - L| ≤ 0 :=
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

/-- Ball membership and continuity of truncated B-form Picard iterates. -/
theorem truncatedConjugatePicardIter_ball
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) {T M : ℝ}
    (hbase : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ 0 t x| ≤ M)
    (hbase_cont : HasContinuousSlices T (truncatedConjugatePicardIter p u₀ 0))
    (hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |truncatedConjugateDuhamelMap p u₀ w t x| ≤ M)
    (hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      HasContinuousSlices T w →
      HasJointMeasurability w →
      HasContinuousSlices T (fun t x => truncatedConjugateDuhamelMap p u₀ w t x))
    (hbase_meas : HasJointMeasurability (truncatedConjugatePicardIter p u₀ 0))
    (hmeas_preserved : ∀ w, HasJointMeasurability w →
      HasJointMeasurability (fun t x => truncatedConjugateDuhamelMap p u₀ w t x))
    (n : ℕ) :
    (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ n t x| ≤ M) ∧
    HasContinuousSlices T (truncatedConjugatePicardIter p u₀ n) := by
  induction n with
  | zero => exact ⟨hbase, hbase_cont⟩
  | succ n ih =>
    have hmeas_iterates : ∀ k, HasJointMeasurability (truncatedConjugatePicardIter p u₀ k) := by
      intro k
      induction k with
      | zero => exact hbase_meas
      | succ j ihj => exact hmeas_preserved _ ihj
    exact ⟨fun t ht htT x => hmapsTo _ ih.1 ih.2 t ht htT x,
      hcont_preserved _ ih.1 ih.2 (hmeas_iterates n)⟩

theorem truncatedConjugatePicardIter_geometric
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K M : ℝ} (_hK_nn : 0 ≤ K)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T →
      ∀ x : intervalDomainPoint, |truncatedConjugatePicardIter p u₀ n t x| ≤ M)
    (hcont_iterates : ∀ n, HasContinuousSlices T (truncatedConjugatePicardIter p u₀ n))
    (hmeas_iterates : ∀ n, HasJointMeasurability (truncatedConjugatePicardIter p u₀ n))
    (hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
      HasJointMeasurability u →
      HasJointMeasurability w →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |truncatedConjugateDuhamelMap p u₀ u t x
          - truncatedConjugateDuhamelMap p u₀ w t x| ≤ K * d)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ 1 t x
        - truncatedConjugatePicardIter p u₀ 0 t x| ≤ C₀)
    (n : ℕ) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ (n + 1) t x
        - truncatedConjugatePicardIter p u₀ n t x| ≤ K ^ n * C₀ := by
  induction n with
  | zero => simpa using hbase_diff
  | succ n ih =>
    intro t ht htT x
    calc |truncatedConjugatePicardIter p u₀ (n + 2) t x
          - truncatedConjugatePicardIter p u₀ (n + 1) t x|
        = |truncatedConjugateDuhamelMap p u₀
              (truncatedConjugatePicardIter p u₀ (n + 1)) t x
            - truncatedConjugateDuhamelMap p u₀
              (truncatedConjugatePicardIter p u₀ n) t x| := rfl
      _ ≤ K * (K ^ n * C₀) :=
          hcontr _ _ _ (hball (n + 1)) (hball n)
            (hcont_iterates (n + 1)) (hcont_iterates n)
            (hmeas_iterates (n + 1)) (hmeas_iterates n) ih t ht htT x
      _ = K ^ (n + 1) * C₀ := by ring

/-- Data sufficient for the truncated B-form Picard construction.  The analytic
maps-to and contraction estimates are explicit fields; the fixed-point equation
itself is proved from them below. -/
structure TruncatedConjugateMildExistenceData (p : CM2Params)
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
    |truncatedConjugatePicardIter p u₀ 0 t x| ≤ M
  hbase_cont : HasContinuousSlices T (truncatedConjugatePicardIter p u₀ 0)
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugateDuhamelMap p u₀ w t x| ≤ M
  hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    HasContinuousSlices T w →
    HasJointMeasurability w →
    HasContinuousSlices T (fun t x => truncatedConjugateDuhamelMap p u₀ w t x)
  hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
    HasJointMeasurability u →
    HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |truncatedConjugateDuhamelMap p u₀ u t x
        - truncatedConjugateDuhamelMap p u₀ w t x| ≤ K * d
  hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |truncatedConjugatePicardIter p u₀ 1 t x
      - truncatedConjugatePicardIter p u₀ 0 t x| ≤ C₀
  hbase_meas : HasJointMeasurability (truncatedConjugatePicardIter p u₀ 0)
  hmeas_preserved : ∀ w, HasJointMeasurability w →
    HasJointMeasurability (fun t x => truncatedConjugateDuhamelMap p u₀ w t x)

private theorem truncatedConjugatePicardLimit_measurable_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀)
    (hgeom : ∀ n t, 0 < t → t ≤ D.T → ∀ x : intervalDomainPoint,
      |truncatedConjugatePicardIter p u₀ (n + 1) t x
        - truncatedConjugatePicardIter p u₀ n t x| ≤ D.K ^ n * D.C₀)
    (hmeas_iterates : ∀ n, HasJointMeasurability (truncatedConjugatePicardIter p u₀ n)) :
    HasJointMeasurability (truncatedConjugatePicardLimit p u₀ D.T) := by
  set f_n : ℕ → ℝ × ℝ → ℝ := fun n q =>
    if 0 < q.1 ∧ q.1 ≤ D.T then
      intervalDomainLift (truncatedConjugatePicardIter p u₀ n q.1) q.2
    else 0
  set g : ℝ × ℝ → ℝ := fun q =>
    intervalDomainLift (truncatedConjugatePicardLimit p u₀ D.T q.1) q.2
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
      unfold truncatedConjugatePicardLimit
      simp only [if_pos hq]
      unfold intervalDomainLift
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp only [dif_pos hy]
        exact tendsto_nhds_limUnder
          (truncatedConjugatePicardIter_pointwise_convergent p u₀ D.hK D.hK_nn
            D.hC₀ hgeom q.1 hq.1 hq.2 ⟨q.2, hy⟩)
      · simp only [dif_neg hy]
        exact tendsto_const_nhds
    · simp only [f_n, if_neg hq]
      have hg0 : g q = 0 := by
        simp only [g, truncatedConjugatePicardLimit, if_neg hq, intervalDomainLift]
        split_ifs <;> rfl
      rw [hg0]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hf_meas hlim

/-- The truncated B-form Picard construction produces a fixed point from honest
maps-to/contraction data. -/
theorem truncatedConjugateMildSolution_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      TruncatedConjugateMildSolution p T u₀ u := by
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ D.hbase_ball D.hbase_cont
      D.hmapsTo D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates : ∀ n, HasJointMeasurability (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ D.hK_nn hball
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
  have hcont_limit := truncatedConjugatePicardLimit_hasContinuousSlices p u₀ D.hT
    D.hK D.hK_nn D.hC₀ (fun n => hgeom n) hcont_iterates
  have hmeas_limit :=
    truncatedConjugatePicardLimit_measurable_of_data D (fun n => hgeom n) hmeas_iterates
  exact ⟨D.T, D.hT, truncatedConjugatePicardLimit p u₀ D.T,
    truncatedConjugatePicardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn
      D.hC₀ D.hM (fun n => hgeom n) hball hcont_iterates hcont_limit
      hmeas_iterates hmeas_limit D.hcontr⟩

/-- Packaged truncated fixed point and the ball bound used to construct it. -/
structure TruncatedConjugateMildSolutionData (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  hT : 0 < T
  M : ℝ
  hM : 0 < M
  u : ℝ → intervalDomainPoint → ℝ
  hmild : TruncatedConjugateMildSolution p T u₀ u
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u

/-- Build the packaged truncated B-form fixed point from Picard data. -/
def truncatedConjugateMildSolutionData_of_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀) :
    TruncatedConjugateMildSolutionData p u₀ := by
  have hball_cont := fun n =>
    truncatedConjugatePicardIter_ball p u₀ D.hbase_ball D.hbase_cont
      D.hmapsTo D.hcont_preserved D.hbase_meas D.hmeas_preserved n
  have hball := fun n => (hball_cont n).1
  have hcont_iterates := fun n => (hball_cont n).2
  have hmeas_iterates : ∀ n, HasJointMeasurability (truncatedConjugatePicardIter p u₀ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hgeom := truncatedConjugatePicardIter_geometric p u₀ D.hK_nn hball
    hcont_iterates hmeas_iterates D.hcontr D.hC₀ D.hbase_diff
  have hcont_limit := truncatedConjugatePicardLimit_hasContinuousSlices p u₀ D.hT
    D.hK D.hK_nn D.hC₀ (fun n => hgeom n) hcont_iterates
  have hmeas_limit :=
    truncatedConjugatePicardLimit_measurable_of_data D (fun n => hgeom n) hmeas_iterates
  exact {
    T := D.T
    hT := D.hT
    M := D.M
    hM := D.hM
    u := truncatedConjugatePicardLimit p u₀ D.T
    hmild := truncatedConjugatePicardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn
      D.hC₀ D.hM (fun n => hgeom n) hball hcont_iterates hcont_limit
      hmeas_iterates hmeas_limit D.hcontr
    hbound := truncatedConjugatePicardLimit_bounded p u₀ D.hK D.hK_nn D.hC₀
      (fun n => hgeom n) hball
    hcont := hcont_limit
    hmeas := hmeas_limit
  }

/-- Existence projection with the constructed ball bound exposed. -/
theorem truncatedConjugateMildSolution_exists_from_data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : TruncatedConjugateMildExistenceData p u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      TruncatedConjugateMildSolution p T u₀ u ∧
      (∀ t, 0 < t → t ≤ T → ∀ x,
        |u t x| ≤ (truncatedConjugateMildSolutionData_of_data D).M) := by
  let C := truncatedConjugateMildSolutionData_of_data D
  exact ⟨C.T, C.hT, C.u, C.hmild, C.hbound⟩

end ShenWork.Paper2.BFormPositiveDatumNegPart
