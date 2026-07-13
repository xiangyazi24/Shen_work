import ShenWork.Paper2.IntervalConjugatePicardFloorCore

/-!
# Generic positive-floor Picard iteration

This is the map-independent convergence core used by the faithful general-`m`
local theory.  Analytic properties of the nonlinear Duhamel map enter only
through the fields of `PositiveFloorPicardData`.
-/

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard

noncomputable section

namespace ShenWork.PDE.PositiveFloorPicard

abbrev Trajectory := ℝ → intervalDomainPoint → ℝ

def picardIter (base : Trajectory) (Φ : Trajectory → Trajectory) : ℕ → Trajectory
  | 0 => base
  | n + 1 => Φ (picardIter base Φ n)

def picardLimit (base : Trajectory) (Φ : Trajectory → Trajectory)
    (T : ℝ) : Trajectory := fun t x =>
  if 0 < t ∧ t ≤ T then atTop.limUnder (fun n => picardIter base Φ n t x) else 0

structure PositiveFloorPicardData (base : Trajectory)
    (Φ : Trajectory → Trajectory) where
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
  hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x, |base t x| ≤ M
  hbase_floor : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ base t x
  hbase_cont : HasContinuousSlices T base
  hbase_meas : HasJointMeasurability base
  hmapsTo : ∀ w,
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x, |Φ w t x| ≤ M
  hmapsTo_floor : ∀ w,
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ Φ w t x
  hcont_preserved : ∀ w,
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T w → HasJointMeasurability w →
    HasContinuousSlices T (Φ w)
  hmeas_preserved : ∀ w, HasJointMeasurability w → HasJointMeasurability (Φ w)
  hcontract : ∀ u w d,
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, c ≤ w t x) →
    HasContinuousSlices T u → HasContinuousSlices T w →
    HasJointMeasurability u → HasJointMeasurability w →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x, |Φ u t x - Φ w t x| ≤ K * d
  hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x,
    |picardIter base Φ 1 t x - picardIter base Φ 0 t x| ≤ C₀

theorem picardIter_floor_ball
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    ∀ n,
      (∀ t, 0 < t → t ≤ D.T → ∀ x, |picardIter base Φ n t x| ≤ D.M) ∧
      (∀ t, 0 < t → t ≤ D.T → ∀ x, D.c ≤ picardIter base Φ n t x) ∧
      HasContinuousSlices D.T (picardIter base Φ n) := by
  intro n
  induction n with
  | zero => exact ⟨D.hbase_ball, D.hbase_floor, D.hbase_cont⟩
  | succ n ih =>
      have hmeas : ∀ k, HasJointMeasurability (picardIter base Φ k) := by
        intro k
        induction k with
        | zero => exact D.hbase_meas
        | succ j hj => exact D.hmeas_preserved _ hj
      exact ⟨D.hmapsTo _ ih.1 ih.2.1 ih.2.2,
        D.hmapsTo_floor _ ih.1 ih.2.1 ih.2.2,
        D.hcont_preserved _ ih.1 ih.2.1 ih.2.2 (hmeas n)⟩

theorem picardIter_geometric
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    ∀ n t, 0 < t → t ≤ D.T → ∀ x,
      |picardIter base Φ (n + 1) t x - picardIter base Φ n t x| ≤
        D.K ^ n * D.C₀ := by
  intro n
  induction n with
  | zero => simpa using D.hbase_diff
  | succ n ih =>
      intro t ht htT x
      have hdata := picardIter_floor_ball D
      have hmeas : ∀ k, HasJointMeasurability (picardIter base Φ k) := by
        intro k
        induction k with
        | zero => exact D.hbase_meas
        | succ j hj => exact D.hmeas_preserved _ hj
      calc
        |picardIter base Φ (n + 2) t x - picardIter base Φ (n + 1) t x|
            = |Φ (picardIter base Φ (n + 1)) t x -
                Φ (picardIter base Φ n) t x| := rfl
        _ ≤ D.K * (D.K ^ n * D.C₀) :=
          D.hcontract _ _ _ (hdata (n + 1)).1 (hdata (n + 1)).2.1
            (hdata n).1 (hdata n).2.1 (hdata (n + 1)).2.2 (hdata n).2.2
            (hmeas (n + 1)) (hmeas n) ih t ht htT x
        _ = D.K ^ (n + 1) * D.C₀ := by ring

theorem picardIter_pointwise_convergent
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ D.T) (x : intervalDomainPoint) :
    ∃ L, Tendsto (fun n => picardIter base Φ n t x) atTop (nhds L) :=
  real_cauchySeq_convergent
    (real_cauchySeq_of_geometric_bound D.hK D.hK_nn D.hC₀
      (fun n => picardIter_geometric D n t ht htT x))

theorem picardIter_tail_bound
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ D.T)
    (x : intervalDomainPoint) (n : ℕ) :
    |picardIter base Φ n t x - picardLimit base Φ D.T t x| ≤
      D.K ^ n * D.C₀ / (1 - D.K) := by
  let a := fun m => picardIter base Φ m t x
  let d := fun m => D.K ^ m * D.C₀
  have hdist : ∀ m, dist (a m) (a m.succ) ≤ d m := by
    intro m
    rw [Real.dist_eq, abs_sub_comm]
    exact picardIter_geometric D m t ht htT x
  have hsum : Summable d :=
    Summable.mul_right D.C₀ (summable_geometric_of_lt_one D.hK_nn D.hK)
  have hcauchy : CauchySeq a := cauchySeq_of_dist_le_of_summable d hdist hsum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : picardLimit base Φ D.T t x = L := by
    unfold picardLimit
    simp only [ht, htT, and_self, ite_true]
    exact hL.limUnder_eq
  rw [hlim, ← Real.dist_eq]
  calc
    dist (a n) L ≤ ∑' m, d (n + m) :=
      dist_le_tsum_of_dist_le_of_tendsto d hdist hsum hL n
    _ = D.K ^ n * D.C₀ / (1 - D.K) := by
      simp_rw [d, pow_add, mul_assoc]
      rw [tsum_mul_left, tsum_mul_right,
        tsum_geometric_of_lt_one D.hK_nn D.hK]
      ring

theorem picardLimit_bounded
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    ∀ t, 0 < t → t ≤ D.T → ∀ x, |picardLimit base Φ D.T t x| ≤ D.M := by
  intro t ht htT x
  unfold picardLimit
  simp only [ht, htT, and_self, ite_true]
  obtain ⟨L, hL⟩ := picardIter_pointwise_convergent D t ht htT x
  rw [hL.limUnder_eq]
  exact le_of_tendsto hL.abs (Eventually.of_forall fun n =>
    (picardIter_floor_ball D n).1 t ht htT x)

theorem picardLimit_floor
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    ∀ t, 0 < t → t ≤ D.T → ∀ x, D.c ≤ picardLimit base Φ D.T t x := by
  intro t ht htT x
  unfold picardLimit
  simp only [ht, htT, and_self, ite_true]
  obtain ⟨L, hL⟩ := picardIter_pointwise_convergent D t ht htT x
  rw [hL.limUnder_eq]
  exact ge_of_tendsto hL (Eventually.of_forall fun n =>
    (picardIter_floor_ball D n).2.1 t ht htT x)

theorem picardLimit_hasContinuousSlices
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    HasContinuousSlices D.T (picardLimit base Φ D.T) := by
  intro t ht htT
  have hunif : TendstoUniformly (fun n => picardIter base Φ n t)
      (picardLimit base Φ D.T t) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have htail0 : Tendsto
        (fun n => D.K ^ n * D.C₀ / (1 - D.K)) atTop (nhds 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one D.hK_nn D.hK
      simpa using (hp.mul_const D.C₀).div_const (1 - D.K)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp htail0) ε hε
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn x => by
      rw [Real.dist_eq, abs_sub_comm]
      exact (picardIter_tail_bound D t ht htT x n).trans_lt (by
        have := hN n hn
        rwa [Real.dist_eq, sub_zero,
          abs_of_nonneg (div_nonneg
            (mul_nonneg (pow_nonneg D.hK_nn n) D.hC₀)
            (sub_nonneg.mpr D.hK.le))] at this)⟩
  exact hunif.continuous
    (Eventually.of_forall (fun n => (picardIter_floor_ball D n).2.2 t ht htT)
      |>.frequently)

theorem picardLimit_measurable
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    HasJointMeasurability (picardLimit base Φ D.T) := by
  let f : ℕ → ℝ × ℝ → ℝ := fun n q =>
    if 0 < q.1 ∧ q.1 ≤ D.T then
      intervalDomainLift (picardIter base Φ n q.1) q.2 else 0
  let g : ℝ × ℝ → ℝ := fun q =>
    intervalDomainLift (picardLimit base Φ D.T q.1) q.2
  have hmeasIter : ∀ n, HasJointMeasurability (picardIter base Φ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hf : ∀ n, Measurable (f n) := fun n =>
    Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
      (hmeasIter n) measurable_const
  have hlim : Tendsto f atTop (nhds g) := by
    rw [tendsto_pi_nhds]
    intro q
    by_cases hq : 0 < q.1 ∧ q.1 ≤ D.T
    · simp only [f, if_pos hq, g]
      unfold picardLimit
      simp only [if_pos hq]
      unfold intervalDomainLift
      by_cases hy : q.2 ∈ Set.Icc (0 : ℝ) 1
      · simp only [dif_pos hy]
        exact tendsto_nhds_limUnder
          (picardIter_pointwise_convergent D q.1 hq.1 hq.2 ⟨q.2, hy⟩)
      · simp only [dif_neg hy]
        exact tendsto_const_nhds
    · simp only [f, if_neg hq]
      have hg : g q = 0 := by
        simp only [g, picardLimit, if_neg hq, intervalDomainLift]
        split_ifs <;> rfl
      rw [hg]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hf hlim

theorem picardLimit_fixed
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) :
    ∀ t, 0 < t → t ≤ D.T → ∀ x,
      picardLimit base Φ D.T t x = Φ (picardLimit base Φ D.T) t x := by
  intro t ht htT x
  let u := picardLimit base Φ D.T
  obtain ⟨L, hL⟩ := picardIter_pointwise_convergent D t ht htT x
  have hL_eq : u t x = L := by
    dsimp [u]
    unfold picardLimit
    simp only [ht, htT, and_self, ite_true]
    exact hL.limUnder_eq
  let tail := fun n => D.K ^ n * D.C₀ / (1 - D.K)
  have htail : ∀ n s, 0 < s → s ≤ D.T → ∀ y,
      |picardIter base Φ n s y - u s y| ≤ tail n :=
    fun n s hs hsT y => picardIter_tail_bound D s hs hsT y n
  have hmeasIter : ∀ n, HasJointMeasurability (picardIter base Φ n) := by
    intro n
    induction n with
    | zero => exact D.hbase_meas
    | succ n ih => exact D.hmeas_preserved _ ih
  have hkey : ∀ n, |Φ u t x - L| ≤ D.K * tail n + tail (n + 1) := by
    intro n
    calc
      |Φ u t x - L| ≤ |Φ u t x - Φ (picardIter base Φ n) t x| +
          |Φ (picardIter base Φ n) t x - L| := abs_sub_le _ _ _
      _ = |Φ u t x - Φ (picardIter base Φ n) t x| +
          |picardIter base Φ (n + 1) t x - L| := rfl
      _ ≤ D.K * tail n + tail (n + 1) := by
        gcongr
        · exact D.hcontract u (picardIter base Φ n) (tail n)
            (picardLimit_bounded D) (picardLimit_floor D)
            (picardIter_floor_ball D n).1 (picardIter_floor_ball D n).2.1
            (picardLimit_hasContinuousSlices D)
            (picardIter_floor_ball D n).2.2 (picardLimit_measurable D)
            (hmeasIter n)
            (fun s hs hsT y => by
              rw [abs_sub_comm]
              exact htail n s hs hsT y)
            t ht htT x
        · rw [← hL_eq]
          exact picardIter_tail_bound D t ht htT x (n + 1)
  have hvanish : Tendsto (fun n => D.K * tail n + tail (n + 1))
      atTop (nhds 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one D.hK_nn D.hK
    have ht0 : Tendsto tail atTop (nhds 0) := by
      simpa [tail] using (hp.mul_const D.C₀).div_const (1 - D.K)
    simpa [Function.comp_def] using
      (ht0.const_mul D.K).add (ht0.comp (tendsto_add_atTop_nat 1))
  have hz : |Φ u t x - L| ≤ 0 :=
    le_of_forall_pos_le_add fun ε hε => by
      rw [zero_add]
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hvanish) ε hε
      exact ((hkey N).trans_lt (by
        have := hN N le_rfl
        have hnn : 0 ≤ D.K * tail N + tail (N + 1) := by
          have hden : 0 ≤ 1 - D.K := sub_nonneg.mpr D.hK.le
          have htailnn : ∀ n, 0 ≤ tail n := fun n =>
            div_nonneg (mul_nonneg (pow_nonneg D.hK_nn n) D.hC₀) hden
          exact add_nonneg (mul_nonneg D.hK_nn (htailnn N))
            (htailnn (N + 1))
        rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at this)).le
  change u t x = Φ u t x
  rw [hL_eq]
  exact (eq_of_abs_sub_nonpos hz).symm

structure PositiveFloorFixedPointData (base : Trajectory)
    (Φ : Trajectory → Trajectory) where
  T : ℝ
  hT : 0 < T
  M : ℝ
  hM : 0 < M
  c : ℝ
  hc : 0 < c
  u : Trajectory
  hfixed : ∀ t, 0 < t → t ≤ T → ∀ x, u t x = Φ u t x
  hbound : ∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M
  hfloor : ∀ t, 0 < t → t ≤ T → ∀ x, c ≤ u t x
  hcont : HasContinuousSlices T u
  hmeas : HasJointMeasurability u

def fixedPointData
    {base : Trajectory} {Φ : Trajectory → Trajectory}
    (D : PositiveFloorPicardData base Φ) : PositiveFloorFixedPointData base Φ where
  T := D.T
  hT := D.hT
  M := D.M
  hM := D.hM
  c := D.c
  hc := D.hc
  u := picardLimit base Φ D.T
  hfixed := picardLimit_fixed D
  hbound := picardLimit_bounded D
  hfloor := picardLimit_floor D
  hcont := picardLimit_hasContinuousSlices D
  hmeas := picardLimit_measurable D

#print axioms picardIter_geometric
#print axioms picardLimit_fixed
#print axioms fixedPointData

end ShenWork.PDE.PositiveFloorPicard
