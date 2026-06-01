/-
  ShenWork/Paper2/IntervalMildPicard.lean

  T7 Atom E/F: Picard iteration → IntervalMildSolution.

  Strategy: define the Picard iteration u_{n+1} = Φ(u₀, u_n) directly
  on plain functions ℝ → intervalDomainPoint → ℝ. The contraction bound
  gives geometric decay ‖u_{n+1} − u_n‖ ≤ K^n · C₀, hence pointwise
  Cauchy, hence convergence. The limit satisfies the fixed-point equation
  by the contraction bound applied to the limit.

  This approach bypasses Q2 (joint continuity / BoundedContinuousFunction)
  entirely — no BCF, no metric space on function types.
-/
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.PDE.IntervalChemFluxLipschitz
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Set Filter
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalChemFluxLipschitz

noncomputable section

namespace ShenWork.IntervalMildPicard

/-! ## Picard iteration -/

/-- The Picard iteration: u₀(t,x) = S(t)u₀(x), u_{n+1} = Φ(u₀, u_n). -/
def picardIter (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    : ℕ → (ℝ → intervalDomainPoint → ℝ)
  | 0 => fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
  | n + 1 => fun t x => intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x

/-! ## Pointwise convergence from geometric bound -/

/-- If a sequence of reals satisfies |a_{n+1} − a_n| ≤ K^n · C₀ with K < 1,
then the sequence is Cauchy, hence converges. -/
theorem real_cauchySeq_of_geometric_bound {a : ℕ → ℝ} {K C₀ : ℝ}
    (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ n : ℕ, |a (n + 1) - a n| ≤ K ^ n * C₀) :
    CauchySeq a := by
  refine cauchySeq_of_dist_le_of_summable (fun n => K ^ n * C₀) ?_ ?_
  · intro n
    rw [Real.dist_eq, abs_sub_comm]
    exact hbound n
  · exact Summable.mul_right C₀ (summable_geometric_of_lt_one hK_nn hK)

/-- A Cauchy sequence in ℝ has a limit. -/
theorem real_cauchySeq_convergent {a : ℕ → ℝ} (h : CauchySeq a) :
    ∃ L : ℝ, Tendsto a atTop (nhds L) :=
  let ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h
  ⟨L, hL⟩

/-! ## Pointwise limit of Picard iteration -/

/-- The pointwise limit of the Picard iterates exists at each (t,x). -/
theorem picardIter_pointwise_convergent (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      ∃ L : ℝ, Tendsto (fun n => picardIter p u₀ n t x) atTop (nhds L) := by
  intro t ht htT x
  exact real_cauchySeq_convergent
    (real_cauchySeq_of_geometric_bound hK hK_nn hC₀ (fun n => hbound n t ht htT x))

/-- The pointwise limit function. -/
def picardLimit (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (T : ℝ)
    (t : ℝ) (x : intervalDomainPoint) : ℝ :=
  if 0 < t ∧ t ≤ T
  then atTop.limUnder (fun n => picardIter p u₀ n t x)
  else 0

/-! ## Uniform convergence from geometric bound -/

/-- The geometric tail sum K^n · C₀ / (1 − K) tends to 0. -/

private theorem geometric_tail_tendsto_zero {K C₀ : ℝ}
    (hK : K < 1) (hK_nn : 0 ≤ K) :
    Tendsto (fun n => K ^ n * C₀ / (1 - K)) atTop (nhds 0) := by
  have h1K : (0 : ℝ) < 1 - K := by linarith
  rw [show (0:ℝ) = 0 / (1 - K) from by simp]
  apply Tendsto.div_const
  have := tendsto_pow_atTop_nhds_zero_of_lt_one hK_nn hK |>.mul_const C₀
  simp [zero_mul] at this
  exact this

/-- At each (t,x), the Cauchy sequence u_n(t,x) satisfies the tail bound
|u_n(t,x) - L| ≤ K^n · C₀ / (1 - K). This is the quantitative rate from
the geometric Cauchy bound. -/
theorem picardIter_pointwise_tail_bound (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (x : intervalDomainPoint) (n : ℕ) :
    |picardIter p u₀ n t x - picardLimit p u₀ T t x| ≤ K ^ n * C₀ / (1 - K) := by
  set a := fun m => picardIter p u₀ m t x
  set d := fun m => K ^ m * C₀
  have hdist : ∀ m, dist (a m) (a m.succ) ≤ d m := by
    intro m; rw [Real.dist_eq, abs_sub_comm]; exact hbound m t ht htT x
  have hd_sum : Summable d :=
    Summable.mul_right C₀ (summable_geometric_of_lt_one hK_nn hK)
  have hcauchy : CauchySeq a := cauchySeq_of_dist_le_of_summable d hdist hd_sum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim_eq : picardLimit p u₀ T t x = L := by
    unfold picardLimit; simp only [ht, htT, and_self, ite_true]
    change (atTop.limUnder fun n => picardIter p u₀ n t x) = L
    exact hL.limUnder_eq
  rw [hlim_eq, ← Real.dist_eq]
  calc dist (a n) L ≤ ∑' m, d (n + m) :=
        dist_le_tsum_of_dist_le_of_tendsto d hdist hd_sum hL n
    _ = K ^ n * C₀ / (1 - K) := by
        simp_rw [d, pow_add, mul_assoc]
        rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hK_nn hK]; ring

theorem picardIter_uniform_convergence (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (_hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x - picardLimit p u₀ T t x| < ε := by
  intro ε hε
  have htend := geometric_tail_tendsto_zero hK hK_nn (C₀ := C₀)
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend ε hε
  exact ⟨N, fun n hn t ht htT x => by
    calc |picardIter p u₀ n t x - picardLimit p u₀ T t x|
        ≤ K ^ n * C₀ / (1 - K) :=
          picardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀ hbound t ht htT x n
      _ < ε := by
          have h1K : (0 : ℝ) < 1 - K := by linarith
          have hnn : 0 ≤ K ^ n * C₀ / (1 - K) :=
            div_nonneg (mul_nonneg (pow_nonneg hK_nn n) hC₀) h1K.le
          have := hN n hn
          rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnn] at this⟩

/-! ## The limit is a fixed point -/

/-- The limit trajectory is bounded: |u(t,x)| ≤ M when all iterates are. -/
theorem picardLimit_bounded (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardLimit p u₀ T t x| ≤ M := by
  intro t ht htT x
  unfold picardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => picardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀ (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact le_of_tendsto (hL.abs) (Eventually.of_forall (fun n => hball n t ht htT x))

theorem picardLimit_is_mildSolution (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (_hM : 0 < M)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M)
    -- Pointwise contraction: Φ is K-Lipschitz in the trajectory
    (hcontract : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ u t x
          - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d) :
    IntervalMildSolution p T u₀ (picardLimit p u₀ T) := by
  intro t ht htT x
  unfold picardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => picardIter p u₀ m t x
  set u := picardLimit p u₀ T
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀ (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  change atTop.limUnder a = _
  rw [hL.limUnder_eq]
  -- Goal: L = intervalGradientDuhamelMap p u₀ u t x
  -- Strategy: |Φ(u₀,u) - L| ≤ K * tail_n + tail_{n+1} → 0
  have h1K : (0:ℝ) < 1 - K := by linarith
  set tail := fun n => K ^ n * C₀ / (1 - K)
  -- u is bounded
  have hu_ball : ∀ s, 0 < s → s ≤ T → ∀ y, |u s y| ≤ M :=
    picardLimit_bounded p u₀ hK hK_nn hC₀ hbound hball
  -- u_n - u tail bound
  have htail : ∀ n s, 0 < s → s ≤ T → ∀ y : intervalDomainPoint,
      |picardIter p u₀ n s y - u s y| ≤ tail n :=
    fun n s hs hsT y => picardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀ hbound s hs hsT y n
  -- For every n: |Φu - L| ≤ |Φu - Φu_n| + |u_{n+1} - L| ≤ K·tail_n + tail_{n+1}
  have hkey : ∀ n, |intervalGradientDuhamelMap p u₀ u t x - L| ≤ K * tail n + tail (n + 1) := by
    intro n
    have htri := abs_sub_abs_le_abs_sub
        (intervalGradientDuhamelMap p u₀ u t x)
        (intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x)
    calc |intervalGradientDuhamelMap p u₀ u t x - L|
        ≤ |intervalGradientDuhamelMap p u₀ u t x
            - intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x|
          + |intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x - L| :=
        abs_sub_le _ _ _
      _ = |intervalGradientDuhamelMap p u₀ u t x
            - intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x|
          + |picardIter p u₀ (n+1) t x - L| := by rfl
      _ ≤ K * tail n + tail (n + 1) := by
          gcongr
          · exact hcontract u (picardIter p u₀ n) (tail n) hu_ball
              (fun s hs hsT y => hball n s hs hsT y)
              (fun s hs hsT y => by
                rw [abs_sub_comm]
                exact htail n s hs hsT y)
              t ht htT x
          · have hconv : L = picardLimit p u₀ T t x := by
              unfold picardLimit
              simp only [ht, htT, and_self, ite_true]
              exact hL.limUnder_eq.symm
            rw [hconv]
            exact picardIter_pointwise_tail_bound p u₀ hK hK_nn hC₀ hbound t ht htT x (n+1)
  -- K·tail_n + tail_{n+1} → 0 as n → ∞
  have hvanish : Tendsto (fun n => K * tail n + tail (n + 1)) atTop (nhds 0) := by
    have := geometric_tail_tendsto_zero hK hK_nn (C₀ := C₀)
    have h2 := this.comp (tendsto_add_atTop_nat 1)
    simpa [add_comm] using this.const_mul K |>.add h2
  -- |Φu - L| ≤ 0, hence = 0
  have habs_le_zero : |intervalGradientDuhamelMap p u₀ u t x - L| ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε => by
      rw [zero_add]
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hvanish) ε hε
      have := hN N le_rfl
      have hnn : 0 ≤ K * tail N + tail (N + 1) := by
        apply add_nonneg <;> apply mul_nonneg
        · exact hK_nn
        · exact div_nonneg (mul_nonneg (pow_nonneg hK_nn N) hC₀) h1K.le
        · exact mul_nonneg (pow_nonneg hK_nn (N + 1)) hC₀
        · exact inv_nonneg.mpr h1K.le
      simp only [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at this
      exact (hkey N).trans this.le)
  exact (eq_of_abs_sub_nonpos habs_le_zero).symm

/-! ## Main existence theorem -/

/-- Conditional mild existence: given suitable constants satisfying the
analytic bounds, Picard iteration produces a mild solution. -/
theorem intervalMildSolution_of_bounds (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hM : 0 < M)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M)
    (hcontract : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ u t x
          - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d) :
    ∃ u : ℝ → intervalDomainPoint → ℝ, IntervalMildSolution p T u₀ u :=
  ⟨picardLimit p u₀ T,
    picardLimit_is_mildSolution p u₀ hT hK hK_nn hC₀ hM hbound hball hcontract⟩

/-- Ball membership of Picard iterates by induction. -/
theorem picardIter_ball (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T M : ℝ}
    (hbase : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ 0 t x| ≤ M)
    (hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ w t x| ≤ M)
    (n : ℕ) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M := by
  induction n with
  | zero => exact hbase
  | succ n ih => exact fun t ht htT x => hmapsTo _ ih t ht htT x

/-- Geometric decay of Picard differences by induction. -/
theorem picardIter_geometric (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K M : ℝ} (hK_nn : 0 ≤ K)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M)
    (hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ u t x
          - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x| ≤ C₀)
    (n : ℕ) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀ := by
  induction n with
  | zero => simpa using hbase_diff
  | succ n ih =>
    intro t ht htT x
    calc |picardIter p u₀ (n + 2) t x - picardIter p u₀ (n + 1) t x|
        = |intervalGradientDuhamelMap p u₀ (picardIter p u₀ (n + 1)) t x
            - intervalGradientDuhamelMap p u₀ (picardIter p u₀ n) t x| := rfl
      _ ≤ K * (K ^ n * C₀) :=
          hcontr _ _ _ (hball (n + 1)) (hball n) ih t ht htT x
      _ = K ^ (n + 1) * C₀ := by ring

/-- All the data needed for mild existence via Picard iteration. -/
structure MildExistenceData (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) where
  T : ℝ
  M : ℝ
  K : ℝ
  C₀ : ℝ
  hT : 0 < T
  hM : 0 < M
  hK : K < 1
  hK_nn : 0 ≤ K
  hC₀ : 0 ≤ C₀
  -- u₀ initial iterate bounded
  hbase_ball : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |picardIter p u₀ 0 t x| ≤ M
  -- MapsTo: Φ maps ball to ball
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalGradientDuhamelMap p u₀ w t x| ≤ M
  -- Contraction
  hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalGradientDuhamelMap p u₀ u t x
        - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d
  -- Initial difference bounded
  hbase_diff : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x| ≤ C₀

/-- Given MildExistenceData, mild solution exists (0 sorry). -/
theorem intervalMildSolution_of_data {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    (D : MildExistenceData p u₀) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u := by
  have hball := picardIter_ball p u₀ D.hbase_ball D.hmapsTo
  have hgeom := picardIter_geometric p u₀ D.hK_nn hball D.hcontr D.hC₀ D.hbase_diff
  exact ⟨D.T, D.hT, picardLimit p u₀ D.T,
    picardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn D.hC₀ D.hM
      (fun n => hgeom n) hball D.hcontr⟩

/-- Full mild existence: constructs MildExistenceData from PDE estimates.
Sorry: instantiating T, M, K, C₀ from Duhamel bounds + flux/logistic Lipschitz.
This is pure plumbing — no new math, just regularity/integrability discharge. -/
theorem intervalMildSolution_exists_picard (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀_bounded : ∃ B : ℝ, ∀ x, |u₀ x| ≤ B) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u := by
  obtain ⟨B, hB⟩ := _hu₀_bounded
  set M := 2 * max B 1 with hMdef
  have hM : 0 < M := by positivity
  have hB_le : ∀ x, |u₀ x| ≤ M / 2 := by
    intro x; calc |u₀ x| ≤ B := hB x
      _ ≤ max B 1 := le_max_left B 1
      _ = M / 2 := by rw [hMdef]; ring
  -- The Duhamel bounds give constants C_grad, C_Q, C_L depending on M and p.
  -- For now we sorry the existence of suitable T, K, C₀ satisfying all conditions.
  -- This is pure PDE-constant instantiation (no new math).
  suffices h : ∃ T K C₀ : ℝ, 0 < T ∧ K < 1 ∧ 0 ≤ K ∧ 0 ≤ C₀ ∧
      (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |picardIter p u₀ 0 t x| ≤ M) ∧
      (∀ (w : ℝ → intervalDomainPoint → ℝ),
        (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
        ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀ w t x| ≤ M) ∧
      (∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
        (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
        (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
        (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
        ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
          |intervalGradientDuhamelMap p u₀ u t x
            - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d) ∧
      (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |picardIter p u₀ 1 t x - picardIter p u₀ 0 t x| ≤ C₀) by
    obtain ⟨T, K, C₀, hT, hK, hK_nn, hC₀, hbase, hmaps, hcontr, hdiff⟩ := h
    exact intervalMildSolution_of_data ⟨T, M, K, C₀, hT, hM, hK, hK_nn, hC₀,
      hbase, hmaps, hcontr, hdiff⟩
  -- Key insight: in Lean, ∫ f dμ = 0 when f is not integrable (integral_undef).
  -- So for non-measurable trajectories, all Duhamel terms are 0, and bounds hold.
  -- For measurable ones, the existing PDE bounds apply.
  -- This makes hmapsTo and hcontr universal over ALL bounded trajectories.
  sorry

end ShenWork.IntervalMildPicard
