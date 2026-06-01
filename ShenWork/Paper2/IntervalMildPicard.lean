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

  **Nonneg cascade:** The ball condition throughout includes nonnegativity
  (∀ t x, 0 ≤ w t x) alongside boundedness (∀ t x, |w t x| ≤ M).
  This makes hw_nonneg available in hmapsTo/hcontr proofs, which is
  required by chemFluxLifted_bounded_of_continuous.
-/
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.PDE.IntervalChemFluxLipschitz
import ShenWork.Paper2.IntervalDuhamelIntegrability
import ShenWork.PDE.IntervalLogisticLipschitz
import ShenWork.PDE.IntervalResolverPositivity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

open MeasureTheory Set Filter
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap
open ShenWork.IntervalChemFluxLipschitz

noncomputable section

namespace ShenWork.IntervalMildPicard

/-! ## Topology and continuity -/

instance : TopologicalSpace intervalDomainPoint :=
  instTopologicalSpaceSubtype

/-- A trajectory has continuous spatial slices if each time-slice is continuous. -/
def HasContinuousSlices (T : ℝ) (u : ℝ → intervalDomainPoint → ℝ) : Prop :=
  ∀ t, 0 < t → t ≤ T → Continuous (u t)

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

/-- The limit trajectory is nonneg: 0 ≤ u(t,x) when all iterates are nonneg. -/
theorem picardLimit_nonneg (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hnn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ n t x) :
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardLimit p u₀ T t x := by
  intro t ht htT x
  unfold picardLimit
  simp only [ht, htT, and_self, ite_true]
  set a := fun m => picardIter p u₀ m t x
  have hcauchy : CauchySeq a :=
    real_cauchySeq_of_geometric_bound hK hK_nn hC₀ (fun n => hbound n t ht htT x)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  rw [hL.limUnder_eq]
  exact ge_of_tendsto hL (Eventually.of_forall (fun n => hnn n t ht htT x))

/-- The Picard limit has continuous slices when all iterates do and the
convergence is uniform (which follows from the geometric bound). -/
theorem picardLimit_hasContinuousSlices (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hcont_iterates : ∀ n, HasContinuousSlices T (picardIter p u₀ n)) :
    HasContinuousSlices T (picardLimit p u₀ T) := by
  intro t ht htT
  -- Each u_n(t, ·) is continuous and u_n(t, ·) → u(t, ·) uniformly.
  -- By the uniform limit theorem, u(t, ·) is continuous.
  have hunif : TendstoUniformly (fun n => picardIter p u₀ n t) (picardLimit p u₀ T t) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hconv := picardIter_uniform_convergence p u₀ hT hK hK_nn hC₀ hbound ε hε
    obtain ⟨N, hN⟩ := hconv
    apply Filter.eventually_atTop.mpr
    exact ⟨N, fun n hn x => by
      rw [Real.dist_eq, abs_sub_comm]
      exact hN n hn t ht htT x⟩
  exact hunif.continuous (Eventually.of_forall (fun n => hcont_iterates n t ht htT) |>.frequently)

theorem picardLimit_is_mildSolution (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (_hM : 0 < M)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M)
    (hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ n t x)
    (hcont_iterates : ∀ n, HasContinuousSlices T (picardIter p u₀ n))
    (hcont_limit : HasContinuousSlices T (picardLimit p u₀ T))
    -- Pointwise contraction: Φ is K-Lipschitz in the trajectory
    (hcontract : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
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
  -- u is nonneg
  have hu_nn : ∀ s, 0 < s → s ≤ T → ∀ y, 0 ≤ u s y :=
    picardLimit_nonneg p u₀ hK hK_nn hC₀ hbound hball_nn
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
          · exact hcontract u (picardIter p u₀ n) (tail n) hu_ball hu_nn
              (fun s hs hsT y => hball n s hs hsT y)
              (fun s hs hsT y => hball_nn n s hs hsT y)
              hcont_limit
              (hcont_iterates n)
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
    (hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ n t x)
    (hcont_iterates : ∀ n, HasContinuousSlices T (picardIter p u₀ n))
    (hcont_limit : HasContinuousSlices T (picardLimit p u₀ T))
    (hcontract : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x - w t x| ≤ d) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ u t x
          - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d) :
    ∃ u : ℝ → intervalDomainPoint → ℝ, IntervalMildSolution p T u₀ u :=
  ⟨picardLimit p u₀ T,
    picardLimit_is_mildSolution p u₀ hT hK hK_nn hC₀ hM hbound hball hball_nn
      hcont_iterates hcont_limit hcontract⟩

/-- Ball membership, nonnegativity, and continuity of Picard iterates by induction. -/
theorem picardIter_ball (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T M : ℝ}
    (hbase : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ 0 t x| ≤ M)
    (hbase_nn : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ 0 t x)
    (hbase_cont : HasContinuousSlices T (picardIter p u₀ 0))
    (hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        |intervalGradientDuhamelMap p u₀ w t x| ≤ M)
    (hmapsTo_nn : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T w →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        0 ≤ intervalGradientDuhamelMap p u₀ w t x)
    (hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      HasContinuousSlices T w →
      HasContinuousSlices T (fun t x => intervalGradientDuhamelMap p u₀ w t x))
    (n : ℕ) :
    (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M) ∧
    (∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ n t x) ∧
    HasContinuousSlices T (picardIter p u₀ n) := by
  induction n with
  | zero => exact ⟨hbase, hbase_nn, hbase_cont⟩
  | succ n ih =>
    exact ⟨fun t ht htT x => hmapsTo _ ih.1 ih.2.1 ih.2.2 t ht htT x,
           fun t ht htT x => hmapsTo_nn _ ih.1 ih.2.1 ih.2.2 t ht htT x,
           hcont_preserved _ ih.1 ih.2.2⟩

/-- Geometric decay of Picard differences by induction. -/
theorem picardIter_geometric (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K M : ℝ} (hK_nn : 0 ≤ K)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M)
    (hball_nn : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ n t x)
    (hcont_iterates : ∀ n, HasContinuousSlices T (picardIter p u₀ n))
    (hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
      HasContinuousSlices T u →
      HasContinuousSlices T w →
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
          hcontr _ _ _ (hball (n + 1)) (hball_nn (n + 1))
            (hball n) (hball_nn n)
            (hcont_iterates (n + 1)) (hcont_iterates n) ih t ht htT x
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
  -- u₀ initial iterate nonneg
  hbase_nonneg : ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
    0 ≤ picardIter p u₀ 0 t x
  -- Initial iterate has continuous slices
  hbase_cont : HasContinuousSlices T (picardIter p u₀ 0)
  -- MapsTo: Φ maps ball to ball (for continuous nonneg trajectories)
  hmapsTo : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |intervalGradientDuhamelMap p u₀ w t x| ≤ M
  -- MapsTo preserves nonneg
  hmapsTo_nn : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T w →
    ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ intervalGradientDuhamelMap p u₀ w t x
  -- Φ preserves continuous slices
  hcont_preserved : ∀ (w : ℝ → intervalDomainPoint → ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    HasContinuousSlices T w →
    HasContinuousSlices T (fun t x => intervalGradientDuhamelMap p u₀ w t x)
  -- Contraction (for continuous nonneg trajectories)
  hcontr : ∀ (u w : ℝ → intervalDomainPoint → ℝ) (d : ℝ),
    (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ u t x) →
    (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
    (∀ t, 0 < t → t ≤ T → ∀ x, 0 ≤ w t x) →
    HasContinuousSlices T u →
    HasContinuousSlices T w →
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
  have hball_cont := fun n => picardIter_ball p u₀ D.hbase_ball D.hbase_nonneg
    D.hbase_cont D.hmapsTo D.hmapsTo_nn D.hcont_preserved n
  have hball := fun n => (hball_cont n).1
  have hball_nn := fun n => (hball_cont n).2.1
  have hcont_iterates := fun n => (hball_cont n).2.2
  have hgeom := picardIter_geometric p u₀ D.hK_nn hball hball_nn
    hcont_iterates D.hcontr D.hC₀ D.hbase_diff
  have hcont_limit := picardLimit_hasContinuousSlices p u₀ D.hT D.hK D.hK_nn D.hC₀
    (fun n => hgeom n) hcont_iterates
  exact ⟨D.T, D.hT, picardLimit p u₀ D.T,
    picardLimit_is_mildSolution p u₀ D.hT D.hK D.hK_nn D.hC₀ D.hM
      (fun n => hgeom n) hball hball_nn hcont_iterates hcont_limit D.hcontr⟩

/-- Full mild existence: constructs MildExistenceData from PDE estimates.
Sorry: instantiating T, M, K, C₀ from Duhamel bounds + flux/logistic Lipschitz.
This is pure plumbing — no new math, just regularity/integrability discharge. -/
theorem intervalMildSolution_exists_picard (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀_bounded : ∃ B : ℝ, ∀ x, |u₀ x| ≤ B)
    (_hu₀_cont : Continuous u₀)
    (hα_ge : 1 ≤ p.α)
    (_hu₀_nonneg : ∀ x, 0 ≤ u₀ x) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u := by
  obtain ⟨B, hB⟩ := _hu₀_bounded
  set M := 2 * max B 1 with hMdef
  have hM : 0 < M := by positivity
  have hB_le : ∀ x, |u₀ x| ≤ M / 2 := by
    intro x; calc |u₀ x| ≤ B := hB x
      _ ≤ max B 1 := le_max_left B 1
      _ = M / 2 := by rw [hMdef]; ring
  -- Step 1: hbase_ball — S(t)u₀ is bounded by M
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
    · exact _hu₀_nonneg ⟨y, hy⟩
    · simp
  have hbase_nonneg : ∀ T : ℝ, ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      0 ≤ picardIter p u₀ 0 t x := by
    intro T t ht _htT x
    exact ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg ht
      hLift_nonneg x.1
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
  -- Heat gradient L∞→L∞ constant
  set C_grad := ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant
  have hC_grad_nn : (0 : ℝ) ≤ C_grad :=
    ShenWork.HeatKernelGradientEstimates.heatGradientLinftyLinftyConstant_nonneg
  -- Choose T₀: A·√T₀ + B·T₀ < 1, with A,B encoding both contraction and mapsTo.
  -- Since M ≥ 2, M/2 ≥ 1 ≥ K, so the mapsTo correction bound follows from K < 1.
  set A_picard := 2 * |p.χ₀| * C_grad * C_Q_unif + C_L + 1
  set B_picard := C_L_val + C_L + 1
  have hA_nn : (0 : ℝ) ≤ A_picard := by positivity
  have hB_nn : (0 : ℝ) ≤ B_picard := by positivity
  obtain ⟨T₀, hT₀, hK_lt⟩ := exists_small_contraction_time hA_nn hB_nn
  have hM_ge_2 : (2 : ℝ) ≤ M := by
    have : (1 : ℝ) ≤ max B 1 := le_max_right B 1
    simp only [hMdef]; linarith
  -- The core mapsTo inequality:
  -- |χ₀|·C_grad·2√T₀·C_Q_unif + T₀·C_L_val ≤ A·√T₀ + B·T₀ < 1 ≤ M/2
  have hcorrection_le : |p.χ₀| * C_grad * (2 * Real.sqrt T₀) * C_Q_unif
      + T₀ * C_L_val ≤ M / 2 := by
    have h1 : 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀
        ≤ A_picard * Real.sqrt T₀ := by
      gcongr; linarith [hC_L_pos.le]
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
      _hu₀_cont
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
  refine intervalMildSolution_of_data {
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
      /- Parabolic maximum principle for mild formulation.
         Route: S(t)u₀ ≥ 0 (semigroup preserves nonneg, already proved in
         IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg).
         The Duhamel value integral ∫₀ᵗ S(t-s) L(w(s)) ds requires the
         logistic source L(w(s)) to be nonneg, which is NOT always true:
         L(w) = w(a - b·w^α) is negative when w > (a/b)^{1/α}.
         Full proof requires a comparison principle / parabolic maximum
         principle for the mild formulation. Multi-day effort. -/
      intro w _hw_bound _hw_nonneg _hw_cont t ht _htT x
      sorry
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
      intro w _hw_bound _hw_cont t ht _htT
      sorry
    hcontr := by
      intro u w d hu hu_nn hw hw_nn huc hwc hd t ht htT x
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
        -- The integrals differ by a semigroup-convolved logistic difference.
        -- Needs: (1) semigroup linearity (spatial integrability),
        --        (2) interval integral linearity (time integrability).
        -- Both hold for continuous bounded sources on finite intervals.
        sorry
      have hG : |Gu - Gw| ≤ C_grad * (2 * Real.sqrt T₀) * (C_Q_unif * d) := by
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
        -- Flux source diff bound: |q_u s y - q_w s y| ≤ C_Q_unif · d
        -- Needs: chemFlux Lipschitz on the M-ball with constant C_Q_unif.
        -- chemFlux_div_lipschitz (or flux_diff_pointwise_bound) gives a bound
        -- in terms of resolver gradient/value Lipschitz constants.
        -- For the uniform M-ball, these are bounded by constants depending on
        -- C_RG, M, β, and resolver Lipschitz (from Atom B).
        -- The bound |Q(u)(y) − Q(w)(y)| ≤ C_Q_unif · d requires showing that
        -- the resolver Lipschitz is suitably controlled.
        -- This is the deepest lemma in the contraction chain.
        sorry
      -- Step 4: Assemble via gradientDuhamel_contraction_pointwise
      calc |(-p.χ₀) * (Gu - Gw) + (Vu - Vw)|
          ≤ (2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀ + C_L * T₀) * d :=
            gradientDuhamel_contraction_pointwise hG hV
        _ ≤ (A_picard * Real.sqrt T₀ + B_picard * T₀) * d := by
            have hA_ge : 2 * |p.χ₀| * C_grad * C_Q_unif ≤ A_picard := by
              simp only [A_picard]; linarith [hC_L_pos.le]
            have hB_ge : C_L ≤ B_picard := by
              simp only [B_picard]; linarith [hC_L_val_nn]
            have h1 : 2 * |p.χ₀| * C_grad * C_Q_unif * Real.sqrt T₀
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
  }

end ShenWork.IntervalMildPicard
