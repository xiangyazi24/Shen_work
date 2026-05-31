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
  sorry

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

/-- **Key theorem:** The limit of the Picard iteration satisfies the
mild solution equation u = Φ(u₀, u).

Proof idea: at each (t,x),
  |Φ(u₀,u)(t,x) − u(t,x)|
    = lim |Φ(u₀,u)(t,x) − u_{n+1}(t,x)|     [u_{n+1} → u]
    = lim |Φ(u₀,u)(t,x) − Φ(u₀,u_n)(t,x)|   [by def of u_{n+1}]
    ≤ lim K · sup|u − u_n|                     [contraction]
    → 0                                          [uniform convergence]
-/
theorem picardLimit_is_mildSolution (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    {T K C₀ M : ℝ} (hT : 0 < T) (hK : K < 1) (hK_nn : 0 ≤ K) (hC₀ : 0 ≤ C₀)
    (_hM : 0 < M)
    (hbound : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ (n + 1) t x - picardIter p u₀ n t x| ≤ K ^ n * C₀)
    (hball : ∀ (n : ℕ) (t : ℝ), 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
      |picardIter p u₀ n t x| ≤ M)
    (hcontract_any : ∀ (u w : ℝ → intervalDomainPoint → ℝ),
      (∀ t, 0 < t → t ≤ T → ∀ x, |u t x| ≤ M) →
      (∀ t, 0 < t → t ≤ T → ∀ x, |w t x| ≤ M) →
      ∀ t, 0 < t → t ≤ T → ∀ x : intervalDomainPoint,
        ∃ d : ℝ, (∀ s, 0 < s → s ≤ T → ∀ y, |u s y - w s y| ≤ d) ∧
          |intervalGradientDuhamelMap p u₀ u t x
            - intervalGradientDuhamelMap p u₀ w t x| ≤ K * d) :
    IntervalMildSolution p T u₀ (picardLimit p u₀ T) := by
  intro t ht htT x
  -- u(t,x) = picardLimit p u₀ T t x = lim u_n(t,x)
  -- Φ(u₀,u)(t,x) = intervalGradientDuhamelMap p u₀ (picardLimit p u₀ T) t x
  -- Need: these are equal
  -- Strategy: show |Φ(u₀,u)(t,x) - u(t,x)| < ε for all ε > 0
  unfold picardLimit
  simp only [ht, htT, and_self, ite_true]
  sorry

/-! ## Main existence theorem -/

/-- **T7 mild existence via Picard iteration.**

For any CM2 parameters and bounded initial datum, there exists T > 0
and a trajectory satisfying the weak Duhamel equation on (0,T].
-/
theorem intervalMildSolution_exists_picard (p : CM2Params)
    (u₀ : intervalDomainPoint → ℝ)
    (_hu₀_bounded : ∃ B : ℝ, ∀ x, |u₀ x| ≤ B) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → intervalDomainPoint → ℝ,
      IntervalMildSolution p T u₀ u := by
  sorry

end ShenWork.IntervalMildPicard
