/-
  Phase-0 / M-gate-2: quantitative homogeneous smoothing bounds.

  For the restart series' homogeneous part `e^{−τλₙ}·a₀ₙ` with `|a₀ₙ| ≤ M`,
  the eigenvalue-weighted (G2) and √eigenvalue-weighted (G1) coefficient sums
  are bounded by `M` times the EXPLICIT (τ-dependent, datum-free) weights

    `eigExpWeight τ     := ∑'ₙ λₙ e^{−τλₙ}`
    `sqrtEigExpWeight τ := ∑'ₙ √λₙ e^{−τλₙ}`,

  which are finite for `τ > 0`.  Together with the Duhamel-part gains
  (IntervalDuhamelQuantGain: `C·τ^{1/4}·B` for G2, `C·B` for G1) and the
  explicit logistic source bound `B_log` (IntervalLogisticSourceQuantBound),
  these are the constants of the n-uniform iterate recursion (R2′ Phase-0,
  DESIGN_F2_CONSENSUS.md).

  No `sorry`/`admit`/custom `axiom`.
-/
import ShenWork.Paper2.IntervalMildRegularityBootstrap

noncomputable section

namespace ShenWork.IntervalHomogeneousQuantBound

open ShenWork.IntervalMildRegularityBootstrap

/-- Explicit homogeneous λ-weight `E₂(τ) = ∑'ₙ λₙ e^{−τλₙ}`. -/
def eigExpWeight (τ : ℝ) : ℝ :=
  ∑' n : ℕ, unitIntervalCosineEigenvalue n *
    Real.exp (-τ * unitIntervalCosineEigenvalue n)

/-- Explicit homogeneous √λ-weight `E₁(τ) = ∑'ₙ √λₙ e^{−τλₙ}`. -/
def sqrtEigExpWeight (τ : ℝ) : ℝ :=
  ∑' n : ℕ, Real.sqrt (unitIntervalCosineEigenvalue n) *
    Real.exp (-τ * unitIntervalCosineEigenvalue n)

/-- `√x ≤ max 1 x` for `x ≥ 0` (used with `x = λₙ`). -/
theorem sqrt_le_max_one (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x ≤ max 1 x := by
  rcases le_or_gt x 1 with h | h
  · calc Real.sqrt x ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
      _ = 1 := Real.sqrt_one
      _ ≤ max 1 _ := le_max_left _ _
  · have h1 : (1:ℝ) ≤ Real.sqrt x := by
      calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h.le
    calc Real.sqrt x = Real.sqrt x * 1 := (mul_one _).symm
      _ ≤ Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ = x := Real.mul_self_sqrt hx
      _ ≤ max 1 _ := le_max_right _ _

/-- The √λ-weight terms are summable for `τ > 0`. -/
theorem sqrtEig_mul_exp_summable {τ : ℝ} (hτ : 0 < τ) :
    Summable (fun n : ℕ =>
      Real.sqrt (unitIntervalCosineEigenvalue n) *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
  have h1 : Summable (fun n : ℕ =>
      Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
    have hc : (-(τ * Real.pi ^ 2) : ℝ) < 0 := neg_lt_zero.mpr (by positivity)
    have hbase : Summable (fun n : ℕ =>
        Real.exp (-(τ * Real.pi ^ 2) * (n : ℝ) ^ 2)) := by
      refine Real.summable_exp_nat_mul_of_ge hc
        (f := fun n : ℕ => (n : ℝ) ^ 2) (fun i => ?_)
      have hnat : i ≤ i ^ 2 := by nlinarith [Nat.zero_le i]
      calc (i : ℝ) = ((i : ℕ) : ℝ) := rfl
        _ ≤ ((i ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (i : ℝ) ^ 2 := by push_cast; ring
    refine hbase.congr fun n => ?_
    congr 1
    unfold unitIntervalCosineEigenvalue
    ring
  have hexp_sum : Summable (fun n : ℕ =>
      (1 + unitIntervalCosineEigenvalue n) *
        Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
    have h2 := unitIntervalCosineEigenvalue_mul_exp_summable hτ
    have := h1.add h2
    refine this.congr fun n => ?_
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hexp_sum
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
  · refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
    calc Real.sqrt (unitIntervalCosineEigenvalue n)
        ≤ max 1 (unitIntervalCosineEigenvalue n) :=
          sqrt_le_max_one _ (by unfold unitIntervalCosineEigenvalue; positivity)
      _ ≤ 1 + unitIntervalCosineEigenvalue n := by
          have : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
            unfold unitIntervalCosineEigenvalue; positivity
          rcases max_cases 1 (unitIntervalCosineEigenvalue n) with ⟨h, -⟩ | ⟨h, -⟩
            <;> rw [h] <;> linarith

/-- **G2 homogeneous bound**: `∑'ₙ λₙ·|e^{−τλₙ}·a₀ₙ| ≤ M · E₂(τ)`. -/
theorem homogeneous_eigenvalue_tsum_le {τ M : ℝ} (hτ : 0 < τ)
    {a₀ : ℕ → ℝ} (ha₀ : ∀ n, |a₀ n| ≤ M) :
    (∑' n : ℕ, unitIntervalCosineEigenvalue n *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
      ≤ M * eigExpWeight τ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hwt := unitIntervalCosineEigenvalue_mul_exp_summable hτ
  have hle : ∀ n : ℕ,
      unitIntervalCosineEigenvalue n *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        ≤ M * (unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
    intro n
    have hlam : (0:ℝ) ≤ unitIntervalCosineEigenvalue n := by
      unfold unitIntervalCosineEigenvalue; positivity
    have hexp : (0:ℝ) ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc unitIntervalCosineEigenvalue n *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        = unitIntervalCosineEigenvalue n *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|) := by
          rw [abs_mul, abs_of_nonneg hexp]
      _ ≤ unitIntervalCosineEigenvalue n *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (ha₀ n) hexp) hlam
      _ = M * (unitIntervalCosineEigenvalue n *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring
  calc (∑' n : ℕ, unitIntervalCosineEigenvalue n *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
      ≤ ∑' n : ℕ, M * (unitIntervalCosineEigenvalue n *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)) :=
        Summable.tsum_le_tsum hle
          (restartHomogeneousCoeff_eigenvalue_summable hτ ha₀)
          (hwt.mul_left M)
    _ = M * eigExpWeight τ := by
        simp only [eigExpWeight]
        exact tsum_mul_left

/-- **G1 homogeneous bound**: `∑'ₙ √λₙ·|e^{−τλₙ}·a₀ₙ| ≤ M · E₁(τ)`. -/
theorem homogeneous_sqrtEigenvalue_tsum_le {τ M : ℝ} (hτ : 0 < τ)
    {a₀ : ℕ → ℝ} (ha₀ : ∀ n, |a₀ n| ≤ M) :
    (∑' n : ℕ, Real.sqrt (unitIntervalCosineEigenvalue n) *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
      ≤ M * sqrtEigExpWeight τ := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (ha₀ 0)
  have hwt := sqrtEig_mul_exp_summable hτ
  have hsummand : Summable (fun n : ℕ =>
      Real.sqrt (unitIntervalCosineEigenvalue n) *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      (fun n => ?_) (hwt.mul_left M)
    have hexp : (0:ℝ) ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc Real.sqrt (unitIntervalCosineEigenvalue n) *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        = Real.sqrt (unitIntervalCosineEigenvalue n) *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|) := by
          rw [abs_mul, abs_of_nonneg hexp]
      _ ≤ Real.sqrt (unitIntervalCosineEigenvalue n) *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (ha₀ n) hexp) (Real.sqrt_nonneg _)
      _ = M * (Real.sqrt (unitIntervalCosineEigenvalue n) *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring
  have hle : ∀ n : ℕ,
      Real.sqrt (unitIntervalCosineEigenvalue n) *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        ≤ M * (Real.sqrt (unitIntervalCosineEigenvalue n) *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by
    intro n
    have hexp : (0:ℝ) ≤ Real.exp (-τ * unitIntervalCosineEigenvalue n) :=
      Real.exp_nonneg _
    calc Real.sqrt (unitIntervalCosineEigenvalue n) *
          |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|
        = Real.sqrt (unitIntervalCosineEigenvalue n) *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * |a₀ n|) := by
          rw [abs_mul, abs_of_nonneg hexp]
      _ ≤ Real.sqrt (unitIntervalCosineEigenvalue n) *
            (Real.exp (-τ * unitIntervalCosineEigenvalue n) * M) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (ha₀ n) hexp) (Real.sqrt_nonneg _)
      _ = M * (Real.sqrt (unitIntervalCosineEigenvalue n) *
            Real.exp (-τ * unitIntervalCosineEigenvalue n)) := by ring
  calc (∑' n : ℕ, Real.sqrt (unitIntervalCosineEigenvalue n) *
        |Real.exp (-τ * unitIntervalCosineEigenvalue n) * a₀ n|)
      ≤ ∑' n : ℕ, M * (Real.sqrt (unitIntervalCosineEigenvalue n) *
          Real.exp (-τ * unitIntervalCosineEigenvalue n)) :=
        Summable.tsum_le_tsum hle hsummand (hwt.mul_left M)
    _ = M * sqrtEigExpWeight τ := by
        simp only [sqrtEigExpWeight]
        exact tsum_mul_left

end ShenWork.IntervalHomogeneousQuantBound
