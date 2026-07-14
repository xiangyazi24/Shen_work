import ShenWork.Paper1.Theorem12RootObstruction

noncomputable section

namespace ShenWork.Paper1

/-!
# The explicit coefficient budgets in Paper 1 (5.20)--(5.33)

This file transcribes the scalar constants used by the exact mean-value
difference equation in Section 5.  The estimates applying these constants to
a Cauchy solution are kept separate from this algebraic layer.
-/

def paper5Sigma : ℝ := 1 / 6

/-- The `b₁` bound displayed in (5.20). -/
def paper520B1 (p : CMParams) (M : ℝ) : ℝ :=
  p.m * M ^ (p.m + p.γ - 1)

/-- The speed-independent first branch used in Remark 5.2. -/
def paper52MTriplePrimeLow (p : CMParams) : ℝ :=
  remark5ChiTwoSigma p paper5Sigma / 2 *
    (5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1) +
      Real.sqrt
        ((5 / 2 + |p.χ| * p.m * (MChi p) ^ (p.m + p.γ - 1)) ^ 2 +
          4 * |p.χ| * (MChi p) ^ (p.m + p.γ - 1) +
          4 * (MChi p) ^ p.α))

/-- The speed-independent second branch used in Remark 5.2. -/
def paper52MTriplePrimeHigh (p : CMParams) : ℝ :=
  max
    (8 * (1 + |p.χ| + 2 * p.m * |p.χ|) *
      (p.γ + remark5ChiSigma p paper5Sigma) / (1 + p.γ) *
        remark51MPrime p)
    (2 * remark51MDoublePrime p paper5Sigma)

/-- One nonnegative constant dominating both branches of `M'''`, uniformly
in the wave speed. -/
def paper52MTriplePrimeUniform (p : CMParams) : ℝ :=
  max 0 (max (paper52MTriplePrimeLow p) (paper52MTriplePrimeHigh p))

theorem paper52MTriplePrimeUniform_nonneg (p : CMParams) :
    0 ≤ paper52MTriplePrimeUniform p := by
  exact le_max_left _ _

theorem remark52MTriplePrime_le_uniform (p : CMParams) (c : ℝ) :
    remark52MTriplePrime p c paper5Sigma ≤
      paper52MTriplePrimeUniform p := by
  by_cases hc : c ≤ (5 / 2 : ℝ)
  · rw [remark52MTriplePrime_eq_of_le hc]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [remark52MTriplePrime_eq_of_gt (lt_of_not_ge hc)]
    exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The raw `m >= 2` contribution to the numerator in (5.24). -/
def paper524B2LargeM (p : CMParams) (M : ℝ) : ℝ :=
  p.m * (p.m - 1) * M ^ (p.m + p.γ - 1) *
    (|p.χ| * M ^ (p.m + p.γ) + M * (M ^ p.α - 1)) *
      remark5ChiSigma p paper5Sigma

/-- The `1 < m < 2` contribution to the numerator in (5.24). -/
def paper524B2IntermediateM (p : CMParams) (M : ℝ) : ℝ :=
  p.m * M ^ (p.m + p.γ - 1) * paper52MTriplePrimeUniform p

/-- A nonnegative common `b₂` budget for all three cases in (5.21)--(5.24).
The case split proving that it bounds the actual mean-value coefficient is a
PDE-layer theorem. -/
def paper524B2 (p : CMParams) (M : ℝ) : ℝ :=
  max 0 (max (paper524B2LargeM p M) (paper524B2IntermediateM p M))

theorem paper524B2_nonneg (p : CMParams) (M : ℝ) :
    0 ≤ paper524B2 p M := by
  exact le_max_left _ _

/-- The numerator `b₃` introduced in (5.25). -/
def paper525B3 (p : CMParams) (M : ℝ) : ℝ :=
  p.m * M ^ (p.m - 1) *
    (|p.χ| * M ^ (p.m + p.γ) + M ^ (1 + p.α))

theorem paper520B1_nonneg (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ paper520B1 p M := by
  unfold paper520B1
  exact mul_nonneg (le_trans zero_le_one p.hm) (Real.rpow_nonneg hM _)

theorem paper525B3_nonneg (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ paper525B3 p M := by
  unfold paper525B3
  have hm : 0 ≤ p.m := le_trans zero_le_one p.hm
  positivity

/-- The constant `D'` in (5.32), with `sigma = 1/6`. -/
def paper532DPrime (p : CMParams) (M : ℝ) : ℝ :=
  |p.χ| ^ (3 * paper5Sigma) * paper520B1 p M +
    paper525B3 p M / 2 *
      (|p.χ| ^ (2 * paper5Sigma) +
        p.γ ^ 2 * (1 + |p.χ| ^ paper5Sigma) ^ 2)

/-- The constant `D''` in (5.33), with `sigma = 1/6`. -/
def paper533DDoublePrime (p : CMParams) (M : ℝ) : ℝ :=
  1 / 2 * |p.χ| ^ (1 + paper5Sigma) * paper520B1 p M +
    |p.χ| ^ (3 * paper5Sigma) * (2 * p.m + p.γ) *
      M ^ (p.m + p.γ - 1) +
    |p.χ| ^ paper5Sigma * paper524B2 p M +
    |p.χ| ^ paper5Sigma / 2 * paper525B3 p M *
      (|p.χ| ^ paper5Sigma +
        p.γ ^ 2 * (1 + |p.χ| ^ paper5Sigma)) +
    1 / 2 * |p.χ| ^ (3 * paper5Sigma) * M ^ p.m *
      (|p.χ| ^ (2 * paper5Sigma) +
        p.γ ^ 2 * (1 + |p.χ| ^ paper5Sigma) ^ 2)

theorem paper532DPrime_nonneg (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ paper532DPrime p M := by
  unfold paper532DPrime
  have hb1 := paper520B1_nonneg p hM
  have hb3 := paper525B3_nonneg p hM
  positivity

theorem paper533DDoublePrime_nonneg
    (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ paper533DDoublePrime p M := by
  unfold paper533DDoublePrime
  have hb1 := paper520B1_nonneg p hM
  have hb2 := paper524B2_nonneg p M
  have hb3 := paper525B3_nonneg p hM
  have hm : 0 ≤ p.m := le_trans zero_le_one p.hm
  have hg : 0 ≤ p.γ := le_trans zero_le_one p.hγ
  positivity

/-- The two nonnegative corrections that enter (5.31). -/
def paper531A (p : CMParams) (M : ℝ) : ℝ :=
  |p.χ| ^ (1 - 3 * paper5Sigma) * paper532DPrime p M

def paper531B (p : CMParams) (M : ℝ) : ℝ :=
  |p.χ| ^ (1 - 3 * paper5Sigma) * paper533DDoublePrime p M

theorem paper531A_nonneg (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ paper531A p M := by
  unfold paper531A
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (paper532DPrime_nonneg p hM)

theorem paper531B_nonneg (p : CMParams) {M : ℝ} (hM : 0 ≤ M) :
    0 ≤ paper531B p M := by
  unfold paper531B
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    (paper533DDoublePrime_nonneg p hM)

section Theorem12Section5BudgetsAxiomAudit
#print axioms remark52MTriplePrime_le_uniform
#print axioms paper532DPrime_nonneg
#print axioms paper533DDoublePrime_nonneg
#print axioms paper531A_nonneg
#print axioms paper531B_nonneg
end Theorem12Section5BudgetsAxiomAudit

end ShenWork.Paper1
