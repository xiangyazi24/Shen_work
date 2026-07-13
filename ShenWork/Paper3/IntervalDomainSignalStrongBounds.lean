/- Strong-ball value, gradient, and elliptic-laplacian signal bounds. -/
import ShenWork.Paper3.IntervalDomainSignalComponentBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain

noncomputable section

def paper3LinearSignalLaplacian
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  p.μ * paper3LinearSignalValue p uStar u x -
    paper3IntervalEllipticLinearProfile p uStar u x

def paper3QuadraticSignalLaplacian
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  p.μ * paper3QuadraticSignalValue p uStar u x -
    paper3IntervalEllipticRemainderProfile p uStar u x

/-- The elliptic gain in the exact strong scaling: the linear signal is
`O(M)` through two derivatives and the nonlinear signal correction is
`O(M²)`.  The laplacian fields are the elliptic-identity representatives;
positive-time classical regularity identifies them with the actual spatial
derivatives. -/
theorem paper3SignalComponents_strong_bounds
    (p : CM2Params) {uStar M : ℝ} (huStar : 0 < uStar) (hM : 0 ≤ M)
    (u : intervalDomainPoint → ℝ)
    (hu_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hphi : MemLp (paper3IntervalPerturbationProfile uStar u) 2
      (intervalMeasure 1))
    (hlin_meas : AEStronglyMeasurable
      (paper3IntervalEllipticLinearProfile p uStar u)
      (intervalMeasure 1))
    (hrem_meas : AEStronglyMeasurable
      (paper3IntervalEllipticRemainderProfile p uStar u)
      (intervalMeasure 1))
    (hphi_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u x| ≤ M)
    (hphi_l2 : Real.sqrt (∫ y in (0 : ℝ)..1,
      (paper3IntervalPerturbationProfile uStar u y) ^ 2) ≤ M) :
    ∃ C > 0, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar u x| ≤ C * M ∧
      |paper3LinearSignalGradient p uStar u x| ≤ C * M ∧
      |paper3LinearSignalLaplacian p uStar u x| ≤ C * M ∧
      |paper3QuadraticSignalValue p uStar u x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar u x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar u x| ≤ C * M ^ 2 := by
  rcases paper3SignalComponents_pointwise_bounds p huStar hM u hu_near
      hphi hlin_meas hrem_meas hphi_sup with ⟨K, hK, hsignal⟩
  rcases paper3EllipticSource_quadratic_remainder p huStar with
    ⟨Kr, hKr, hsourceRem⟩
  let A0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
      (2 * |p.ν * paper3PowerDeriv p.γ uStar|)
  let A1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
      (2 * |p.ν * paper3PowerDeriv p.γ uStar|)
  let B0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * K)
  let B1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * K)
  let D := |p.ν * paper3PowerDeriv p.γ uStar|
  let C := 1 + A0 + A1 + (p.μ * A0 + D) + B0 + B1 +
    (p.μ * B0 + Kr)
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hD : 0 ≤ D := abs_nonneg _
  have hC : 0 < C := by
    dsimp [C]
    have hmu := p.hμ.le
    linarith [mul_nonneg hmu hA0, mul_nonneg hmu hB0, hKr.le]
  refine ⟨C, hC, ?_⟩
  intro x hx
  rcases hsignal x with ⟨hz1, hz1x, hz2, hz2x⟩
  have hz1' : |paper3LinearSignalValue p uStar u x| ≤ A0 * M := by
    calc
      _ ≤ A0 * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        simpa [A0, mul_assoc] using hz1
      _ ≤ A0 * M := mul_le_mul_of_nonneg_left hphi_l2 hA0
  have hz1x' : |paper3LinearSignalGradient p uStar u x| ≤ A1 * M := by
    calc
      _ ≤ A1 * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        simpa [A1, mul_assoc] using hz1x
      _ ≤ A1 * M := mul_le_mul_of_nonneg_left hphi_l2 hA1
  have hz2' : |paper3QuadraticSignalValue p uStar u x| ≤ B0 * M ^ 2 := by
    calc
      _ ≤ B0 * M * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        simpa [B0, mul_assoc] using hz2
      _ ≤ B0 * M * M :=
        mul_le_mul_of_nonneg_left hphi_l2 (mul_nonneg hB0 hM)
      _ = B0 * M ^ 2 := by ring
  have hz2x' : |paper3QuadraticSignalGradient p uStar u x| ≤ B1 * M ^ 2 := by
    calc
      _ ≤ B1 * M * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        simpa [B1, mul_assoc] using hz2x
      _ ≤ B1 * M * M :=
        mul_le_mul_of_nonneg_left hphi_l2 (mul_nonneg hB1 hM)
      _ = B1 * M ^ 2 := by ring
  have hlinSource : |paper3IntervalEllipticLinearProfile p uStar u x| ≤
      D * M := by
    dsimp [paper3IntervalEllipticLinearProfile,
      paper3IntervalPerturbationProfile, D]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hphi_sup x hx) (abs_nonneg _)
  have hremSource : |paper3IntervalEllipticRemainderProfile p uStar u x| ≤
      Kr * M ^ 2 := by
    have hr := hsourceRem (intervalDomainLift u x) (hu_near x hx)
    have hs := hphi_sup x hx
    dsimp [paper3IntervalEllipticRemainderProfile,
      paper3IntervalPerturbationProfile] at hr hs ⊢
    calc
      _ ≤ Kr * |intervalDomainLift u x - uStar| ^ 2 := hr
      _ ≤ Kr * M ^ 2 := by
        gcongr
  have hz1xx : |paper3LinearSignalLaplacian p uStar u x| ≤
      (p.μ * A0 + D) * M := by
    unfold paper3LinearSignalLaplacian
    calc
      _ ≤ |p.μ * paper3LinearSignalValue p uStar u x| +
          |paper3IntervalEllipticLinearProfile p uStar u x| := abs_sub _ _
      _ ≤ p.μ * (A0 * M) + D * M := by
        rw [abs_mul, abs_of_pos p.hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hz1' p.hμ.le) hlinSource
      _ = _ := by ring
  have hz2xx : |paper3QuadraticSignalLaplacian p uStar u x| ≤
      (p.μ * B0 + Kr) * M ^ 2 := by
    unfold paper3QuadraticSignalLaplacian
    calc
      _ ≤ |p.μ * paper3QuadraticSignalValue p uStar u x| +
          |paper3IntervalEllipticRemainderProfile p uStar u x| := abs_sub _ _
      _ ≤ p.μ * (B0 * M ^ 2) + Kr * M ^ 2 := by
        rw [abs_mul, abs_of_pos p.hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hz2' p.hμ.le) hremSource
      _ = _ := by ring
  have hmuA0 : 0 ≤ p.μ * A0 := mul_nonneg p.hμ.le hA0
  have hmuB0 : 0 ≤ p.μ * B0 := mul_nonneg p.hμ.le hB0
  have hA0C : A0 ≤ C := by
    dsimp [C]
    linarith [hA1, hmuA0, hD, hB0, hB1, hmuB0, hKr.le]
  have hA1C : A1 ≤ C := by
    dsimp [C]
    linarith [hA0, hmuA0, hD, hB0, hB1, hmuB0, hKr.le]
  have hA2C : p.μ * A0 + D ≤ C := by
    dsimp [C]
    linarith [hA0, hA1, hB0, hB1, hmuB0, hKr.le]
  have hB0C : B0 ≤ C := by
    dsimp [C]
    linarith [hA0, hA1, hmuA0, hD, hB1, hmuB0, hKr.le]
  have hB1C : B1 ≤ C := by
    dsimp [C]
    linarith [hA0, hA1, hmuA0, hD, hB0, hmuB0, hKr.le]
  have hB2C : p.μ * B0 + Kr ≤ C := by
    dsimp [C]
    linarith [hA0, hA1, hmuA0, hD, hB0, hB1]
  refine ⟨hz1'.trans (mul_le_mul_of_nonneg_right hA0C hM),
    hz1x'.trans (mul_le_mul_of_nonneg_right hA1C hM),
    hz1xx.trans (mul_le_mul_of_nonneg_right hA2C hM),
    hz2'.trans (mul_le_mul_of_nonneg_right hB0C (sq_nonneg M)),
    hz2x'.trans (mul_le_mul_of_nonneg_right hB1C (sq_nonneg M)),
    hz2xx.trans (mul_le_mul_of_nonneg_right hB2C (sq_nonneg M))⟩

#print axioms paper3SignalComponents_strong_bounds

end

end ShenWork.Paper3
