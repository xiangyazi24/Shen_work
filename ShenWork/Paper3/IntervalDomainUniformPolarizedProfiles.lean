/- Uniform polarized physical-profile estimates on the strong positivity ball. -/
import ShenWork.Paper3.IntervalDomainUniformNemytskiiConstants
import ShenWork.Paper3.IntervalDomainL2ProductBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain

noncomputable section

/-- The elliptic Taylor remainder is locally Lipschitz with the polarized
strong factor, with a constant fixed by the equilibrium rather than the
individual profiles. -/
theorem paper3IntervalEllipticRemainderDifference_uniform_l2
    (p : CM2Params) {uStar M₁ M₂ D : ℝ} (huStar : 0 < uStar)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (u₁ u₂ : intervalDomainPoint → ℝ)
    (hu₁_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₁ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hu₂_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₂ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hdiff : MemLp (paper3IntervalPerturbationDifferenceProfile u₁ u₂) 2
      (intervalMeasure 1))
    (hrem_meas : AEStronglyMeasurable
      (paper3IntervalEllipticRemainderDifferenceProfile p uStar u₁ u₂)
      (intervalMeasure 1))
    (hphi₁_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₁ x| ≤ M₁)
    (hphi₂_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₂ x| ≤ M₂)
    (hdiff_l2 : intervalL2Size
      (paper3IntervalPerturbationDifferenceProfile u₁ u₂) ≤ D) :
    let K := paper3UniformEllipticPolarConstant p uStar huStar
    MemLp (paper3IntervalEllipticRemainderDifferenceProfile
      p uStar u₁ u₂) 2 (intervalMeasure 1) ∧
    intervalL2Size (paper3IntervalEllipticRemainderDifferenceProfile
      p uStar u₁ u₂) ≤ K * (M₁ + M₂) * D := by
  dsimp only
  let K := paper3UniformEllipticPolarConstant p uStar huStar
  have hK : 0 < K := by
    simpa [K] using paper3UniformEllipticPolarConstant_pos p uStar huStar
  let B := K * (M₁ + M₂)
  have hB : 0 ≤ B := mul_nonneg hK.le (add_nonneg hM₁ hM₂)
  have hpoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3IntervalEllipticRemainderDifferenceProfile
          p uStar u₁ u₂ x| ≤
        B * |paper3IntervalPerturbationDifferenceProfile u₁ u₂ x| := by
    intro x hx
    have hp := paper3UniformEllipticPolarConstant_bound
      p uStar huStar (intervalDomainLift u₁ x)
        (hu₁_near x (Set.Ioo_subset_Icc_self hx))
        (intervalDomainLift u₂ x)
        (hu₂_near x (Set.Ioo_subset_Icc_self hx))
    have h1 := hphi₁_sup x (Set.Ioo_subset_Icc_self hx)
    have h2 := hphi₂_sup x (Set.Ioo_subset_Icc_self hx)
    dsimp [paper3IntervalEllipticRemainderDifferenceProfile,
      paper3IntervalEllipticRemainderProfile,
      paper3IntervalPerturbationDifferenceProfile,
      paper3IntervalPerturbationProfile] at hp h1 h2 ⊢
    calc
      _ ≤ K * (|intervalDomainLift u₁ x - uStar| +
          |intervalDomainLift u₂ x - uStar|) *
            |intervalDomainLift u₁ x - intervalDomainLift u₂ x| := hp
      _ ≤ K * (M₁ + M₂) *
          |intervalDomainLift u₁ x - intervalDomainLift u₂ x| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK.le)
          (abs_nonneg _)
      _ = _ := by rfl
  have hmem := memLp_two_of_pointwise_mul_Ioo hB hrem_meas hdiff hpoint
  refine ⟨hmem, ?_⟩
  calc
    intervalL2Size (paper3IntervalEllipticRemainderDifferenceProfile
        p uStar u₁ u₂) ≤
      B * intervalL2Size
        (paper3IntervalPerturbationDifferenceProfile u₁ u₂) :=
          intervalL2Size_le_of_pointwise_mul hB hmem hdiff hpoint
    _ ≤ B * D := mul_le_mul_of_nonneg_left hdiff_l2 hB
    _ = K * (M₁ + M₂) * D := rfl

/-- Uniform polarized logistic remainder estimate, with the same positivity
interval threaded into the real-power Taylor bound. -/
theorem paper3IntervalLogisticRemainderDifference_uniform_l2
    (p : CM2Params) {uStar vStar M₁ M₂ D : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (u₁ u₂ : intervalDomainPoint → ℝ)
    (hu₁_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₁ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hu₂_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₂ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hdiff : MemLp (paper3IntervalPerturbationDifferenceProfile u₁ u₂) 2
      (intervalMeasure 1))
    (hrem_meas : AEStronglyMeasurable
      (paper3IntervalLogisticRemainderDifferenceProfile p uStar u₁ u₂)
      (intervalMeasure 1))
    (hphi₁_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₁ x| ≤ M₁)
    (hphi₂_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₂ x| ≤ M₂)
    (hdiff_l2 : intervalL2Size
      (paper3IntervalPerturbationDifferenceProfile u₁ u₂) ≤ D) :
    let K := paper3UniformLogisticPolarConstant p heq
    MemLp (paper3IntervalLogisticRemainderDifferenceProfile
      p uStar u₁ u₂) 2 (intervalMeasure 1) ∧
    intervalL2Size (paper3IntervalLogisticRemainderDifferenceProfile
      p uStar u₁ u₂) ≤ K * (M₁ + M₂) * D := by
  dsimp only
  let K := paper3UniformLogisticPolarConstant p heq
  have hK : 0 < K := by
    simpa [K] using paper3UniformLogisticPolarConstant_pos p heq
  let B := K * (M₁ + M₂)
  have hB : 0 ≤ B := mul_nonneg hK.le (add_nonneg hM₁ hM₂)
  have hpoint : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      |paper3IntervalLogisticRemainderDifferenceProfile
          p uStar u₁ u₂ x| ≤
        B * |paper3IntervalPerturbationDifferenceProfile u₁ u₂ x| := by
    intro x hx
    have hp := paper3UniformLogisticPolarConstant_bound
      p heq (intervalDomainLift u₁ x)
        (hu₁_near x (Set.Ioo_subset_Icc_self hx))
        (intervalDomainLift u₂ x)
        (hu₂_near x (Set.Ioo_subset_Icc_self hx))
    have h1 := hphi₁_sup x (Set.Ioo_subset_Icc_self hx)
    have h2 := hphi₂_sup x (Set.Ioo_subset_Icc_self hx)
    dsimp [paper3IntervalLogisticRemainderDifferenceProfile,
      paper3IntervalLogisticRemainderProfile,
      paper3IntervalPerturbationDifferenceProfile,
      paper3IntervalPerturbationProfile] at hp h1 h2 ⊢
    calc
      _ ≤ K * (|intervalDomainLift u₁ x - uStar| +
          |intervalDomainLift u₂ x - uStar|) *
            |intervalDomainLift u₁ x - intervalDomainLift u₂ x| := hp
      _ ≤ K * (M₁ + M₂) *
          |intervalDomainLift u₁ x - intervalDomainLift u₂ x| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK.le)
          (abs_nonneg _)
      _ = _ := by rfl
  have hmem := memLp_two_of_pointwise_mul_Ioo hB hrem_meas hdiff hpoint
  refine ⟨hmem, ?_⟩
  calc
    intervalL2Size (paper3IntervalLogisticRemainderDifferenceProfile
        p uStar u₁ u₂) ≤
      B * intervalL2Size
        (paper3IntervalPerturbationDifferenceProfile u₁ u₂) :=
          intervalL2Size_le_of_pointwise_mul hB hmem hdiff hpoint
    _ ≤ B * D := mul_le_mul_of_nonneg_left hdiff_l2 hB
    _ = K * (M₁ + M₂) * D := rfl

#print axioms paper3IntervalEllipticRemainderDifference_uniform_l2
#print axioms paper3IntervalLogisticRemainderDifference_uniform_l2

end

end ShenWork.Paper3
