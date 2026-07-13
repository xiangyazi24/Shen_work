/- Uniform polarized value/gradient/laplacian bounds for the eliminated signal. -/
import ShenWork.Paper3.IntervalDomainUniformPolarizedProfiles
import ShenWork.Paper3.IntervalDomainSignalStrongBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- Fixed resolver constant for linear and quadratic signal differences. -/
def paper3UniformSignalDifferenceConstant
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) : ℝ :=
  let K := paper3UniformEllipticPolarConstant p uStar huStar
  let Dlin := |p.ν * paper3PowerDeriv p.γ uStar|
  let A0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * Dlin)
  let A1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * Dlin)
  let B0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * K)
  let B1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * K)
  1 + A0 + A1 + (p.μ * A0 + Dlin) +
    B0 + B1 + (p.μ * B0 + K)

theorem paper3UniformSignalDifferenceConstant_pos
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) :
    0 < paper3UniformSignalDifferenceConstant p uStar huStar := by
  let K := paper3UniformEllipticPolarConstant p uStar huStar
  let Dlin := |p.ν * paper3PowerDeriv p.γ uStar|
  let A0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * Dlin)
  let A1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * Dlin)
  let B0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * K)
  let B1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * K)
  have hK : 0 < K := by
    simpa [K] using paper3UniformEllipticPolarConstant_pos p uStar huStar
  have hDlin : 0 ≤ Dlin := by dsimp [Dlin]; positivity
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  unfold paper3UniformSignalDifferenceConstant
  dsimp only
  linarith [mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0, hK.le]

/-- Polarized resolver estimate.  Linear components cost one difference
factor; quadratic components cost `(M1+M2)` times that difference. -/
theorem paper3SignalComponents_strong_difference_bounds_uniform
    (p : CM2Params) {uStar M₁ M₂ D : ℝ} (huStar : 0 < uStar)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hD : 0 ≤ D)
    (u₁ u₂ : intervalDomainPoint → ℝ)
    (hu₁_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₁ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hu₂_near : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      intervalDomainLift u₂ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2))
    (hdiff : MemLp (paper3IntervalPerturbationDifferenceProfile u₁ u₂) 2
      (intervalMeasure 1))
    (hlin₁ : MemLp (paper3IntervalEllipticLinearProfile p uStar u₁) 2
      (intervalMeasure 1))
    (hlin₂ : MemLp (paper3IntervalEllipticLinearProfile p uStar u₂) 2
      (intervalMeasure 1))
    (hquad₁ : MemLp (paper3IntervalEllipticRemainderProfile p uStar u₁) 2
      (intervalMeasure 1))
    (hquad₂ : MemLp (paper3IntervalEllipticRemainderProfile p uStar u₂) 2
      (intervalMeasure 1))
    (hlin₁Int : IntervalIntegrable
      (paper3IntervalEllipticLinearProfile p uStar u₁) volume 0 1)
    (hlin₂Int : IntervalIntegrable
      (paper3IntervalEllipticLinearProfile p uStar u₂) volume 0 1)
    (hquad₁Int : IntervalIntegrable
      (paper3IntervalEllipticRemainderProfile p uStar u₁) volume 0 1)
    (hquad₂Int : IntervalIntegrable
      (paper3IntervalEllipticRemainderProfile p uStar u₂) volume 0 1)
    (hphi₁_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₁ x| ≤ M₁)
    (hphi₂_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationProfile uStar u₂ x| ≤ M₂)
    (hdiff_sup : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalPerturbationDifferenceProfile u₁ u₂ x| ≤ D)
    (hdiff_l2 : intervalL2Size
      (paper3IntervalPerturbationDifferenceProfile u₁ u₂) ≤ D) :
    let C := paper3UniformSignalDifferenceConstant p uStar huStar
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar u₁ x -
          paper3LinearSignalValue p uStar u₂ x| ≤ C * D ∧
      |paper3LinearSignalGradient p uStar u₁ x -
          paper3LinearSignalGradient p uStar u₂ x| ≤ C * D ∧
      |paper3LinearSignalLaplacian p uStar u₁ x -
          paper3LinearSignalLaplacian p uStar u₂ x| ≤ C * D ∧
      |paper3QuadraticSignalValue p uStar u₁ x -
          paper3QuadraticSignalValue p uStar u₂ x| ≤ C * (M₁ + M₂) * D ∧
      |paper3QuadraticSignalGradient p uStar u₁ x -
          paper3QuadraticSignalGradient p uStar u₂ x| ≤ C * (M₁ + M₂) * D ∧
      |paper3QuadraticSignalLaplacian p uStar u₁ x -
          paper3QuadraticSignalLaplacian p uStar u₂ x| ≤
            C * (M₁ + M₂) * D := by
  dsimp only
  let K := paper3UniformEllipticPolarConstant p uStar huStar
  let Dlin := |p.ν * paper3PowerDeriv p.γ uStar|
  let A0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * Dlin)
  let A1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * Dlin)
  let B0 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 * K)
  let B1 := Real.sqrt (∑' k : ℕ,
    (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 * K)
  let C := paper3UniformSignalDifferenceConstant p uStar huStar
  have hK : 0 < K := by
    simpa [K] using paper3UniformEllipticPolarConstant_pos p uStar huStar
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hDlin : 0 ≤ Dlin := by dsimp [Dlin]; positivity
  have hC : 0 < C := by
    simpa [C] using paper3UniformSignalDifferenceConstant_pos p uStar huStar
  have hlinDiffMeas : AEStronglyMeasurable
      (fun x => paper3IntervalEllipticLinearProfile p uStar u₁ x -
        paper3IntervalEllipticLinearProfile p uStar u₂ x)
      (intervalMeasure 1) := hlin₁.1.sub hlin₂.1
  have hlinPoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalEllipticLinearProfile p uStar u₁ x -
          paper3IntervalEllipticLinearProfile p uStar u₂ x| ≤
        Dlin * |paper3IntervalPerturbationDifferenceProfile u₁ u₂ x| := by
    intro x _hx
    dsimp [paper3IntervalEllipticLinearProfile,
      paper3IntervalPerturbationProfile,
      paper3IntervalPerturbationDifferenceProfile, Dlin]
    apply le_of_eq
    rw [← mul_sub, abs_mul]
    congr 2
    ring
  have hlinDiffCoeff := cosineCoeffs_l2_norm_le_of_pointwise_mul
    hDlin hdiff hlinDiffMeas hlinPoint
  have hquadDiffMeas : AEStronglyMeasurable
      (paper3IntervalEllipticRemainderDifferenceProfile p uStar u₁ u₂)
      (intervalMeasure 1) := hquad₁.1.sub hquad₂.1
  have hquadDiff := paper3IntervalEllipticRemainderDifference_uniform_l2
    p huStar hM₁ hM₂ u₁ u₂ hu₁_near hu₂_near hdiff hquadDiffMeas
      hphi₁_sup hphi₂_sup hdiff_l2
  have hquadDiffCoeff :=
    ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hquadDiff.1
  have hquadRoot : Real.sqrt (∑' k : ℕ,
      (cosineCoeffs
        (paper3IntervalEllipticRemainderDifferenceProfile
          p uStar u₁ u₂) k) ^ 2) ≤
      2 * K * (M₁ + M₂) * D := by
    calc
      _ ≤ 2 * intervalL2Size
          (paper3IntervalEllipticRemainderDifferenceProfile
            p uStar u₁ u₂) := hquadDiffCoeff.2
      _ ≤ 2 * (K * (M₁ + M₂) * D) :=
        mul_le_mul_of_nonneg_left hquadDiff.2 (by norm_num)
      _ = _ := by ring
  have hlin₁Coeff := ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hlin₁
  have hlin₂Coeff := ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hlin₂
  have hquad₁Coeff := ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hquad₁
  have hquad₂Coeff := ShenWork.IntervalNHGBrickB.cosineCoeffs_l2_of_memLp hquad₂
  have hlinCoeffEq : ∀ k,
      cosineCoeffs
          (fun y => paper3IntervalEllipticLinearProfile p uStar u₁ y -
            paper3IntervalEllipticLinearProfile p uStar u₂ y) k =
        paper3LinearEllipticSourceCoeffReal p uStar u₁ k -
          paper3LinearEllipticSourceCoeffReal p uStar u₂ k := by
    intro k
    simpa [paper3LinearEllipticSourceCoeffReal] using
      cosineCoeffs_sub_of_intervalIntegrable k hlin₁Int hlin₂Int
  have hquadCoeffEq : ∀ k,
      cosineCoeffs
          (paper3IntervalEllipticRemainderDifferenceProfile
            p uStar u₁ u₂) k =
        paper3QuadraticEllipticSourceCoeffReal p uStar u₁ k -
          paper3QuadraticEllipticSourceCoeffReal p uStar u₂ k := by
    intro k
    simpa [paper3IntervalEllipticRemainderDifferenceProfile,
      paper3QuadraticEllipticSourceCoeffReal] using
      cosineCoeffs_sub_of_intervalIntegrable k hquad₁Int hquad₂Int
  have hlinValueEq : ∀ x,
      paper3LinearSignalValue p uStar u₁ x -
          paper3LinearSignalValue p uStar u₂ x =
        paper3ResolvedSourceValue p
          (cosineCoeffs (fun y =>
            paper3IntervalEllipticLinearProfile p uStar u₁ y -
              paper3IntervalEllipticLinearProfile p uStar u₂ y)) x := by
    intro x
    unfold paper3LinearSignalValue paper3LinearEllipticSourceCoeffReal
    rw [← paper3ResolvedSourceValue_sub p hlin₁Coeff.1 hlin₂Coeff.1]
    congr 1
    funext k
    exact (hlinCoeffEq k).symm
  have hlinGradEq : ∀ x,
      paper3LinearSignalGradient p uStar u₁ x -
          paper3LinearSignalGradient p uStar u₂ x =
        paper3ResolvedSourceGradient p
          (cosineCoeffs (fun y =>
            paper3IntervalEllipticLinearProfile p uStar u₁ y -
              paper3IntervalEllipticLinearProfile p uStar u₂ y)) x := by
    intro x
    unfold paper3LinearSignalGradient paper3LinearEllipticSourceCoeffReal
    rw [← paper3ResolvedSourceGradient_sub p hlin₁Coeff.1 hlin₂Coeff.1]
    congr 1
    funext k
    exact (hlinCoeffEq k).symm
  have hquadValueEq : ∀ x,
      paper3QuadraticSignalValue p uStar u₁ x -
          paper3QuadraticSignalValue p uStar u₂ x =
        paper3ResolvedSourceValue p
          (cosineCoeffs
            (paper3IntervalEllipticRemainderDifferenceProfile
              p uStar u₁ u₂)) x := by
    intro x
    unfold paper3QuadraticSignalValue paper3QuadraticEllipticSourceCoeffReal
    rw [← paper3ResolvedSourceValue_sub p hquad₁Coeff.1 hquad₂Coeff.1]
    congr 1
    funext k
    exact (hquadCoeffEq k).symm
  have hquadGradEq : ∀ x,
      paper3QuadraticSignalGradient p uStar u₁ x -
          paper3QuadraticSignalGradient p uStar u₂ x =
        paper3ResolvedSourceGradient p
          (cosineCoeffs
            (paper3IntervalEllipticRemainderDifferenceProfile
              p uStar u₁ u₂)) x := by
    intro x
    unfold paper3QuadraticSignalGradient paper3QuadraticEllipticSourceCoeffReal
    rw [← paper3ResolvedSourceGradient_sub p hquad₁Coeff.1 hquad₂Coeff.1]
    congr 1
    funext k
    exact (hquadCoeffEq k).symm
  have hA0C : A0 ≤ C := by
    dsimp [C, paper3UniformSignalDifferenceConstant]
    linarith [hA1, hB0, hB1, hDlin,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0, hK.le]
  have hA1C : A1 ≤ C := by
    dsimp [C, paper3UniformSignalDifferenceConstant]
    linarith [hA0, hB0, hB1, hDlin,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0, hK.le]
  have hA2C : p.μ * A0 + Dlin ≤ C := by
    dsimp [C, paper3UniformSignalDifferenceConstant]
    linarith [hA0, hA1, hB0, hB1,
      mul_nonneg p.hμ.le hB0, hK.le]
  have hB0C : B0 ≤ C := by
    dsimp [C, paper3UniformSignalDifferenceConstant]
    linarith [hA0, hA1, hB1, hDlin,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0, hK.le]
  have hB1C : B1 ≤ C := by
    dsimp [C, paper3UniformSignalDifferenceConstant]
    linarith [hA0, hA1, hB0, hDlin,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0, hK.le]
  have hB2C : p.μ * B0 + K ≤ C := by
    dsimp [C, paper3UniformSignalDifferenceConstant]
    linarith [hA0, hA1, hB0, hB1, hDlin,
      mul_nonneg p.hμ.le hA0]
  intro x hx
  have hz1 : |paper3LinearSignalValue p uStar u₁ x -
      paper3LinearSignalValue p uStar u₂ x| ≤ A0 * D := by
    rw [hlinValueEq]
    calc
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          Real.sqrt (∑' k : ℕ,
            (cosineCoeffs (fun y =>
              paper3IntervalEllipticLinearProfile p uStar u₁ y -
                paper3IntervalEllipticLinearProfile p uStar u₂ y) k) ^ 2) :=
        paper3ResolvedSourceValue_abs_le p hlinDiffCoeff.1 x
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * Dlin * D) :=
        mul_le_mul_of_nonneg_left
          (hlinDiffCoeff.2.trans
            (mul_le_mul_of_nonneg_left hdiff_l2
              (mul_nonneg (by norm_num) hDlin))) (Real.sqrt_nonneg _)
      _ = A0 * D := by dsimp [A0]; ring
  have hz1x : |paper3LinearSignalGradient p uStar u₁ x -
      paper3LinearSignalGradient p uStar u₂ x| ≤ A1 * D := by
    rw [hlinGradEq]
    calc
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          Real.sqrt (∑' k : ℕ,
            (cosineCoeffs (fun y =>
              paper3IntervalEllipticLinearProfile p uStar u₁ y -
                paper3IntervalEllipticLinearProfile p uStar u₂ y) k) ^ 2) :=
        paper3ResolvedSourceGradient_abs_le p hlinDiffCoeff.1 x
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * Dlin * D) :=
        mul_le_mul_of_nonneg_left
          (hlinDiffCoeff.2.trans
            (mul_le_mul_of_nonneg_left hdiff_l2
              (mul_nonneg (by norm_num) hDlin))) (Real.sqrt_nonneg _)
      _ = A1 * D := by dsimp [A1]; ring
  have hz2 : |paper3QuadraticSignalValue p uStar u₁ x -
      paper3QuadraticSignalValue p uStar u₂ x| ≤ B0 * (M₁ + M₂) * D := by
    rw [hquadValueEq]
    calc
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          Real.sqrt (∑' k : ℕ,
            (cosineCoeffs
              (paper3IntervalEllipticRemainderDifferenceProfile
                p uStar u₁ u₂) k) ^ 2) :=
        paper3ResolvedSourceValue_abs_le p hquadDiffCoeff.1 x
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * K * (M₁ + M₂) * D) :=
        mul_le_mul_of_nonneg_left hquadRoot (Real.sqrt_nonneg _)
      _ = B0 * (M₁ + M₂) * D := by dsimp [B0]; ring
  have hz2x : |paper3QuadraticSignalGradient p uStar u₁ x -
      paper3QuadraticSignalGradient p uStar u₂ x| ≤
      B1 * (M₁ + M₂) * D := by
    rw [hquadGradEq]
    calc
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          Real.sqrt (∑' k : ℕ,
            (cosineCoeffs
              (paper3IntervalEllipticRemainderDifferenceProfile
                p uStar u₁ u₂) k) ^ 2) :=
        paper3ResolvedSourceGradient_abs_le p hquadDiffCoeff.1 x
      _ ≤ Real.sqrt (∑' k : ℕ,
          (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * K * (M₁ + M₂) * D) :=
        mul_le_mul_of_nonneg_left hquadRoot (Real.sqrt_nonneg _)
      _ = B1 * (M₁ + M₂) * D := by dsimp [B1]; ring
  have hlinSource : |paper3IntervalEllipticLinearProfile p uStar u₁ x -
      paper3IntervalEllipticLinearProfile p uStar u₂ x| ≤ Dlin * D :=
    (hlinPoint x hx).trans (mul_le_mul_of_nonneg_left (hdiff_sup x hx) hDlin)
  have hquadSource :
      |paper3IntervalEllipticRemainderProfile p uStar u₁ x -
        paper3IntervalEllipticRemainderProfile p uStar u₂ x| ≤
          K * (M₁ + M₂) * D := by
    have hp := paper3UniformEllipticPolarConstant_bound
      p uStar huStar (intervalDomainLift u₁ x) (hu₁_near x hx)
        (intervalDomainLift u₂ x) (hu₂_near x hx)
    have h1 := hphi₁_sup x hx
    have h2 := hphi₂_sup x hx
    have hd := hdiff_sup x hx
    dsimp [paper3IntervalEllipticRemainderProfile,
      paper3IntervalPerturbationProfile,
      paper3IntervalPerturbationDifferenceProfile] at hp h1 h2 hd ⊢
    calc
      _ ≤ K * (|intervalDomainLift u₁ x - uStar| +
          |intervalDomainLift u₂ x - uStar|) *
            |intervalDomainLift u₁ x - intervalDomainLift u₂ x| := hp
      _ ≤ K * (M₁ + M₂) * D :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK.le) hd
          (abs_nonneg _) (mul_nonneg hK.le (add_nonneg hM₁ hM₂))
  have hz1xx : |paper3LinearSignalLaplacian p uStar u₁ x -
      paper3LinearSignalLaplacian p uStar u₂ x| ≤
        (p.μ * A0 + Dlin) * D := by
    unfold paper3LinearSignalLaplacian
    calc
      _ ≤ |p.μ * (paper3LinearSignalValue p uStar u₁ x -
            paper3LinearSignalValue p uStar u₂ x)| +
          |paper3IntervalEllipticLinearProfile p uStar u₁ x -
            paper3IntervalEllipticLinearProfile p uStar u₂ x| := by
        rw [show
          (p.μ * paper3LinearSignalValue p uStar u₁ x -
              paper3IntervalEllipticLinearProfile p uStar u₁ x) -
            (p.μ * paper3LinearSignalValue p uStar u₂ x -
              paper3IntervalEllipticLinearProfile p uStar u₂ x) =
            p.μ * (paper3LinearSignalValue p uStar u₁ x -
              paper3LinearSignalValue p uStar u₂ x) -
            (paper3IntervalEllipticLinearProfile p uStar u₁ x -
              paper3IntervalEllipticLinearProfile p uStar u₂ x) by ring]
        exact abs_sub
          (p.μ * (paper3LinearSignalValue p uStar u₁ x -
            paper3LinearSignalValue p uStar u₂ x))
          (paper3IntervalEllipticLinearProfile p uStar u₁ x -
            paper3IntervalEllipticLinearProfile p uStar u₂ x)
      _ ≤ p.μ * (A0 * D) + Dlin * D := by
        rw [abs_mul, abs_of_pos p.hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hz1 p.hμ.le) hlinSource
      _ = _ := by ring
  have hz2xx : |paper3QuadraticSignalLaplacian p uStar u₁ x -
      paper3QuadraticSignalLaplacian p uStar u₂ x| ≤
        (p.μ * B0 + K) * (M₁ + M₂) * D := by
    unfold paper3QuadraticSignalLaplacian
    calc
      _ ≤ |p.μ * (paper3QuadraticSignalValue p uStar u₁ x -
            paper3QuadraticSignalValue p uStar u₂ x)| +
          |paper3IntervalEllipticRemainderProfile p uStar u₁ x -
            paper3IntervalEllipticRemainderProfile p uStar u₂ x| := by
        rw [show
          (p.μ * paper3QuadraticSignalValue p uStar u₁ x -
              paper3IntervalEllipticRemainderProfile p uStar u₁ x) -
            (p.μ * paper3QuadraticSignalValue p uStar u₂ x -
              paper3IntervalEllipticRemainderProfile p uStar u₂ x) =
            p.μ * (paper3QuadraticSignalValue p uStar u₁ x -
              paper3QuadraticSignalValue p uStar u₂ x) -
            (paper3IntervalEllipticRemainderProfile p uStar u₁ x -
              paper3IntervalEllipticRemainderProfile p uStar u₂ x) by ring]
        exact abs_sub
          (p.μ * (paper3QuadraticSignalValue p uStar u₁ x -
            paper3QuadraticSignalValue p uStar u₂ x))
          (paper3IntervalEllipticRemainderProfile p uStar u₁ x -
            paper3IntervalEllipticRemainderProfile p uStar u₂ x)
      _ ≤ p.μ * (B0 * (M₁ + M₂) * D) + K * (M₁ + M₂) * D := by
        rw [abs_mul, abs_of_pos p.hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hz2 p.hμ.le) hquadSource
      _ = _ := by ring
  exact ⟨hz1.trans (mul_le_mul_of_nonneg_right hA0C hD),
    hz1x.trans (mul_le_mul_of_nonneg_right hA1C hD),
    hz1xx.trans (mul_le_mul_of_nonneg_right hA2C hD),
    hz2.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB0C (add_nonneg hM₁ hM₂)) hD)),
    hz2x.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB1C (add_nonneg hM₁ hM₂)) hD)),
    hz2xx.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hB2C (add_nonneg hM₁ hM₂)) hD))⟩

#print axioms paper3SignalComponents_strong_difference_bounds_uniform
#print axioms paper3UniformSignalDifferenceConstant_pos

end

end ShenWork.Paper3
