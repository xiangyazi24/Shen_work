/- Uniform local constants for the physical route-(a) Nemytskii estimate. -/
import ShenWork.Paper3.IntervalDomainRouteANonlinearSnapshot

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- A fixed elliptic Taylor constant on the positive equilibrium
neighborhood. -/
def paper3UniformEllipticTaylorConstant
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) : ℝ :=
  Classical.choose (paper3EllipticSource_quadratic_remainder p huStar)

theorem paper3UniformEllipticTaylorConstant_pos
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) :
    0 < paper3UniformEllipticTaylorConstant p uStar huStar :=
  (Classical.choose_spec
    (paper3EllipticSource_quadratic_remainder p huStar)).1

theorem paper3UniformEllipticTaylorConstant_bound
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) :
    ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |paper3EllipticSourceRemainder p uStar x| ≤
        paper3UniformEllipticTaylorConstant p uStar huStar *
          |x - uStar| ^ 2 :=
  (Classical.choose_spec
    (paper3EllipticSource_quadratic_remainder p huStar)).2

/-- Fixed polarized elliptic Taylor constant on the positivity interval. -/
def paper3UniformEllipticPolarConstant
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) : ℝ :=
  Classical.choose (paper3EllipticSource_quadratic_remainder_sub p huStar)

theorem paper3UniformEllipticPolarConstant_pos
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) :
    0 < paper3UniformEllipticPolarConstant p uStar huStar :=
  (Classical.choose_spec
    (paper3EllipticSource_quadratic_remainder_sub p huStar)).1

theorem paper3UniformEllipticPolarConstant_bound
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) :
    ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      ∀ y ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
        |paper3EllipticSourceRemainder p uStar x -
            paper3EllipticSourceRemainder p uStar y| ≤
          paper3UniformEllipticPolarConstant p uStar huStar *
            (|x - uStar| + |y - uStar|) * |x - y| :=
  (Classical.choose_spec
    (paper3EllipticSource_quadratic_remainder_sub p huStar)).2

/-- A fixed logistic Taylor constant on the same positive neighborhood. -/
def paper3UniformLogisticTaylorConstant
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  Classical.choose (paper3LogisticReaction_quadratic_remainder p heq)

theorem paper3UniformLogisticTaylorConstant_pos
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    0 < paper3UniformLogisticTaylorConstant p heq :=
  (Classical.choose_spec
    (paper3LogisticReaction_quadratic_remainder p heq)).1

theorem paper3UniformLogisticTaylorConstant_bound
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      |paper3LogisticReaction p x + p.a * p.α * (x - uStar)| ≤
        paper3UniformLogisticTaylorConstant p heq * |x - uStar| ^ 2 :=
  (Classical.choose_spec
    (paper3LogisticReaction_quadratic_remainder p heq)).2

/-- Fixed polarized logistic Taylor constant on the positivity interval. -/
def paper3UniformLogisticPolarConstant
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) : ℝ :=
  Classical.choose (paper3LogisticRemainder_sub_local_lipschitz p heq)

theorem paper3UniformLogisticPolarConstant_pos
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    0 < paper3UniformLogisticPolarConstant p heq :=
  (Classical.choose_spec
    (paper3LogisticRemainder_sub_local_lipschitz p heq)).1

theorem paper3UniformLogisticPolarConstant_bound
    (p : CM2Params) {uStar vStar : ℝ}
    (heq : Paper3ConstantEquilibrium p uStar vStar) :
    ∀ x ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
      ∀ y ∈ Set.Icc (uStar / 2) (3 * uStar / 2),
        |paper3LogisticRemainder p uStar x -
            paper3LogisticRemainder p uStar y| ≤
          paper3UniformLogisticPolarConstant p heq *
            (|x - uStar| + |y - uStar|) * |x - y| :=
  (Classical.choose_spec
    (paper3LogisticRemainder_sub_local_lipschitz p heq)).2

/-- One fixed constant controlling the linear and quadratic resolver values,
gradients, and elliptic-laplacian representatives. -/
def paper3UniformSignalStrongConstant
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) : ℝ :=
  let K := paper3UniformEllipticTaylorConstant p uStar huStar
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
  1 + A0 + A1 + (p.μ * A0 + D) + B0 + B1 + (p.μ * B0 + K)

theorem paper3UniformSignalStrongConstant_pos
    (p : CM2Params) (uStar : ℝ) (huStar : 0 < uStar) :
    0 < paper3UniformSignalStrongConstant p uStar huStar := by
  unfold paper3UniformSignalStrongConstant
  dsimp only
  have hK := paper3UniformEllipticTaylorConstant_pos p uStar huStar
  have hA0 : 0 ≤ Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
        (2 * |p.ν * paper3PowerDeriv p.γ uStar|) := by positivity
  have hA1 : 0 ≤ Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
        (2 * |p.ν * paper3PowerDeriv p.γ uStar|) := by positivity
  have hB0 : 0 ≤ Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) * (2 *
        paper3UniformEllipticTaylorConstant p uStar huStar) := by positivity
  have hB1 : 0 ≤ Real.sqrt (∑' k : ℕ,
      (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) * (2 *
        paper3UniformEllipticTaylorConstant p uStar huStar) := by positivity
  have hD : 0 ≤ |p.ν * paper3PowerDeriv p.γ uStar| := abs_nonneg _
  linarith [mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0, hK.le]

/-- The fixed signal constant controls every profile in the same positivity
and strong ball. -/
theorem paper3SignalComponents_strong_bounds_uniform
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
    let C := paper3UniformSignalStrongConstant p uStar huStar
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3LinearSignalValue p uStar u x| ≤ C * M ∧
      |paper3LinearSignalGradient p uStar u x| ≤ C * M ∧
      |paper3LinearSignalLaplacian p uStar u x| ≤ C * M ∧
      |paper3QuadraticSignalValue p uStar u x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalGradient p uStar u x| ≤ C * M ^ 2 ∧
      |paper3QuadraticSignalLaplacian p uStar u x| ≤ C * M ^ 2 := by
  dsimp only
  let K := paper3UniformEllipticTaylorConstant p uStar huStar
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
  let C := paper3UniformSignalStrongConstant p uStar huStar
  have hK : 0 < K := paper3UniformEllipticTaylorConstant_pos p uStar huStar
  have hlin := paper3LinearEllipticSourceCoeffReal_l2
    p uStar u hphi hlin_meas
  have hremPoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalEllipticRemainderProfile p uStar u x| ≤
        (K * M) * |paper3IntervalPerturbationProfile uStar u x| := by
    intro x hx
    have hq := paper3UniformEllipticTaylorConstant_bound
      p uStar huStar (intervalDomainLift u x) (hu_near x hx)
    have hs := hphi_sup x hx
    dsimp [paper3IntervalEllipticRemainderProfile,
      paper3IntervalPerturbationProfile] at hq hs ⊢
    calc
      _ ≤ K * |intervalDomainLift u x - uStar| ^ 2 := hq
      _ ≤ (K * M) * |intervalDomainLift u x - uStar| := by
        have ha : 0 ≤ |intervalDomainLift u x - uStar| := abs_nonneg _
        have hp : 0 ≤ K * |intervalDomainLift u x - uStar| *
            (M - |intervalDomainLift u x - uStar|) :=
          mul_nonneg (mul_nonneg hK.le ha) (sub_nonneg.mpr hs)
        nlinarith
  have hrem := cosineCoeffs_l2_norm_le_of_pointwise_mul
    (B := K * M) (mul_nonneg hK.le hM) hphi hrem_meas hremPoint
  have hlinVal := fun x => paper3ResolvedSourceValue_abs_le p hlin.1 x
  have hlinGrad := fun x => paper3ResolvedSourceGradient_abs_le p hlin.1 x
  have hremVal := fun x => paper3ResolvedSourceValue_abs_le p hrem.1 x
  have hremGrad := fun x => paper3ResolvedSourceGradient_abs_le p hrem.1 x
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA1 : 0 ≤ A1 := by dsimp [A1]; positivity
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < C := by
    simpa [C] using paper3UniformSignalStrongConstant_pos p uStar huStar
  have hA0C : A0 ≤ C := by
    dsimp [C, paper3UniformSignalStrongConstant]
    linarith [hA1, hB0, hB1, hD, hK.le,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0]
  have hA1C : A1 ≤ C := by
    dsimp [C, paper3UniformSignalStrongConstant]
    linarith [hA0, hB0, hB1, hD, hK.le,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0]
  have hA2C : p.μ * A0 + D ≤ C := by
    dsimp [C, paper3UniformSignalStrongConstant]
    linarith [hA0, hA1, hB0, hB1, hK.le,
      mul_nonneg p.hμ.le hB0]
  have hB0C : B0 ≤ C := by
    dsimp [C, paper3UniformSignalStrongConstant]
    linarith [hA0, hA1, hB1, hD, hK.le,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0]
  have hB1C : B1 ≤ C := by
    dsimp [C, paper3UniformSignalStrongConstant]
    linarith [hA0, hA1, hB0, hD, hK.le,
      mul_nonneg p.hμ.le hA0, mul_nonneg p.hμ.le hB0]
  have hB2C : p.μ * B0 + K ≤ C := by
    dsimp [C, paper3UniformSignalStrongConstant]
    linarith [hA0, hA1, hB0, hB1, hD,
      mul_nonneg p.hμ.le hA0]
  intro x hx
  have hz1 : |paper3LinearSignalValue p uStar u x| ≤ A0 * M := by
    calc
      _ ≤ A0 * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        apply (hlinVal x).trans
        have hsqrt : 0 ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
          Real.sqrt_nonneg _
        have := mul_le_mul_of_nonneg_left hlin.2 hsqrt
        simpa [A0, paper3LinearSignalValue,
          paper3LinearEllipticSourceCoeffReal, mul_assoc] using this
      _ ≤ A0 * M := mul_le_mul_of_nonneg_left hphi_l2 hA0
  have hz1x : |paper3LinearSignalGradient p uStar u x| ≤ A1 * M := by
    calc
      _ ≤ A1 * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        apply (hlinGrad x).trans
        have hsqrt : 0 ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
          Real.sqrt_nonneg _
        have := mul_le_mul_of_nonneg_left hlin.2 hsqrt
        simpa [A1, paper3LinearSignalGradient,
          paper3LinearEllipticSourceCoeffReal, mul_assoc] using this
      _ ≤ A1 * M := mul_le_mul_of_nonneg_left hphi_l2 hA1
  have hz2 : |paper3QuadraticSignalValue p uStar u x| ≤ B0 * M ^ 2 := by
    calc
      _ ≤ B0 * M * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        apply (hremVal x).trans
        have hsqrt : 0 ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) :=
          Real.sqrt_nonneg _
        have := mul_le_mul_of_nonneg_left hrem.2 hsqrt
        simpa [B0, paper3QuadraticSignalValue,
          paper3QuadraticEllipticSourceCoeffReal, mul_assoc] using this
      _ ≤ B0 * M * M :=
        mul_le_mul_of_nonneg_left hphi_l2 (mul_nonneg hB0 hM)
      _ = B0 * M ^ 2 := by ring
  have hz2x : |paper3QuadraticSignalGradient p uStar u x| ≤ B1 * M ^ 2 := by
    calc
      _ ≤ B1 * M * Real.sqrt (∫ y in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
        apply (hremGrad x).trans
        have hsqrt : 0 ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) :=
          Real.sqrt_nonneg _
        have := mul_le_mul_of_nonneg_left hrem.2 hsqrt
        simpa [B1, paper3QuadraticSignalGradient,
          paper3QuadraticEllipticSourceCoeffReal, mul_assoc] using this
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
      K * M ^ 2 := by
    have hq := paper3UniformEllipticTaylorConstant_bound
      p uStar huStar (intervalDomainLift u x) (hu_near x hx)
    have hs := hphi_sup x hx
    dsimp [paper3IntervalEllipticRemainderProfile,
      paper3IntervalPerturbationProfile] at hq hs ⊢
    have hsquare : |intervalDomainLift u x - uStar| ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hM).2 hs
    exact hq.trans (mul_le_mul_of_nonneg_left hsquare hK.le)
  have hz1xx : |paper3LinearSignalLaplacian p uStar u x| ≤
      (p.μ * A0 + D) * M := by
    unfold paper3LinearSignalLaplacian
    calc
      _ ≤ |p.μ * paper3LinearSignalValue p uStar u x| +
          |paper3IntervalEllipticLinearProfile p uStar u x| := abs_sub _ _
      _ ≤ p.μ * (A0 * M) + D * M := by
        rw [abs_mul, abs_of_pos p.hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hz1 p.hμ.le) hlinSource
      _ = _ := by ring
  have hz2xx : |paper3QuadraticSignalLaplacian p uStar u x| ≤
      (p.μ * B0 + K) * M ^ 2 := by
    unfold paper3QuadraticSignalLaplacian
    calc
      _ ≤ |p.μ * paper3QuadraticSignalValue p uStar u x| +
          |paper3IntervalEllipticRemainderProfile p uStar u x| := abs_sub _ _
      _ ≤ p.μ * (B0 * M ^ 2) + K * M ^ 2 := by
        rw [abs_mul, abs_of_pos p.hμ]
        exact add_le_add (mul_le_mul_of_nonneg_left hz2 p.hμ.le) hremSource
      _ = _ := by ring
  exact ⟨hz1.trans (mul_le_mul_of_nonneg_right hA0C hM),
    hz1x.trans (mul_le_mul_of_nonneg_right hA1C hM),
    hz1xx.trans (mul_le_mul_of_nonneg_right hA2C hM),
    hz2.trans (mul_le_mul_of_nonneg_right hB0C (sq_nonneg M)),
    hz2x.trans (mul_le_mul_of_nonneg_right hB1C (sq_nonneg M)),
    hz2xx.trans (mul_le_mul_of_nonneg_right hB2C (sq_nonneg M))⟩

#print axioms paper3SignalComponents_strong_bounds_uniform
#print axioms paper3UniformSignalStrongConstant_pos
#print axioms paper3UniformLogisticTaylorConstant_bound
#print axioms paper3UniformEllipticPolarConstant_bound
#print axioms paper3UniformLogisticPolarConstant_bound

end

end ShenWork.Paper3
