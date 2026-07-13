/-
  Linear and quadratic elliptic signal components in physical value/gradient
  norms.  Bessel controls the source coefficients; the diagonal resolver
  weights then give pointwise bounds.
-/
import ShenWork.Paper3.IntervalDomainResolvedSourceBounds

namespace ShenWork.Paper3

open MeasureTheory Set Real
open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel

noncomputable section

/-- Real linear elliptic source coefficient. -/
def paper3LinearEllipticSourceCoeffReal
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (paper3IntervalEllipticLinearProfile p uStar u) k

/-- Real quadratic elliptic source coefficient. -/
def paper3QuadraticEllipticSourceCoeffReal
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (k : ℕ) : ℝ :=
  cosineCoeffs (paper3IntervalEllipticRemainderProfile p uStar u) k

def paper3LinearSignalValue
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3ResolvedSourceValue p
    (paper3LinearEllipticSourceCoeffReal p uStar u) x

def paper3LinearSignalGradient
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3ResolvedSourceGradient p
    (paper3LinearEllipticSourceCoeffReal p uStar u) x

def paper3QuadraticSignalValue
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3ResolvedSourceValue p
    (paper3QuadraticEllipticSourceCoeffReal p uStar u) x

def paper3QuadraticSignalGradient
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  paper3ResolvedSourceGradient p
    (paper3QuadraticEllipticSourceCoeffReal p uStar u) x

/-- Linear source coefficients are `O(L2(phi))`. -/
theorem paper3LinearEllipticSourceCoeffReal_l2
    (p : CM2Params) (uStar : ℝ)
    (u : intervalDomainPoint → ℝ)
    (hphi : MemLp (paper3IntervalPerturbationProfile uStar u) 2
      (intervalMeasure 1))
    (hlin_meas : AEStronglyMeasurable
      (paper3IntervalEllipticLinearProfile p uStar u)
      (intervalMeasure 1)) :
    Summable (fun k =>
      (paper3LinearEllipticSourceCoeffReal p uStar u k) ^ 2) ∧
    Real.sqrt (∑' k,
      (paper3LinearEllipticSourceCoeffReal p uStar u k) ^ 2) ≤
      2 * |p.ν * paper3PowerDeriv p.γ uStar| *
        Real.sqrt (∫ x in (0 : ℝ)..1,
          (paper3IntervalPerturbationProfile uStar u x) ^ 2) := by
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |paper3IntervalEllipticLinearProfile p uStar u x| ≤
        |p.ν * paper3PowerDeriv p.γ uStar| *
          |paper3IntervalPerturbationProfile uStar u x| := by
    intro x _
    simp [paper3IntervalEllipticLinearProfile, abs_mul, mul_assoc]
  simpa [paper3LinearEllipticSourceCoeffReal] using
    (cosineCoeffs_l2_norm_le_of_pointwise_mul
      (B := |p.ν * paper3PowerDeriv p.γ uStar|)
      (abs_nonneg _) hphi hlin_meas hpoint)

/-- Combined pointwise bounds for `Z1` and the quadratic elliptic correction
`Z2`. -/
theorem paper3SignalComponents_pointwise_bounds
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
      |paper3IntervalPerturbationProfile uStar u x| ≤ M) :
    ∃ K > 0, ∀ x : ℝ,
      |paper3LinearSignalValue p uStar u x| ≤
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
            (2 * |p.ν * paper3PowerDeriv p.γ uStar|) *
              Real.sqrt (∫ y in (0 : ℝ)..1,
                (paper3IntervalPerturbationProfile uStar u y) ^ 2) ∧
      |paper3LinearSignalGradient p uStar u x| ≤
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * |p.ν * paper3PowerDeriv p.γ uStar|) *
              Real.sqrt (∫ y in (0 : ℝ)..1,
                (paper3IntervalPerturbationProfile uStar u y) ^ 2) ∧
      |paper3QuadraticSignalValue p uStar u x| ≤
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
            (2 * K) * M *
              Real.sqrt (∫ y in (0 : ℝ)..1,
                (paper3IntervalPerturbationProfile uStar u y) ^ 2) ∧
      |paper3QuadraticSignalGradient p uStar u x| ≤
          Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
            (2 * K) * M *
              Real.sqrt (∫ y in (0 : ℝ)..1,
                (paper3IntervalPerturbationProfile uStar u y) ^ 2) := by
  have hlin := paper3LinearEllipticSourceCoeffReal_l2
    p uStar u hphi hlin_meas
  rcases paper3IntervalEllipticRemainder_coeff_l2 p huStar hM u
      hu_near hphi hrem_meas hphi_sup with
    ⟨K, hK, hrem⟩
  refine ⟨K, hK, ?_⟩
  intro x
  have hlinVal := paper3ResolvedSourceValue_abs_le p hlin.1 x
  have hlinGrad := paper3ResolvedSourceGradient_abs_le p hlin.1 x
  have hremVal := paper3ResolvedSourceValue_abs_le p hrem.1 x
  have hremGrad := paper3ResolvedSourceGradient_abs_le p hrem.1 x
  refine ⟨hlinVal.trans ?_, hlinGrad.trans ?_, hremVal.trans ?_,
    hremGrad.trans ?_⟩
  · calc
      _ ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * |p.ν * paper3PowerDeriv p.γ uStar| *
            Real.sqrt (∫ y in (0 : ℝ)..1,
              (paper3IntervalPerturbationProfile uStar u y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hlin.2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * |p.ν * paper3PowerDeriv p.γ uStar| *
            Real.sqrt (∫ y in (0 : ℝ)..1,
              (paper3IntervalPerturbationProfile uStar u y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hlin.2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverWeight p k) ^ 2) *
          (2 * K * M * Real.sqrt (∫ y in (0 : ℝ)..1,
            (paper3IntervalPerturbationProfile uStar u y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hrem.2 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      _ ≤ Real.sqrt (∑' k : ℕ,
            (ShenWork.PDE.intervalNeumannResolverGradWeight p k) ^ 2) *
          (2 * K * M * Real.sqrt (∫ y in (0 : ℝ)..1,
            (paper3IntervalPerturbationProfile uStar u y) ^ 2)) :=
        mul_le_mul_of_nonneg_left hrem.2 (Real.sqrt_nonneg _)
      _ = _ := by ring

#print axioms paper3LinearEllipticSourceCoeffReal_l2
#print axioms paper3SignalComponents_pointwise_bounds

end

end ShenWork.Paper3
