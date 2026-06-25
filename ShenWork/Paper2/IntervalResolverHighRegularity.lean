/-
  ShenWork/Paper2/IntervalResolverHighRegularity.lean

  High spatial regularity and symmetry facts for the concrete interval Neumann
  elliptic resolver.

  The file is intentionally coefficient-level.  It upgrades the committed C²
  resolver route to C⁴ whenever the resolver source coefficients carry one
  eigenvalue weight in `ℓ¹`.  The static resolvent identity gives

    λₖ * |v̂ₖ| ≤ |âₖ|,

  already proved in `IntervalResolverPhysicalC2`; multiplying by `λₖ ≥ 0`
  gives the C⁴ summability driver

    λₖ * (λₖ * |v̂ₖ|) ≤ λₖ * |âₖ|.

  The symmetry statements are for the real-line cosine synthesis of the resolver;
  the actual `intervalNeumannResolverR p u` has domain `intervalDomainPoint`.

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalResolverPhysicalC2
import ShenWork.PDE.IntervalResolverPositivity
import ShenWork.Paper2.IntervalParabolicDuhamelGainNonCircular
import ShenWork.Wiener.EWA.HeatFloor

open scoped BigOperators Topology
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.PDE
  (intervalNeumannResolverCoeff intervalNeumannResolverSourceCoeff intervalNeumannResolverR)

noncomputable section

namespace ShenWork.Paper2.ResolverHighRegularity

/-- The real-line cosine synthesis associated to the interval Neumann resolver.

This is the natural globally-defined representative of `intervalNeumannResolverR p u`.
On the fundamental interval `[0,1]`, it agrees with the subtype-valued resolver via
`IntervalResolverSpatialC2.resolverR_eq_cosineSeries`. -/
def resolverRSynthesis (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x

/-- The resolver value on the interval agrees with the real-line synthesis. -/
theorem intervalNeumannResolverR_eq_resolverRSynthesis
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x = resolverRSynthesis p u x.1 := by
  simpa [resolverRSynthesis] using
    ShenWork.IntervalResolverSpatialC2.resolverR_eq_cosineSeries (p := p) (u := u) x

private theorem unitIntervalCosineEigenvalue_nonneg (k : ℕ) :
    0 ≤ unitIntervalCosineEigenvalue k := by
  unfold unitIntervalCosineEigenvalue
  positivity

/-- Pointwise C⁴ summability driver for resolver coefficients.

The committed physical C² bridge gives `λₖ * |v̂ₖ| ≤ |âₖ|`.  Multiplying by
`λₖ ≥ 0` gives `λₖ² * |v̂ₖ| ≤ λₖ * |âₖ|`, exactly the input comparison needed by
`cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable`. -/
theorem resolverR_eigenSqWeighted_le_sourceEigenWeighted
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    unitIntervalCosineEigenvalue k *
        (unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|) ≤
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re| := by
  exact mul_le_mul_of_nonneg_left
    (ShenWork.IntervalResolverPhysicalC2.resolverR_eigenWeighted_le_source p u k)
    (unitIntervalCosineEigenvalue_nonneg k)

/-- Eigenvalue-squared weighted resolver summability from eigenvalue-weighted source
summability. -/
theorem resolverR_eigenSqWeighted_summable_of_sourceEigenWeighted
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        (unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|)) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsrc
  · exact mul_nonneg (unitIntervalCosineEigenvalue_nonneg k)
      (mul_nonneg (unitIntervalCosineEigenvalue_nonneg k) (abs_nonneg _))
  · exact resolverR_eigenSqWeighted_le_sourceEigenWeighted p u k

/-- **C⁴ regularity of the real-line resolver synthesis.**

This is the resolver analogue of the heat-semigroup C⁴ engine: once the source
coefficients have one eigenvalue weight in `ℓ¹`, the static resolvent supplies the
second eigenvalue weight needed for `ContDiff ℝ 4`. -/
theorem resolverR_contDiff_four
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 4 (resolverRSynthesis p u) := by
  simpa [resolverRSynthesis] using
    ShenWork.Paper2.ParabolicDuhamelGainNonCircular
      .cosineCoeffSeries_contDiff_four_of_eigenvalue_sq_summable
        (b := fun k : ℕ => (intervalNeumannResolverCoeff p u k).re)
        (resolverR_eigenSqWeighted_summable_of_sourceEigenWeighted hsrc)

/-- Evenness of the real-line resolver synthesis. -/
theorem resolverR_even (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    resolverRSynthesis p u (-x) = resolverRSynthesis p u x := by
  unfold resolverRSynthesis
  refine tsum_congr (fun k => ?_)
  rw [ShenWork.EWA.cosineMode_neg k x]

/-- Symmetry of the real-line resolver synthesis about `x = 1`: `R(2 - x) = R(x)`. -/
theorem resolverR_symm1 (p : CM2Params) (u : intervalDomainPoint → ℝ) (x : ℝ) :
    resolverRSynthesis p u (2 - x) = resolverRSynthesis p u x := by
  unfold resolverRSynthesis
  refine tsum_congr (fun k => ?_)
  rw [show (2 : ℝ) - x = -x + 2 by ring,
    ShenWork.EWA.cosineMode_add_two k (-x),
    ShenWork.EWA.cosineMode_neg k x]

/-- Positivity of the chemotactic denominator `1 + R(u)`. -/
theorem resolverR_pos_denom
    {p : CM2Params} {u : intervalDomainPoint → ℝ} {f : ℝ → ℝ}
    (hf_cont : Continuous f) (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_coeff : ∀ k, cosineCoeffs f k = (intervalNeumannResolverSourceCoeff p u k).re)
    (hâ : Summable (fun k => (cosineCoeffs f k) ^ 2))
    (x : intervalDomainPoint) :
    0 < 1 + intervalNeumannResolverR p u x := by
  exact add_pos_of_pos_of_nonneg zero_lt_one
    (ShenWork.IntervalResolverPositivity.intervalNeumannResolverR_nonneg_of_nonneg_source
      (p := p) (u := u) (f := f) hf_cont hf_nonneg hf_coeff hâ x)

end ShenWork.Paper2.ResolverHighRegularity
