import ShenWork.Paper1.WholeLineWeightedRegularityRawDQIdentity

open Filter Topology

noncomputable section

namespace ShenWork.Paper1

/-- A spatial difference quotient converges to the classical derivative as
the nonzero step tends to zero. -/
theorem spatialDifferenceQuotient_tendsto_deriv
    {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) :
    Tendsto (fun h : ℝ => spatialDifferenceQuotient h f x)
      (𝓝[≠] (0 : ℝ)) (𝓝 d) := by
  simpa only [spatialDifferenceQuotient, div_eq_mul_inv, smul_eq_mul,
    mul_comm] using hf.tendsto_slope_zero

/-- The conjugated raw quotient converges to `eta*f + f'` pointwise. -/
theorem rawSpatialDifferenceQuotient_tendsto
    {f : ℝ → ℝ} {x d eta : ℝ} (hf : HasDerivAt f d x) :
    Tendsto (fun h : ℝ => rawSpatialDifferenceQuotient eta h f x)
      (𝓝[≠] (0 : ℝ)) (𝓝 (eta * f x + d)) := by
  simpa only [rawSpatialDifferenceQuotient] using
    tendsto_const_nhds.add (spatialDifferenceQuotient_tendsto_deriv hf)

#print axioms spatialDifferenceQuotient_tendsto_deriv
#print axioms rawSpatialDifferenceQuotient_tendsto

end ShenWork.Paper1
