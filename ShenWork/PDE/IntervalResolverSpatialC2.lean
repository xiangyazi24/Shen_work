/-
# Spatial C² regularity of the elliptic resolver `R u`

This file proves that the elliptic resolver

  `R u : intervalDomainPoint → ℝ`,   `R u x = ∑' k, (v̂_k).re · cos(kπ x.1)`,

has `ContDiff ℝ 2` spatial regularity and Neumann boundary conditions at both
endpoints, whenever the source satisfies `SourceCoeffQuadraticDecay`.

## What is proved here (0 sorry, 0 admit, 0 custom axiom)

* `resolverR_summability` — the eigenvalue-weighted coefficient summability
  `Summable (fun k => unitIntervalCosineEigenvalue k * |(v̂_k).re|)`, the driver
  for the `C²`-engine.
* `resolverR_eq_cosineSeries` — `intervalNeumannResolverR p u x` equals
  `∑' k, (v̂_k).re * cosineMode k x.1` (bridge from `unitIntervalCosineMode`
  to `cosineMode`, which are definitionally equal).
* `resolverR_contDiff_two` — `ContDiff ℝ 2 (fun x => intervalNeumannResolverR p u ⟨x, hx⟩)`
  for the lifted real function, from `cosineCoeffSeries_contDiff_two`.
* `resolverR_deriv_at_zero` — `deriv (fun x => intervalNeumannResolverR p u ⟨x, hx⟩) 0 = 0`
  (Neumann left endpoint).
* `resolverR_deriv_at_one` — `deriv (fun x => intervalNeumannResolverR p u ⟨x, hx⟩) 1 = 0`
  (Neumann right endpoint).

## Proof route

From `SourceCoeffQuadraticDecay p u`, `resolverGrad2_majorant_summable_of_sourceDecay`
(in `IntervalResolverGradientBridge`) gives `Summable (fun k => |(v̂_k).re| * (kπ)²)`.
Since `unitIntervalCosineEigenvalue k = (kπ)²`, this is exactly the eigenvalue-weighted
summability `Summable (fun k => unitIntervalCosineEigenvalue k * |(v̂_k).re|)` needed by
the `C²`-engine `cosineCoeffSeries_contDiff_two` (in `IntervalDuhamelClosedC2`).
The resolver value `intervalNeumannResolverR p u x = ∑ (v̂_k).re * unitIntervalCosineMode k x.1`
(definition), and `unitIntervalCosineMode k y = cosineMode k y` (proven in
`HeatKernelLpEstimates`), so we rewrite to the form expected by the `C²`-engine.
-/
import ShenWork.PDE.IntervalResolverLaplacianBridge
import ShenWork.PDE.IntervalDuhamelClosedC2
import ShenWork.PDE.IntervalNeumannEllipticResolverR

open MeasureTheory
open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.HeatKernelGradientEstimates
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.IntervalResolverSpatialC2

noncomputable section

open ShenWork.PDE
open ShenWork.IntervalResolverGradientBridge
open ShenWork.IntervalDuhamelClosedC2
open ShenWork.Paper2

/-! ## Step 1: eigenvalue-weighted coefficient summability -/

/-- **Eigenvalue-weighted summability of resolver coefficients.**
From `SourceCoeffQuadraticDecay`, the `(kπ)²`-weighted coefficient sum
`∑ unitIntervalCosineEigenvalue k * |(v̂_k).re|` converges.  This is the key
summability input for the `C²`-cosine-series engine. -/
theorem resolverR_summability
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|) := by
  have hmaj := resolverGrad2_majorant_summable_of_sourceDecay
    hdecay.C_nonneg hdecay.decay
  -- `resolverGrad2_majorant_summable_of_sourceDecay` gives
  -- `Summable (fun k => |(v̂_k).re| * (kπ)²)`.
  -- Rewrite to `unitIntervalCosineEigenvalue k * |...| = |...| * (kπ)²`.
  refine hmaj.congr (fun k => ?_)
  have hlam : unitIntervalCosineEigenvalue k = ((k : ℝ) * Real.pi) ^ 2 := by
    unfold unitIntervalCosineEigenvalue; ring
  rw [hlam, mul_comm]

/-! ## Step 2: write the resolver value in `cosineMode` form -/

/-- **Bridge: resolver value equals cosine series in `cosineMode` form.**
`intervalNeumannResolverR p u x = ∑' k, (v̂_k).re * cosineMode k x.1`,
obtained by rewriting `unitIntervalCosineMode = cosineMode`. -/
theorem resolverR_eq_cosineSeries
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (x : intervalDomainPoint) :
    intervalNeumannResolverR p u x =
      ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re * cosineMode k x.1 := by
  unfold intervalNeumannResolverR
  refine tsum_congr (fun k => ?_)
  rw [unitIntervalCosineMode_eq_cosineMode]

/-! ## Step 3: C² and Neumann for the lifted real function -/

/-- **Spatial `C²` of the resolver.**  The function `x ↦ intervalNeumannResolverR p u ⟨x, hx⟩`
(the resolver value lifted to a real function on `ℝ`) is `ContDiff ℝ 2`, under
`SourceCoeffQuadraticDecay`. -/
theorem resolverR_contDiff_two
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    ContDiff ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) :=
  cosineCoeffSeries_contDiff_two (resolverR_summability hdecay)

/-- **Neumann left endpoint.**  The spatial derivative of the resolver value series
vanishes at `x = 0`, i.e.
`deriv (fun x => ∑' k, (v̂_k).re * cosineMode k x) 0 = 0`. -/
theorem resolverR_deriv_at_zero
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    deriv (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) 0 = 0 :=
  cosineCoeffSeries_deriv_at_zero (resolverR_summability hdecay)

/-- **Neumann right endpoint.**  The spatial derivative of the resolver value series
vanishes at `x = 1`, i.e.
`deriv (fun x => ∑' k, (v̂_k).re * cosineMode k x) 1 = 0`. -/
theorem resolverR_deriv_at_one
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    deriv (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) 1 = 0 :=
  cosineCoeffSeries_deriv_at_one (resolverR_summability hdecay)

/-! ## Corollary: ContDiffOn on the closed interval -/

/-- **`ContDiffOn` on `[0,1]`** for the resolver cosine series, the `Icc`-restricted
form of `resolverR_contDiff_two`. -/
theorem resolverR_contDiffOn_Icc
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hdecay : SourceCoeffQuadraticDecay p u) :
    ContDiffOn ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) :=
  (resolverR_contDiff_two hdecay).contDiffOn

/-! ## ℓ¹ summability of the resolver weights -/

/-- **Resolver weights are ℓ¹ summable**: `∑ 1/(μ+λₖ) < ∞`.

Since `wₖ = 1/(μ + (kπ)²) ~ 1/k²π²` for large `k`, this follows from
comparison with the convergent p-series `∑ 1/k²`.  For `k ≥ 1` the denominator
satisfies `μ + λₖ ≥ (kπ)²`, so `wₖ ≤ 1/(kπ)² = (1/π²)·(1/k²)`.  The `k = 0`
term `w₀ = 1/μ` is handled by restricting the comparison to `k ≥ 1` via
`summable_nat_add_iff`. -/
theorem resolverWeight_summable (p : CM2Params) :
    Summable (fun k : ℕ => intervalNeumannResolverWeight p k) := by
  -- Reduce to summability from index 1 onward (the k=0 term is a single
  -- finite value and does not affect summability).
  rw [← summable_nat_add_iff 1]
  have hlam : ∀ k : ℕ,
      unitIntervalNeumannSpectrum.eigenvalue k = (k : ℝ) ^ 2 * Real.pi ^ 2 := fun k => rfl
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- The majorant: `(1/π²) · 1/(k+1)²`, summable by the p-series `∑ 1/k²`.
  have hmaj : Summable fun k : ℕ =>
      (1 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2) := by
    have hp2 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
      have := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) 1).2 this
    exact hp2.mul_left _
  refine Summable.of_nonneg_of_le
    (fun k => (intervalNeumannResolverWeight_nonneg p (k + 1)))
    ?_ hmaj
  intro k
  -- The denominator at `k+1` is positive.
  have hden_pos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1) :=
    intervalNeumannResolver_denom_pos p (k + 1)
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- Lower bound: `μ + λ_{k+1} ≥ ((k+1)π)²`.
  have hlow : ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 ≤
      p.μ + unitIntervalNeumannSpectrum.eigenvalue (k + 1) := by
    rw [hlam (k + 1)]
    push_cast
    nlinarith [p.hμ.le, sq_nonneg ((k : ℝ) + 1), sq_nonneg Real.pi]
  have hbase_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by positivity
  -- Therefore `w_{k+1} = 1/(μ+λ_{k+1}) ≤ 1/((k+1)²π²) = (1/π²)·1/(k+1)²`.
  show intervalNeumannResolverWeight p (k + 1) ≤ _
  unfold intervalNeumannResolverWeight
  have hineq := one_div_le_one_div_of_le hbase_pos hlow
  have heq : 1 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) =
      1 / Real.pi ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
    rw [div_mul_div_comm, one_mul, mul_comm]
  linarith

end

end ShenWork.IntervalResolverSpatialC2
