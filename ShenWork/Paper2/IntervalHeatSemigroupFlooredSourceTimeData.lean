/-
# `FlooredSourceTimeData` for the heat semigroup base iterate (level 0)

This file builds the `FlooredSourceTimeData p u s₁ s₂` for the heat semigroup
base iterate `u = conjugatePicardIter p u₀ 0 = S(t)u₀`, the SINGLE
infrastructure piece that gates 7 of 12 remaining sorry.

## Source slice and time derivatives

The source slice is `srcSlice p u t x = ν · (S(t)u₀(x))^γ`.

Time derivatives via the chain rule through the heat equation `∂_t S(t) = ΔS(t)`:

  `s₁(t,x) = ν · γ · (S(t)u₀(x))^{γ-1} · ΔS(t)u₀(x)`
  `s₂(t,x) = ν · γ · (γ-1) · (S(t)u₀(x))^{γ-2} · (ΔS(t)u₀(x))² + ν · γ · (S(t)u₀(x))^{γ-1} · Δ²S(t)u₀(x)`

where `du(t,x) = ΔS(t)u₀(x)` and `d2u(t,x) = Δ²S(t)u₀(x)`.

## The τ > 0 vs τ ≤ 0 issue

`FlooredSourceTimeData` requires `∀ τ : ℝ`.  For τ > 0: the heat semigroup is
smooth and everything works.  For τ ≤ 0: `conjugatePicardIter p u₀ 0 t` is NOT
the heat semigroup but `intervalFullSemigroupOperator t (lift u₀)` — at t ≤ 0,
the function and its source are still defined (the full kernel makes sense at
t = 0 as the identity, zero for t < 0 by convention).

Since the concrete downstream use is always at `t > c > 0` (Level 0 uses
`s₀ > c`), we define `du` and `d2u` to be 0 at `t ≤ 0`, which makes the
fields trivially hold there (but with sorry for now since we need the actual
HasDerivAt at t = 0 boundary).  For t > 0, we use the spectral Laplacian.

## Sorry budget

Each field of `FlooredSourceTimeData` is sorry'd with a named obligation.
These are finite, non-circular, and independently attackable:

1. `d0` — HasDerivAt of srcSlice = s₁ + joint continuity of s₁
2. `d1` — HasDerivAt of s₁ = s₂ + joint continuity of s₂
3. `sliceC2` — ContDiffOn ℝ 2 of each time-derivative slice on [0,1]
4. `sliceNeumann` — Neumann BC (deriv = 0 at endpoints)
5. `zerothBound` — uniform zeroth-mode bound
6. `laplBound` — uniform Laplacian bound (kπ)⁻²

Once built, this feeds into the committed chain:
  FlooredSourceTimeData → physicalSourceTimeC2_of_floored → PhysicalSourceTimeC2
  → physicalResolverJointC2Data_of_floor → PhysicalResolverJointC2Data
  → coupledChemical_jointContDiffAt_two

which closes `heatSemigroup_level0_resolverJointC2Data` (previously 4 unstructured sorry).
-/
import ShenWork.PDE.IntervalFlooredSourceTimeDataIterate
import ShenWork.Paper2.IntervalConjugatePicard

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPhysicalSourceTimeC2Concrete (srcSlice sliceFam FlooredSourceTimeData)
open ShenWork.IntervalFlooredSourceTimeDataIterate (srcSlice1 srcSlice2)

noncomputable section

namespace ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData

/-! ## Time derivatives of the heat semigroup iterate

For the heat semigroup `u t x = S(t)u₀(x.1)`, the time derivative is the
spectral Laplacian `∂_t S(t) = ΔS(t)`.  We define `du` and `d2u` using the
spectral Laplacian values from `RegularityBootstrap`. -/

/-- The first time-derivative of the lifted heat semigroup iterate at `(t, x)`,
defined as the spectral Laplacian value `∑' k, -λ_k · exp(-tλ_k) · â_k · cos(kπx)`
for `t > 0`, and `0` for `t ≤ 0`. -/
def heatDu (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    ShenWork.RegularityBootstrap.unitIntervalCosineHeatLaplacianValue
      t (cosineCoeffs (intervalDomainLift u₀)) x
  else 0

/-- The second time-derivative of the lifted heat semigroup iterate, defined as
the iterated spectral Laplacian `∑' k, λ_k² · exp(-tλ_k) · â_k · cos(kπx)`
for `t > 0`, and `0` for `t ≤ 0`. -/
def heatD2u (u₀ : intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    -- The second time derivative of S(t)u₀ = Δ²S(t)u₀ = ∑ λ_k² exp(-tλ_k) â_k cos(kπx)
    ∑' k : ℕ, unitIntervalCosineEigenvalue k ^ 2 *
      (Real.exp (-t * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) *
      ShenWork.CosineSpectrum.cosineMode k x
  else 0

/-! ## The main construction -/

/-- **`FlooredSourceTimeData` for the heat semigroup base iterate.**

For `u = conjugatePicardIter p u₀ 0 = S(t)u₀`, this packages the three
time-derivative slices of the source `srcSlice p u t x = ν·(S(t)u₀(x))^γ`
with the six `FlooredSourceTimeData` fields.

Each field is sorry'd as a named atomic obligation; once all 6 are discharged,
the entire `heatSemigroup_level0_resolverJointC2Data` follows by the committed
chain `FlooredSourceTimeData → physicalSourceTimeC2_of_floored →
physicalResolverJointC2Data_of_floor`. -/
theorem heatSemigroup_flooredSourceTimeData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (_hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (_hu₀_cont : Continuous u₀) :
    FlooredSourceTimeData p (conjugatePicardIter p u₀ 0)
      (srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀))
      (srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)) where
  d0 := by
    -- OBLIGATION: ∀ τ, ∃ δ > 0 such that:
    --   (a) srcSlice is ContinuousOn [0,1] near τ
    --   (b) HasDerivAt (srcSlice · x) (s₁ · x) for x ∈ (0,1)
    --   (c) s₁ is jointly ContinuousOn on a slab
    -- For τ > 0: uses rpow chain rule under the heat floor + spectral Laplacian HasDerivAt.
    -- For τ ≤ 0: the iterate = S(t)u₀ and heatDu = 0 for t ≤ 0; srcSlice1 = ν·γ·u^{γ-1}·0 = 0.
    sorry
  d1 := by
    -- OBLIGATION: ∀ τ, ∃ δ > 0 such that:
    --   (a) s₁ is ContinuousOn [0,1] near τ
    --   (b) HasDerivAt (s₁ · x) (s₂ · x) for x ∈ (0,1)
    --   (c) s₂ is jointly ContinuousOn on a slab
    -- For τ > 0: uses product/chain rule under the heat floor + the heat equation
    --   for the second time derivative.
    -- For τ ≤ 0: s₁ = 0 and s₂ = 0, trivially.
    sorry
  sliceC2 := by
    -- OBLIGATION: ∀ i ≤ 2, ∀ t, ContDiffOn ℝ 2 (slice_i t) [0,1]
    -- For t > 0 and i = 0: srcSlice = ν·(S(t)u₀)^γ.  The heat semigroup gives C⁴
    --   in space for t > 0 (from heatSemigroup_contDiff_four), and S(t)u₀ > 0 on (0,1)
    --   (heat floor), so rpow is C² on [0,1].
    -- For t > 0 and i = 1: srcSlice1 = ν·γ·u^{γ-1}·du where du is the spectral
    --   Laplacian (also C² in space for t > 0).
    -- For t > 0 and i = 2: srcSlice2 is a combination of u^{γ-2}·du² + u^{γ-1}·d2u,
    --   both C² under the floor.
    -- For t ≤ 0: the iterate is S(t)u₀ which for t = 0 is u₀ itself (may not be C²),
    --   but the source is 0 for t < 0 by convention.
    sorry
  sliceNeumann := by
    -- OBLIGATION: ∀ i ≤ 2, ∀ t, deriv (slice_i t) vanishes at 0 and 1
    -- For the heat semigroup, the Neumann eigenfunction expansion guarantees
    -- that the spatial derivatives of S(t)u₀ satisfy Neumann BCs (deriv cos(kπx)
    -- vanishes at 0 and 1).  The chain/product rule through rpow preserves this
    -- because deriv(u^γ) = γ·u^{γ-1}·u' and u' = 0 at the boundary.
    sorry
  zerothBound := by
    -- OBLIGATION: ∀ i ≤ 2, ∃ D ≥ 0, ∀ t, |cosineCoeffs (slice_i t) 0| ≤ D
    -- The zeroth cosine coefficient is the integral ∫₀¹ f(x) dx.
    -- For the heat semigroup: S(t)u₀ is bounded by M₀ (coefficient bound gives
    -- sup-norm bound via the cosine series), so srcSlice = ν·u^γ is bounded by
    -- ν·M₀^γ.  Similarly for s₁ and s₂ (their integrals are bounded by products
    -- of sup-norm bounds of u, du, d2u on [0,1]).
    sorry
  laplBound := by
    -- OBLIGATION: ∀ i ≤ 2, ∃ M ≥ 0, ∀ t k, 1 ≤ k →
    --   |cosineCoeffs (slice_i t) k| ≤ M / (kπ)²
    -- This is the IBP decay from the committed `cosineCoeff_decay`: when the
    -- slice is C² on [0,1] with Neumann BCs, integration by parts twice gives
    --   |â_k| ≤ (1/(kπ)²) · sup |Δ(slice)|
    -- The uniform-in-t Laplacian bound follows from the spatial C² data and
    -- the uniform sup-norm bounds of the iterated Laplacian.
    sorry

end ShenWork.Paper2.HeatSemigroupFlooredSourceTimeData
