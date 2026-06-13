/-
# Physical (elliptic-equation) spatial C² of the Neumann resolver

The committed spatial-C² theorem `IntervalResolverSpatialC2.resolverR_contDiff_two`
takes the hypothesis `SourceCoeffQuadraticDecay p u` (each source coefficient
`|â_k| ≤ C/(kπ)²`).  This file gives the **physical / elliptic-equation** form of
that bootstrap: it requires only that the *source coefficient sequence is `ℓ¹`*
(`Summable (fun k => |(â_k).re|)`), which is exactly the statement "the elliptic
source `ν·u^γ` is `C²`-Neumann on `[0,1]`" packaged at the coefficient layer
(absolute convergence of a `C²`-Neumann function's cosine coefficients).

## The elliptic-equation mechanism

The resolver coefficient satisfies the **coefficient-form elliptic equation**
`(μ + λ_k)·v̂_k = â_k` (`intervalNeumannResolverCoeff_elliptic`).  Hence the
eigenvalue-weighted resolver coefficient is

  `λ_k · v̂_k = (λ_k / (μ + λ_k)) · â_k`,

with the **bounded multiplier** `λ_k/(μ+λ_k) ∈ [0,1)`.  Therefore

  `λ_k · |v̂_k| ≤ |â_k|`,

so `ℓ¹` of the source coefficients implies the eigenvalue-weighted `ℓ¹` of the
resolver coefficients — precisely the hypothesis of the `C²`-cosine-series engine
`cosineCoeffSeries_contDiff_two`.  This is the elliptic equation `v'' = μ·v − source`
read off term by term: the second spatial derivative picks up exactly the factor
`λ_k`, and the bounded resolvent multiplier never lets it grow past `|â_k|`.  The
heat/Duhamel eigenvalue-cube ladder is bypassed entirely: the static resolvent
weight `1/(μ+λ_k)` exactly cancels the `λ_k` produced by `∂ₓₓ`.

## What is proved (0 sorry, 0 admit, 0 custom axiom)

* `resolverR_eigenWeighted_summable_of_sourceL1` — from `ℓ¹` source coefficients,
  the eigenvalue-weighted resolver coefficients `λ_k·|v̂_k.re|` are summable.
* `resolverR_contDiff_two_of_source_l1` — the lifted resolver cosine series is
  `ContDiff ℝ 2`, from `ℓ¹` source coefficients alone (physical route).
* `resolverR_contDiffOn_Icc_of_source_l1` — the `Icc`-restricted corollary.
-/
import ShenWork.PDE.IntervalResolverSpatialC2

open ShenWork.IntervalDomain ShenWork.CosineSpectrum
open ShenWork.Paper3 (unitIntervalNeumannSpectrum)
open scoped Topology BigOperators

namespace ShenWork.IntervalResolverPhysicalC2

noncomputable section

open ShenWork.PDE
open ShenWork.IntervalDuhamelClosedC2

/-- **Bounded resolvent multiplier on the eigenvalue-weighted coefficient.**
From the coefficient-form elliptic equation `(μ+λ_k)·v̂_k = â_k`, the second-
derivative-weighted resolver coefficient is dominated by the source coefficient:

  `λ_k · |(v̂_k).re| ≤ |(â_k).re|`.

This is the pointwise statement of the elliptic equation `∂ₓₓ v = μ v − source`:
`∂ₓₓ` contributes `λ_k`, and the static resolvent weight `1/(μ+λ_k)` caps it. -/
theorem resolverR_eigenWeighted_le_source
    (p : CM2Params) (u : intervalDomainPoint → ℝ) (k : ℕ) :
    unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re| ≤
      |(intervalNeumannResolverSourceCoeff p u k).re| := by
  -- `(μ + λ_k)·v̂_k.re = â_k.re`, with `μ + λ_k > 0`.
  have hpos : 0 < p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by
    have hlam : 0 ≤ unitIntervalNeumannSpectrum.eigenvalue k := by
      change (0 : ℝ) ≤ (k : ℝ) ^ 2 * Real.pi ^ 2; positivity
    linarith [p.hμ]
  have hellRe : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
        (intervalNeumannResolverCoeff p u k).re =
      (intervalNeumannResolverSourceCoeff p u k).re := by
    have hcast :
        ((p.μ : ℂ) + (unitIntervalNeumannSpectrum.eigenvalue k : ℂ)) =
          (((p.μ + unitIntervalNeumannSpectrum.eigenvalue k : ℝ)) : ℂ) := by
      push_cast; ring
    have hk := congrArg Complex.re (intervalNeumannResolverCoeff_elliptic p u k)
    rw [hcast, Complex.re_ofReal_mul] at hk
    exact hk
  -- `λ_k = (kπ)²`, and `λ_k ≤ μ + λ_k`.
  have hlam : unitIntervalCosineEigenvalue k = unitIntervalNeumannSpectrum.eigenvalue k := by
    change ((k : ℝ) * Real.pi) ^ 2 = (k : ℝ) ^ 2 * Real.pi ^ 2; ring
  rw [hlam]
  -- Take absolute values: `(μ+λ_k)·|v̂_k.re| = |â_k.re|`, and `λ_k ≤ μ+λ_k`.
  have habs : (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
      |(intervalNeumannResolverCoeff p u k).re| =
      |(intervalNeumannResolverSourceCoeff p u k).re| := by
    rw [← abs_of_pos hpos, ← abs_mul, hellRe]
  have hle : unitIntervalNeumannSpectrum.eigenvalue k ≤
      p.μ + unitIntervalNeumannSpectrum.eigenvalue k := by linarith [p.hμ]
  have hvabs_nonneg : 0 ≤ |(intervalNeumannResolverCoeff p u k).re| := abs_nonneg _
  calc unitIntervalNeumannSpectrum.eigenvalue k *
          |(intervalNeumannResolverCoeff p u k).re|
      ≤ (p.μ + unitIntervalNeumannSpectrum.eigenvalue k) *
          |(intervalNeumannResolverCoeff p u k).re| :=
        mul_le_mul_of_nonneg_right hle hvabs_nonneg
    _ = |(intervalNeumannResolverSourceCoeff p u k).re| := habs

/-- **Eigenvalue-weighted resolver-coefficient summability from `ℓ¹` source.**
If the source's real cosine coefficients are absolutely summable
(`Summable (fun k => |(â_k).re|)` — equivalently the elliptic source is
`C²`-Neumann), then the `(kπ)²`-weighted resolver coefficients
`λ_k · |(v̂_k).re|` are summable.  Comparison against `|(â_k).re|` via
`resolverR_eigenWeighted_le_source`.  This is the **physical** driver for the
`C²`-engine, replacing `SourceCoeffQuadraticDecay`. -/
theorem resolverR_eigenWeighted_summable_of_sourceL1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |(intervalNeumannResolverCoeff p u k).re|) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsrc
  · have h0 : (0 : ℝ) ≤ unitIntervalCosineEigenvalue k := by
      change (0 : ℝ) ≤ ((k : ℝ) * Real.pi) ^ 2; positivity
    exact mul_nonneg h0 (abs_nonneg _)
  · exact resolverR_eigenWeighted_le_source p u k

/-- **Physical spatial `C²` of the resolver.**  The lifted resolver cosine series
`x ↦ ∑' k, (v̂_k).re · cosineMode k x` is `ContDiff ℝ 2`, given only that the
*source coefficient sequence is `ℓ¹`* — i.e. the elliptic source `ν·u^γ` is
`C²`-Neumann.  This is the elliptic-equation bootstrap `v ∈ C² ⇐ source ∈ C²`,
bypassing the spectral coefficient-decay ladder. -/
theorem resolverR_contDiff_two_of_source_l1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiff ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x) :=
  cosineCoeffSeries_contDiff_two (resolverR_eigenWeighted_summable_of_sourceL1 hsrc)

/-- **`ContDiffOn` on `[0,1]`** for the physical-route resolver cosine series. -/
theorem resolverR_contDiffOn_Icc_of_source_l1
    {p : CM2Params} {u : intervalDomainPoint → ℝ}
    (hsrc : Summable (fun k : ℕ => |(intervalNeumannResolverSourceCoeff p u k).re|)) :
    ContDiffOn ℝ 2
      (fun x : ℝ => ∑' k : ℕ,
        (intervalNeumannResolverCoeff p u k).re * cosineMode k x)
      (Set.Icc (0 : ℝ) 1) :=
  (resolverR_contDiff_two_of_source_l1 hsrc).contDiffOn

end

#print axioms resolverR_contDiff_two_of_source_l1

end ShenWork.IntervalResolverPhysicalC2
