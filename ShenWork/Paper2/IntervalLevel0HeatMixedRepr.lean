import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalChemDivMixedReprWitness
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalResolverSpectralJointC2Cutoff
  (smoothRightCutoff smoothRightCutoff_contDiff smoothRightCutoff_eq_one_of_ge)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.Level0HeatMixedRepr

/-- Heat Level0 cosine coefficient:
`S(t)u₀ = ∑ exp(-t λ_k) û₀_k cos(kπx)`.

This is the u-side coefficient family used by the smooth representative. -/
def level0HeatCoeff (u₀ : intervalDomainPoint → ℝ) : ℕ → ℝ → ℝ :=
  fun k t =>
    Real.exp (-t * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k

/-- Left endpoint of the canonical positive-time slab with
`δ = min 1 (τ/2)`. -/
def canonicalSlabLeft (τ : ℝ) : ℝ :=
  τ - min 1 (τ / 2)

/-- For `τ > 0`, the left endpoint `τ - min 1 (τ/2)` is positive. -/
lemma canonicalSlabLeft_pos {τ : ℝ} (hτ : 0 < τ) :
    0 < canonicalSlabLeft τ := by
  unfold canonicalSlabLeft
  have hmin_le : min (1 : ℝ) (τ / 2) ≤ τ / 2 := min_le_right _ _
  linarith

/-- Smooth cutoff used for the global representatives.  It is `1` on the whole
canonical slab and kills the representative near nonpositive times. -/
def level0SlabCutoff (τ : ℝ) : ℝ → ℝ :=
  smoothRightCutoff (canonicalSlabLeft τ / 4) (canonicalSlabLeft τ / 2)

/-- The cutoff is identically `1` on the canonical closed slab. -/
lemma level0SlabCutoff_eq_one_on_slab {τ t : ℝ} (hτ : 0 < τ)
    (ht : t ∈ Icc (τ - min (1 : ℝ) (τ / 2)) (τ + min (1 : ℝ) (τ / 2))) :
    level0SlabCutoff τ t = 1 := by
  have hLpos : 0 < canonicalSlabLeft τ := canonicalSlabLeft_pos hτ
  unfold level0SlabCutoff
  apply smoothRightCutoff_eq_one_of_ge
  · linarith
  · have htL : canonicalSlabLeft τ ≤ t := by
      simpa [canonicalSlabLeft] using ht.1
    linarith

/-- Multiply a raw spectral representative by the Level0 time cutoff. -/
def cutoffRep (τ : ℝ) (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun q => level0SlabCutoff τ q.1 * F q

/-- The actual global smooth representative `Gmix` for heat Level0.

It is `mixedAlgebra` applied to cutoff-patched smooth cosine-series reps.  On the
positive slab the cutoff is `1`, so this agrees with the raw mixed derivative;
globally it is continuous because the cutoff suppresses the bad negative-time heat
coefficients. -/
def level0HeatGmix (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (τ : ℝ) :
    ℝ × ℝ → ℝ :=
  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
  let cH : ℕ → ℝ → ℝ := level0HeatCoeff u₀
  mixedAlgebra p.β
    (cutoffRep τ (valueSeriesRep cH))
    (cutoffRep τ (iterateDtValue cH))
    (cutoffRep τ (iterateDtGrad cH))
    (cutoffRep τ (gradSeriesRep cH))
    (cutoffRep τ (valueSeriesRep (resolverTimeCoeff p u)))
    (cutoffRep τ (gradSeriesRep (resolverTimeCoeff p u)))
    (cutoffRep τ (grad2SeriesRep (resolverTimeCoeff p u)))
    (cutoffRep τ (resolverDtValue p u))
    (cutoffRep τ (resolverDtGrad p u))
    (cutoffRep τ (resolverDtGrad2 p u))

/-- Heat Level0 construction of `ChemDivMixedTimeDerivClosedRepr`.

The proof uses the existing `chemDivMixedTimeDerivClosedRepr_of_data` constructor.
The only remaining work is the expected analytic work:

* continuity of the ten cutoff-patched reps;
* global floor `0 < 1 + Vc`;
* closed-slab agreement, with endpoints handled by the smooth cosine/sin-series
  Neumann boundary facts rather than by the raw `intervalDomainLift` derivative.
-/
theorem chemDivMixedTimeDerivClosedRepr_level0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ (min (1 : ℝ) (τ / 2)) := by
  classical
  let δ : ℝ := min (1 : ℝ) (τ / 2)
  change ChemDivMixedTimeDerivClosedRepr
    p (conjugatePicardIter p u₀ 0) τ δ

  let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
  let cH : ℕ → ℝ → ℝ := level0HeatCoeff u₀

  -- The ten global representatives.  These are the cutoff-patched cosine-series
  -- representatives; on the slab they reduce to the raw heat/resolver series.
  let Uc    : ℝ × ℝ → ℝ := cutoffRep τ (valueSeriesRep cH)
  let Utc   : ℝ × ℝ → ℝ := cutoffRep τ (iterateDtValue cH)
  let Utxc  : ℝ × ℝ → ℝ := cutoffRep τ (iterateDtGrad cH)
  let Uxc   : ℝ × ℝ → ℝ := cutoffRep τ (gradSeriesRep cH)
  let Vc    : ℝ × ℝ → ℝ := cutoffRep τ (valueSeriesRep (resolverTimeCoeff p u))
  let Vxc   : ℝ × ℝ → ℝ := cutoffRep τ (gradSeriesRep (resolverTimeCoeff p u))
  let Vxxc  : ℝ × ℝ → ℝ := cutoffRep τ (grad2SeriesRep (resolverTimeCoeff p u))
  let Vtc   : ℝ × ℝ → ℝ := cutoffRep τ (resolverDtValue p u)
  let Vtxc  : ℝ × ℝ → ℝ := cutoffRep τ (resolverDtGrad p u)
  let Vtxxc : ℝ × ℝ → ℝ := cutoffRep τ (resolverDtGrad2 p u)

  -- Continuity of the reps.  Each proof follows the existing pattern in
  -- `IntervalChemDivMixedReprWitness.lean`, but with the heat-specific coefficient
  -- family `cH` and the smooth time cutoff.
  have hUc : Continuous Uc := by
    -- `smoothRightCutoff_contDiff.continuous` times
    -- `valueSeriesRep_continuous` for `cH`.
    -- The coefficient bound is exponential on positive time and cutoff-killed
    -- outside, exactly as in `cutoffHeatSeries_contDiff_two`.
    sorry
  have hUtc : Continuous Utc := by
    -- Same as `iterateDtValue_continuous`, but for
    -- `deriv (level0HeatCoeff u₀ k)` directly.
    sorry
  have hUtxc : Continuous Utxc := by
    -- Same as `iterateDtGrad_continuous`, using the eigenvalue-weighted heat
    -- derivative envelope.
    sorry
  have hUxc : Continuous Uxc := by
    -- Same as `gradSeriesRep_continuous` for the heat value coefficient family.
    sorry
  have hVc : Continuous Vc := by
    -- Resolver value rep continuity from heat-level resolver coefficient bounds;
    -- this is the direct replacement for using `PhysicalResolverJointC2Data`.
    sorry
  have hVxc : Continuous Vxc := by
    -- Resolver gradient rep continuity.
    sorry
  have hVxxc : Continuous Vxxc := by
    -- Resolver second-gradient rep continuity.
    sorry
  have hVtc : Continuous Vtc := by
    -- Resolver time-derivative value rep continuity (`deriv resolverTimeCoeff`).
    sorry
  have hVtxc : Continuous Vtxc := by
    -- Resolver mixed time/spatial-gradient rep continuity.
    sorry
  have hVtxxc : Continuous Vtxxc := by
    -- Resolver second-spatial-gradient of the time derivative.
    sorry

  -- Global floor for the denominator.  The intended proof uses positivity of the
  -- heat semigroup Level0 resolver and the fact that the cosine representative
  -- agrees with the resolver on `[0,1]`, plus the cutoff construction.  If using a
  -- cutoff that can make `Vc = 0` outside the positive window, the floor is
  -- immediate there; on the slab it is the resolver positivity floor.
  have hfloor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q := by
    sorry

  -- Closed-slab agreement.  On the slab, `level0SlabCutoff τ t = 1`, so all ten
  -- representatives reduce to their raw cosine-series representatives.  The
  -- interior proof is the algebraic chain rule from `mixedAlgebra`; the endpoints
  -- are handled by the Neumann/sin-series boundary facts, not by differentiating
  -- the raw `intervalDomainLift` at the boundary.
  have hagree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x =
        mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x) := by
    intro t ht x hx
    have hcut : level0SlabCutoff τ t = 1 := by
      -- Rewrite the local `δ` back to `min 1 (τ/2)` for the cutoff lemma.
      have ht' : t ∈ Icc (τ - min (1 : ℝ) (τ / 2))
          (τ + min (1 : ℝ) (τ / 2)) := by
        simpa [δ] using ht
      exact level0SlabCutoff_eq_one_on_slab hτ ht'
    -- After `hcut`, all reps simplify to the raw spectral representatives.
    -- Interior `x ∈ Ioo 0 1`: use the spatial derivative of the flux-time
    -- derivative, i.e. the `mixedAlgebra` product/quotient/rpow chain rule.
    -- Boundary `x = 0 ∨ x = 1`: use the Neumann sine-series endpoint vanishing,
    -- matching Lean's endpoint derivative/junk convention for `intervalDomainLift`.
    -- This is exactly the split implemented by
    -- `IntervalChemDivMixedReprWitness.witness_agree`.
    sorry

  let D : ChemDivMixedReprData p u τ δ :=
    { Uc := Uc
      Utc := Utc
      Utxc := Utxc
      Uxc := Uxc
      Vc := Vc
      Vxc := Vxc
      Vxxc := Vxxc
      Vtc := Vtc
      Vtxc := Vtxc
      Vtxxc := Vtxxc
      cont_Uc := hUc
      cont_Utc := hUtc
      cont_Utxc := hUtxc
      cont_Uxc := hUxc
      cont_Vc := hVc
      cont_Vxc := hVxc
      cont_Vxxc := hVxxc
      cont_Vtc := hVtc
      cont_Vtxc := hVtxc
      cont_Vtxxc := hVtxxc
      floor := hfloor
      agree := hagree }

  -- This theorem chooses
  --   Gmix = mixedAlgebra p.β D.Uc D.Utc D.Utxc D.Uxc
  --                    D.Vc D.Vxc D.Vxxc D.Vtc D.Vtxc D.Vtxxc
  -- and proves its global continuity from the fields above.
  exact chemDivMixedTimeDerivClosedRepr_of_data D

/-- The theorem above makes the intended `Gmix` explicit. -/
example {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {τ : ℝ} :
    level0HeatGmix p u₀ τ =
      let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
      let cH : ℕ → ℝ → ℝ := level0HeatCoeff u₀
      mixedAlgebra p.β
        (cutoffRep τ (valueSeriesRep cH))
        (cutoffRep τ (iterateDtValue cH))
        (cutoffRep τ (iterateDtGrad cH))
        (cutoffRep τ (gradSeriesRep cH))
        (cutoffRep τ (valueSeriesRep (resolverTimeCoeff p u)))
        (cutoffRep τ (gradSeriesRep (resolverTimeCoeff p u)))
        (cutoffRep τ (grad2SeriesRep (resolverTimeCoeff p u)))
        (cutoffRep τ (resolverDtValue p u))
        (cutoffRep τ (resolverDtGrad p u))
        (cutoffRep τ (resolverDtGrad2 p u)) := by
  rfl

end ShenWork.Paper2.Level0HeatMixedRepr
