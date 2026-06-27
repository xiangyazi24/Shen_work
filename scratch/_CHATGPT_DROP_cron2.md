# Q1028 (cron2/cron3) — `ChemDivMixedTimeDerivClosedRepr` for heat Level0

Static repo inspection only; I did **not** run Lean.

I read:

- `ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean`
- `ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean`
- also the already-related follow-up file `ShenWork/PDE/IntervalChemDivMixedReprWitness.lean`, because it contains the concrete witness route for the constructor.

## Executive verdict

The simplest route is **not** to set

```lean
Gmix q := Function.uncurry (coupledChemDivTimeDerivativeLift p u) q
```

and then try to prove `Continuous Gmix` directly.  That would re-open the exact closed-boundary/lift-junk problem that `ChemDivMixedTimeDerivClosedRepr` was designed to isolate.

Instead, use the already committed split:

```lean
mixedAlgebra
  : ℝ →
    (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ... →
    (ℝ × ℝ → ℝ)
```

from `IntervalChemDivMixedReprConstruct.lean`, and provide the ten smooth representatives

```text
U, ∂ₜU, ∂ₓ∂ₜU, ∂ₓU,
v, ∂ₓv, ∂ₓ²v, ∂ₜv, ∂ₓ∂ₜv, ∂ₓ²∂ₜv
```

as globally continuous functions on `ℝ × ℝ`, agreeing with the actual heat/resolver fields on the closed positive-time slab.

Then set

```lean
Gmix := mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc
```

and feed the resulting `ChemDivMixedReprData` to

```lean
ShenWork.IntervalChemDivMixedReprConstruct.chemDivMixedTimeDerivClosedRepr_of_data
```

or, if using the more detailed witness bundle, feed `ChemDivMixedReprWitnessData` to

```lean
ShenWork.IntervalChemDivMixedReprWitness.chemDivMixedTimeDerivClosedRepr_of_witness
```

The existing code already proves the continuity of `mixedAlgebra` from the ten `Continuous` fields and the global floor `0 < 1 + Vc q`.

## Answer to the three concrete questions

### 1. What should `Gmix` be?

Use the explicit algebraic representative:

```lean
Gmix :=
  ShenWork.IntervalChemDivMixedReprConstruct.mixedAlgebra p.β
    Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc
```

For heat Level0, the intended representatives are the smooth cosine-series representatives, with a time cutoff if needed to make them globally continuous:

```lean
u := conjugatePicardIter p u₀ 0
```

u-side:

```lean
cHeat k t :=
  Real.exp (-t * unitIntervalCosineEigenvalue k) *
    cosineCoeffs (intervalDomainLift u₀) k

Uc    := valueSeriesRep cHeat
Uxc   := gradSeriesRep cHeat
Utc   := iterateDtValue cHeat       -- sums deriv (cHeat k) t · cos(kπx)
Utxc  := iterateDtGrad cHeat        -- sums deriv (cHeat k) t · (-(kπ) sin(kπx))
```

v-side:

```lean
Vc    := valueSeriesRep (resolverTimeCoeff p u)
Vxc   := gradSeriesRep (resolverTimeCoeff p u)
Vxxc  := grad2SeriesRep (resolverTimeCoeff p u)
Vtc   := resolverDtValue p u
Vtxc  := resolverDtGrad p u
Vtxxc := resolverDtGrad2 p u
```

where the names `valueSeriesRep`, `gradSeriesRep`, `grad2SeriesRep`, `iterateDtValue`, `iterateDtGrad`, `resolverDtValue`, `resolverDtGrad`, and `resolverDtGrad2` are in

```lean
ShenWork.IntervalChemDivMixedReprWitness
```

For the heat-only direct route, these same definitions should be used, but the `Continuous`/agreement fields should be proved directly from heat/resolver coefficient estimates rather than from `PhysicalResolverJointC2Data`.

A practical point: because `ChemDivMixedTimeDerivClosedRepr` wants **global** `Continuous Gmix`, and raw heat coefficients `exp(-t λ_k)` blow up as `t → -∞`, the robust Level0 construction should use a smooth time cutoff.  For a positive slab

```lean
τ > 0,   δ = min 1 (τ / 2),   L := τ - δ
```

we have `0 < L`.  Choose a cutoff that equals `1` on the slab and kills the series near nonpositive time, for example

```lean
φ t := smoothRightCutoff (L / 4) (L / 2) t
```

using the cutoff API imported in `IntervalHeatSemigroupHighRegularity.lean`:

```lean
smoothRightCutoff
smoothRightCutoff_contDiff
smoothRightCutoff_eq_zero_of_le
smoothRightCutoff_eq_one_of_ge
smoothRightCutoff_eventually_eq_one
```

Then define the actual global reps as `φ(t)` times the corresponding raw series reps.  On the closed slab, `L ≤ t`, hence `(L / 2) ≤ t`, so `smoothRightCutoff_eq_one_of_ge` gives `φ t = 1`, and the reps agree with the raw heat/resolver fields there.

### 2. How to prove `Continuous Gmix`?

Do **not** prove it by differentiating the committed lift.  Use the theorem already written for this purpose:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (D : ChemDivMixedReprData p u τ δ) :
    ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Inside this theorem, the proof constructs

```lean
mixedAlgebra p.β D.Uc D.Utc D.Utxc D.Uxc
  D.Vc D.Vxc D.Vxxc D.Vtc D.Vtxc D.Vtxxc
```

and proves continuity by:

```lean
have hB : Continuous (fun q : ℝ × ℝ => 1 + D.Vc q) :=
  continuous_const.add D.cont_Vc
have hBne : ∀ q : ℝ × ℝ, (1 + D.Vc q) ≠ 0 := fun q => ne_of_gt (D.floor q)
have hpb : Continuous (fun q : ℝ × ℝ => (1 + D.Vc q) ^ p.β) :=
  hB.rpow_const (fun q => Or.inl (hBne q))
```

and the analogous denominator facts for `p.β + 1` and `p.β + 2`, followed by `Continuous.add`, `Continuous.sub`, `Continuous.mul`, and `Continuous.div`.

So the proof obligation for Level0 is **only** to provide the ten `Continuous` fields and the floor field of `ChemDivMixedReprData` (or `ChemDivMixedReprWitnessData`).

For heat Level0, the u-side continuous reps should come from heat-series estimates:

```lean
ShenWork.Paper2.HeatSemigroupHighRegularity.heatSemigroup_contDiff_four
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

The first gives fixed-positive-time spatial `C⁴`; the second gives joint `(t,x)` `C²` locally at positive times using the committed smooth cutoff route.

For the resolver side, the direct heat route should use the resolver coefficient series and the high-regularity resolver theorem:

```lean
ShenWork.Paper2.IntervalResolverHighRegularity.intervalResolverLiftR_contDiff_four
```

for fixed-time spatial regularity, plus direct time-regularity of the heat-resolver coefficients.  The existing physical route packages this as

```lean
PhysicalResolverJointC2Data
resolverTimeCoeff
resolverDtValue_continuous
resolverDtGrad_continuous
resolverDtGrad2_continuous
```

but if the goal is to avoid `PhysicalResolverJointC2Data`, then reproduce those three continuity proofs with the heat-specific coefficient bounds instead of calling the physical bundle.

### 3. How to prove agreement on the closed slab?

Use the witness route's split.  The closed slab includes `x = 0, 1`, so a pure interior chain-rule proof is insufficient.

The existing file `IntervalChemDivMixedReprWitness.lean` provides:

```lean
theorem fluxTimeDeriv_hasDerivAt_space
```

which proves the interior algebraic spatial derivative identity for the flux-time derivative.  It also provides:

```lean
theorem witness_agree
```

which splits `x ∈ Icc 0 1` into:

1. `x ∈ Ioo 0 1`: use `fluxTimeDeriv_hasDerivAt_space` and the rep/value/derivative fields;
2. `x = 0` or `x = 1`: use the supplied `boundary_agree` field.

So the heat Level0 agreement proof should be:

```lean
agree := fun t ht x hx =>
  ShenWork.IntervalChemDivMixedReprWitness.witness_agree W t ht x hx
```

where `W : ChemDivMixedReprWitnessData p (conjugatePicardIter p u₀ 0) τ δ` is the heat-specific witness bundle.

The boundary leg for heat should be proved from the Neumann/sin-series facts: the spatial gradient representatives are sine series, hence vanish at `x = 0,1`; the zero-extension/junk derivative of the lifted endpoint is also the Lean value used by `coupledChemDivTimeDerivativeLift`.  This is exactly why `ChemDivMixedReprWitnessData` has the separate field

```lean
boundary_agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
  coupledChemDivTimeDerivativeLift p u t x =
    mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

## Concrete Lean skeleton: constructor from closed reps

This is the minimal code I would add for the Level0 heat route.  It avoids `PhysicalResolverJointC2Data` and states exactly the heat-specific analytic data still needed.

```lean
import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct
open ShenWork.IntervalChemDivMixedReprWitness
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.Level0HeatMixedRepr

/-- Heat Level0 wrapper: once the ten closed-slab smooth representatives are built,
`ChemDivMixedTimeDerivClosedRepr` follows from the generic `mixedAlgebra`
constructor. -/
theorem chemDivMixedTimeDerivClosedRepr_level0_of_reprData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {τ δ : ℝ}
    (D : ChemDivMixedReprData p (conjugatePicardIter p u₀ 0) τ δ) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ δ := by
  exact chemDivMixedTimeDerivClosedRepr_of_data D

/-- Same wrapper using the more concrete witness bundle.  This is usually the most
convenient endpoint because `witness_agree` already handles the interior/boundary
split for the closed spatial interval. -/
theorem chemDivMixedTimeDerivClosedRepr_level0_of_witness
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p (conjugatePicardIter p u₀ 0) τ δ) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ δ := by
  exact chemDivMixedTimeDerivClosedRepr_of_witness W

end ShenWork.Paper2.Level0HeatMixedRepr
```

This code is intentionally small: it uses the committed generic constructors and keeps the actual heat analytic work in the construction of `D` or `W`.

## More concrete heat-specific witness shape

For `τ > 0` and

```lean
δ = min 1 (τ / 2)
```

let

```lean
u := conjugatePicardIter p u₀ 0
L := τ - δ
φ t := smoothRightCutoff (L / 4) (L / 2) t
```

Then `0 < L`, and for `t ∈ Icc (τ - δ) (τ + δ)`, `φ t = 1` by `smoothRightCutoff_eq_one_of_ge`.

The witness should instantiate the ten representatives as cutoff-patched versions of the raw heat/resolver series:

```lean
Uc    q := φ q.1 * valueSeriesRep cHeat q
Utc   q := φ q.1 * iterateDtValue cHeat q
Utxc  q := φ q.1 * iterateDtGrad cHeat q
Uxc   q := φ q.1 * gradSeriesRep cHeat q

Vc    q := φ q.1 * valueSeriesRep (resolverTimeCoeff p u) q
Vxc   q := φ q.1 * gradSeriesRep (resolverTimeCoeff p u) q
Vxxc  q := φ q.1 * grad2SeriesRep (resolverTimeCoeff p u) q
Vtc   q := φ q.1 * resolverDtValue p u q
Vtxc  q := φ q.1 * resolverDtGrad p u q
Vtxxc q := φ q.1 * resolverDtGrad2 p u q
```

where

```lean
cHeat k t :=
  Real.exp (-t * unitIntervalCosineEigenvalue k) *
    cosineCoeffs (intervalDomainLift u₀) k
```

On the slab, all `φ q.1` simplify to `1`, so the existing witness agreement proof applies exactly as in `witness_agree`.

Outside the slab, the cutoff makes the functions globally continuous and prevents the backward-heat blowup at negative time.  This is the same reason `heatSemigroup_jointContDiffAt_two` in `IntervalHeatSemigroupHighRegularity.lean` uses the smooth cutoff series.

## Recommended theorem target

The theorem I would actually aim to prove next is not a monolithic direct proof of `ChemDivMixedTimeDerivClosedRepr`.  I would first prove a heat-specific witness-data theorem:

```lean
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
open ShenWork.IntervalChemDivMixedReprWitness
open Set Filter Topology

noncomputable section

namespace ShenWork.Paper2.Level0HeatMixedRepr

/-- Target heat-specific witness bundle.  This is the honest analytic core:
construct the ten globally continuous cutoff-patched series representatives and
prove their closed-slab agreement/boundary facts. -/
theorem level0_heat_mixedReprWitnessData
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ δ : ℝ}
    (hτ : 0 < τ)
    (hδ : δ = min 1 (τ / 2))
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    -- plus the heat positivity/floor and resolver coefficient time-regularity data,
    -- proved directly from heat smoothing, not via PhysicalResolverJointC2Data:
    (Hreps : True) :
    ChemDivMixedReprWitnessData p (conjugatePicardIter p u₀ 0) τ δ := by
  -- 1. Define L := τ - δ and φ := smoothRightCutoff (L/4) (L/2).
  -- 2. Prove 0 < L from hτ and hδ.
  -- 3. Define cHeat k t := exp(-t λ_k) * heatCoeff u₀ k.
  -- 4. Fill Uc/Utc/Utxc/Uxc from cutoff-patched heat reps.
  -- 5. Fill Vc/Vxc/Vxxc/Vtc/Vtxc/Vtxxc from cutoff-patched resolver reps.
  -- 6. Continuous fields:
  --      u-side: heat exponential estimates / heatSemigroup_jointContDiffAt_two style cutoff bounds;
  --      v-side: intervalResolverLiftR_contDiff_four + time-coefficient analogues.
  -- 7. Agreement fields: cutoff = 1 on Icc (τ-δ) (τ+δ), then cosine-series identities.
  -- 8. Interior derivative fields: valueRep_hasDerivAt_grad, gradRep_hasDerivAt_grad2,
  --      heat analogues for slopeSlice and resolverDt fields.
  -- 9. boundary_agree: Neumann sin-series vanishing at x=0,1 plus endpoint junk-value convention.
  sorry

/-- Final Level0 heat closed representative, after the witness bundle is available. -/
theorem level0_heat_chemDivMixedTimeDerivClosedRepr
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ δ : ℝ}
    (hτ : 0 < τ)
    (hδ : δ = min 1 (τ / 2))
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    (Hreps : True) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ δ := by
  exact chemDivMixedTimeDerivClosedRepr_of_witness
    (level0_heat_mixedReprWitnessData
      (p := p) (u₀ := u₀) (M₀ := M₀) (τ := τ) (δ := δ)
      hτ hδ hu₀_bound hu₀_cont Hreps)

end ShenWork.Paper2.Level0HeatMixedRepr
```

The `Hreps : True` placeholder should be replaced by the actual heat-specific coefficient regularity/floor data as it is developed.  The point is that the final theorem should be a one-line call to `chemDivMixedTimeDerivClosedRepr_of_witness`; all real work belongs in `level0_heat_mixedReprWitnessData`.

## Why not just use joint C² of flux components?

A pointwise `ContDiffAt ℝ 2` story is enough for the **interior** `x ∈ Ioo 0 1`, but the target agreement is on the **closed** slab `Icc 0 1`.  The endpoints are exactly where `intervalDomainLift` uses the zero-extension/junk derivative convention.  The existing design already reflects this:

- `fluxTimeDeriv_hasDerivAt_space` proves the interior algebraic derivative.
- `ChemDivMixedReprWitnessData.boundary_agree` handles `x = 0,1` separately.
- `witness_agree` combines them.
- `chemDivMixedTimeDerivClosedRepr_of_witness` packages everything into `ChemDivMixedTimeDerivClosedRepr`.

So the most Lean-friendly construction is:

```text
cutoff-patched continuous spectral reps
  → ChemDivMixedReprWitnessData
  → witness_agree
  → ChemDivMixedReprData
  → chemDivMixedTimeDerivClosedRepr_of_data
```

rather than:

```text
joint C² of raw lifted flux components
  → try to prove closed-slab ContinuousOn/agreement directly
```

The latter will run straight into endpoint lift derivatives again.
