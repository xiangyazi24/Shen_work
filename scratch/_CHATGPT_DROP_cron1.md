# Q1618 (cron1 / cron3) -- `IntervalLevel0HeatMixedRepr.lean` sorry census

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The user prompt was:

```text
Q1618 (cron1): cron3 /tmp/q_cron3.txt
```

The literal local path `/tmp/q_cron3.txt` is not accessible through the GitHub connector. I therefore interpreted this as the earlier `cron3` task: inspect

```text
ShenWork/Paper2/IntervalLevel0HeatMixedRepr.lean
```

and count/classify its `sorry` lines. I used the GitHub connector only. I did not use Python, the sandbox, `/mnt/data`, or a sandbox download link.

One branch wrinkle: fetching `ShenWork/Paper2/IntervalLevel0HeatMixedRepr.lean` at ref `chatgpt-scratch` returned `Not Found`, so the source inspection below is for the repository default branch. The report itself is committed on `chatgpt-scratch`, as requested.

## Import context

The inspected file begins with:

```lean
import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalChemDivMixedReprWitness
import ShenWork.PDE.IntervalResolverJointC2PhysicalConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff
import ShenWork.Paper2.IntervalConjugatePicard
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity
```

The file declares namespace:

```lean
namespace ShenWork.Paper2.Level0HeatMixedRepr
```

## Important import-status correction

The file itself still has a header saying:

```text
DEAD CODE: This file is not imported by any other file in the repo.
Its sorry terms are not on any critical path.
```

That header is stale on the default branch I inspected. The root file `ShenWork.lean` currently ends by importing:

```lean
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr
```

So, on the current default branch, the file is in the root build closure. The `sorry` terms should not be treated as harmless dead-code placeholders unless the branch being built differs from the default branch I inspected.

## Count

There are exactly **12** `sorry` lines in `ShenWork/Paper2/IntervalLevel0HeatMixedRepr.lean`.

All 12 are inside the theorem:

```lean
theorem chemDivMixedTimeDerivClosedRepr_level0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ (min (1 : ℝ) (τ / 2)) := by
```

There are no other `sorry` lines elsewhere in the file.

## Sorry list and classification

| # | Source line | Local obligation | Comment-obligation name / description | Classification |
|---:|---:|---|---|---|
| 1 | 139 | `hUc : Continuous Uc` | `smoothRightCutoff_contDiff.continuous` times `valueSeriesRep_continuous` for `cH`; heat coefficient bound exponential on positive time and cutoff-killed outside, as in `cutoffHeatSeries_contDiff_two`. | Mechanical / spectral-cutoff wiring, assuming the heat-series continuity API is already available. |
| 2 | 143 | `hUtc : Continuous Utc` | Same as `iterateDtValue_continuous`, but for `deriv (level0HeatCoeff u₀ k)` directly. | Mechanical spectral calculus: explicit derivative of `exp (-t λ_k) * coeff`. Not a new PDE estimate. |
| 3 | 147 | `hUtxc : Continuous Utxc` | Same as `iterateDtGrad_continuous`, using the eigenvalue-weighted heat derivative envelope. | Mostly mechanical once the weighted heat envelope is packaged; the estimate is explicit but not a pure `simp` proof. |
| 4 | 150 | `hUxc : Continuous Uxc` | Same as `gradSeriesRep_continuous` for the heat value coefficient family. | Mechanical / spectral-cutoff wiring. |
| 5 | 154 | `hVc : Continuous Vc` | Resolver value rep continuity from heat-level resolver coefficient bounds; direct replacement for using `PhysicalResolverJointC2Data`. | Genuine analytic/data-interface gap. Need the resolver coefficient continuity and summability package for this exact Level0/conjugate iterate. |
| 6 | 157 | `hVxc : Continuous Vxc` | Resolver gradient rep continuity. | Genuine analytic/data-interface gap. Needs eigenvalue-weighted resolver bounds. |
| 7 | 160 | `hVxxc : Continuous Vxxc` | Resolver second-gradient rep continuity. | Genuine analytic/data-interface gap. Needs second spatial weighted resolver bounds. |
| 8 | 163 | `hVtc : Continuous Vtc` | Resolver time-derivative value rep continuity, i.e. `deriv resolverTimeCoeff`. | Genuine analytic/data-interface gap. Needs time-derivative coefficient series continuity. |
| 9 | 166 | `hVtxc : Continuous Vtxc` | Resolver mixed time/spatial-gradient rep continuity. | Genuine analytic/data-interface gap. Needs time-derivative plus spatial-weighted resolver bounds. |
| 10 | 169 | `hVtxxc : Continuous Vtxxc` | Resolver second-spatial-gradient of the time derivative. | Genuine analytic/data-interface gap. Strongest resolver coefficient regularity obligation in this file. |
| 11 | 177 | `hfloor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q` | Global denominator floor; intended proof uses positivity of the heat semigroup Level0 resolver, agreement of cosine representative with resolver on `[0,1]`, and cutoff construction. | Genuine analytic/order gap. Also needs a global-in-`x` reduction/periodic-reflection argument, since the goal quantifies over all `q : ℝ × ℝ`, not just `x ∈ [0,1]`. |
| 12 | 201 | `hagree : ...` | Closed-slab agreement: cutoff is `1` on the slab, raw spectral reps remain, interior uses `mixedAlgebra` chain rule, endpoints use Neumann/sin-series boundary facts; comment says this is exactly the split implemented by `IntervalChemDivMixedReprWitness.witness_agree`. | Mechanical witness assembly **after** the missing analytic witness fields are available. As written, it cannot follow from the ten continuity facts plus `hfloor` alone. |

## Mechanical vs genuine summary

Strictly separating “new analysis” from “wiring once the analytic bundle exists”:

* **Mechanical / spectral-cutoff wiring:** lines 139, 143, 147, 150. These are the four heat-side continuity representatives `Uc`, `Utc`, `Utxc`, `Uxc`. They still require invoking the right spectral-continuity lemmas and explicit heat coefficient envelopes, but the analysis is the elementary heat exponential/eigenvalue estimate already suggested by the comments.
* **Genuine analytic/data-interface gaps:** lines 154, 157, 160, 163, 166, 169, 177. These are the six resolver-side continuity representatives plus the global floor. They require a committed Level0 resolver coefficient package or an instantiation of the existing `PhysicalResolverJointC2Data`/bounded-weight machinery for `u = conjugatePicardIter p u₀ 0`.
* **Mechanical agreement assembly, conditional on data:** line 201. The chain-rule and endpoint split should be delegated to `IntervalChemDivMixedReprWitness.witness_agree`, but only after constructing a `ChemDivMixedReprWitnessData` bundle with all value-match, `HasDerivAt`, boundary, continuity, and floor fields.

So the compact count is:

```text
12 total sorry lines
  4 heat-side continuity / spectral-cutoff wiring
  6 resolver-side continuity / genuine analytic data-interface gaps
  1 global floor / genuine analytic-order gap
  1 closed-slab agreement / mechanical witness assembly after analytic fields
```

## Recommended closing route

The file already imports `IntervalChemDivMixedReprWitness`, whose witness layer is designed to avoid manually proving `hagree` in this theorem. The cleaner route is not to fill `hagree` directly from the current local context. Instead:

1. Build a Level0-specific `ChemDivMixedReprWitnessData p u τ δ` with
   `u := conjugatePicardIter p u₀ 0` and the ten cutoff representatives already defined in this file.
2. Discharge the four heat-side continuity fields by a small Level0 heat coefficient API for
   `level0HeatCoeff u₀ k t = exp (-t * λ_k) * cosineCoeffs (intervalDomainLift u₀) k`.
3. Discharge the six resolver-side continuity fields by reusing or specializing the existing resolver bounded-weight/joint-`C²` coefficient machinery for the same `u`.
4. Prove the global floor for `Vc`; be careful that the goal is over all `x : ℝ`, so positivity on `[0,1]` alone is not enough unless the cosine representative is reduced by periodic/reflection symmetry.
5. Replace the local `hagree` proof with `witness_agree W t ht x hx`, where `W` is the constructed witness bundle.
6. Feed `witnessData W` or `chemDivMixedTimeDerivClosedRepr_of_witness W` into the final constructor instead of manually assembling only `ChemDivMixedReprData` fields.

The main structural issue is that `ChemDivMixedReprData` only asks for continuities, `floor`, and `agree`, but proving `agree` needs the richer witness facts. The already-existing `ChemDivMixedReprWitnessData` layer is exactly the right intermediate abstraction.
