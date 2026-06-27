# Q1117 (cron2) — `3E-nonneg` in `level0_chemDiv_timeDerivData`

Static inspection via the GitHub connector only. I did **not** run Lean locally.

## Verdict

Choose **Option A**: add the explicit hypothesis

```lean
(hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x)
```

to the chem-div time-derivative data path, and propagate it through the level-0 auto constructors.

This is the cleaner Lean engineering choice because the current proof path is already deliberately using

```lean
ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg
```

which requires nonnegativity of the input function to the heat semigroup. Supplying `u₀ ≥ 0` makes the local gap a one-line proof. By contrast, Option B is mathematically valid but requires a separate compact-in-time tube argument, a shrink of the local `δ`, and care around the endpoints because `intervalDomainLift` is a zero extension and is not the right object for joint continuity at `x = 0,1` when the trace is positive.

The downstream data already has `PositiveInitialDatum intervalDomain u₀`, and the repo already has a lemma deriving closed-interval nonnegativity from it:

```text
ShenWork.Paper2.BFormPositiveDatumNegPart.positiveInitialDatum_intervalDomainLift_nonneg
```

So Option A does not add a new mathematical assumption for the actual downstream use; it only exposes an assumption already available at the call site.

## What I checked

In `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, the theorem signature for `level0_chemDiv_timeDerivData` currently includes continuity, coefficient boundedness, positive-window strict positivity, and a positive-window upper bound, but no initial nonnegativity hypothesis:

```lean
(_hu₀_cont : Continuous u₀)
(_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
(_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
(_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
```

The open proof obligation is exactly in the branch where `intervalDomainLift u₀ y = u₀ ⟨y, hy⟩`:

```lean
have h_r_nonneg : ∀ x' : intervalDomainPoint, 0 ≤ conjugatePicardIter p u₀ 0 r x' := by
  intro x'
  simp only [conjugatePicardIter]
  apply ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg hr_pos'
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · sorry -- need 0 ≤ u₀ ⟨y,hy⟩
  · norm_num
```

The theorem is called directly by `level0ChemDivSourceData`. That constructor is then used by `level0_bFormSource_duhamelSourceTimeC1On_auto`. Code search found no compiled external use of `level0ChemDivSourceData`; `IntervalConjugateBFormSourceTower.lean` contains a future/commented level-0 call under a `sorry`.

## Caller impact for Option A

Current compiled impact is small:

1. Add `hu₀_nonneg` to `level0_chemDiv_timeDerivData`.
2. Add `hu₀_nonneg` to `level0ChemDivSourceData`, and pass it to `level0_chemDiv_timeDerivData`.
3. Add `hu₀_nonneg` to `level0_bFormSource_duhamelSourceTimeC1On_auto`, and pass it to `level0ChemDivSourceData`.

So the real caller changes are **two current call sites inside the same file**:

```text
level0ChemDivSourceData → level0_chemDiv_timeDerivData
level0_bFormSource_duhamelSourceTimeC1On_auto → level0ChemDivSourceData
```

There is also **one future tower call** to adjust when the `sorry` in `IntervalConjugateBFormSourceTower.lean` is replaced. That tower already has

```lean
(hu₀pos : PositiveInitialDatum intervalDomain u₀)
```

so it can derive the new argument locally.

The explicit `chemData` constructor

```lean
level0_bFormSource_duhamelSourceTimeC1On ... (chemData : Level0ChemDivSourceData p u₀ c T)
```

should not need a signature change because it receives prebuilt chem-div data.

## Option A patch shape

The local `sorry` fill is this:

```lean
import ShenWork.Paper2.IntervalConjugateIterSourceTower
import ShenWork.Paper2.IntervalBFormSpectralHtime
import ShenWork.Paper2.IntervalBFormNegPartStrictPosBarrier
import ShenWork.Paper2.IntervalChemDivSpatialC2
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity
import ShenWork.Paper2.IntervalResolverHighRegularity
import ShenWork.PDE.IntervalChemDivTimeDerivative

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs intervalFullSemigroupOperator)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (picardIter)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter ConjugateMildExistenceData)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledChemDivSourceCoeffs
   coupledChemDivSourceLift coupledChemicalConcentration)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)
open ShenWork.Paper2.ConjugateIterSourceTower (conjLogSourceTimeC1On_level0)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.Paper2 (PaperPositiveInitialDatum PositiveInitialDatum)
open ShenWork.IntervalDomain (intervalDomain)
open ShenWork.Paper2.HeatSemigroupHighRegularity (heatSemigroup_contDiff_four)
open ShenWork.Paper2.ChemDivSpatialC2 (chemDivSource_weakH2_of_cosineRep)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.IntervalResolverHighRegularity
  (intervalResolverLiftR intervalResolverLiftR_contDiff_four
   intervalResolverLiftR_even intervalResolverLiftR_reflect_one)
open ShenWork.PDE (intervalNeumannResolverR)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

-- Add this hypothesis to `level0_chemDiv_timeDerivData`:
--   (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x)
-- Then replace the 3E-nonneg block with:

example
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {r : ℝ} (hr_pos' : 0 < r)
    (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x) :
    ∀ x' : intervalDomainPoint, 0 ≤ conjugatePicardIter p u₀ 0 r x' := by
  intro x'
  simp only [conjugatePicardIter]
  apply ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg hr_pos'
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · exact hu₀_nonneg ⟨y, hy⟩
  · norm_num

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

If Lean does not accept the exact line because of definitional elaboration around the subtype proof, this equivalent branch is usually more robust:

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

example
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {r : ℝ} (hr_pos' : 0 < r)
    (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x) :
    ∀ x' : intervalDomainPoint, 0 ≤ conjugatePicardIter p u₀ 0 r x' := by
  intro x'
  simp only [conjugatePicardIter]
  apply ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg hr_pos'
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · simpa using hu₀_nonneg ⟨y, hy⟩
  · norm_num

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

## Suggested propagation shape

I would keep the low-level hypothesis exactly as pointwise nonnegativity, not as `PositiveInitialDatum`. That keeps `level0_chemDiv_timeDerivData` focused on the minimum fact needed by the heat-kernel positivity lemma.

Sketch of the signature/call-site changes:

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open MeasureTheory Set Filter
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomain)
open ShenWork.IntervalConjugatePicard
  (conjugatePicardIter ConjugateMildExistenceData)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)
open ShenWork.IntervalDuhamelSourceTimeC1On (DuhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledLogisticSourceCoeffs coupledChemDivSourceCoeffs)
open ShenWork.IntervalBFormSpectral (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1On)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

-- In `level0_chemDiv_timeDerivData`:
--
-- theorem level0_chemDiv_timeDerivData
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
--     (_hu₀_cont : Continuous u₀)
--     (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
--     (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x)
--     (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
--       0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
--     (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
--       intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
--     ...

-- In `level0ChemDivSourceData`:
--
-- noncomputable def level0ChemDivSourceData
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
--     (hu₀_cont : Continuous u₀)
--     (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
--     (hu₀_nonneg : ∀ x : intervalDomainPoint, 0 ≤ u₀ x)
--     (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
--       0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
--     (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
--       intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
--     Level0ChemDivSourceData p u₀ c T :=
--   let envData := level0_chemDiv_envelope_summable p hc hcT hu₀_cont hu₀_bound hpos hub
--   ...
--   let tdData := level0_chemDiv_timeDerivData p hc hcT
--     hu₀_cont hu₀_bound hu₀_nonneg hpos hub
--   ...

-- In `level0_bFormSource_duhamelSourceTimeC1On_auto`, add the same
-- `hu₀_nonneg` parameter and pass it through:
--
--     (level0ChemDivSourceData p hc hcT.le hu₀_cont hu₀_bound
--       hu₀_nonneg hpos hub)

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

## Deriving the new argument from `PositiveInitialDatum`

For the tower/final consumer, derive pointwise nonnegativity from the existing lemma on the lift:

```lean
import ShenWork.Paper2.IntervalConjugateBFormSourceTower

open Set
open ShenWork.IntervalDomain
  (intervalDomain intervalDomainPoint intervalDomainLift)
open ShenWork.Paper2 (PositiveInitialDatum)

noncomputable section

namespace ShenWork.Paper2.ConjugateBFormSourceTower

example
    {u₀ : intervalDomainPoint → ℝ}
    (hu₀pos : PositiveInitialDatum intervalDomain u₀) :
    ∀ x : intervalDomainPoint, 0 ≤ u₀ x := by
  intro x
  have hLift : 0 ≤ intervalDomainLift u₀ x.1 :=
    ShenWork.Paper2.BFormPositiveDatumNegPart
      .positiveInitialDatum_intervalDomainLift_nonneg hu₀pos x.1 x.2
  simpa [intervalDomainLift] using hLift

end ShenWork.Paper2.ConjugateBFormSourceTower
```

That is the extra argument the future tower base can pass to `level0_bFormSource_duhamelSourceTimeC1On_auto` once the current `sorry` is replaced.

## Why Option B is not the clean route here

Option B is mathematically plausible, but the Lean route is significantly more involved than the local gap suggests.

The key subtlety is that the current `hlocal_slab` proof takes

```lean
r ∈ Metric.ball s δ
```

not

```lean
r ∈ Metric.ball s δ ∩ Icc c T
```

At an endpoint `s = c` or `s = T`, no open ball around `s` is contained in `[c,T]`, so `_hpos` cannot be used directly at `r`. The current `δ = min 1 (s / 2)` only guarantees `r > 0`, not `c ≤ r ≤ T`.

To make Option B work, one has to prove a separate positive-time tube lemma around each `s ∈ Icc c T`:

```lean
import ShenWork.Paper2.IntervalConjugateLevel0BFormSourceOn

open Set Filter Topology
open scoped Topology
open ShenWork.IntervalDomain
  (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalPicardLevel0SourceTimeC1On (heatCoeff)

noncomputable section

namespace ShenWork.Paper2.ConjugateLevel0BFormSourceOn

/-- Statement shape for the Option B tube lemma.

The proof should use joint continuity of
`(t, x : intervalDomainPoint) ↦ conjugatePicardIter p u₀ 0 t x`, positivity at
`time = s` from `_hpos`, compactness of `intervalDomainPoint`, and then shrink the
main local `δ` by the produced radius.
-/
theorem optionB_needed_heat_positive_tube_statement
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    {s : ℝ} (hs : s ∈ Icc c T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ s / 2 ∧
      ∀ r ∈ Metric.ball s ρ,
        ∀ x : intervalDomainPoint,
          0 ≤ conjugatePicardIter p u₀ 0 r x := by
  -- Proof route, not a recommended replacement for Option A:
  -- 1. Define F : ℝ × intervalDomainPoint → ℝ by
  --      F q = conjugatePicardIter p u₀ 0 q.1 q.2.
  -- 2. Prove `ContinuousAt F (s, x)` for each subtype point x using
  --      `heatSemigroup_jointContDiffAt_two` plus the same cosine-series bridge
  --      already used in `level0_chemDiv_timeDerivData`.
  -- 3. Get `0 < F (s, x)` from `_hpos s hs x.1 x.2`.
  -- 4. Use compactness of `intervalDomainPoint` to turn the pointwise
  --      neighborhoods into a uniform time radius ρ.
  -- 5. Shrink ρ so `ρ ≤ s/2`, preserving the existing `r > 0` argument.
  -- This is intentionally left as a statement sketch; the point is that this is
  -- the extra infrastructure Option B requires.
  sorry

end ShenWork.Paper2.ConjugateLevel0BFormSourceOn
```

If that helper existed, the `hlocal_slab` proof would have to change from

```lean
refine ⟨min 1 (s / 2), lt_min one_pos (half_pos hs_pos), ?_, ?_, ?_⟩
```

to a shrunk radius, for example:

```lean
obtain ⟨ρ, hρ_pos, hρ_le_half, hρ_tube⟩ :=
  optionB_needed_heat_positive_tube_statement p hc _hcT
    _hu₀_cont _hu₀_bound _hpos hs

refine ⟨min (min 1 (s / 2)) ρ, ?_, ?_, ?_, ?_⟩
```

and every place that currently uses `Metric.mem_ball.mp hr` with the old `min 1 (s/2)` would need minor monotonicity rewrites. Then the `h_r_nonneg` proof would become a lookup into the tube:

```lean
have h_r_nonneg : ∀ x' : intervalDomainPoint,
    0 ≤ conjugatePicardIter p u₀ 0 r x' := by
  intro x'
  exact hρ_tube r hr_to_rho_ball x'
```

Two details make this longer in Lean than it looks on paper:

* Per-slice continuity of `S(r)u₀` is not enough. The proof needs joint continuity in `(r,x)` to compare the `r`-slice to the `s`-slice uniformly over all `x`.
* The joint-continuity object should be `ℝ × intervalDomainPoint → ℝ`, not the zero-extended `intervalDomainLift` as a function on `ℝ`, because the zero extension can be discontinuous at the endpoints when the boundary values are positive.

## Final recommendation

Use Option A now. It is local, faithful to the existing kernel-positivity route, and adds only the assumption already available from downstream `PositiveInitialDatum`.

Option B is worth doing only if you strongly want the lower-level theorem to remain true for sign-changing `u₀` whose heat semigroup becomes positive on `[c,T]`. That is a strictly weaker theorem, but it costs a new compact tube lemma and a `δ` refactor. For this specific `3E-nonneg` hole, that is not the cleanest use of proof effort.
