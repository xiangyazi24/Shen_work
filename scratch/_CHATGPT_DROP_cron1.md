# Q865 / cron1: wire `heatResolverJointContDiffAt_two` into Level0 2A-sup?

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Refs inspected:

- `main` for `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` and `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`.
- `chatgpt-scratch` for the existing physical resolver joint-C² producer file `ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean`.

Note: the connector returned `404` for `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` at `chatgpt-scratch`, so the Level0 diagnosis below is based on the `main` snapshot. The requested scratch file itself was updated on `chatgpt-scratch`.

## Verdict

**Yes — wire it now**, but do not wire only the theorem

```lean
heatResolverJointContDiffAt_two
```

as if it were sufficient by itself.

The wiring is mathematically correct and it is a good idea to do it now, even though the upstream theorem still contains sorry through

```lean
heatSemigroup_level0_resolverJointC2Data
```

The sorry will propagate, but the downstream Level0 wiring becomes honest and testable.

However, there are two important caveats:

1. `heatResolverJointContDiffAt_two` gives joint `C²` only for the resolver **value** `v`.
2. The flux composition theorem also needs joint `C²` for the resolver **spatial gradient** `∂ₓv`.

So the immediate wiring should first expose a tiny heat-level gradient wrapper, then use both wrappers in `2A-sup`.

## Why value-only is not enough

The existing flux factor theorem is:

```lean
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x))
    (hgradv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
          q.2)
      (s, x))
    (hbase : 0 <
      1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

Thus `heatResolverJointContDiffAt_two` supplies `hv`, but **not** `hgradv`.

The good news: the lower-level theorem already exists:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

So add the heat-level wrapper:

```lean
namespace ShenWork.Paper2.HeatResolverJointRegularity

open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalConjugatePicard (conjugatePicardIter)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemicalConcentration)
open ShenWork.IntervalResolverJointC2PhysicalConcrete
  (PhysicalResolverJointC2Data coupledChemical_grad_jointContDiffAt_two)

/-- Joint `ContDiffAt ℝ 2` of the resolver spatial-gradient factor at the heat
semigroup base iterate.  This is the gradient companion to
`heatResolverJointContDiffAt_two`. -/
theorem heatResolverGradJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      deriv (intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1)) q.2) (s₀, x₀) := by
  obtain ⟨Bt, hBt⟩ := heatSemigroup_level0_resolverJointC2Data
    (p := p) hu₀_bound hu₀_cont
  exact coupledChemical_grad_jointContDiffAt_two hBt hx₀

end ShenWork.Paper2.HeatResolverJointRegularity
```

This wrapper is pure wiring. It has the same upstream sorry dependency as `heatResolverJointContDiffAt_two`.

## What `2A-sup` currently needs

Inside `level0_chemDiv_envelope_summable`, the relevant target is currently:

```lean
have hsup_bound : ∃ (Msup : ℝ), 0 ≤ Msup ∧
    ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup := by
  ...
  sorry -- [SUB-SORRY 2A-core / 2A-sup]
```

The comments around that sorry are already the right proof plan:

- boundary values are zero via `hbdry_zero`;
- interior values agree with the smooth flux-divergence representative;
- the uniform bound comes from compactness once the representative is jointly continuous on `[c,T] × [0,1]`.

So yes, `heatSemigroup_jointContDiffAt_two` plus `heatResolverJointContDiffAt_two` plus the gradient companion above are exactly the missing inputs for the interior flux-continuity part.

## The correct wiring shape

For `s ∈ Icc c T` and `x ∈ Ioo 0 1`:

```lean
have hs_pos : 0 < s := lt_of_lt_of_le hc hs.1
have hs_gt_c : c < s := lt_of_lt_of_le hc hs.1 -- if the theorem wants strict `c < s`
```

Actually, if `s = c`, then `c < s` is false.  For points at the left endpoint of the window, use a smaller cutoff parameter, for example `c / 2`:

```lean
have hc2 : 0 < c / 2 := by positivity
have hs_gt_c2 : c / 2 < s := by nlinarith [hc, hs.1]
```

Then:

```lean
have hu_series : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
    ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
      cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s, x) :=
  ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
    (u₀ := u₀) (M₀ := M₀) _hu₀_bound hc2 hs_gt_c2
```

Then convert the heat series to the lifted base iterate using the existing level-0 agreement theorem, as already used elsewhere in the file:

```lean
ShenWork.IntervalPicardIterateRepresentation.hagree_zero
  p u₀ hs_pos _hu₀_cont _hu₀_bound
```

That gives the needed `hu`.

For the resolver value:

```lean
have hv : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
    intervalDomainLift (coupledChemicalConcentration p
      (conjugatePicardIter p u₀ 0) q.1) q.2) (s, x) :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatResolverJointContDiffAt_two
    (p := p) (u₀ := u₀) (M₀ := M₀)
    _hu₀_bound _hu₀_cont hc2 hs_gt_c2 hx
```

For the resolver gradient, after adding the companion wrapper:

```lean
have hgradv : ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
    deriv (intervalDomainLift (coupledChemicalConcentration p
      (conjugatePicardIter p u₀ 0) q.1)) q.2) (s, x) :=
  ShenWork.Paper2.HeatResolverJointRegularity.heatResolverGradJointContDiffAt_two
    (p := p) (u₀ := u₀) (M₀ := M₀)
    _hu₀_bound _hu₀_cont hc2 hs_gt_c2 hx
```

For denominator positivity, use the resolver nonnegativity route already in the repo, or expose a heat-level floor wrapper.  The target needed by flux composition is:

```lean
have hbase :
    0 < 1 + intervalDomainLift (coupledChemicalConcentration p
      (conjugatePicardIter p u₀ 0) s) x := by
  -- resolver nonnegativity from continuous/nonnegative heat slice, then `1 + v > 0`
```

Then:

```lean
have hflux_c2 : ContDiffAt ℝ 2
    (Function.uncurry (coupledChemDivFluxLift p
      (conjugatePicardIter p u₀ 0))) (s, x) :=
  ShenWork.IntervalCoupledRegularityBootstrap
    .coupledChemDivFlux_contDiffAt_of_factorJointC2
      hu hv hgradv hbase
```

From this, the spatial derivative representative is continuous near `(s,x)`:

```lean
fun q : ℝ × ℝ =>
  fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p
    (conjugatePicardIter p u₀ 0))) q (0, 1)
```

This is the representative for the interior source value.

## Important endpoint caveat

Do **not** claim that the actual `coupledChemDivSourceLift` is `ContinuousOn` on the closed rectangle.  The comments in `IntervalConjugateLevel0BFormSourceOn.lean` are right: the zero-extension at the boundary can make closed-interval continuity false.

For `2A-sup`, you only need a bound, not closed-set continuity of the lifted source itself.

So prove the bound using a continuous **representative** `G` on the compact rectangle, plus the already-proved boundary-zero fact:

```lean
G (q : ℝ × ℝ) :=
  fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p
    (conjugatePicardIter p u₀ 0))) q (0, 1)
```

Then show:

```lean
ContinuousOn G (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

and use compactness:

```lean
have hK : IsCompact (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
  isCompact_Icc.prod isCompact_Icc

have hGabs : ContinuousOn (fun q => |G q|) (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
  hGcont.abs

obtain ⟨qmax, hqmax, hmax⟩ :=
  hK.exists_isMaxOn (Icc c T ×ˢ Icc (0 : ℝ) 1) (fun q => |G q|) ?nonempty hGabs

let Msup := |G qmax|
```

For `x ∈ Ioo 0 1`, use the interior agreement between `coupledChemDivSourceLift` and `G`.  For `x = 0` or `x = 1`, use `hbdry_zero`.

## One more subtlety: closed compactness needs a closed representative

The currently exported theorem `heatResolverJointContDiffAt_two` has the hypothesis

```lean
hx₀ : x₀ ∈ Ioo 0 1
```

This is enough for interior agreement but **not by itself** enough to prove a continuous representative on the closed rectangle, because compactness includes `x = 0` and `x = 1`.

There are two ways around this:

### Option A: expose global resolver-series representatives

This is the cleanest for `2A-sup`.

From the same upstream data used in `heatResolverJointContDiffAt_two`, expose theorem(s) for the actual series representative before the `intervalDomainLift` congruence restriction to `Ioo`:

```lean
heatResolverSeriesContDiff_two
heatResolverGradSeriesContDiff_two
```

These should follow directly from:

```lean
heatSemigroup_level0_resolverJointC2Data
boundedWeightJointSeries_contDiff_two
boundedWeightJointGradSeries_contDiff_two
```

Then build `G` from the series representatives and get `ContinuousOn G` on the closed rectangle.  Interior agreement identifies `G` with `coupledChemDivSourceLift`; boundary values are handled by `hbdry_zero`.

### Option B: prove local boundedness near endpoints separately

This is more awkward.  Interior pointwise `ContDiffAt` plus boundary-zero values does not by itself imply a uniform bound near the boundary.  You need a representative continuous up to the endpoint or a direct endpoint-neighborhood estimate.

So I recommend Option A.

## Recommended implementation order

Do this now, in this order:

1. Add `heatResolverGradJointContDiffAt_two` next to `heatResolverJointContDiffAt_two`.
2. Add, if needed for compactness, global representative wrappers for resolver value and gradient series. These are also pure wiring from `PhysicalResolverJointC2Data`.
3. In `level0_chemDiv_envelope_summable`, replace the `2A-sup` sorry by:
   - existing `hbdry_zero` for endpoints;
   - `hu`, `hv`, `hgradv`, `hbase` on interior;
   - `coupledChemDivFlux_contDiffAt_of_factorJointC2`;
   - continuity of the spatial derivative representative;
   - compactness bound on `Icc c T ×ˢ Icc 0 1`;
   - interior agreement + boundary-zero to bound the actual `coupledChemDivSourceLift`.

## Bottom line

Yes, wire it now.  The wiring will be logically correct and will isolate the remaining upstream sorry exactly where it belongs: the construction of heat-level physical resolver/source joint-`C²` data.

But wire it as:

```lean
heatSemigroup_jointContDiffAt_two
+ heatResolverJointContDiffAt_two
+ heatResolverGradJointContDiffAt_two   -- tiny wrapper needed
+ resolver/floor positivity
→ coupledChemDivFlux_contDiffAt_of_factorJointC2
→ continuity of the spatial derivative representative
→ compactness bound for representative
→ interior agreement + boundary-zero
→ hsup_bound
```

Do **not** rely on value-only `heatResolverJointContDiffAt_two`, and do **not** try to prove `ContinuousOn coupledChemDivSourceLift` on the closed interval.  Use a smooth representative for the compact bound and the actual lifted source only for interior agreement plus boundary-zero.