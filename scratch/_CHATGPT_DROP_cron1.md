# Q1062 / cron1 — Level0 `hlocal_slab` vs `PhysicalResolverJointC2Data` producers

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

**No: `coupledChemDivFluxJointC2Hyp_of_FACInputs` does not close Level0's `hlocal_slab` automatically in the current post-`9dd3a4b` / `7f0f703` shape.**

The reason is structural, not mathematical: the current `IntervalConjugateLevel0BFormSourceOn.lean` no longer constructs a `CoupledChemDivFluxJointC2Hyp` and then routes through the old source-time-C¹ wrappers. Instead, `level0_chemDiv_timeDerivData` constructs the exact positive-time local slab inline:

```text
hlocal_slab : ∀ s, s ∈ Icc c T → ∃ δ > 0,
  (∀ᶠ r in 𝓝 s, IntervalIntegrable (coupledChemDivSourceLift ... r) volume 0 1) ∧
  (∀ x ∈ Ioo 0 1, ∀ r ∈ Metric.ball s δ,
    HasDerivAt (fun t => coupledChemDivSourceLift ... t x)
      (coupledChemDivTimeDerivativeLift ... r x) r) ∧
  ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift ...))
    (Icc (s - δ) (s + δ) ×ˢ Icc 0 1)
```

So existing physical resolver producers can be used, but only if they are explicitly threaded into this direct `hlocal_slab` proof, or if a new positive-window wrapper is introduced that returns exactly this slab. Merely making `PhysicalResolverJointC2Data` available will not cause Lean to find and apply the old flux-joint route.

The most precise answer is:

```text
PhysicalResolverJointC2Data closes the resolver-side analytic content for 3C/3D and
supplies the inner commute needed for 3F.

It does not itself close 3A, and it does not by itself provide the closed-slab
mixed time-derivative continuity required for 3G.

3G is closed by `chemDivMixedTimeDeriv_jointContinuousOn_closed` once a
`ChemDivMixedTimeDerivClosedRepr` witness is available; for heat Level0 the intended
witness is `chemDivMixedTimeDerivClosedRepr_level0`, but that witness currently has
its own proof obligations.
```

## Current file shape that matters

In the current `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, the relevant theorem is:

```lean
level0_chemDiv_timeDerivData
```

Inside it, Step 1 constructs:

```lean
have hlocal_slab : ∀ s, s ∈ Icc c T → ∃ δ : ℝ, 0 < δ ∧ ... := by
  intro s hs
  have hs_pos : 0 < s := lt_of_lt_of_le hc hs.1
  refine ⟨min 1 (s / 2), lt_min one_pos (half_pos hs_pos), ?_, ?_, ?_⟩
```

The three holes are exactly the local-slab fields later consumed by:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
```

That means the useful target is not `DuhamelSourceTimeC1`, and not even necessarily `CoupledChemDivFluxJointC2Hyp`; the useful target is the three fields of `hlocal_slab` itself.

One additional observation from the current file: although the comment says 3E positivity is proved, the current code still contains two nested 3E-style sorries inside the local `hbase` proof:

```text
[3E-bdd]    u₀ continuous on compact intervalDomainPoint → bounded range
[3E-nonneg] need 0 ≤ u₀ ⟨y,hy⟩
```

Those are not resolved by `PhysicalResolverJointC2Data` either. They are separate heat/initial-datum facts.

## Map from `hlocal_slab` sorries to available producers

| Current hole | Exact local need | Existing producer | Does `PhysicalResolverJointC2Data` close it? | Wiring needed |
|---|---|---|---|---|
| **3A** | `∀ᶠ r in 𝓝 s, IntervalIntegrable (coupledChemDivSourceLift p u r) volume 0 1` | None of the listed physical resolver producers. In the flux-joint wrappers this is an input field, not an output. | **No.** | Need a separate positive-time source-integrability lemma, probably from heat smoothness / weak-H² per slice / bounded measurable source. |
| **3C** | Joint `C²` of `v = coupledChemicalConcentration p u`: `ContDiffAt ℝ 2 (fun q => intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (r,x)` | `coupledChemical_jointContDiffAt_two` | **Yes. Directly**, once `Hphys : PhysicalResolverJointC2Data p u Bt` is in scope. | Add/pass `Hphys`; apply producer at `hx : x ∈ Ioo 0 1`. |
| **3D** | Joint `C²` of `∂ₓv`: `ContDiffAt ℝ 2 (fun q => deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2) (r,x)` | `coupledChemical_grad_jointContDiffAt_two` | **Yes. Directly**, once `Hphys` is in scope. | Add/pass `Hphys`; apply producer at `hx`. |
| **3F** | Chain-rule / outer commute giving `HasDerivAt (fun t => coupledChemDivSourceLift p u t x) (coupledChemDivTimeDerivativeLift p u r x) r` | `coupledChemical_innerCommute_of_physicalJointC2` supplies the resolver inner commute. Then use the existing flux time bridge / flux joint C² / outer commute chain. | **Partly.** `PhysicalResolverJointC2Data` supplies the missing resolver commute, but not the whole source `HasDerivAt` by itself. | Assemble with `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`, `coupledChemDivFlux_contDiffAt_of_factorJointC2`, and the outer-commute bridge, or build a local factor-joint wrapper. |
| **3G** | `ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u)) (Icc (s-δ) (s+δ) ×ˢ Icc 0 1)` | `chemDivMixedTimeDeriv_jointContinuousOn_closed` | **Not from `PhysicalResolverJointC2Data` alone.** | Need `ChemDivMixedTimeDerivClosedRepr p u s δ`; for heat Level0 the intended theorem is `chemDivMixedTimeDerivClosedRepr_level0`. |

## About `coupledChemDivFluxJointC2Hyp_of_FACInputs`

The exact current producer name in the repo is:

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

and the FAC route is:

```text
CoupledChemDivFluxFactorFACInputs
  -- coupledChemDivFluxFactorJointC2Inputs_of_FACInputs -->
CoupledChemDivFluxFactorJointC2Inputs
  -- coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs -->
CoupledChemDivFluxJointC2Hyp
  -- coupledChemDivOuterCommuteAtoms_of_fluxJointC2 -->
CoupledChemDivOuterCommuteAtoms
  -- coupledChemDivLocalChainRule_of_outerCommuteAtoms -->
CoupledChemDivLocalChainRule
```

That route is still mathematically relevant for 3F, but it is not the route currently used by Level0. Also, the current FAC-local source input still has the older `ContinuousOn (coupledChemDivSourceLift ...) (Icc 0 1)` flavor in some wrappers, while the Level0 file deliberately weakened the local source field to `IntervalIntegrable` because the zero-extension boundary behavior obstructs closed-interval source continuity.

Therefore, using the old global FAC wrapper as-is risks reintroducing exactly the global / boundary / nonpositive-time problem that commit `9dd3a4b` avoided. The safer path is either:

1. fill `hlocal_slab` directly, using the physical producers only for the resolver subfacts, or
2. add a new positive-window / integrability-weakened wrapper that returns exactly the `hlocal_slab` fields.

## Recommended minimal wiring

The cleanest local change is to make `level0_chemDiv_timeDerivData` accept or construct the physical resolver datum for the heat Level0 iterate:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.Paper2.Level0HeatMixedRepr

-- Suggested shape only: thread this datum into `level0_chemDiv_timeDerivData`
-- or build it immediately before `hlocal_slab` once Option A is committed.
--
-- {Bt : ℕ → ℕ → ℝ}
-- (Hphys : PhysicalResolverJointC2Data
--   p (conjugatePicardIter p u₀ 0) Bt)
```

Then the 3C and 3D local facts become one-liners at each `r,x`:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.Paper2.Level0HeatMixedRepr

-- inside the `intro x hx r hr` branch of `hlocal_slab`
-- abbreviate the Level0 heat iterate
let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0

have hv_c2 : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
    (r, x) := by
  simpa [u] using
    coupledChemical_jointContDiffAt_two
      (p := p) (u := u) (H := Hphys) (s := r) (x := x) hx

have hgradv_c2 : ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
    (r, x) := by
  simpa [u] using
    coupledChemical_grad_jointContDiffAt_two
      (p := p) (u := u) (H := Hphys) (s := r) (x := x) hx
```

For 3F, use the physical datum for the inner resolver commute, then feed the existing flux bridge / outer commute machinery. The important point is that `coupledChemical_innerCommute_of_physicalJointC2` is the missing resolver-side atom, not the whole 3F proof by itself:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.Paper2.Level0HeatMixedRepr

let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0

-- Inner commute supplied by the physical resolver C² data:
have hgv_at : HasDerivAt
    (fun t => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x)
    (deriv (coupledChemicalTimeDerivativeLift p u r) x) r := by
  simpa [u] using
    coupledChemical_innerCommute_of_physicalJointC2
      (p := p) (u := u) (H := Hphys) (s := r) (y := x) hx

-- To turn this into the source HasDerivAt, do NOT stop here.
-- Feed it with:
--   * heat-side joint C² for u near x,
--   * `hv_c2` and `hgradv_c2` above,
--   * local floor `0 < 1 + v`,
--   * `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`, and
--   * the outer-commute bridge from `IntervalChemDivOuterCommuteProducer`.
--
-- Conceptual endpoint:
--
-- have hsource_deriv : HasDerivAt
--     (fun t => coupledChemDivSourceLift p u t x)
--     (coupledChemDivTimeDerivativeLift p u r x) r := by
--   -- source = spatial derivative of flux on Ioo 0 1
--   -- time derivative of spatial derivative = spatial derivative of time derivative
--   -- via `real_twoVar_clairaut_hasDerivAt_of_fderiv_partials`
--   -- and the time bridge above.
--   ...
```

For 3G, the direct closure is the closed-representative theorem, not the physical resolver C² theorem:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.Paper2.Level0HeatMixedRepr

-- In the third field of `hlocal_slab`, where δ is `min 1 (s / 2)`:
have hcoeff_bound : ∀ k,
    |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀ := by
  -- `heatCoeff` is the Level0 cosine coefficient abbreviation.
  simpa [heatCoeff] using _hu₀_bound

have hrepr : ChemDivMixedTimeDerivClosedRepr
    p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2)) := by
  exact chemDivMixedTimeDerivClosedRepr_level0
    (p := p) (u₀ := u₀) (M₀ := M₀) (τ := s)
    hs_pos hcoeff_bound _hu₀_cont

exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

Caveat: `chemDivMixedTimeDerivClosedRepr_level0` currently records the intended Level0 heat witness but itself still contains analytic sorries for continuity/agreement of the ten spectral representatives. So 3G is structurally mapped, but it is only completely closed once that witness theorem is completed or accepted as the available producer.

## What should *not* be done

Do not expect a global `CoupledChemDivFluxJointC2Hyp` route to solve the current Level0 slab silently. It will not, because:

1. the current Level0 code does not call it;
2. `PhysicalResolverJointC2Data` is not currently an argument/local fact of `level0_chemDiv_timeDerivData`;
3. the old global wrapper shape wants all-time slabs, while the Level0 proof intentionally works only at positive `s ≥ c > 0`;
4. 3A is source integrability and is an input to the flux-joint/factor route, not an output of resolver joint C²;
5. 3G needs a closed mixed-time representative, not just resolver value/gradient joint C².

## Best next patch shape

I would make a small positive-window helper theorem whose conclusion is exactly the direct slab shape. That keeps the post-`9dd3a4b` design and avoids resurrecting the nonpositive-time branch:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalResolverJointC2PhysicalConcrete
open ShenWork.Paper2.Level0HeatMixedRepr

-- Suggested new helper; statement shape, not a drop-in completed proof.
theorem level0_hlocal_slab_of_physicalResolverJointC2
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {c T M₀ : ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : 0 < c) (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (Hphys : PhysicalResolverJointC2Data
      p (conjugatePicardIter p u₀ 0) Bt)
    -- separate non-resolver facts still needed:
    (hsource_int_pos : ∀ r, 0 < r →
      IntervalIntegrable
        (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
        volume 0 1)
    (hfloor_pos : ∀ r, 0 < r → ∀ x ∈ Ioo (0 : ℝ) 1,
      0 < 1 + intervalDomainLift
        (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) r) x) :
    ∀ s, s ∈ Icc c T → ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ r in 𝓝 s,
        IntervalIntegrable
          (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
          volume 0 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Metric.ball s δ,
        HasDerivAt
          (fun t => coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) t x)
          (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) r x)
          r) ∧
      ContinuousOn
        (Function.uncurry
          (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
        (Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1) := by
  -- choose δ = min 1 (s/2), exactly as current Level0 does;
  -- 3A from `hsource_int_pos` and positivity of the ball;
  -- 3C/3D from `coupledChemical_jointContDiffAt_two` and
  --   `coupledChemical_grad_jointContDiffAt_two`;
  -- 3F from physical inner commute + flux time bridge + outer commute;
  -- 3G from `chemDivMixedTimeDeriv_jointContinuousOn_closed` applied to the
  --   Level0 closed representative.
  sorry
```

Then `level0_chemDiv_timeDerivData` can call this helper for `hlocal_slab`, and the later `hjointcont`, `hderiv_global`, `hadotcont`, and `hMdot` code can remain essentially unchanged.

## Bottom line

`PhysicalResolverJointC2Data` is still very useful after `9dd3a4b`, but it is not an automatic drop-in closer for the current direct Level0 `hlocal_slab`.

Use it as follows:

```text
3C  := coupledChemical_jointContDiffAt_two Hphys
3D  := coupledChemical_grad_jointContDiffAt_two Hphys
3F  := coupledChemical_innerCommute_of_physicalJointC2 Hphys
       + existing flux bridge / outer commute assembly
3G  := chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
       where hrepr is the Level0 heat mixed closed representative
3A  := separate positive-time IntervalIntegrable lemma; not produced by Hphys
```

So the answer to the core question is:

```text
No, not automatically.
Yes, the PhysicalResolverJointC2Data-based producers can still be used,
but only by explicitly threading Hphys into the direct positive-time hlocal_slab proof
or by adding a new positive-window/integrability-weakened wrapper whose conclusion is
exactly that slab.
```
