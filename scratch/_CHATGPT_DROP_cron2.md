# Q1012 (cron2) — Level0 sub-sorry 3F/3G without `PhysicalResolverJointC2Data`

Static repo inspection only; I did **not** run Lean.

## Verdict

Yes, both 3F and 3G can be discharged for the **positive-time heat semigroup Level0 branch** without `PhysicalResolverJointC2Data`.

But the exact split is important:

* **3F is not obtained from flux joint-C² alone.**  There is an existing time analogue of the spatial fderiv bridge, but it identifies
  `deriv (fun r => coupledChemDivFluxLift p u r y) s` with the `(1,0)` Fréchet partial.  The LHS in 3F is the **explicit formula** `coupledChemDivFluxTimeDerivativeLift p u s y`, so you still need the existing time-chain lemma showing that this explicit formula is the actual time derivative of the flux slice.
* **3G does not need the physical resolver chain.**  It can be proved either directly from a joint-continuous closed-slab representative of `coupledChemDivTimeDerivativeLift`, or from a sufficiently strong joint-C²/closed-slab smooth representative of the flux time derivative.  The committed generic producer is `chemDivMixedTimeDeriv_jointContinuousOn_closed`, which only needs `ChemDivMixedTimeDerivClosedRepr`; the physical-chain theorem is only one way to manufacture that representative.

For Level0, the shortest no-physical route is:

```text
heat semigroup positive-time joint smoothness
+ resolver restart/cutoff joint C² (`resolverSpectralJointC2At_of_restartSmoothCutoff`)
+ direct resolver inner commute from value C² / time fderiv bridge
+ `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`
+ direct closed-slab mixed representative for Level0
```

This avoids `PhysicalResolverJointC2Data` completely.

## What the inspected files say

### `IntervalChemDivFluxJointC2Producer.lean` lines 117–175

The producer

```lean
coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs
```

builds `CoupledChemDivFluxJointC2Hyp` from `CoupledChemDivFluxFactorJointC2Inputs`.  Inside it:

1. It derives flux joint-C² from factor joint-C²:

```lean
have hflux_joint_c2_from_product_quotient_rpow :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (Function.uncurry (coupledChemDivFluxLift p u)) (s, x) :=
  fun x hx s hs =>
    coupledChemDivFlux_contDiffAt_of_factorJointC2
      (hu_c2 x hx s hs) (hv_c2 x hx s hs) (hgradv_c2 x hx s hs)
      (hbase x hx s hs)
```

2. It constructs only the **spatial** deriv/fderiv bridge internally:

```lean
have hspatial_deriv_fderiv_bridge :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun r : ℝ => deriv (coupledChemDivFluxLift p u r) x) =ᶠ[𝓝 s]
        (fun r : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (r, x) (0, 1)) :=
  fun x hx s hs => by
    ...
    simpa [Function.uncurry] using
      real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt hdiff_r
```

3. It does **not** construct 3F.  It simply forwards the input field `htime`:

```lean
have htime_deriv_fderiv_bridge :
    ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0)) :=
  htime
```

So sub-sorry 3F is exactly the missing `htime` field of `CoupledChemDivFluxFactorJointC2Inputs`.

### `IntervalChemDivFluxTimeBridge.lean`

This file already has the time mirror theorem:

```lean
theorem real_twoVar_time_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun r : ℝ => F (r, x)) s =
      fderiv ℝ F (s, x) (1, 0)
```

It also has the actual 3F-style producer:

```lean
theorem coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, y))
    (hv : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, y))
    (hgradv : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
          q.2)
      (s, y))
    (hbase : ∀ᶠ y in 𝓝 x,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) y)
    (hgv : ∀ᶠ y in 𝓝 x, HasDerivAt
      (fun r => deriv
        (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
          (s, y) (1, 0))
```

This theorem proves 3F by combining:

* `slopeSlice_hasDerivAt_of_jointC2` for the `u` time factor;
* `coupledChemicalTimeDeriv_hasDerivAt_of_jointC2` for the `v` time factor;
* `coupledChemDivFlux_hasDerivAt_time` for the explicit flux time derivative formula;
* `real_twoVar_time_deriv_eq_fderiv_of_differentiableAt` to identify the actual time derivative with the `(1,0)` Fréchet partial.

Thus 3F should be discharged with this theorem, not by reproving the algebra.

### `IntervalChemDivFACCommuteDischarge.lean`

The physical producer currently does exactly the right logical thing, but its source of resolver C² is `PhysicalResolverJointC2Data`:

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s
```

and then:

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2 ... :
  (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
    (fun y : ℝ =>
      fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))
```

For Level0, clone these proofs but replace every call to

```lean
coupledChemical_jointContDiffAt_two H hy
coupledChemical_grad_jointContDiffAt_two H hy
```

by the direct restart/cutoff resolver joint-C² facts.

### `IntervalChemDivTimeDerivClosed.lean`

This file already separates 3G into a physical-free core and a physical-chain convenience wrapper.

The physical-free core is:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

and:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

The physical-chain theorem

```lean
coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

is only a wrapper that uses `PhysicalResolverJointC2Data` to help build the hypotheses.  It is not needed if Level0 supplies `ChemDivMixedTimeDerivClosedRepr` directly.

## Answer to the three questions

### 1. Can 3F be proved directly from joint C² of the flux?

**Not from flux joint-C² alone.**

Flux joint-C² plus the existing theorem

```lean
real_twoVar_time_deriv_eq_fderiv_of_differentiableAt
```

gives:

```lean
deriv (fun r => coupledChemDivFluxLift p u r y) s =
  fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0)
```

But 3F needs:

```lean
coupledChemDivFluxTimeDerivativeLift p u s y =
  fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0)
```

eventually near `x`.  The explicit formula `coupledChemDivFluxTimeDerivativeLift` is **not definitionally** `deriv (fun r => coupledChemDivFluxLift p u r y) s`; it is a product/quotient/rpow formula.  Therefore one must also prove the chain-rule fact:

```lean
HasDerivAt (fun r => coupledChemDivFluxLift p u r y)
  (coupledChemDivFluxTimeDerivativeLift p u s y) s
```

The existing shortest theorem for exactly this is:

```lean
coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
```

So the practical answer is:

* There **is** an analogous time fderiv theorem: `real_twoVar_time_deriv_eq_fderiv_of_differentiableAt`.
* 3F should be proved via `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`, not just by applying the time fderiv theorem to flux C².
* This route avoids `PhysicalResolverJointC2Data` if `hu`, `hv`, `hgradv`, `hbase`, and `hgv` are supplied directly.

### 2. Can 3G be proved from joint C² of the time-derivative? Or does it need the physical resolver chain?

3G does **not** need the physical resolver chain.

The exact 3G target is already a continuity statement:

```lean
ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

So any direct proof of joint continuity of this function on the closed slab suffices.  A stronger `ContDiffOn` / joint-C² theorem for the time-derivative would certainly imply it, but that is more than necessary.

The shortest committed abstraction is:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

which only requires:

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

For Level0 positive time, prove this representative directly from explicit heat and resolver spectral series on the positive slab.  This is exactly the intended non-physical route.

## Shortest no-physical route for Level0 positive-time branch

Let

```lean
u := conjugatePicardIter p u₀ 0
δ := min 1 (τ / 2)
```

in the branch `hτ : 0 < τ`.  For any `s ∈ Metric.ball τ δ`, we have:

```lean
τ / 2 < s
0 < s
```

For any `t ∈ Icc (τ - δ) (τ + δ)`, we also have `0 < t` because `δ ≤ τ/2`, so the whole closed slab stays in positive time.

### Step A — keep the existing F2 heat joint-C² proof

The existing proof in `IntervalConjugateLevel0BFormSourceOn.lean` already proves F2 by:

```lean
ShenWork.Paper2.HeatSemigroupJointRegularity.heatSemigroup_jointContDiffAt_two
```

plus eventual equality between the heat cosine series and

```lean
fun q => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2
```

on `Ioi 0 ×ˢ Ioo 0 1`.

### Step B — prove resolver value/gradient C² directly by restart/cutoff

For each `s` and `x`, define a local pair:

```lean
have hresolver_pair :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x) ∧
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x) := by
  exact coupledChemicalConcentration_resolver_jointC2At_c2Data
    (p := p) (u := u) (U := U) (s := s) (x := x)
    HRc2 hs_pos hsU hx
    (by
      intro a₀ M _hM ha₀ a src offset hτoffset _hagree
      exact resolverSpectralJointC2At_of_restartSmoothCutoff
        (a₀ := a₀) (M := M) (a := a)
        (offset := offset) (s := s) (x := x)
        hτoffset ha₀ src)
```

This uses the same restart/cutoff theorem from Q931/Q987 and avoids `PhysicalResolverJointC2Data`.

If the Level0 file does not yet expose `HRc2 : ResolverHasSpectralAgreementC2Coeff U (coupledChemicalConcentration p u)`, make that the upstream Level0 resolver package target.  It is the correct positive-time spectral package, unlike `PhysicalResolverJointC2Data`.

### Step C — prove resolver inner commute directly

Add a direct clone of `coupledChemical_innerCommute_of_physicalJointC2` that takes value C² (and optionally gradient C²) as arguments instead of `PhysicalResolverJointC2Data`.

Minimal theorem shape:

```lean
import ShenWork.PDE.IntervalChemDivFluxTimeBridge
import ShenWork.PDE.IntervalCoupledResolverJointC2
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap

noncomputable section

namespace ShenWork.Paper2.Level0DirectFluxBridge

/-- Direct resolver inner commute from local resolver value joint-C².
This is `coupledChemical_innerCommute_of_physicalJointC2` with the physical data
removed. -/
theorem coupledChemical_innerCommute_of_directJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1)
    (hv_all : ∀ z ∈ Ioo (0 : ℝ) 1,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (s, z))
    (hv_time_near : ∀ᶠ r in 𝓝 s,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ =>
          intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
        (r, y)) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s := by
  let F : ℝ → ℝ → ℝ :=
    fun r => intervalDomainLift (coupledChemicalConcentration p u r)
  have hFC2 : ContDiffAt ℝ 2 (Function.uncurry F) (s, y) := by
    simpa [F, Function.uncurry] using hv_all y hy

  have hspatial :
      (fun r : ℝ => deriv (F r) y) =ᶠ[𝓝 s]
        (fun r : ℝ => fderiv ℝ (Function.uncurry F) (r, y) (0, 1)) := by
    filter_upwards [hv_time_near] with r hr
    have hdiff : DifferentiableAt ℝ (Function.uncurry F) (r, y) := by
      simpa [F, Function.uncurry] using hr.differentiableAt (by norm_num)
    simpa [F, Function.uncurry] using
      real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt hdiff

  have htime :
      (fun z : ℝ => coupledChemicalTimeDerivativeLift p u s z) =ᶠ[𝓝 y]
        (fun z : ℝ => fderiv ℝ (Function.uncurry F) (s, z) (1, 0)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    have hdiff : DifferentiableAt ℝ (Function.uncurry F) (s, z) := by
      simpa [F, Function.uncurry] using (hv_all z hz).differentiableAt (by norm_num)
    have := real_twoVar_time_deriv_eq_fderiv_of_differentiableAt hdiff
    simpa [coupledChemicalTimeDerivativeLift, F, Function.uncurry] using this

  simpa [F] using
    real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
      (F := F) (Ft := coupledChemicalTimeDerivativeLift p u)
      hFC2 hspatial htime

end ShenWork.Paper2.Level0DirectFluxBridge
```

For the Level0 positive branch, `hv_all` and `hv_time_near` come from the same restart/cutoff resolver theorem.  For `hv_time_near`, use the neighborhood `Metric.ball τ δ ∈ 𝓝 s` and the fact that every `r` in that ball is positive.

### Step D — prove 3F using the existing flux time bridge

Inside the 3F subgoal, use:

```lean
have hopen : Ioo (0 : ℝ) 1 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
refine coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
  (hu := ?_) (hv := ?_) (hgradv := ?_) (hbase := ?_) (hgv := ?_)
```

Fill the five eventual inputs as follows:

```lean
· filter_upwards [hopen] with y hy
  exact hu_c2 y hy s hs

· filter_upwards [hopen] with y hy
  exact (hresolver_pair_at y hy s hs).1

· filter_upwards [hopen] with y hy
  exact (hresolver_pair_at y hy s hs).2

· filter_upwards [hopen] with y hy
  exact hbase y hy s hs

· filter_upwards [hopen] with y hy
  exact coupledChemical_innerCommute_of_directJointC2
    (p := p) (u := u) (s := s) (y := y) hy
    (hv_all := fun z hz => (hresolver_pair_at z hz s hs).1)
    (hv_time_near := by
      have hball_nhds : Metric.ball τ δ ∈ 𝓝 s :=
        Metric.isOpen_ball.mem_nhds hs
      filter_upwards [hball_nhds] with r hr
      exact (hresolver_pair_at y hy r hr).1)
```

Here `hresolver_pair_at` is the local helper that packages direct restart/cutoff resolver value/gradient C² for any `s ∈ ball τ δ` and `x ∈ Ioo 0 1`.

This is the shortest 3F route.  It uses:

```lean
real_twoVar_time_deriv_eq_fderiv_of_differentiableAt
coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
resolverSpectralJointC2At_of_restartSmoothCutoff
```

and no physical resolver data.

### Step E — prove 3G by a direct Level0 mixed representative

Use the physical-free core from `IntervalChemDivTimeDerivClosed.lean`:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

So the Level0 3G subgoal should be reduced to:

```lean
have hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ := by
  exact level0_chemDivMixedTimeDerivClosedRepr
    (p := p) (u₀ := u₀) (τ := τ) (δ := δ) hτ -- plus bounds/spectral package
exact chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

Add the Level0-specific target:

```lean
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.PDE.IntervalChemDivMixedReprConstruct
import ShenWork.PDE.IntervalCoupledResolverJointC2
import ShenWork.PDE.IntervalResolverSpectralJointC2Concrete
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalChemDivMixedReprConstruct

noncomputable section

namespace ShenWork.Paper2.Level0DirectMixed

/-- Level0 positive-time closed-slab representative for the mixed time derivative.
This is the 3G replacement for the physical resolver chain. -/
theorem level0_chemDivMixedTimeDerivClosedRepr
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {τ δ : ℝ}
    (hτ : 0 < τ)
    (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ τ / 2)
    -- plus the Level0 heat coefficient bounds/continuity and resolver spectral package
    -- e.g. `_hu₀_cont`, `_hu₀_bound`, `HRc2`, and the summability data needed to build
    -- the closed-slab representatives below
    :
    ChemDivMixedTimeDerivClosedRepr p (conjugatePicardIter p u₀ 0) τ δ := by
  -- Route:
  -- 1. Since `δ ≤ τ/2`, every t in `Icc (τ-δ) (τ+δ)` satisfies `0 < t`.
  -- 2. Build globally continuous representatives for:
  --      U, Ut, Utx, Ux,
  --      V, Vx, Vxx, Vt, Vtx, Vtxx.
  --    For U-side use explicit heat cosine series and its t/x derivatives.
  --    For V-side use the resolver restart/spectral series on this positive slab.
  -- 3. Package them as `ChemDivMixedReprData`.
  -- 4. Apply `chemDivMixedTimeDerivClosedRepr_of_data`.
  sorry

end ShenWork.Paper2.Level0DirectMixed
```

This is better than trying to push through `PhysicalResolverJointC2Data`: it targets exactly what 3G needs, i.e. closed-slab continuity of the already-defined mixed time derivative.

## Why 3G should not be proved merely from pointwise restart `ContDiffAt`

The direct restart theorem

```lean
resolverSpectralJointC2At_of_restartSmoothCutoff
```

is an **interior pointwise** joint-C² statement.  It is perfect for 3C, 3D, and the interior 3F bridge.

But 3G is on the **closed spatial slab**:

```lean
Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1
```

and `coupledChemDivTimeDerivativeLift` contains outer `deriv` in `x`, so endpoint/junk-value behavior matters.  That is why `IntervalChemDivTimeDerivClosed.lean` uses the representative formulation: construct a globally continuous `Gmix` and prove equality on the closed slab.  For Level0, use the explicit heat/resolver cosine-series representatives, including the sine-series endpoint facts, to get the closed-slab equality.

## Final recommended patch plan

1. In a new small helper file, add `coupledChemical_innerCommute_of_directJointC2` as above.  This is the physical-free clone of `coupledChemical_innerCommute_of_physicalJointC2`.
2. In `IntervalConjugateLevel0BFormSourceOn.lean`, define a local helper in the positive branch:

```lean
hresolver_pair_at :
  ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
    ContDiffAt ℝ 2 resolverValue (s, x) ∧
    ContDiffAt ℝ 2 resolverGrad (s, x)
```

using `coupledChemicalConcentration_resolver_jointC2At_c2Data` plus `resolverSpectralJointC2At_of_restartSmoothCutoff`.

3. Fill 3C and 3D from `hresolver_pair_at`.
4. Fill 3E from `coupledChemical_floor_pos_of_nonneg_continuous` (or the existing resolver positivity route), using the heat semigroup slice continuity/nonnegativity.
5. Fill 3F with `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`, where `hgv` is supplied by `coupledChemical_innerCommute_of_directJointC2` and `hresolver_pair_at`.
6. Add the Level0 target `level0_chemDivMixedTimeDerivClosedRepr` and fill 3G by:

```lean
exact chemDivMixedTimeDeriv_jointContinuousOn_closed
  (level0_chemDivMixedTimeDerivClosedRepr ...)
```

This path uses the already-committed restart/cutoff resolver regularity and the already-committed flux time bridge.  It completely avoids `PhysicalResolverJointC2Data` and therefore avoids the unfillable global `FlooredSourceTimeData`/`S(0)>0` obstruction.
