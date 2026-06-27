# Q1090 / cron1 — remaining Level0 sorries after direct heat-Level0 resolver joint C²

Repo inspected: `xiangyazi24/Shen_work`

Current `IntervalConjugateLevel0BFormSourceOn.lean` blob inspected: `d4ae918c6d7276e32cd5c230c3cf47cb1ffa32ff`

Branch written: `chatgpt-scratch`

Target drop file:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

With the hypothesized **direct non-FSTD heat-Level0 resolver joint C²** facts:

```lean
ContDiffAt ℝ 2
  (fun q => intervalDomainLift
    (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
  (s₀, x₀)

ContDiffAt ℝ 2
  (fun q => deriv (intervalDomainLift
    (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1)) q.2)
  (s₀, x₀)
```

for all `s₀ > 0`, `x₀ ∈ Ioo 0 1`, plus the listed existing pieces:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.Paper2.IntervalLevel0DirectResolverCommute
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.Paper2.Level0DirectResolverCommute
```

**only the combined 3C+3D+3F chain-rule `HasDerivAt` sorry closes automatically.**

The 3E positivity sub-sorries also become short wiring if the existing heat-slice continuity/nonnegativity facts are supplied to `coupledChemical_floor_pos_of_nonneg_continuous`, but that is a positivity/initial-data wiring issue, not a consequence of direct resolver C² itself.

The envelope/H² compactness holes and 3G do **not** close automatically from direct resolver joint C². They need additional analytic work: higher spatial regularity / weak-H² envelope machinery for `level0_chemDiv_envelope_summable`, and a closed-slab mixed time-derivative representative for `3G`.

Compact verdict:

| # | Sorry site | Verdict after direct resolver joint C² | Why |
|---:|---|---|---|
| 1 | `SUB-SORRY 1A` uniform pointwise bound of `hH2_per_slice.secondDeriv` | **NEEDS WORK** | Needs uniform compact-slab control of second derivative of the weak-H² source representative; direct resolver C² is not enough. |
| 2 | `SUB-SORRY 2A-core` uniform sup bound of `coupledChemDivSourceLift` | **NEEDS WORK** | Needs compact-slab joint continuity/boundedness of the source representative on `[c,T]×[0,1]`; direct C² helps but does not automatically supply the closed-slab source bound. |
| 3 | `3A` local integrability subhole: `hV_C4` for `V_cos` | **NEEDS WORK** | Current proof asks for resolver spatial `C⁴`; direct resolver joint `C²` does not prove that. Can be avoided by rewriting 3A, but not automatic. |
| 4 | `3A` local integrability subhole: `hV_pos` for `1+V_cos>0` | **CLOSES** with positivity wiring | Use resolver nonnegativity / `coupledChemical_floor_pos_of_nonneg_continuous`; no direct C² needed. |
| 5 | `3E-bdd` inside `hbase` | **CLOSES** with positivity wiring | Replace local boundedness/continuity derivation by already available heat continuity / floor path. Current exact subproof still needs wiring. |
| 6 | `3E-nonneg` inside `hbase` | **CLOSES** with positivity wiring | Needs nonnegative/positive initial datum propagated by heat semigroup; not resolver C². |
| 7 | combined `SORRY 3C+3D+3F` chain-rule `HasDerivAt` | **CLOSES** | Direct resolver value/gradient C² + direct inner commute + existing flux time bridge produce the pointwise source chain rule. |
| 8 | `SORRY 3G` closed-slab continuity of `coupledChemDivTimeDerivativeLift` | **NEEDS WORK** | Requires closed-slab mixed time-derivative continuity/representative; direct pointwise resolver C² and inner commute are not enough. |

## Actual remaining `sorry` sites and detailed verdicts

### 1. `SUB-SORRY 1A`: uniform pointwise bound for the weak-H² second derivative

Current site:

```lean
-- inside level0_chemDiv_envelope_summable
have hL1_uniform : ∃ (B : ℝ), 0 ≤ B ∧ ∀ s (hs : s ∈ Icc c T),
    (∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x|) ≤ B := by
  ...
  have hunif_ptwise : ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
      ∀ x ∈ Icc (0 : ℝ) 1,
        |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
    sorry -- [SUB-SORRY 1A: joint continuity + compactness → ptwise bound]
```

Verdict: **NEEDS WORK**.

Direct resolver joint C² gives local information about:

```lean
v(t,x)      := intervalDomainLift (coupledChemicalConcentration p u t) x
∂ₓv(t,x)   := deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
```

up to joint order two at interior points. This is exactly enough for the flux chain rule in 3C/3D/3F, but this envelope proof is about a **uniform weak-H² source envelope**. It needs control of the source representative’s second derivative on the compact slab.

The source is schematically:

```text
source = ∂ₓ( u * ∂ₓv / (1+v)^β )
```

A weak-H² source certificate involves two more spatial derivatives of `source`, hence several higher spatial derivatives of `u` and `v` than the direct value/gradient joint-C² facts provide. The existing proof already signals this by building `IntervalWeakH2Neumann` and then uniformly bounding `hH2_per_slice.secondDeriv`.

What work is needed:

```text
- identify `hH2_per_slice.secondDeriv` with a classical second derivative of the source representative;
- prove joint continuity / boundedness of that representative on `[c,T] × [0,1]`;
- likely use a stronger direct resolver spatial regularity theorem than C², or a NeumannTower/depth-IBP route for the chem-div source;
- then apply compactness to get the uniform bound.
```

So this does **not** close automatically.

### 2. `SUB-SORRY 2A-core`: uniform sup bound for `coupledChemDivSourceLift`

Current site:

```lean
-- inside level0_chemDiv_envelope_summable
have hSup : ∃ (Msup : ℝ), 0 ≤ Msup ∧
    (∀ s ∈ Icc c T,
      IntervalIntegrable (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s)
        volume 0 1) ∧
    (∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup) := by
  ...
  have hsup_bound : ∃ (Msup : ℝ), 0 ≤ Msup ∧
      ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
        |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup := by
    ...
    sorry -- [SUB-SORRY 2A-core: uniform sup bound over s ∈ [c,T].]
```

Verdict: **NEEDS WORK**.

This is weaker than 1A, and direct resolver C² is relevant, but it still does not close automatically. The needed statement is a closed-slab bound for the source itself, including endpoint handling for the zero-extension `intervalDomainLift`.

Direct resolver joint C² gives interior smoothness. To close this one, still prove:

```text
- an interior representative for the source as `deriv(flux)`;
- joint continuity / boundedness on `[c,T]×Ioo(0,1)`;
- endpoint values are controlled (the file already proves `hbdry_zero`);
- compactness or a closed representative to obtain a uniform `Msup`.
```

This is likely much easier than 1A and may be attacked using direct C² plus the endpoint zero lemma already present, but it is not automatic from the C² theorem alone.

### 3. `3A` local integrability: `hV_C4` for `V_cos`

Current site in `hlocal_slab`, Field 1:

```lean
-- Field 1: IntervalIntegrable of source near s
set V_cos := intervalResolverLiftR p (conjugatePicardIter p u₀ 0 r) with hV_cos_def
have hV_C4 : ContDiff ℝ 4 V_cos := by
  apply intervalResolverLiftR_contDiff_four
  sorry -- [KNOWN GAP: eigenvalue-weighted ℓ¹ summability of resolver source.
         --  Same obstacle as line 315; needs depth-1 NeumannTower.]
```

Verdict: **NEEDS WORK**.

Direct resolver joint C² does **not** imply `ContDiff ℝ 4 V_cos`. The current local-integrability proof is overpowered: for `IntervalIntegrable` of the source, it tries to build a C⁴ resolver cosine representative and then use a smooth flux representative.

There are two possible ways forward:

```text
A. keep the current proof: then prove the eigenvalue-weighted source summability / resolver C⁴ fact;
B. rewrite Field 1 (3A) to use weaker regularity: direct resolver C² + gradient C² should be enough to show the chem-div source is continuous/measurable on the interior and bounded on compact subintervals, then transfer to IntervalIntegrable with endpoint handling.
```

Either way, direct C² does not simply fill this exact hole.

### 4. `3A` local integrability: `hV_pos` for `1 + V_cos > 0`

Current site in `hlocal_slab`, Field 1:

```lean
have hV_pos : ∀ x, (0 : ℝ) < 1 + V_cos x := by
  apply IntervalResolverHighRegularity.intervalResolverLiftR_one_add_pos_of_nonneg_on_Icc
  intro x hx
  sorry -- [KNOWN GAP: resolver nonnegativity on [0,1] at time r.
         --  Same infrastructure as lines 591-690; needs
         --  intervalNeumannResolverR_nonneg_of_nonneg_source.]
```

Verdict: **CLOSES** with positivity wiring.

This is not closed by direct resolver C², but it is closed by the existing positivity path named in the prompt, provided the heat slice nonnegativity/continuity facts are in scope:

```lean
import ShenWork.PDE.IntervalChemDivFluxFactorFAC

open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap

-- Existing shape:
#check coupledChemical_floor_pos_of_nonneg_continuous
```

The current `hV_pos` target is phrased for the periodic/even lifted cosine representative `V_cos`; the proof still needs the standard bridge:

```text
V_cos agrees with intervalDomainLift(coupledChemicalConcentration ...) on [0,1]
resolver nonnegativity on [0,1]
periodic/even/reflection argument gives global `0 < 1 + V_cos x`
```

But analytically, no new resolver-C² theorem is needed. This is a short positivity/nonnegativity wiring task.

### 5. `3E-bdd`: boundedness for heat-slice continuity inside `hbase`

Current site inside the local `hbase` proof:

```lean
have hLift_bdd : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ y, |intervalDomainLift u₀ y| ≤ M' :=
  sorry -- [3E-bdd: u₀ continuous on compact intervalDomainPoint →
        --  bounded range; needs haveI CompactSpace + isCompact_range.bddAbove]
```

Verdict: **CLOSES** with positivity wiring, but not from direct resolver C².

This is just an auxiliary proof needed by the current route to show `Continuous (conjugatePicardIter p u₀ 0 r)`. It can be handled in two ways:

```text
1. keep the current route and prove boundedness of `intervalDomainLift u₀` from compactness/continuity;
2. better: replace the whole local `hbase` proof by the existing floor lemma
   `coupledChemical_floor_pos_of_nonneg_continuous`, after supplying heat-slice
   continuity and nonnegativity.
```

Since the prompt explicitly includes the existing positivity/floor lemma, this is a closing/wiring item rather than a remaining analytic blocker.

### 6. `3E-nonneg`: initial nonnegativity for heat-slice nonnegativity inside `hbase`

Current site:

```lean
have h_r_nonneg : ∀ x' : intervalDomainPoint,
    0 ≤ conjugatePicardIter p u₀ 0 r x' := by
  intro x'
  simp only [conjugatePicardIter]
  apply ShenWork.IntervalResolverPositivity.intervalFullSemigroupOperator_nonneg hr_pos'
  intro y
  unfold intervalDomainLift
  split_ifs with hy
  · sorry -- [3E-nonneg: need 0 ≤ u₀ ⟨y,hy⟩;
          --  available when outer caller has PositiveInitialDatum or u₀ ≥ 0]
  · norm_num
```

Verdict: **CLOSES** with positivity/initial-data wiring, but not from direct resolver C².

The file already has a final interface with `PositiveInitialDatum`, and `level0_heat_pos_of_data` later proves strict heat positivity on `[c,T]`. For this local ball proof, use the global nonnegativity/positivity of the heat semigroup for positive time, or add/pass the needed nonnegativity hypothesis explicitly.

No resolver-C² work is needed.

### 7. Combined `SORRY 3C+3D+3F`: pointwise source chain rule `HasDerivAt`

Current site:

```lean
sorry -- [SORRY 3C+3D+3F: chain rule HasDerivAt.
       --  Heat semigroup u joint C² is PROVED above (_hu_c2_bridged).
       --  3E positivity (hbase) is PROVED above.
       --  Blocked on:
       --    3C — resolver v joint C² (restart cutoff infrastructure)
       --    3D — resolver ∇v joint C² (same)
       --    3F — flux time fderiv bridge (resolver inner commute)]
```

Verdict: **CLOSES**.

This is the one hole that the direct resolver joint C² route is designed to close automatically.

The replacement proof uses:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.Paper2.IntervalLevel0DirectResolverCommute
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.Paper2.Level0DirectResolverCommute
```

Proof map:

```text
F2/u joint C²:
  already in local context as `_hu_c2_bridged`, or from
  heatSemigroup_jointContDiffAt_two.

3C/v joint C²:
  direct resolver value joint C² theorem at `(r,x)`.

3D/∂ₓv joint C²:
  direct resolver gradient joint C² theorem at `(r,x)`.

Inner commute:
  coupledChemical_innerCommute_of_directJointC2
  using direct value C² at `(r,x)` and eventually in time near `r`.

3F time bridge:
  coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
  using u/v/∂ₓv C², floor positivity, and the inner commute.

Outer commute / source bridge:
  real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
  plus `coupledChemDivSourceLift_eq_deriv_fluxLift_interior` and
  `coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative`.
```

Skeleton of the local replacement:

```lean
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.Paper2.IntervalLevel0DirectResolverCommute
import ShenWork.Paper2.IntervalHeatSemigroupHighRegularity

open MeasureTheory Set Filter Topology
open ShenWork.IntervalDomain
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.Paper2.Level0DirectResolverCommute

-- Inside the existing `intro x hx r hr` branch:
-- let u := conjugatePicardIter p u₀ 0
-- have hu := _hu_c2_bridged
-- have hv := direct resolver value joint C² at (r,x)
-- have hgradv := direct resolver gradient joint C² at (r,x)
-- have hgv := coupledChemical_innerCommute_of_directJointC2 hv hv_time
-- have htime := coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt ...
-- have houter := real_twoVar_clairaut_hasDerivAt_of_fderiv_partials ...
-- simpa [source=deriv flux, timeDerivative=deriv fluxTimeDerivative] using houter
```

No new analytic theorem is required beyond the direct resolver value/gradient C² and the direct inner-commute theorem named in the prompt.

### 8. `SORRY 3G`: closed-slab continuity of `coupledChemDivTimeDerivativeLift`

Current site:

```lean
· -- Field 3: ContinuousOn of time derivative on closed slab.
  -- Needs resolver time-derivative closed-slab representative.
  sorry -- [SORRY 3G: time-derivative joint continuity on slab.
         --  Needs the resolver spectral route to produce ContinuousOn
         --  for coupledChemDivTimeDerivativeLift on a closed slab
         --  around s > 0.  Provable once resolver time-regularity is
         --  committed.]
```

Verdict: **NEEDS WORK**.

Direct resolver joint C² at interior points plus inner commute gives pointwise `HasDerivAt` and local differentiability information. It does **not** give the closed-slab continuity target:

```lean
ContinuousOn
  (Function.uncurry
    (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
  (Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1)
```

The target includes the closed spatial endpoints `0` and `1`, and it concerns the full mixed time-derivative lift, not only value/gradient resolver C² at interior points.

Needed work:

```text
- produce a closed-slab representative for `coupledChemDivTimeDerivativeLift`;
- show it agrees with the committed lift on `[s-δ,s+δ]×[0,1]`;
- prove global/closed-slab continuity, including endpoint behavior.
```

This is exactly the role of the separate closed-representative route, e.g. a theorem like:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed
```

when supplied with a heat-Level0 `ChemDivMixedTimeDerivClosedRepr`. Without that representative, 3G does not close automatically.

## Dependency graph after direct resolver C²

The useful graph is:

```text
Direct resolver value C² + direct resolver gradient C²
  ├─ closes 3C / 3D
  ├─ with direct inner commute + flux time bridge closes 3F
  └─ helps, but does not itself close:
       - 3A integrability
       - envelope compactness / weak-H² uniform bounds
       - 3G closed-slab mixed derivative continuity
```

The remaining non-automatic work splits cleanly into three work packages:

```text
Package E: envelope / coefficient envelope
  - SUB-SORRY 1A
  - SUB-SORRY 2A-core
  - likely rewrite or strengthen the weak-H² source representative proof

Package I: local integrability 3A
  - hV_C4 or replacement proof avoiding C4
  - hV_pos positivity wiring

Package G: closed-slab time-derivative continuity
  - 3G via closed mixed-time representative
```

## Recommended next patch order

1. **Patch 3C+3D+3F first.** This should be a direct replacement using the facts in the prompt.
2. **Patch 3E/hbase and `hV_pos` positivity wiring.** These are short once heat nonnegativity/continuity is available.
3. **Patch or rewrite 3A.** Prefer a direct integrability proof from C²/interior regularity rather than forcing resolver `C⁴`.
4. **Patch 3G via closed-slab representative.** This is independent of the envelope proof.
5. **Return to `level0_chemDiv_envelope_summable`.** This remains the largest analytic block; direct resolver C² alone is not enough for its weak-H² uniform compactness claims.

## Final answer

After direct heat-Level0 resolver joint C², **not all Level0 sorries close**.

The combined 3C+3D+3F chain-rule `HasDerivAt` closes. Positivity sub-sorries close with the existing floor/nonnegativity wiring. Everything tied to source integrability, weak-H² coefficient envelopes, compact uniform bounds, and closed-slab mixed time-derivative continuity still needs additional proof work.
