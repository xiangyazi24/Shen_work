# PAPER1-POSITIVE-CAP-LOWER-PINNED-DATA-AUDIT

Repo: `xiangyazi24/Shen_work`  
Question: which current Lemma 4.2 / Route-A / cubeApprox / lower-pinned producer wrappers can feed a cap-specialized positive provider

```lean
κtilde := positiveBranchTailCap p c
M := MChi p
φ := lowerBarrierPlateau (kappa c) κtilde D
```

for `Paper1PositiveCriticalFrozenStationaryContactBranch` / `...StrictBarrierBranch`?

## 0. Bottom line

There is **no current positive Route-A/cubeApprox wrapper that directly returns**

```lean
InLowerPinnedMonotoneTrap (kappa c) (MChi p)
  (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U
```

with contact facts.  The existing Route-A/cubeApprox positive wrappers return a **raw** lower pin:

```lean
InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U
```

not the plateau pin required by the current tail-squeeze theorem/provider interface.

The shortest honest path for the **plateau interface** is therefore a named residual/data package that supplies the lower-pinned Schauder data at the cap for the plateau trap.  Existing sign-agnostic `WaveRotheSchauder` then turns those data into the lower-pinned stationary profile, and `lowerPinnedMonotoneTrap_tail_family_for_branch` closes the tail.

The shortest path if we are willing to change the provider from plateau to raw is different: the current positive Route-A/cubeApprox wrappers can already produce a raw lower-pinned profile at cap once `PositivePaperLemma42ExactConditions` is instantiated with `κtilde = cap`.  Then add a raw-pin analogue of the tail squeeze.  But that is a change of interface, not a feed into the plateau provider.

## 1. The exact current producer inventory

### 1.1 Generic lower-pinned plateau-capable producer

File: `ShenWork/Paper1/WaveRotheSchauder.lean`.

The generic lower-pinned bridge is:

```lean
theorem b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
    {p : CMParams} {c lam κ κtilde D M : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hgap : 0 < κtilde - κ)
    (hD : 0 < D)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap κ M
          (lowerBarrierPlateau κ κtilde D)))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InLowerPinnedMonotoneTrap κ M
          (lowerBarrierPlateau κ κtilde D)) Tmap)
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U →
      Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap κ M
        (lowerBarrierPlateau κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U
```

This theorem is sign-agnostic despite the historical `chiNeg` prefix.  It can feed the cap-specialized provider **if** the four plateau-trap inputs are supplied:

* `LocalUniformSchauderFixedPointPrinciple` for the plateau lower-pinned trap,
* `FrozenStationaryMapSchauderData` for the same plateau trap,
* fixed-point stationarity on that trap,
* flatness on that trap.

It exposes free `κtilde`, so it can be called with

```lean
κtilde = positiveBranchTailCap p c
κ = kappa c
M = MChi p
```

provided `0 < positiveBranchTailCap p c - kappa c` is proved.

### 1.2 Generic data restriction tool

File: `ShenWork/Paper1/WaveRotheSchauder.lean`.

Useful if bare positive Schauder data already exist:

```lean
theorem FrozenStationaryMapSchauderData.lowerPinned
    {κ M : ℝ} {φ : ℝ → ℝ}
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InMonotoneWaveTrapSet κ M) Tmap)
    (hlower : ∀ u, InLowerPinnedMonotoneTrap κ M φ u →
      ∀ x, φ x ≤ Tmap u x) :
    FrozenStationaryMapSchauderData p c lam
      (InLowerPinnedMonotoneTrap κ M φ) Tmap
```

For the plateau cap provider, the missing field would be:

```lean
∀ u,
  InLowerPinnedMonotoneTrap (kappa c) (MChi p)
    (lowerBarrierPlateau (kappa c) cap D) u →
  ∀ x, lowerBarrierPlateau (kappa c) cap D x ≤ Tmap u x
```

No current positive Route-A theorem provides this plateau lower-invariance field.

### 1.3 Concrete positive Route-A/cubeApprox producers: raw, not plateau

Files: `WaveLemma42G1Discharge.lean` and `WaveLemma42ParamCore.lean`.

The positive wrappers that are closest to the requested provider are:

```lean
b1_chiPos_existence_paper_of_cubeApproxData
b1_chiPos_existence_paper'_of_cubeApproxData
b1_chiPos_existence_paper_clean_of_cubeApproxData
b1_chiPos_existence_paper_clean_autoBar_of_cubeApproxData
b1_chiPos_existence_paper_min_of_cubeApproxData
b1_chiPos_existence_paper_min_noBar_of_cubeApproxData
b1_chiPos_existence_paper_min_core_of_cubeApproxData
b1_chiPos_existence_paper_min_core_noBar_of_cubeApproxData
b1_chiPos_existence_paper_routeA_core_of_cubeApproxData
b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
```

and, from `WaveLemma42ParamCore.lean`:

```lean
b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
```

But all of these produce raw lower-pinned witnesses.  For example the Route-A no-bar wrapper has shape:

```lean
theorem b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
    (p : CMParams) (c lam M κ κtilde D Λ : ℝ)
    (hcond : PositivePaperLemma42ExactConditions p c κ κtilde M)
    (hD : paperDMin p.χ M κ κtilde p.m p.γ c < D)
    (hD_ge_one : 1 ≤ D)
    (hΛ0 : 0 ≤ Λ) (hΛM : Λ ≤ M)
    (hpar :
      PaperLowerRawParabolicFloorRouteACoreNoBar p c lam M κ κtilde D Λ
        hcond.hκ0.le (le_trans zero_le_one hcond.hM))
    (hconv :
      PaperLowerPinnedStationaryFlatFloor p c κ M
        (lowerBarrierRaw κ κtilde D)
        (rotheSeqOfPaperFromPositiveCond p c lam M κ κtilde Λ hcond
          (fun u =>
            (paperLowerRawParabolicFloor_of_routeA_core
              (positivePaperLowerRawParabolicFloorRouteACore_of_noBar
                hcond hpar)).producer u
              |>.producer)))
    (hsmp : StationaryStrongMaxPrinciple p c κ M) :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U
```

The `paramCore` version is the same endpoint after replacing the monolithic Route-A per-step producer residual by explicit source-box parameter data:

```lean
theorem b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
    ... :
    ∃ U, InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D) U ∧
      FrozenStationaryWaveProfile p c U
```

### 1.4 Why the cubeApprox path is raw

`WaveLemma42G1Discharge.lean` defines the finite-dimensional lift as:

```lean
noncomputable def waveRawLift (κ M κtilde D : ℝ) (N : ℕ)
    (a : Fin (waveCubeDim N) → ℝ) (x : ℝ) : ℝ :=
  max (lowerBarrierPlateau κ κtilde D x)
    (min (upperBarrier κ M x) (waveOrderEnvelope M N a x))
```

This lift visibly uses `lowerBarrierPlateau`, but the membership theorem records only a raw pin:

```lean
lemma waveRawLift_mem_lowerPinned ... :
  InLowerPinnedMonotoneTrap κ M (lowerBarrierRaw κ κtilde D)
    (waveRawLift κ M κtilde D N a)
```

because the proof uses:

```lean
lowerBarrierRaw_le_plateau
```

and `le_max_left`.  The subsequent cubeApprox data and the final fixed point are all parameterized by `lowerBarrierRaw κ κtilde D`, not by the plateau.

This is the central API mismatch with the cap-specialized plateau provider.

## 2. Cap equality and old `κtilde ≤ cap` constraints

### 2.1 Existing Lemma 4.2 condition direction

File: `WaveLemma42Paper.lean`.

The negative exact conditions include:

```lean
hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
```

and the positive condition package used by `b1_chiPos_existence_paper_*` mirrors this range condition under `PositivePaperLemma42ExactConditions`.

The new tail family theorem needs the opposite inequality:

```lean
min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde
```

Therefore the only non-wasteful way to satisfy both old Lemma 4.2 and new tail-cover constraints is to specialize to exact equality:

```lean
κtilde = positiveBranchTailCap p c
```

where

```lean
def positiveBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

Then the old side is `le_rfl` after unfolding the cap, and the new tail cover is also `le_rfl`.

### 2.2 Needed cap gap lemma

To call any lower-pinned producer, the cap must be strictly above `kappa c`:

```lean
theorem kappa_lt_positiveBranchTailCap
    (p : CMParams) {c : ℝ} (hc : 2 < c) :
    kappa c < positiveBranchTailCap p c
```

This is pure arithmetic from:

```lean
kappa_pos_of_two_lt hc
kappa_lt_one_of_two_lt hc
p.hα : 1 ≤ p.α
p.hm : 1 ≤ p.m
```

This lemma is a genuine next small theorem if not already in local changes.

## 3. Shortest honest route for the plateau cap provider

If the target interface is fixed as:

```lean
Paper1PositiveLowerPinnedCapSchauderContactData
```

with plateau lower pin at the cap, then existing Route-A/cubeApprox raw producers do **not** directly feed it.  The shortest honest provider should expose the plateau-trap Schauder data as named fields and not pretend it is already produced by the raw wrappers.

Recommended structure:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.StationaryUpperTail
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Cap-specialized lower-pinned Schauder/contact data for the positive branch.
This is the exact residual needed to use the plateau-pin tail squeeze. -/
structure Paper1PositiveLowerPinnedCapSchauderContactData
    (p : CMParams) (c : ℝ) : Prop where
  lam : ℝ
  D : ℝ
  Tmap : (ℝ → ℝ) → ℝ → ℝ
  hD : 0 < D
  hprinciple :
    LocalUniformSchauderFixedPointPrinciple
      (InLowerPinnedMonotoneTrap (kappa c) (MChi p)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D))
  hdata :
    FrozenStationaryMapSchauderData p c lam
      (InLowerPinnedMonotoneTrap (kappa c) (MChi p)
        (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D)) Tmap
  hstationary : ∀ U,
    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U →
    Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0
  hflat : ∀ U,
    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U →
    (∀ x, frozenWaveOperator p c U U x = 0) →
      FrozenStationaryFlatAtLeft p U
  hcontact : ∀ U,
    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U →
    FrozenStationaryWaveProfile p c U →
      PositiveUpperBarrierContactContradictions p c U

end ShenWork.Paper1
```

Then the wrapper into the existing contact branch is pure:

```lean
namespace ShenWork.Paper1

/-- Cap-specialized plateau provider feeds the existing contact branch.
The tail field is discharged by `lowerPinnedMonotoneTrap_tail_family_for_branch`. -/
theorem paper1_positiveContactBranch_of_capSchauderContactData
    (hcap :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          Paper1PositiveLowerPinnedCapSchauderContactData p c) :
    Paper1PositiveCriticalFrozenStationaryContactBranch := by
  intro p hα hχ0 hχsmall c hc
  let cap := positiveBranchTailCap p c
  rcases hcap p hα hχ0 hχsmall c hc with
    ⟨lam, D, Tmap, hD, hprinciple, hdata, hstationary, hflat, hcontact⟩
  have hgap : 0 < cap - kappa c := by
    exact sub_pos.mpr (kappa_lt_positiveBranchTailCap p hc)
  obtain ⟨U, hU, hprofile⟩ :=
    b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
      (p := p) (c := c) (lam := lam) (κ := kappa c)
      (κtilde := cap) (D := D) (M := MChi p) (Tmap := Tmap)
      (lt_of_lt_of_le two_pos hc.le) (kappa_pos_of_two_lt hc)
      hgap hD hprinciple hdata hstationary hflat
  refine ⟨U, hprofile, hU.bare, hcontact U hU hprofile, ?_⟩
  exact lowerPinnedMonotoneTrap_tail_family_for_branch
    (p := p) (c := c) (κtilde := cap) (D := D)
    (M := MChi p) (U := U)
    hD.le (by simp [cap, positiveBranchTailCap]) hU

/-- Same provider feeds the strict-barrier branch via the existing contact wrapper. -/
theorem paper1_positiveStrictBarrierBranch_of_capSchauderContactData
    (hcap :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          Paper1PositiveLowerPinnedCapSchauderContactData p c) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_contactBranch
    (paper1_positiveContactBranch_of_capSchauderContactData hcap)

end ShenWork.Paper1
```

This is the correct producer-wiring theorem for the plateau interface.

## 4. Can existing Route-A wrappers fill `Paper1PositiveLowerPinnedCapSchauderContactData`?

Not as stated.

### What they can fill

At `κtilde = positiveBranchTailCap p c`, the existing positive raw Route-A wrappers can plausibly feed a **raw-cap** provider:

```lean
structure Paper1PositiveLowerRawCapRouteAData
    (p : CMParams) (c : ℝ) : Prop where
  lam D Λ : ℝ
  hcond : PositivePaperLemma42ExactConditions p c (kappa c)
    (positiveBranchTailCap p c) (MChi p)
  hD : paperDMin p.χ (MChi p) (kappa c)
    (positiveBranchTailCap p c) p.m p.γ c < D
  hD_ge_one : 1 ≤ D
  hΛ0 : 0 ≤ Λ
  hΛM : Λ ≤ MChi p
  hpar : PaperLowerRawParabolicFloorRouteACoreNoBar p c lam
    (MChi p) (kappa c) (positiveBranchTailCap p c) D Λ
    hcond.hκ0.le (le_trans zero_le_one hcond.hM)
  hconv : PaperLowerPinnedStationaryFlatFloor p c (kappa c) (MChi p)
    (lowerBarrierRaw (kappa c) (positiveBranchTailCap p c) D)
    (rotheSeqOfPaperFromPositiveCond p c lam (MChi p) (kappa c)
      (positiveBranchTailCap p c) Λ hcond
      (fun u =>
        (paperLowerRawParabolicFloor_of_routeA_core
          (positivePaperLowerRawParabolicFloorRouteACore_of_noBar
            hcond hpar)).producer u |>.producer))
  hsmp : StationaryStrongMaxPrinciple p c (kappa c) (MChi p)
```

Then call:

```lean
b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData
```

or, if using explicit source-box parameters,

```lean
b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData
```

The result is:

```lean
∃ U, InLowerPinnedMonotoneTrap (kappa c) (MChi p)
    (lowerBarrierRaw (kappa c) (positiveBranchTailCap p c) D) U ∧
  FrozenStationaryWaveProfile p c U
```

### What they cannot fill

They do not fill the plateau provider field:

```lean
InLowerPinnedMonotoneTrap ...
  (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U
```

A raw lower pin does not imply a plateau lower pin, because `lowerBarrierPlateau ≥ lowerBarrierRaw` on the left plateau region.  The committed `waveRawLift_mem_lowerPinned` deliberately records a raw pin, not a plateau pin.

## 5. Genuine residuals if insisting on plateau provider

For `Paper1PositiveLowerPinnedCapSchauderContactData`, the genuine residual fields are:

1. `hprinciple` for the cap plateau lower-pinned trap:

```lean
LocalUniformSchauderFixedPointPrinciple
  (InLowerPinnedMonotoneTrap (kappa c) (MChi p)
    (lowerBarrierPlateau (kappa c) cap D))
```

2. `hdata` for the cap plateau lower-pinned trap:

```lean
FrozenStationaryMapSchauderData p c lam
  (InLowerPinnedMonotoneTrap (kappa c) (MChi p)
    (lowerBarrierPlateau (kappa c) cap D)) Tmap
```

The natural way to build this from bare data is `FrozenStationaryMapSchauderData.lowerPinned`, but this requires the missing plateau lower-invariance:

```lean
∀ u,
  InLowerPinnedMonotoneTrap (kappa c) (MChi p)
    (lowerBarrierPlateau (kappa c) cap D) u →
  ∀ x, lowerBarrierPlateau (kappa c) cap D x ≤ Tmap u x
```

3. `hstationary` on the plateau trap.  This may be mostly wiring if the map is still `Tmap u = rotheLimit (rotheSeq u)` and the existing stationarity theorem is trap-polymorphic, but it must be stated for the plateau trap.

4. `hflat` on the plateau trap.  Same comment: likely a wrapper if flatness theorem only needs the bare trap and stationary equation; still a field until wired.

5. `hcontact`, the positive upper no-contact facts:

```lean
PositiveUpperBarrierContactContradictions p c U
```

This is the remaining upper-bound analytic frontier, independent of the lower-tail squeeze.

The tail family is **not** residual anymore.

## 6. Alternative shortest route: raw-cap provider plus raw-tail theorem

If the aim is to exploit the existing positive Route-A/cubeApprox wrappers immediately, the shortest route is to change the provider to raw lower pin and add the raw analogue of the tail squeeze:

```lean
theorem lowerPinnedRawMonotoneTrap_tail_family_for_branch
    {p : CMParams} {c κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hcover :
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierRaw (kappa c) κtilde D) U) :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U
```

This is not a new analytic idea; it is the same far-right raw-branch squeeze without the preliminary plateau-to-raw step.  But it is a new theorem/API because the committed squeeze currently consumes `lowerBarrierPlateau`.

Then the existing positive wrappers `b1_chiPos_existence_paper_routeA_core_noBar_of_cubeApproxData` or `b1_chiPos_existence_paper_routeA_paramCore_noBar_of_cubeApproxData` can feed the raw-contact branch.  That is likely the shortest path to use the existing Route-A machinery, but it does not feed the plateau-cap provider as stated.

## 7. Avoid these false routes

* Do not claim the current `b1_chiPos_existence_paper_routeA_*` wrappers feed the plateau provider.  They produce `lowerBarrierRaw`, not `lowerBarrierPlateau`.
* Do not use `κtilde ≤ cap` from `PositivePaperLemma42ExactConditions` as the tail cover.  The tail cover is `cap ≤ κtilde`.  Use `κtilde = cap` to satisfy both.
* Do not add tail as a field to the cap provider.  The tail is now generated by `lowerPinnedMonotoneTrap_tail_family_for_branch`.
* Do not hide no-contact by assuming `ShenUpperBoundPositive`; keep `PositiveUpperBarrierContactContradictions` or strict comparison as the upper-bound residual.
* Do not use the raw lower pin to infer the plateau lower pin.  The inequality is in the wrong direction on the plateau side.

## 8. Exact next declarations to add

For the plateau interface:

```lean
positiveBranchTailCap
kappa_lt_positiveBranchTailCap
Paper1PositiveLowerPinnedCapSchauderContactData
paper1_positiveContactBranch_of_capSchauderContactData
paper1_positiveStrictBarrierBranch_of_capSchauderContactData
```

For the Route-A raw fast path:

```lean
Paper1PositiveLowerRawCapRouteAData
paper1_positiveRawContactBranch_of_routeAData
lowerPinnedRawMonotoneTrap_tail_family_for_branch
```

Pick one path explicitly.  If the local `StatementAssembly` already has the plateau cap provider and wrappers, the remaining honest residual is exactly to prove/fill `Paper1PositiveLowerPinnedCapSchauderContactData`; current positive Route-A cubeApprox wrappers do not fill it without additional plateau lower-invariance data.
