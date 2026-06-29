# PAPER1-POSITIVE-LOWER-PINNED-PRODUCER-WIRING

Repo: `xiangyazi24/Shen_work`  
Relevant commits: `fc6fb1d9` for pure tail squeeze, `9ae764e2` for contact/strict-barrier split  
Task: shortest honest Lean-facing route to feed

```lean
Paper1PositiveCriticalFrozenStationaryContactBranch
Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
```

from existing positive construction infrastructure while preserving the lower-pinned witness.  This response is **producer-wiring only**; it does not re-prove the already-committed tail squeeze.

## 0. Current available names

### StatementAssembly positive branch interfaces

File: `ShenWork/Paper1/StatementAssembly.lean`.

Already available:

```lean
ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
PositiveUpperBarrierContactContradictions
strict_upperBarrier_MChi_of_contactContradictions
Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
paper1_positiveCriticalBranch_of_strictBarrier
Paper1PositiveCriticalFrozenStationaryContactBranch
paper1_positiveStrictBarrierBranch_of_contactBranch
Paper1MainStatementStrictBarrierData
paper1_mainStatementTargets_of_strictBarrierData
```

Current target for the producer-wiring step should be the contact branch:

```lean
def Paper1PositiveCriticalFrozenStationaryContactBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
          InMonotoneWaveTrapSet (kappa c) (MChi p) U ∧
          PositiveUpperBarrierContactContradictions p c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U
```

The tail field is now derivable from a lower-pinned witness, so the next API should produce the same data **except** carry lower-pinned membership and exponent cover instead of the tail.

### Pure tail squeeze

File: `ShenWork/Paper1/StationaryUpperTail.lean`.

Available:

```lean
HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
```

and the branch-family version:

```lean
theorem lowerPinnedMonotoneTrap_tail_family_for_branch
    {p : CMParams} {c κtilde D M : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hcover :
      min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U) :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U
```

Use this theorem directly.  Do not carry `HasWaveRightTailAsymptotic` in any new positive provider.

### Lower-pinned trap and sign-agnostic lower-pinned producer

File: `ShenWork/Paper1/WaveRotheSchauder.lean`.

Available lower-pinned shape:

```lean
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

Available projections:

```lean
InLowerPinnedMonotoneTrap.bare
InLowerPinnedMonotoneTrap.lower
InLowerPinnedMonotoneTrap.profileNontrivial
InLowerPinnedMonotoneTrap.pos
```

Available data restriction helper:

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

Available lower-pinned stationary profile producer:

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

Despite the historical `chiNeg` name, this theorem is the existing lower-pinned Schauder/profile producer.  It is the shortest existing route that preserves `InLowerPinnedMonotoneTrap`.

### Positive wrappers currently do not preserve the lower pin

File: `ShenWork/Paper1/WaveRothePos.lean`.

Current positive wrappers include:

```lean
b1_chiPos_existence
b1_chiPos_existence_rootPin
b1_chiPos_existence_profileClean
b1_chiPos_existence_profileClean_rootPin
b1_chiPos_existence_stationary_floor
b1_chiPos_existence_stationary_floor_rootPin
b1_chiPos_existence_profileClean_stationary_floor
b1_chiPos_existence_profileClean_stationary_floor_rootPin
```

All current `b1_chiPos_*` wrappers return only:

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

They erase the lower pin, so they cannot feed `lowerPinnedMonotoneTrap_tail_family_for_branch` directly.

## 1. Does an existing positive producer already return suitable `InLowerPinnedMonotoneTrap`?

No positive-named producer currently returns:

```lean
InLowerPinnedMonotoneTrap (kappa c) (MChi p)
  (lowerBarrierPlateau (kappa c) κtilde D) U
```

The only existing producer that preserves this shape is the sign-agnostic theorem:

```lean
b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
```

Therefore the positive branch needs either:

1. a thin positive-name alias/wrapper around this theorem, plus positive lower-pinned Route-A data; or
2. a named residual/provider that directly returns the lower-pinned produced profile.

This must remain a named residual until the positive Route-A construction supplies the lower-pinned Schauder principle/data/stationarity/flatness for the desired `κtilde`.

## 2. Does the lower-pinned producer expose free `κtilde`?

Yes.  The sign-agnostic lower-pinned producer exposes free parameters:

```lean
κ κtilde D M : ℝ
```

with assumptions:

```lean
0 < κ
0 < κtilde - κ
0 < D
```

and all topological/analytic data specialized to the lower-pinned trap at that exact `κtilde`:

```lean
InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D)
```

For the positive branch, specialize:

```lean
κ := kappa c
M := MChi p
```

and require:

```lean
min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde
```

Then the committed `lowerPinnedMonotoneTrap_tail_family_for_branch` closes the full tail field.

Important mismatch: the older paper Lemma 4.2 parameter structure `PaperLemma42ExactConditions` has

```lean
hrange : κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
```

which is the **opposite direction** from the tail-family cover.  If the lower-barrier subsolution proof still needs `κtilde ≤ cap`, the shortest compatible specialization is equality:

```lean
κtilde = positiveBranchTailCap p c
```

where:

```lean
def positiveBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

Then both directions close by `le_rfl`, and the required positive gap follows from a pure parameter lemma.

## 3. Minimal theorem/structure names to add next

### 3.1 Parameter cap definition and gap lemma

Add near the positive branch assembly or in a small parameter helper file:

```lean
import ShenWork.Paper1.StatementAssembly

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- The branch cap for the Paper1 positive right-tail interval. -/
def positiveBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)

/-- The cap is strictly above `kappa c` when `2 < c`. -/
theorem kappa_lt_positiveBranchTailCap
    (p : CMParams) {c : ℝ} (hc : 2 < c) :
    kappa c < positiveBranchTailCap p c := by
  -- pure arithmetic target:
  -- use `kappa_pos_of_two_lt hc`, `kappa_lt_one_of_two_lt hc`,
  -- `p.hα : 1 ≤ p.α`, `p.hm : 1 ≤ p.m`, and `lt_min`.
  -- No construction data and no PDE facts.
  sorry

end ShenWork.Paper1
```

This theorem is needed only to derive:

```lean
0 < κtilde - kappa c
```

from `positiveBranchTailCap p c ≤ κtilde`.

### 3.2 Positive-name lower-pinned Schauder wrapper

This is just a routing alias around the sign-agnostic lower-pinned wrapper.  It is useful because downstream code should not call a `chiNeg` name from the positive branch.

```lean
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Positive-name lower-pinned Schauder wrapper.

This preserves the lower pin and returns the exact witness shape needed by the
pure tail squeeze.  It does not prove contact/no-contact, strict upper bound, or
the tail itself. -/
theorem b1_chiPos_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
    {p : CMParams} {c lam κtilde D M : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c) (hκ : 0 < kappa c) (hgap : 0 < κtilde - kappa c)
    (hD : 0 < D)
    (hprinciple :
      LocalUniformSchauderFixedPointPrinciple
        (InLowerPinnedMonotoneTrap (kappa c) M
          (lowerBarrierPlateau (kappa c) κtilde D)))
    (hdata :
      FrozenStationaryMapSchauderData p c lam
        (InLowerPinnedMonotoneTrap (kappa c) M
          (lowerBarrierPlateau (kappa c) κtilde D)) Tmap)
    (hstationary : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0)
    (hflat : ∀ U,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        FrozenStationaryFlatAtLeft p U) :
    ∃ U, InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U ∧
      FrozenStationaryWaveProfile p c U :=
  b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
    hc hκ hgap hD hprinciple hdata hstationary hflat

end ShenWork.Paper1
```

This should compile as a direct alias, assuming imports expose the sign-agnostic theorem.

### 3.3 Route-A lower-pinned provider: named residual, no tail field

This is the shortest honest residual that represents exactly what is not yet wired in `WaveRothePos.lean`: positive Route-A data on the lower-pinned trap at an exponent covering the branch cap.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.StationaryUpperTail
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Positive Route-A data preserving the lower pin at a branch-covering exponent.

No tail asymptotic is included: it is produced later by
`lowerPinnedMonotoneTrap_tail_family_for_branch`.  No `ShenUpperBoundPositive` is
included: upper comparison remains the separate contact/no-contact frontier. -/
def PositiveLowerPinnedRouteAProvider : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ lam κtilde D : ℝ, ∃ Tmap : (ℝ → ℝ) → ℝ → ℝ,
        0 < D ∧
        positiveBranchTailCap p c ≤ κtilde ∧
        LocalUniformSchauderFixedPointPrinciple
          (InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierPlateau (kappa c) κtilde D)) ∧
        FrozenStationaryMapSchauderData p c lam
          (InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierPlateau (kappa c) κtilde D)) Tmap ∧
        (∀ U,
          InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierPlateau (kappa c) κtilde D) U →
          Tmap U = U → ∀ x, frozenWaveOperator p c U U x = 0) ∧
        (∀ U,
          InLowerPinnedMonotoneTrap (kappa c) (MChi p)
            (lowerBarrierPlateau (kappa c) κtilde D) U →
          (∀ x, frozenWaveOperator p c U U x = 0) →
            FrozenStationaryFlatAtLeft p U)

end ShenWork.Paper1
```

This provider is not circular.  It does not contain:

```lean
HasWaveRightTailAsymptotic c κ₁ U
ShenUpperBoundPositive p c U
∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

It only contains lower-pinned construction data.

### 3.4 Contact-branch wrapper using provider + no-contact residual

This wrapper removes the tail residual from the contact branch.  It consumes local no-contact because that is still open.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.StationaryUpperTail
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- From lower-pinned positive Route-A data plus local no-contact, build the
current contact branch.  The tail is generated by the pure lower-pinned squeeze. -/
theorem paper1_positiveContactBranch_of_lowerPinnedRouteAProvider
    (hroute : PositiveLowerPinnedRouteAProvider)
    (hcontact :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∀ κtilde D U,
            0 < D →
            positiveBranchTailCap p c ≤ κtilde →
            InLowerPinnedMonotoneTrap (kappa c) (MChi p)
              (lowerBarrierPlateau (kappa c) κtilde D) U →
            FrozenStationaryWaveProfile p c U →
              PositiveUpperBarrierContactContradictions p c U) :
    Paper1PositiveCriticalFrozenStationaryContactBranch := by
  intro p hα hχ0 hχsmall c hc
  rcases hroute p hα hχ0 hχsmall c hc with
    ⟨lam, κtilde, D, Tmap, hD, hcover, hprinciple, hdata, hstationary, hflat⟩
  have hgap : 0 < κtilde - kappa c := by
    have hκcap : kappa c < positiveBranchTailCap p c :=
      kappa_lt_positiveBranchTailCap p hc
    exact sub_pos.mpr (lt_of_lt_of_le hκcap hcover)
  obtain ⟨U, hU, hprofile⟩ :=
    b1_chiPos_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
      (p := p) (c := c) (lam := lam) (κtilde := κtilde) (D := D)
      (M := MChi p) (Tmap := Tmap)
      (lt_of_lt_of_le two_pos hc.le)
      (kappa_pos_of_two_lt hc) hgap hD
      hprinciple hdata hstationary hflat
  refine ⟨U, hprofile, hU.bare, ?_, ?_⟩
  · exact hcontact p hα hχ0 hχsmall c hc κtilde D U hD hcover hU hprofile
  · exact lowerPinnedMonotoneTrap_tail_family_for_branch
      (p := p) (c := c) (κtilde := κtilde) (D := D) (M := MChi p) (U := U)
      hD.le (by simpa [positiveBranchTailCap] using hcover) hU

/-- Strict-barrier branch follows from the contact branch wrapper already in
`StatementAssembly.lean`. -/
theorem paper1_positiveStrictBarrierBranch_of_lowerPinnedRouteAProvider
    (hroute : PositiveLowerPinnedRouteAProvider)
    (hcontact :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∀ κtilde D U,
            0 < D →
            positiveBranchTailCap p c ≤ κtilde →
            InLowerPinnedMonotoneTrap (kappa c) (MChi p)
              (lowerBarrierPlateau (kappa c) κtilde D) U →
            FrozenStationaryWaveProfile p c U →
              PositiveUpperBarrierContactContradictions p c U) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch :=
  paper1_positiveStrictBarrierBranch_of_contactBranch
    (paper1_positiveContactBranch_of_lowerPinnedRouteAProvider hroute hcontact)

end ShenWork.Paper1
```

This is the recommended next code.  It is producer-wiring only and uses the committed tail squeeze exactly once.

## 4. How to discharge `PositiveLowerPinnedRouteAProvider` later

There are two honest ways.

### Option A: direct lower-pinned Route-A data

Prove the lower-pinned Schauder principle and `FrozenStationaryMapSchauderData` directly for:

```lean
InLowerPinnedMonotoneTrap (kappa c) (MChi p)
  (lowerBarrierPlateau (kappa c) κtilde D)
```

with `positiveBranchTailCap p c ≤ κtilde`.

This is the cleanest external API but may duplicate existing bare-route work.

### Option B: reuse bare positive data via `FrozenStationaryMapSchauderData.lowerPinned`

If existing positive route data are available on the bare monotone trap:

```lean
FrozenStationaryMapSchauderData p c lam
  (InMonotoneWaveTrapSet (kappa c) (MChi p)) Tmap
```

then use:

```lean
FrozenStationaryMapSchauderData.lowerPinned
```

provided you prove the lower-barrier invariance residual:

```lean
∀ u,
  InLowerPinnedMonotoneTrap (kappa c) (MChi p)
    (lowerBarrierPlateau (kappa c) κtilde D) u →
  ∀ x, lowerBarrierPlateau (kappa c) κtilde D x ≤ Tmap u x
```

This should be named explicitly, e.g.

```lean
def PositiveRouteALowerBarrierInvariant
    (p : CMParams) (c lam κtilde D : ℝ)
    (Tmap : (ℝ → ℝ) → ℝ → ℝ) : Prop :=
  ∀ u,
    InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) u →
    ∀ x, lowerBarrierPlateau (kappa c) κtilde D x ≤ Tmap u x
```

This is the actual construction-side analytic residual: does the positive Route-A map preserve the lower barrier?  It is not tail and not strict upper comparison.

## 5. Exact answer to the audit questions

### Existing producer preserving lower pin?

Yes, but not positive-named:

```lean
b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
```

No current `b1_chiPos_existence_*` wrapper preserves the lower pin.

### Does it expose free `κtilde`?

Yes.  It exposes free `κtilde` and `D`, but all lower-pinned principle/data/stationarity/flatness inputs must be supplied at that exact `κtilde`.

### Can it satisfy branch-cover inequality?

It can if the positive lower-pinned Route-A data are supplied with

```lean
positiveBranchTailCap p c ≤ κtilde
```

The safest specialization, especially if old subsolution constraints require `κtilde ≤ cap`, is equality:

```lean
κtilde = positiveBranchTailCap p c
```

Need new pure lemma:

```lean
kappa_lt_positiveBranchTailCap
```

for the gap assumption.

### Minimal new wrapper/data to replace carried tail residual?

Add:

```lean
positiveBranchTailCap
kappa_lt_positiveBranchTailCap
b1_chiPos_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
PositiveLowerPinnedRouteAProvider
paper1_positiveContactBranch_of_lowerPinnedRouteAProvider
paper1_positiveStrictBarrierBranch_of_lowerPinnedRouteAProvider
```

The critical wrapper is:

```lean
paper1_positiveContactBranch_of_lowerPinnedRouteAProvider
```

because it constructs the existing contact branch and fills the tail field by:

```lean
lowerPinnedMonotoneTrap_tail_family_for_branch hD.le hcover hU
```

## 6. False routes to avoid

* Do not use current `b1_chiPos_existence_*` outputs for the tail squeeze; the lower pin is erased.
* Do not add `HasWaveRightTailAsymptotic` as a field in the new provider; the tail squeeze now proves it.
* Do not add `ShenUpperBoundPositive` or global strict barrier as a field in the lower-pinned provider; upper no-contact remains a separate frontier.
* Do not rely on `PaperLemma42ExactConditions.hrange` alone; it gives `κtilde ≤ cap`, but the tail theorem needs `cap ≤ κtilde`.  Use equality at the cap if both directions are needed.
* Do not replace the produced profile by `logisticProfile`; this route is about the actual lower-pinned fixed point.
