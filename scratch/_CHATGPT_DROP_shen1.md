# PAPER1-POSITIVE-LOWER-PINNED-TAIL-FEED

Repo: `xiangyazi24/Shen_work`  
Relevant commit: `fc6fb1d9`  
Task: shortest honest route to feed the Paper1 positive branch with a lower-pinned produced profile whose lower-barrier exponent covers

```lean
min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

using the new pure tail squeeze theorems in `StationaryUpperTail.lean`.

## Current facts read

### New tail squeeze API

File: `ShenWork/Paper1/StationaryUpperTail.lean`.

The newly added theorem is exactly the useful local tail producer:

```lean
theorem HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
    {c κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (_hκ₁lo : kappa c < κ₁) (hκ₁hi : κ₁ < κtilde) :
    HasWaveRightTailAsymptotic c κ₁ U
```

It then packages the whole branch interval as:

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

This is the theorem to use.  It consumes only `0 ≤ D`, lower-pinned trap membership, and the cover inequality.  It does **not** require stationarity or `FrozenStationaryWaveProfile`.

### Current positive branches in `StatementAssembly.lean`

`Paper1PositiveCriticalFrozenStationaryBranch` still asks for

```lean
FrozenStationaryWaveProfile p c U ∧
  ShenUpperBoundPositive p c U ∧
  ∀ κ₁, ... → HasWaveRightTailAsymptotic c κ₁ U
```

`StatementAssembly.lean` has already split the upper-bound side into smaller APIs:

```lean
ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
PositiveUpperBarrierContactContradictions
strict_upperBarrier_MChi_of_contactContradictions
Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
Paper1PositiveCriticalFrozenStationaryContactBranch
paper1_positiveStrictBarrierBranch_of_contactBranch
paper1_positiveCriticalBranch_of_strictBarrier
```

The key existing target to feed now is the contact branch:

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

The fourth field is now removable once the witness is lower-pinned with an exponent `κtilde` covering the branch cap.

### Lower-pinned producer shape

File: `ShenWork/Paper1/WaveRotheSchauder.lean`.

The lower-pinned trap is:

```lean
def InLowerPinnedMonotoneTrap
    (κ M : ℝ) (φ : ℝ → ℝ) (U : ℝ → ℝ) : Prop :=
  InMonotoneWaveTrapSet κ M U ∧ ∀ x, φ x ≤ U x
```

with projections:

```lean
InLowerPinnedMonotoneTrap.bare
InLowerPinnedMonotoneTrap.lower
InLowerPinnedMonotoneTrap.pos
```

The existing lower-pinned Schauder wrapper that preserves the lower pin is:

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

Despite the historical `chiNeg` name, this wrapper is sign-agnostic at the Schauder/profile layer.  It is currently the best existing producer shape for the tail squeeze because it preserves `InLowerPinnedMonotoneTrap`.

### Current positive wrappers

File: `ShenWork/Paper1/WaveRothePos.lean`.

The positive wrappers currently return only bare monotone-trap profile shape:

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

including:

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

So: **no current positive-named wrapper preserves the lower pin**.  The sign-agnostic lower-pinned wrapper exists in `WaveRotheSchauder.lean`, but `WaveRothePos.lean` has not yet routed its positive data through that wrapper.

## 1. Which existing producer preserves `InLowerPinnedMonotoneTrap`?

Existing preserving producer:

```lean
b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
```

in `WaveRotheSchauder.lean`.

It preserves exactly:

```lean
InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D) U
```

and returns the frozen stationary profile.

There is **not yet** an equivalent positive-named wrapper in `WaveRothePos.lean`.  All current `b1_chiPos_existence_*` wrappers erase the lower pin and therefore cannot feed `lowerPinnedMonotoneTrap_tail_family_for_branch` directly.

Recommended alias/wrapper name:

```lean
b1_chiPos_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
```

This should be a thin positive-named wrapper around `b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin`, with `κ := kappa c` and `M := MChi p` at the final branch call sites.

## 2. Does the existing producer expose a free `κtilde`?

Yes, the lower-pinned Schauder wrapper exposes free parameters:

```lean
κtilde D M : ℝ
```

with assumptions:

```lean
0 < κtilde - κ
0 < D
```

and the input trap/data/principle are all specialized to

```lean
InLowerPinnedMonotoneTrap κ M (lowerBarrierPlateau κ κtilde D)
```

So it can be run at any chosen `κtilde` **provided the lower-pinned Schauder principle/data/stationarity/flatness are available for that exact `κtilde`**.

For the new branch tail theorem, we need the cover inequality:

```lean
min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) ≤ κtilde
```

Existing paper Lemma 4.2 parameter structures go the other direction.  In `WaveLemma42Paper.lean`, `PaperLemma42ExactConditions.hrange` has:

```lean
κtilde ≤ min ((1 + p.α) * κ) (min (p.m * κ + 1 / 2) 1)
```

This is **not** enough for the tail theorem.  The shortest compatible choice is to set

```lean
κtilde = min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

so both the old upper bound `κtilde ≤ cap` and the new cover `cap ≤ κtilde` hold by `le_rfl`.

Needed parameter lemma:

```lean
def positiveBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)

theorem kappa_lt_positiveBranchTailCap
    (p : CMParams) {c : ℝ} (hc : 2 < c) :
    kappa c < positiveBranchTailCap p c := by
  -- uses:
  --   kappa_pos_of_two_lt hc
  --   kappa_lt_one_of_two_lt hc
  --   p.hα : 1 ≤ p.α
  --   p.hm : 1 ≤ p.m
```

Sketch:

* `kappa c < (1 + p.α) * kappa c` because `0 < kappa c` and `1 < 1 + p.α`.
* `kappa c < p.m * kappa c + 1 / 2` because `1 ≤ p.m` and `0 < 1 / 2`.
* `kappa c < 1` by `kappa_lt_one_of_two_lt hc`.
* combine with `lt_min` twice.

Then set:

```lean
κtilde := positiveBranchTailCap p c
hgap : 0 < κtilde - kappa c := sub_pos.mpr (kappa_lt_positiveBranchTailCap p hc)
hcover : positiveBranchTailCap p c ≤ κtilde := le_rfl
```

## 3. Minimal new wrapper/data to remove the carried tail residual

### 3.1 Lower-pinned contact branch without tail

Add a branch object that preserves the lower pin and the lower-barrier exponent cover.  It should not carry tail asymptotics.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.StationaryUpperTail
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- The positive branch cap appearing in the Paper1 right-tail interval. -/
def positiveBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)

/-- Parameter lemma needed to run the lower-barrier plateau at the branch cap. -/
theorem kappa_lt_positiveBranchTailCap
    (p : CMParams) {c : ℝ} (hc : 2 < c) :
    kappa c < positiveBranchTailCap p c := by
  -- arithmetic proof target
  sorry

/-- Lower-pinned/contact positive branch, with no carried tail residual.
The `hcover` field is exactly what feeds
`lowerPinnedMonotoneTrap_tail_family_for_branch`. -/
def Paper1PositiveCriticalLowerPinnedContactBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ κtilde D : ℝ, ∃ U : ℝ → ℝ,
        0 < D ∧
        positiveBranchTailCap p c ≤ κtilde ∧
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U ∧
        FrozenStationaryWaveProfile p c U ∧
        PositiveUpperBarrierContactContradictions p c U

/-- Pure tail squeeze wrapper from lower-pinned/contact branch to the existing
contact branch.  This is the direct replacement for the carried tail residual in
`Paper1PositiveCriticalFrozenStationaryContactBranch`. -/
theorem paper1_positiveContactBranch_of_lowerPinnedContactBranch
    (hbranch : Paper1PositiveCriticalLowerPinnedContactBranch) :
    Paper1PositiveCriticalFrozenStationaryContactBranch := by
  intro p hα hχ0 hχsmall c hc
  rcases hbranch p hα hχ0 hχsmall c hc with
    ⟨κtilde, D, U, hD, hcover, hU, hprofile, hcontact⟩
  refine ⟨U, hprofile, hU.bare, hcontact, ?_⟩
  exact lowerPinnedMonotoneTrap_tail_family_for_branch
    (p := p) (c := c) (κtilde := κtilde) (D := D) (M := MChi p) (U := U)
    hD.le ?_ hU
  -- close `?_: min ... ≤ κtilde` by unfolding `positiveBranchTailCap` at `hcover`
  -- exact hcover
```

In the proof above, the only small adjustment is whether `positiveBranchTailCap` is definitional abbreviation or needs `simpa [positiveBranchTailCap] using hcover`.

### 3.2 Lower-pinned strict-barrier branch without tail

If you want to bypass `PositiveUpperBarrierContactContradictions` and feed the strict-barrier branch directly, use this alternative:

```lean
/-- Lower-pinned/strict-barrier positive branch, with no carried tail residual. -/
def Paper1PositiveCriticalLowerPinnedStrictBarrierBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ κtilde D : ℝ, ∃ U : ℝ → ℝ,
        0 < D ∧
        positiveBranchTailCap p c ≤ κtilde ∧
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U ∧
        FrozenStationaryWaveProfile p c U ∧
        (∀ x, U x < upperBarrier (kappa c) (MChi p) x)

/-- Pure tail squeeze wrapper from lower-pinned/strict-barrier branch to the
existing strict-barrier branch. -/
theorem paper1_positiveStrictBarrierBranch_of_lowerPinnedStrictBarrierBranch
    (hbranch : Paper1PositiveCriticalLowerPinnedStrictBarrierBranch) :
    Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch := by
  intro p hα hχ0 hχsmall c hc
  rcases hbranch p hα hχ0 hχsmall c hc with
    ⟨κtilde, D, U, hD, hcover, hU, hprofile, hstrict⟩
  refine ⟨U, hprofile, hstrict, ?_⟩
  exact lowerPinnedMonotoneTrap_tail_family_for_branch
    (p := p) (c := c) (κtilde := κtilde) (D := D) (M := MChi p) (U := U)
    hD.le (by simpa [positiveBranchTailCap] using hcover) hU
```

The contact-branch version is preferable because `StatementAssembly.lean` already has the local no-contact API and the pure contact-to-strict wrapper:

```lean
paper1_positiveStrictBarrierBranch_of_contactBranch
```

## 4. Exact next theorem signatures to add

### 4.1 Positive lower-pinned Schauder wrapper

This is the missing positive-named wrapper that preserves the lower pin.  It should be a direct call to the sign-agnostic lower-pinned wrapper in `WaveRotheSchauder.lean`.

```lean
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Positive-name lower-pinned Schauder wrapper.
No sign-specific proof is hidden here; this is a routing wrapper that preserves
`InLowerPinnedMonotoneTrap` so the tail squeeze can be used. -/
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

This is honest: it does not assert `ShenUpperBoundPositive`, local no-contact, or tail asymptotics.  It only preserves the lower-pinned witness.

### 4.2 Cap-specialized producer provider

The positive construction data must be available at a `κtilde` covering the cap, ideally at equality.  Introduce the provider shape explicitly:

```lean
/-- Data needed to run the positive lower-pinned route at a branch-covering
lower-barrier exponent. -/
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
```

Do **not** include tail in this provider; the whole point is that tail is now produced by `lowerPinnedMonotoneTrap_tail_family_for_branch`.

If the lower barrier subsolution machinery still requires the old upper range `κtilde ≤ cap`, then specialize the provider to

```lean
κtilde = positiveBranchTailCap p c
```

using the `kappa_lt_positiveBranchTailCap` gap lemma.  That is the shortest path satisfying both old and new inequalities.

### 4.3 Contact branch provider using lower-pinned Route-A data

The local no-contact facts are still separate.  The wrapper below removes the tail residual only.

```lean
/-- Route-A lower-pinned data plus local no-contact facts imply the current
contact branch; tail is generated by the pure lower-pinned squeeze. -/
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
```

This is the cleanest immediate replacement for the carried tail field in the contact branch.

## 5. API gaps / non-circularity checklist

### Gap A: positive lower-pinned construction data at covering `κtilde`

Current positive wrappers erase the lower pin, so they cannot be used directly.  Need either:

1. positive lower-pinned Route-A data specialized to `κtilde = positiveBranchTailCap p c`, or
2. positive lower-pinned Route-A data with `positiveBranchTailCap p c ≤ κtilde`.

This is the real construction-side gap.

### Gap B: parameter lemma `kappa_lt_positiveBranchTailCap`

Needed to turn `hcover` into the wrapper’s required gap:

```lean
0 < κtilde - kappa c
```

This is pure arithmetic and should be added near the branch cap definition.

### Gap C: local no-contact facts

Still needed for `Paper1PositiveCriticalFrozenStationaryContactBranch`:

```lean
PositiveUpperBarrierContactContradictions p c U
```

This is independent of the tail squeeze and should remain separate.

### Not a gap anymore: right-tail asymptotics

Once `InLowerPinnedMonotoneTrap ... (lowerBarrierPlateau ... κtilde D) U` and `cap ≤ κtilde` are available, the branch tail is closed by:

```lean
lowerPinnedMonotoneTrap_tail_family_for_branch hD.le hcover hU
```

No stationarity, no `HasWaveRightTailAsymptotic` hypothesis, and no logistic-profile substitution are required.

## 6. False routes to avoid

* Do not feed the new tail theorem from current `b1_chiPos_existence_*` outputs.  Those outputs have only `InMonotoneWaveTrapSet`; the lower pin was erased.
* Do not use `PaperLemma42ExactConditions.hrange` alone.  It gives `κtilde ≤ cap`; the tail theorem needs `cap ≤ κtilde`.  Use equality `κtilde = cap` if the subsolution machinery needs the old upper range.
* Do not add a provider field carrying the tail family again.  That would undo the new squeeze theorem.
* Do not carry `ShenUpperBoundPositive`; keep using `PositiveUpperBarrierContactContradictions` or strict barrier comparison as the separate upper-bound frontier.
* Do not replace `U` by `logisticProfile`; the tail squeeze is specifically valuable because it applies to the produced lower-pinned `U`.
