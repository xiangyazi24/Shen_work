# PAPER1-POSITIVE-BRANCH-CLOSURE-ROUTE

Repo: `xiangyazi24/Shen_work`  
Source inspected: `main` at `b98c3a392ad264b7b57c9f7598a6b6a7dbcf1d12`  
Scope: the two remaining fields of `Paper1PositiveCriticalFrozenStationaryBranch`:

```lean
ShenUpperBoundPositive p c U
```

and

```lean
∀ κ₁, kappa c < κ₁ →
  κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
  HasWaveRightTailAsymptotic c κ₁ U
```

for the same non-explicit `U` produced by the positive Rothe/Schauder Route-A construction.

This is a route proposal, not an audit table.

## 1. Existing theorem candidates and statement mismatch

### A. Candidates for `ShenUpperBoundPositive p c U`

**Current positive Route-A wrappers.**  The wrappers in `ShenWork/Paper1/WaveRothePos.lean`

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

all stop at

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

They do not append `ShenUpperBoundPositive p c U`.

**Lower-pinned Schauder wrapper.**  `b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin` in `WaveRotheSchauder.lean` has the more useful output shape

```lean
∃ U, InLowerPinnedMonotoneTrap κ M
    (lowerBarrierPlateau κ κtilde D) U ∧
  FrozenStationaryWaveProfile p c U
```

Despite the historical `chiNeg` name, the theorem itself is a sign-agnostic lower-pinned Schauder wrapper: it consumes a lower-pinned `FrozenStationaryMapSchauderData`, fixed-point stationarity, and flatness.  It can be wrapped under a positive name once the positive Route-A data are supplied on the lower-pinned trap.  Mismatch: it still gives only the non-strict upper trap membership through `hU.bare`, not strict `ShenUpperBoundPositive`.

**Strict positivity from the lower pin.**  `InLowerPinnedMonotoneTrap.pos` proves

```lean
(∀ x, 0 < φ x) → InLowerPinnedMonotoneTrap κ M φ U → ∀ x, 0 < U x
```

and the plateau positivity used by the lower-pinned wrapper is `lowerBarrierPlateau_pos`.  Mismatch: this gives the first conjunct of `ShenUpperBoundPositive`, but not the strict upper inequalities.

**Non-strict trap upper bounds.**  Trap methods such as `hU.bare.le_M` and `hU.bare.le_exp` give only

```lean
U x ≤ M
U x ≤ Real.exp (-(κ) * x)
```

or equivalently non-strict membership below `upperBarrier κ M`.  Mismatch: `ShenUpperBoundPositive` requires strict

```lean
U x < min ((1 / (1 - p.χ)) ^ (1 / p.α)) (Real.exp (-(kappa c) * x)).
```

The strictness is not a trap-membership fact.

**`whole_line_super_barrier_pos`.**  This proves the positive-regime whole-line supersolution inequality for `upperBarrier κ M`:

```lean
whole_line_super_barrier_pos
  (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
  (hα : p.α = p.m + p.γ - 1)
  (hκ : 0 < κ) (hκ1 : κ < 1) (hmκ : p.m * κ ≤ 1)
  (hM : 1 ≤ M)
  (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
  (hc : c = κ + κ⁻¹) :
  InWaveTrapSet κ M u →
  ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

Mismatch: it is the non-strict superbarrier used to keep the Rothe step inside the trap.  It does not prove that the fixed point has no contact with the barrier.

**`ShenUpperBoundPositive` projections and shifts.**  `ShenUpperBoundPositive.pos`, `.lt_constant`, `.lt_exp`, `.le_constant`, `.le_exp`, and `ShenUpperBoundPositive.shift_right` / `shift_right_of_two_lt` all consume an existing `ShenUpperBoundPositive`.  Mismatch: no production for the constructed fixed point.

**Explicit logistic profile lemmas.**  `logisticProfile_shenUpperBoundPositive`, `logisticProfile_tail_bounds`, `logisticProfile_positive_construction_seed_data`, and `logisticProfile_positive_construction_seed_data_of_chi_lt_half_chiStar` prove positive upper data only for

```lean
logisticProfile (kappa c)
```

Mismatch: the constructed Route-A profile is an arbitrary non-explicit fixed point `U`.  There is no theorem proving that this `U` is equal to the logistic profile.

### B. Candidates for `HasWaveRightTailAsymptotic c κ₁ U`

**`HasWaveRightTailAsymptotic_of_stationary`.**  In `StationaryUpperTail.lean`, this theorem has the right-looking name but is intentionally only a carried interface:

```lean
theorem HasWaveRightTailAsymptotic_of_stationary
    {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    HasWaveRightTailAsymptotic c κ₁ U
```

Mismatch: it consumes `htail`; it does not produce it.  It is also specialized to trap height `1`, while the positive branch naturally wants the height `MChi p`.

**Consumer lemmas.**  `HasWaveRightTailAsymptotic.ratio_tendsto_one` and `HasWaveRightTailAsymptotic.tendsto_atTop_zero` only extract consequences from an already-proved asymptotic.  Mismatch: wrong direction.

**Explicit logistic profile lemmas.**  `logisticProfile_hasWaveRightTailAsymptotic`, `logisticProfile_exists_waveRightTailAsymptotic`, `_of_kappa_lt_one`, `_of_two_lt`, and the positive logistic seed-data wrappers again apply only to `logisticProfile (kappa c)`.  Mismatch: not the constructed fixed point; also several wrappers are existential in `κ₁`, whereas the branch requires the full `∀ κ₁` family.

**Lower-barrier facts.**  These are the most promising existing ingredients for B:

```lean
lowerBarrierRaw_eq_exp_mul
lowerBarrierPlateau_eq_raw_of_xplus_lt
InLowerPinnedMonotoneTrap.lower
InLowerPinnedMonotoneTrap.bare
```

`lowerBarrierRaw_eq_exp_mul` exposes

```lean
lowerBarrierRaw κ κtilde D x =
  Real.exp (-κ * x) * (1 - D * Real.exp (-(κtilde - κ) * x))
```

Mismatch: these facts do not directly mention `HasWaveRightTailAsymptotic`, but they should let us prove it by a squeeze argument for every `κ₁ < κtilde`, provided the constructed profile is kept in the lower-pinned trap.

## 2. Minimal new theorem statements to aim for

### 2.1 Keep the lower-pinned witness and choose the sharp tail cap

The current positive wrappers erase the lower pin by returning only `InMonotoneWaveTrapSet κ M U`.  For the right-tail field, do not erase it.  Add a positive-name wrapper around the existing lower-pinned Schauder theorem, then run it at

```lean
κ = kappa c
M = MChi p
κtilde = positiveBranchTailCap p c
```

where:

```lean
positiveBranchTailCap p c =
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

Target statements:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real

namespace ShenWork.Paper1

/- Target definition. -/

def positiveBranchTailCap (p : CMParams) (c : ℝ) : ℝ :=
  min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)

/-
Target theorem.  This is pure parameter arithmetic from `2 < c`, `1 ≤ p.α`,
`1 ≤ p.m`, and `0 < kappa c < 1`.

theorem kappa_lt_positiveBranchTailCap
    (p : CMParams) {c : ℝ} (hc : 2 < c) :
    kappa c < positiveBranchTailCap p c := by
  -- prove each branch of the min is strictly above `kappa c`
-/

/-
Positive-name wrapper around the existing lower-pinned Schauder theorem.
The proof should be a direct call to
`b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin`;
the theorem name `chiNeg` is historical here, not a sign hypothesis.

theorem b1_chiPos_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
    {p : CMParams} {c lam κtilde D M : ℝ}
    {Tmap : (ℝ → ℝ) → ℝ → ℝ}
    (hc : 0 < c) (hκ : 0 < kappa c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
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
    ∃ U : ℝ → ℝ,
      InLowerPinnedMonotoneTrap (kappa c) M
        (lowerBarrierPlateau (kappa c) κtilde D) U ∧
      FrozenStationaryWaveProfile p c U := by
  -- exact b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
  --   hc hκ hgap hD hprinciple hdata hstationary hflat
-/

end ShenWork.Paper1
```

This wrapper is not mathematically new; it just prevents losing the lower pin before proving B.

### 2.2 A: reduce `ShenUpperBoundPositive` to a strict no-contact theorem

First add the pure wiring lemma from strict exact-barrier control to `ShenUpperBoundPositive`.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real

namespace ShenWork.Paper1

/-
Pure wiring target.  The proof should unfold `upperBarrier`, rewrite
`MChi p` using `MChi_eq_rpow_of_chi_nonneg_lt_one`, and split the `min`.

theorem ShenUpperBoundPositive_of_pos_strict_upperBarrier_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt_one : p.χ < 1)
    (hpos : ∀ x, 0 < U x)
    (hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x) :
    ShenUpperBoundPositive p c U := by
  intro x
  refine ⟨hpos x, ?_⟩
  -- expected core:
  -- have hMx := hstrict x
  -- rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt_one] at hMx
  -- simpa [upperBarrier] using hMx
-/

end ShenWork.Paper1
```

Then isolate the real missing comparison theorem.  This should consume exactly the produced lower-pinned stationary object.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real

namespace ShenWork.Paper1

/-
Real comparison target for A.
Trap membership gives only `≤ upperBarrier`; this theorem upgrades to strict
non-contact using the stationary equation, lower pin / nontriviality, and the
positive whole-line superbarrier.

theorem strict_upperBarrier_MChi_of_positive_lowerPinned_stationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x := by
  -- suggested proof route:
  -- 1. `hU.bare` gives `U ≤ upperBarrier`.
  -- 2. `whole_line_super_barrier_pos` gives the weak supersolution inequality
  --    for `upperBarrier (kappa c) (MChi p)`.
  -- 3. Use `hprofile.stationary_eq` plus a strong comparison / no-contact lemma
  --    for the difference `upperBarrier - U`.
  -- 4. Exclude the identically-contact case using the lower pin and right decay.
-/

/-
Combined target for A after strict no-contact is available.

theorem ShenUpperBoundPositive_of_positive_lowerPinned_stationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U) :
    ShenUpperBoundPositive p c U := by
  have hχ_lt_one : p.χ < 1 := by
    have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχ_small (min_le_left _ _)
    linarith
  exact ShenUpperBoundPositive_of_pos_strict_upperBarrier_MChi
    hχ_nonneg hχ_lt_one hprofile.U_pos
    (strict_upperBarrier_MChi_of_positive_lowerPinned_stationary
      hα hχ_nonneg hχ_small hc hgap hD hU hprofile)
-/

end ShenWork.Paper1
```

This is the smallest honest reduction for A: the only genuinely new analytic content is the strict no-contact theorem.

### 2.3 B: prove the right-tail asymptotic by lower-barrier squeeze, not by replacing `U`

For B, the lower-pinned trap carries more information than the bare trap.  On the right tail,

```lean
lowerBarrierPlateau (kappa c) κtilde D x
  = lowerBarrierRaw (kappa c) κtilde D x
  = exp (-(kappa c) * x) *
      (1 - D * exp (-(κtilde - kappa c) * x)).
```

Together with the trap upper bound `U x ≤ exp (-(kappa c) * x)`, this squeezes

```lean
U x / exp (-(kappa c) * x) - 1
```

between `-D * exp (-(κtilde - kappa c) * x)` and `0` eventually.  Multiplication by `exp ((κ₁ - kappa c) * x)` tends to zero whenever `κ₁ < κtilde`.

First prove the rate-below-`κtilde` squeeze theorem:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real

namespace ShenWork.Paper1

/-
Mostly pure barrier/asymptotic theorem for B.
It should not use stationarity; it uses only the lower pin and the upper trap.

theorem HasWaveRightTailAsymptotic_of_lowerBarrierPinnedTrap
    {c κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (hM : 1 ≤ M)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hκ₁lo : kappa c < κ₁) (hκ₁hi : κ₁ < κtilde) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  -- proof route:
  -- 1. eventually atTop, `lowerBarrierPlateau = lowerBarrierRaw` using
  --    `lowerBarrierPlateau_eq_raw_of_xplus_lt`.
  -- 2. rewrite lower barrier with `lowerBarrierRaw_eq_exp_mul`.
  -- 3. upper trap gives `U x ≤ exp (-(kappa c) * x)` eventually
  --    because `1 ≤ M` and `exp (-(kappa c) * x) ≤ 1` for `x ≥ 0`.
  -- 4. divide by positive `exp (-(kappa c) * x)` and squeeze the ratio error.
  -- 5. use `κ₁ < κtilde` to make
  --    `exp ((κ₁ - κtilde) * x) → 0`.
-/

end ShenWork.Paper1
```

Then choose `κtilde` to be the branch cap.  This gives the full `∀ κ₁` family required by `Paper1PositiveCriticalFrozenStationaryBranch`.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real

namespace ShenWork.Paper1

/-
Full-family B theorem for a lower-pinned produced object at the sharp cap.
The produced object is the same `U`; no logistic substitution is involved.

theorem HasWaveRightTailAsymptotic_of_positive_lowerPinned_tailCap
    {p : CMParams} {c D : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U) :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < positiveBranchTailCap p c →
      HasWaveRightTailAsymptotic c κ₁ U := by
  intro κ₁ hκ₁lo hκ₁hi
  have hχ_lt_one : p.χ < 1 := by
    have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχ_small (min_le_left _ _)
    linarith
  have hM : 1 ≤ MChi p :=
    one_le_MChi_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt_one
  have hgap : 0 < positiveBranchTailCap p c - kappa c := by
    exact sub_pos.mpr (kappa_lt_positiveBranchTailCap p hc)
  exact HasWaveRightTailAsymptotic_of_lowerBarrierPinnedTrap
    (hκ := kappa_pos_of_two_lt hc)
    (hM := hM) (hgap := hgap) (hD := hD)
    (hU := hU) hκ₁lo hκ₁hi
-/

end ShenWork.Paper1
```

For the branch's exact upper bound expression, unfold `positiveBranchTailCap` in the final wrapper.

### 2.4 Final branch wrapper after A and B are reduced

Once the positive Route-A construction returns the lower-pinned object at `κtilde = positiveBranchTailCap p c`, the final assembly becomes ordinary existential wiring.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder

open Filter Topology Real

namespace ShenWork.Paper1

/-
Route-A closure skeleton.  `hroute` is the positive lower-pinned Route-A provider,
specialized to the exact height `MChi p` and the sharp lower-barrier exponent
`positiveBranchTailCap p c`.

theorem Paper1PositiveCriticalFrozenStationaryBranch_of_lowerPinnedRouteA
    (hroute :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ D : ℝ, 0 < D ∧
          ∃ U : ℝ → ℝ,
            InLowerPinnedMonotoneTrap (kappa c) (MChi p)
              (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U ∧
            FrozenStationaryWaveProfile p c U)
    (hupper :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∀ D : ℝ, 0 < D →
          ∀ U : ℝ → ℝ,
            InLowerPinnedMonotoneTrap (kappa c) (MChi p)
              (lowerBarrierPlateau (kappa c) (positiveBranchTailCap p c) D) U →
            FrozenStationaryWaveProfile p c U →
            ShenUpperBoundPositive p c U) :
    Paper1PositiveCriticalFrozenStationaryBranch := by
  intro p hα hχ0 hχsmall c hc
  rcases hroute p hα hχ0 hχsmall c hc with ⟨D, hD, U, hU, hprofile⟩
  have hupperU := hupper p hα hχ0 hχsmall c hc D hD U hU hprofile
  refine ⟨U, hprofile, hupperU, ?_⟩
  intro κ₁ hκ₁lo hκ₁hi
  exact HasWaveRightTailAsymptotic_of_positive_lowerPinned_tailCap
    (p := p) (c := c) (D := D) (U := U)
    hχ0 hχsmall hc hD hU κ₁ hκ₁lo (by
      simpa [positiveBranchTailCap] using hκ₁hi)
-/

end ShenWork.Paper1
```

This wrapper deliberately makes A the only remaining analytic provider once B is reduced by the lower-barrier squeeze.

## 3. Which field is wiring vs real new analysis?

### A. `ShenUpperBoundPositive p c U`

A has a pure-wiring tail, but not a pure-wiring proof.

Pure wiring:

```lean
∀ x, 0 < U x
∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

implies `ShenUpperBoundPositive p c U` by unfolding `upperBarrier` and rewriting `MChi` in the positive regime.

Real new analysis:

```lean
∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

The trap gives only `≤`.  Upgrading to strict non-contact needs a strong comparison/no-contact theorem using the stationary equation and the positive whole-line superbarrier.  This is the substantive A residual.

### B. `HasWaveRightTailAsymptotic c κ₁ U`

B is likely reducible much more than the prior carried-tail interface suggests, provided the lower pin is preserved and the construction chooses `κtilde` at the sharp cap.

For a lower-pinned object, the lower barrier itself has the exact right-tail expansion

```lean
exp (-(kappa c) * x) * (1 - D * exp (-(κtilde - kappa c) * x)).
```

The upper trap gives the matching upper envelope `exp (-(kappa c) * x)` eventually.  Therefore a squeeze should prove `HasWaveRightTailAsymptotic c κ₁ U` for every `κ₁ < κtilde`.  If `κtilde` is set to

```lean
positiveBranchTailCap p c
```

then this is exactly the full family required in the branch.

So B is not just final wiring, but it should be mostly barrier/asymptotic calculus and trap squeezing, not a full new stationary ODE linearisation, as long as the lower-pinned witness is retained.  If only the currently erased output

```lean
InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

is available, then B becomes genuinely underdetermined from trap data alone; the lower pin is the key extra datum.

## 4. Anti-fake warnings

Do not close A or B by switching the witness to `logisticProfile (kappa c)`.  The repository has good logistic-profile lemmas, including

```lean
logisticProfile_shenUpperBoundPositive
logisticProfile_hasWaveRightTailAsymptotic
logisticProfile_positive_construction_seed_data_of_chi_lt_half_chiStar
```

but these prove properties of the explicit logistic profile only.  They do not apply to the non-explicit `U` returned by the positive Rothe/Schauder fixed-point construction.

Do not use `HasWaveRightTailAsymptotic_of_stationary` as if it were a producer.  Its last hypothesis is exactly the desired tail statement.

Do not erase the lower pin before proving B.  The bare monotone trap gives only the crude upper envelope.  The lower-pinned trap gives the lower asymptotic expansion needed for the squeeze.

Do not run the positive branch at an arbitrary larger height `M` if the goal is `ShenUpperBoundPositive`.  The strict upper bound is stated with the exact positive-regime constant `MChi p`, so the route should specialize the construction to `M = MChi p` or prove a separate comparison down to that exact height.
