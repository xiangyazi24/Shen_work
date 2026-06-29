# PAPER1-POSITIVE-BRANCH-CLOSURE-ROUTE

Repo: `xiangyazi24/Shen_work`  
Inspected source commit: `b98c3a392ad264b7b57c9f7598a6b6a7dbcf1d12`  
Target frontier: `Paper1PositiveCriticalFrozenStationaryBranch` in `ShenWork/Paper1/StatementAssembly.lean`

## Executive conclusion

The current source does **not** contain a producer of either

```lean
ShenUpperBoundPositive p c U
```

or the full sharp family

```lean
∀ κ₁, kappa c < κ₁ →
  κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1) →
  HasWaveRightTailAsymptotic c κ₁ U
```

for the non-explicit stationary profile produced by the positive Rothe/Schauder/Route-A route.

The positive existence wrappers in `WaveRothePos.lean` produce a trapped stationary profile, and in the stronger variants they thread stationarity/floor/left endpoint data, but their conclusion remains only

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

They do not append `ShenUpperBoundPositive` or `HasWaveRightTailAsymptotic`.

The shortest honest route is therefore:

1. keep the positive Route-A produced witness, preferably with its lower-pinned trap data and with the **exact** upper trap height `M = MChi p`;
2. prove a strict-superbarrier theorem for that stationary profile, yielding strict membership below `upperBarrier (kappa c) (MChi p)`;
3. wire that strict trap theorem to `ShenUpperBoundPositive` by unfolding `upperBarrier` and rewriting `MChi`;
4. prove a genuinely new right-tail linearisation theorem from the stationary equation; and
5. add a final assembly wrapper that combines the existing `b1_chiPos_existence_*` witness with those two new producers.

The upper-bound residual has a small pure-wiring shell but still needs a real strict comparison theorem.  The sharp tail residual is the main new analysis; it is not a wiring problem.

## 1. Current frontier shape

`StatementAssembly.lean` defines the positive branch as:

```lean
def Paper1PositiveCriticalFrozenStationaryBranch : Prop :=
  ∀ p : CMParams, p.α = p.m + p.γ - 1 →
    0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
    ∀ c : ℝ, 2 < c →
      ∃ U : ℝ → ℝ,
        FrozenStationaryWaveProfile p c U ∧
          ShenUpperBoundPositive p c U ∧
          ∀ κ₁, kappa c < κ₁ →
            κ₁ < min ((1 + p.α) * kappa c)
              (min (p.m * kappa c + 1 / 2) 1) →
            HasWaveRightTailAsymptotic c κ₁ U
```

The nearby comment is accurate: the positive Rothe/Schauder route can produce lower-pinned frozen stationary profiles, but the branch still needs the strict positive Shen upper bound and the sharp right-tail asymptotic for the **same produced profile**.

## 2. Exact existing lemmas/producers found

### 2.1 `ShenUpperBoundPositive` for a non-explicit produced profile

No existing producer was found.

What exists:

* `ShenUpperBoundPositive.pos`, `.nonneg`, `.lt_constant`, `.le_constant`, `.lt_exp`, `.le_exp` in `Statements.lean`: consumers/projections from an already-proved `ShenUpperBoundPositive`.
* `ShenUpperBoundPositive.shift_right` and `ShenUpperBoundPositive.shift_right_of_two_lt` in `Statements.lean`: transport an already-proved bound under a right shift; they are not producers for a new stationary profile.
* `ShenUpperBoundPositive.hasStrictWaveUpperTailBound` is used in `TravelingWaveConstruction.lean`; it consumes `ShenUpperBoundPositive` and produces a weaker strict tail bound, not the branch requirement.
* `logisticProfile_shenUpperBoundPositive` in `ShenWork/PDE/TravelingWaveConstruction.lean`: proves the bound for the explicit profile `logisticProfile (kappa c)` under `0 ≤ p.χ` and `p.χ < 1`.
* `logisticProfile_tail_bounds`, `logisticProfile_positive_construction_seed_data`, and `logisticProfile_positive_construction_seed_data_of_chi_lt_half_chiStar`: package logistic-profile-only positive upper/tail data.

None of the above applies to the arbitrary/non-explicit `U` returned by the Rothe/Schauder fixed point unless the source also proves that produced `U = logisticProfile (kappa c)`.  I found no such equality theorem.

Negative-branch upper-bound lemmas in `StationaryUpperTail.lean` are also not positive-branch producers:

* `ShenUpperBoundNegative_of_strictAtZero` reduces the negative bound to `U 0 < 1` plus trap/positivity.
* `ShenUpperBoundNegative_of_stationary_strongMaxPrinciple` is still negative-branch-specific and still consumes an `hSMP : U 0 < 1` input.

There is no analogous committed theorem

```lean
ShenUpperBoundPositive_of_stationary ... : ShenUpperBoundPositive p c U
```

for a positive stationary profile.

### 2.2 `HasWaveRightTailAsymptotic` for a non-explicit produced profile

No existing producer was found.

What exists:

* `HasWaveRightTailAsymptotic.ratio_tendsto_one` and `.tendsto_atTop_zero` in `Statements.lean`: consumers. They extract consequences after the asymptotic is already known.
* `HasWaveRightTailAsymptotic_of_stationary` in `StationaryUpperTail.lean`: this is a carried/no-op interface. Its final hypothesis is exactly

  ```lean
  htail : HasWaveRightTailAsymptotic c κ₁ U
  ```

  and its conclusion is `htail`. It is not a producer from stationarity.
* `logisticProfile_hasWaveRightTailAsymptotic` in `TravelingWaveConstruction.lean`: proves the sharp tail only for `logisticProfile (kappa c)` when `kappa c < κ₁` and `κ₁ < 2 * kappa c`.
* `logisticProfile_exists_waveRightTailAsymptotic`, `_of_kappa_lt_one`, `_of_two_lt`, and the logistic seed-data wrappers: explicit-profile-only existential tail data.

`WaveBridgeWrappers.lean` and the stall block in `StationaryUpperTail.lean` both record the same gap: the trap envelope gives only `0 ≤ U x ≤ exp (-(kappa c) * x)` on the right; it does not imply

```lean
U x / Real.exp (-(kappa c) * x) → 1
```

much less the rate-`κ₁` estimate required by `HasWaveRightTailAsymptotic`.

### 2.3 What the positive Route-A wrappers currently produce

The exact positive wrappers in `WaveRothePos.lean` all end at a frozen stationary profile, not at the full `hpos` branch:

* `b1_chiPos_existence`
* `b1_chiPos_existence_rootPin`
* `b1_chiPos_existence_profileClean`
* `b1_chiPos_existence_profileClean_rootPin`
* `b1_chiPos_existence_stationary_floor`
* `b1_chiPos_existence_stationary_floor_rootPin`
* `b1_chiPos_existence_profileClean_stationary_floor`
* `b1_chiPos_existence_profileClean_stationary_floor_rootPin`

Their conclusion is of the form

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

Some variants improve the construction-side inputs by replacing `hGreen`/`hpos`/endpoint obligations with stationarity, floor, flatness, or trap-derived facts, but the output type remains the same.

`WavePaperStationaryFloor.lean` supplies useful stationarity and regularity infrastructure, for example:

* `paperLowerPinnedStationary_of_stepConsistency`
* `paperLowerPinnedStationary_of_fixedStepIdentity`
* `stationaryC2RegularityFromEquation_of_c2CompactConvergence`
* `stationaryStrongMaxPrinciple_of_c2CompactConvergence`
* `stationaryStrongMaxPrinciple_of_rotheLimit_greenRepresentation`
* `stationaryGreenRepresentationFromEquation_of_rotheLimit`

These are relevant support for strict comparison and regularity, but they do not currently conclude either `ShenUpperBoundPositive` or `HasWaveRightTailAsymptotic`.

## 3. Smallest honest new intermediate theorem targets

The route should not try to replace the produced fixed point by the explicit logistic profile.  The new theorems should consume the actual fixed point and the data already produced by the positive construction.

### 3.1 Keep or re-export the lower-pinned witness

If the current positive wrapper available at the final call site has erased the lower pin and returns only `InMonotoneWaveTrapSet`, add a thin preserving wrapper.  The strict upper-bound proof is much cleaner if it can see the lower-pinned/nontrivial witness, although the final assembly can later expose only the bare trap.

The useful target shape is:

```lean
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.WavePaperStationaryFloor

open Filter Topology

namespace ShenWork.Paper1

/-
Target shape only.  Do not add as an axiom.
The point is to preserve the lower-pinned witness instead of immediately erasing it.

theorem b1_chiPos_existence_lowerPinned_profileClean_stationary_floor_rootPin
    (p : CMParams) (c lam Bv κtilde D Λ : ℝ)
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    -- plus exactly the same Route-A/Schauder/Green/compactness inputs used by the
    -- existing positive wrapper, specialized to κ = kappa c and M = MChi p
    : ∃ U : ℝ → ℝ,
        InLowerPinnedMonotoneTrap (kappa c) (MChi p)
          (lowerBarrierPlateau (kappa c) κtilde D) U ∧
        FrozenStationaryWaveProfile p c U := by
  -- thin wrapper around the already-existing lower-pinned positive construction,
  -- if exported; otherwise this is the smallest wrapper to expose the witness.
-/

end ShenWork.Paper1
```

The important specialization is `M = MChi p`.  If the positive construction is run with some larger `M`, the trap gives at best `U ≤ M`, while `ShenUpperBoundPositive` requires strict control below the smaller paper constant

```lean
(1 / (1 - p.χ)) ^ (1 / p.α)
```

which is `MChi p` in the positive regime.

### 3.2 Pure wiring: strict exact trap bound implies `ShenUpperBoundPositive`

Once one has strict control below the exact upper barrier, turning it into `ShenUpperBoundPositive` is pure Lean wiring.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRothePos

open Filter Topology

namespace ShenWork.Paper1

/-
Target theorem; proof should be just unfolding `upperBarrier`, rewriting `MChi`,
and using the strict barrier inequality.

theorem ShenUpperBoundPositive_of_pos_strict_upperBarrier_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt_one : p.χ < 1)
    (hpos : ∀ x, 0 < U x)
    (hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x) :
    ShenUpperBoundPositive p c U := by
  intro x
  refine ⟨hpos x, ?_⟩
  -- Expected core:
  --   rw [MChi_eq_rpow_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt_one] at hstrict
  --   simpa [upperBarrier] using hstrict x
-/

end ShenWork.Paper1
```

This theorem is the likely pure-wiring part of the upper-bound residual.

### 3.3 Real analysis but probably smaller than the tail: strict upper barrier for the produced stationary profile

The missing analytic statement for the positive upper bound is a strong comparison theorem against the positive superbarrier:

```lean
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.WavePaperStationaryFloor

open Filter Topology

namespace ShenWork.Paper1

/-
Target theorem; this is not pure wiring.
It should use the stationary equation, the positive χ super-barrier inequality,
and a strong maximum/comparison principle to upgrade non-strict trap membership
U ≤ upperBarrier to strict U < upperBarrier.

theorem positive_lowerPinnedStationary_strict_upperBarrier_MChi
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x := by
  -- Real comparison/SMP proof target.
  -- Trap gives only ≤.  The lower pin/nontriviality and stationarity should rule
  -- out contact with the strict positive supersolution.
-/

end ShenWork.Paper1
```

A convenient combined theorem can then use `FrozenStationaryWaveProfile.U_pos` for positivity:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRothePos

open Filter Topology

namespace ShenWork.Paper1

/-
theorem ShenUpperBoundPositive_of_positive_lowerPinnedStationary
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
    (positive_lowerPinnedStationary_strict_upperBarrier_MChi
      hα hχ_nonneg hχ_small hc hgap hD hU hprofile.stationary_eq)
-/

end ShenWork.Paper1
```

This is the smallest honest way to reduce the positive upper-bound slot: prove one strict comparison theorem, then the rest is unfolding/wiring.

### 3.4 Real new analysis: right-tail linearisation for the produced profile

The sharp tail theorem should be stated directly for the produced stationary profile.  It should probably consume `ShenUpperBoundPositive` as a smallness/strictness input, because the nonlinear error terms at `+∞` need upper-tail control.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.WavePaperStationaryFloor

open Filter Topology

namespace ShenWork.Paper1

/-
Target theorem; this is the main analytic frontier.
It should be proved by linearising the stationary frozen equation at U = 0 on
`x → +∞`, with nonlinear remainders controlled by the positive upper bound.

theorem HasWaveRightTailAsymptotic_of_positive_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hupper : ShenUpperBoundPositive p c U) :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      HasWaveRightTailAsymptotic c κ₁ U := by
  -- Real +∞ asymptotic proof target.
-/

end ShenWork.Paper1
```

A useful split, if the full theorem is too large, is:

```lean
import ShenWork.Paper1.StatementAssembly

open Filter Topology

namespace ShenWork.Paper1

/-
-- leading amplitude normalization

theorem positive_stationary_right_ratio_tendsto_one
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hupper : ShenUpperBoundPositive p c U) :
    Tendsto (fun x => U x / Real.exp (-(kappa c) * x)) atTop (𝓝 1) := by
  -- first tail subtarget

-- rate improvement / sharp nonlinear remainder

theorem positive_stationary_right_ratio_error_decay
    {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hupper : ShenUpperBoundPositive p c U)
    (hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < min ((1 + p.α) * kappa c)
      (min (p.m * kappa c + 1 / 2) 1)) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  -- second tail subtarget
-/

end ShenWork.Paper1
```

The full target range

```lean
κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1)
```

should not be weakened in the final branch theorem, because `Paper1PositiveCriticalFrozenStationaryBranch` asks for exactly that family.

### 3.5 Final assembly wrapper once the two producers exist

After the strict upper and tail producers are proved, the final closure is ordinary existential wiring.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRothePos

open Filter Topology

namespace ShenWork.Paper1

/-
Target wrapper.  The exact `hroute` type can either be an existing `b1_chiPos_*`
wrapper specialized to κ = kappa c and M = MChi p, or a thin lower-pinned wrapper
that preserves `InLowerPinnedMonotoneTrap`.

theorem Paper1PositiveCriticalFrozenStationaryBranch_of_chiPos_routeA
    (hroute :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∃ U : ℝ → ℝ,
            InMonotoneWaveTrapSet (kappa c) (MChi p) U ∧
            FrozenStationaryWaveProfile p c U)
    (hupperProd :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∀ U : ℝ → ℝ,
            InMonotoneWaveTrapSet (kappa c) (MChi p) U →
            FrozenStationaryWaveProfile p c U →
            ShenUpperBoundPositive p c U)
    (htailProd :
      ∀ p : CMParams, p.α = p.m + p.γ - 1 →
        0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
        ∀ c : ℝ, 2 < c →
          ∀ U : ℝ → ℝ,
            InMonotoneWaveTrapSet (kappa c) (MChi p) U →
            FrozenStationaryWaveProfile p c U →
            ShenUpperBoundPositive p c U →
            ∀ κ₁, kappa c < κ₁ →
              κ₁ < min ((1 + p.α) * kappa c)
                (min (p.m * kappa c + 1 / 2) 1) →
              HasWaveRightTailAsymptotic c κ₁ U) :
    Paper1PositiveCriticalFrozenStationaryBranch := by
  intro p hα hχ0 hχsmall c hc
  rcases hroute p hα hχ0 hχsmall c hc with ⟨U, htrap, hprofile⟩
  have hupper := hupperProd p hα hχ0 hχsmall c hc U htrap hprofile
  exact ⟨U, hprofile, hupper,
    htailProd p hα hχ0 hχsmall c hc U htrap hprofile hupper⟩
-/

end ShenWork.Paper1
```

If `hupperProd` needs lower-pinned data rather than bare trap, then make `hroute` preserve and return that lower-pinned data and use `hU.bare` for the tail theorem.  That change is still wiring.

## 4. Which residual is wiring vs real analysis?

### More likely pure wiring

The final branch assembly is pure wiring once the two producers exist.  The reduction

```lean
(∀ x, 0 < U x) →
(∀ x, U x < upperBarrier (kappa c) (MChi p) x) →
ShenUpperBoundPositive p c U
```

is also pure wiring in the positive regime: rewrite `MChi p` to `(1 / (1 - p.χ)) ^ (1 / p.α)`, unfold `upperBarrier`, and use the strict inequality.

### Upper bound: partly wiring, partly analysis

Producing the strict exact upper-barrier inequality for the fixed point is not just wiring.  The trap only gives a non-strict inequality

```lean
U x ≤ upperBarrier (kappa c) (MChi p) x
```

Strictness requires a comparison/strong-maximum-principle argument using the stationary equation and the positive superbarrier.  This should be smaller than the sharp tail problem because much of the trap/superbarrier infrastructure already exists:

* `whole_line_super_barrier_pos` is already used by `rotheFloorResidual_of_trap_pos`;
* lower-pinned/nontriviality infrastructure exists;
* stationarity/regularity/SMP routes exist in `WaveTrapProps.lean` and `WavePaperStationaryFloor.lean`.

So the strict upper bound is likely the first residual to attack.

### Tail asymptotic: real new analysis

The right-tail residual is the major frontier.  Existing code repeatedly treats it as carried data.  The statement is not merely `U → 0`; it is the rate-sharp ratio statement

```lean
Real.exp ((κ₁ - kappa c) * x) *
  (U x / Real.exp (-(kappa c) * x) - 1) → 0.
```

The trap envelope cannot prove the leading coefficient is exactly `1`, and it cannot prove the full rate family.  The proof has to use the stationary equation at `+∞`, the characteristic root `kappa c`, and nonlinear remainder estimates corresponding to the three rate restrictions

```lean
(1 + p.α) * kappa c,
p.m * kappa c + 1 / 2,
1.
```

This is not present in the repository except for the explicit logistic profile, and that explicit proof is not usable for the produced fixed point without an equality theorem.

## 5. Explicit logistic profile is not a valid closure route

The following exact lemmas are useful seed/examples but must not be used to close the positive branch for the produced profile:

* `logisticProfile_shenUpperBoundPositive`
* `logisticProfile_hasWaveRightTailAsymptotic`
* `logisticProfile_positive_construction_seed_data`
* `logisticProfile_positive_construction_seed_data_of_chi_lt_half_chiStar`

They all concern

```lean
logisticProfile (kappa c)
```

not the `U` returned by `b1_chiPos_existence_*`.  I found no theorem proving that the positive Rothe/Schauder fixed point coincides with the explicit logistic profile.  Replacing the produced profile by `logisticProfile` would therefore be a fake closure.

## 6. Recommended next Lean work order

1. **Specialize/export the positive route at exact height `MChi p`.**  The final `ShenUpperBoundPositive` target uses exactly the positive-regime `MChi` constant, so avoid producing only a larger-trap witness.
2. **Add the pure lemma `ShenUpperBoundPositive_of_pos_strict_upperBarrier_MChi`.**  This is a small deterministic proof and will make the remaining upper-bound theorem sharply isolated.
3. **Prove `positive_lowerPinnedStationary_strict_upperBarrier_MChi`.**  This is the strict-comparison/SMP step.  It should consume the lower-pinned produced object and `FrozenStationaryWaveProfile.stationary_eq`.
4. **Only then attack `HasWaveRightTailAsymptotic_of_positive_stationary`.**  Treat it as new asymptotic analysis, not a wrapper around existing trap lemmas.
5. **Add the final branch wrapper in `StatementAssembly.lean` or a new assembly file.**  This wrapper should be essentially the `Paper1PositiveCriticalFrozenStationaryBranch_of_chiPos_routeA` skeleton above.
