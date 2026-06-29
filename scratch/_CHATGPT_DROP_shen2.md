# Q2264 shen2: Paper1 positive right-tail asymptotic route

Audited target: `xiangyazi24/Shen_work` main around `7dcd04a300abeb15aab275dfd96bf0ffbd868ff1`.

## Bottom line

There is currently no in-repository theorem that produces

```lean
HasWaveRightTailAsymptotic c κ₁ U
```

from a constructed positive frozen stationary profile, even with a strict positive upper bound. The only theorem with the expected producer-looking name,

```lean
HasWaveRightTailAsymptotic_of_stationary
```

in `ShenWork/Paper1/StationaryUpperTail.lean`, is a no-op wrapper: it assumes `htail : HasWaveRightTailAsymptotic c κ₁ U` and returns `htail`.

The smallest honest route is not to pretend that `HasWaveUpperTailBound` or `ShenUpperBoundPositive` contains asymptotic information. It is to add one positive-tail linearization residual: stationary equation plus elliptic tail estimates plus nonlinear forcing decay plus leading coefficient normalization. A pure wrapper can then convert that residual into the current `Paper1PositiveCriticalFrozenStationaryBranch` shape.

## 1. Relevant theorem names, files, and grep targets

### Current branch consumer

File: `ShenWork/Paper1/StatementAssembly.lean`

Relevant names:

```lean
Paper1PositiveCriticalFrozenStationaryBranch
paper1_Theorem_1_1_of_constructionNegSMPProvider
Paper1MainStatementSMPMainlineData
```

Current target shape:

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

Grep target:

```bash
grep -R -n -E 'Paper1PositiveCriticalFrozenStationaryBranch|paper1_Theorem_1_1_of_constructionNegSMPProvider|Paper1MainStatementSMPMainlineData' ShenWork/Paper1/StatementAssembly.lean
```

### Definition and current consumers of the tail predicate

File: `ShenWork/Paper1/Statements.lean`

Relevant names:

```lean
HasWaveRightTailAsymptotic
HasWaveRightTailAsymptotic.ratio_tendsto_one
HasWaveRightTailAsymptotic.tendsto_atTop_zero
```

Definition:

```lean
def HasWaveRightTailAsymptotic (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp ((κ₁ - kappa c) * x) *
      (U x / Real.exp (-(kappa c) * x) - 1))
    atTop (𝓝 0)
```

File: `ShenWork/Paper1/Lemma25Helpers.lean`

Relevant consumer names:

```lean
HasWaveRightTailAsymptotic.eventually_abs_sub_exp_le
HasWaveRightTailAsymptotic.eventually_abs_sub_abs_le_two_exp
WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic
```

These are downstream consumers. They extract error bounds and weighted closeness from an already supplied asymptotic. They do not produce the asymptotic.

Grep target:

```bash
grep -R -n -E 'def HasWaveRightTailAsymptotic|theorem HasWaveRightTailAsymptotic|eventually_abs_sub_exp_le|eventually_abs_sub_abs_le_two_exp|WeightedL2InitialCloseness.of_common_waveRightTailAsymptotic' ShenWork/Paper1/Statements.lean ShenWork/Paper1/Lemma25Helpers.lean
```

### The non-producer wrapper that must not be mistaken for a proof

File: `ShenWork/Paper1/StationaryUpperTail.lean`

Relevant name:

```lean
HasWaveRightTailAsymptotic_of_stationary
```

Actual shape:

```lean
theorem HasWaveRightTailAsymptotic_of_stationary
    {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c)
    (hU : InMonotoneWaveTrapSet (kappa c) 1 U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hκ₁lo : kappa c < κ₁)
    (hκ₁hi : κ₁ < min ((1 + p.α) * kappa c) (min (p.m * kappa c + 1 / 2) 1))
    (htail : HasWaveRightTailAsymptotic c κ₁ U) :
    HasWaveRightTailAsymptotic c κ₁ U :=
  htail
```

Grep target:

```bash
grep -R -n 'HasWaveRightTailAsymptotic_of_stationary' ShenWork/Paper1/StationaryUpperTail.lean
```

### Positive frozen stationary profile construction route

File: `ShenWork/Paper1/WaveRothePos.lean`

Relevant names:

```lean
rotheFloorResidual_of_trap_pos
b1_chiPos_existence
b1_chiPos_existence_rootPin
b1_chiPos_existence_profileClean
b1_chiPos_existence_profileClean_rootPin
b1_chiPos_existence_stationary_floor
b1_chiPos_existence_stationary_floor_rootPin
b1_chiPos_existence_profileClean_stationary_floor
b1_chiPos_existence_profileClean_stationary_floor_rootPin
```

The cleanest existing positive-side producer is the `b1_chiPos_existence_*` family. These theorems produce

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

under carried Rothe/Schauder, Green/stationarity, floor, flatness, and tail-uniformity inputs. They do not produce either `ShenUpperBoundPositive p c U` or `HasWaveRightTailAsymptotic c κ₁ U` for the produced `U`.

Grep target:

```bash
grep -R -n -E 'rotheFloorResidual_of_trap_pos|b1_chiPos_existence' ShenWork/Paper1/WaveRothePos.lean
```

### Upper-tail, strict-tail, and trap APIs

Files:

```text
ShenWork/Paper1/Statements.lean
ShenWork/PDE/TravelingWaveConstruction.lean
ShenWork/Paper1/Lemma25Helpers.lean
```

Relevant names:

```lean
ShenUpperBoundPositive
ShenUpperBoundPositive.pos
ShenUpperBoundPositive.lt_exp
ShenUpperBoundPositive.le_exp
ShenUpperBoundPositive.shift_right
ShenUpperBoundPositive.shift_right_of_two_lt
ShenUpperBoundPositive.hasStrictWaveUpperTailBound
HasWaveUpperTailBound
HasStrictWaveUpperTailBound
HasStrictWaveUpperTailBound.hasWaveUpperTailBound
InMonotoneWaveTrapSet.hasWaveUpperTailBound_of_pos
FrozenStationaryWaveProfile.hasWaveUpperTailBound_of_inMonotoneWaveTrapSet
```

The explicit logistic-profile file also has useful non-route examples:

```lean
logisticProfile_shenUpperBoundPositive
logisticProfile_hasStrictWaveUpperTailBound
logisticProfile_hasStrictWaveUpperTailBound_of_one_le_MChi
logisticProfile_hasStrictWaveUpperTailBound_of_stable_regime
```

Those are for the explicit profile `logisticProfile (kappa c)`, not for the constructed stationary fixed point.

Grep target:

```bash
grep -R -n -E 'ShenUpperBoundPositive|HasWaveUpperTailBound|HasStrictWaveUpperTailBound|hasWaveUpperTailBound|logisticProfile_shenUpperBoundPositive|logisticProfile_hasStrictWaveUpperTailBound' ShenWork/Paper1/Statements.lean ShenWork/PDE/TravelingWaveConstruction.lean ShenWork/Paper1/Lemma25Helpers.lean
```

### Lemma 5 and elliptic/resolvent infrastructure

Files:

```text
ShenWork/Paper1/StatementAssembly.lean
ShenWork/Paper1/Statements.lean
ShenWork/Paper1/Lemma25Helpers.lean
```

Relevant names:

```lean
Paper1Lemma51FrontierData
paper1_Lemma_5_1_of_frontierData
Lemma_5_1.of_resolvent_derivative_bounds
Lemma_5_3_pair_weighted_signal_derivative_from_Lemma_2_5
Lemma_5_3_pair_weighted_signal_derivative_of_tail_bounds
Lemma_5_3_pair_weighted_signal_derivative_of_regular_waves
Lemma_5_3_profile_initial_signal_derivative_from_Lemma_2_5
frozenElliptic_C2_globally
frozenElliptic_bounded
frozenElliptic_deriv_bounded
V_eq_frozenElliptic_strong
IsTravelingWave.V_eq_frozenElliptic_full
Remark_5_2_frozen_monotone_trap_direct
```

`Paper1Lemma51FrontierData` is important but it is a frontier bundle: its fields are carried inputs such as `resolvent`, `continuous`, `deriv_tends`, `deriv_bound`, and `deriv_exp`. It does not itself prove the sharp right-tail asymptotic. The Section 5 signal estimates control `V` and `V'` in weighted norms; they are necessary for the chemotaxis forcing estimate, but they do not determine the coefficient of `e^{-κx}` in `U`.

Grep target:

```bash
grep -R -n -E 'Paper1Lemma51FrontierData|Lemma_5_1.of_resolvent_derivative_bounds|Lemma_5_3_pair_weighted_signal_derivative|frozenElliptic_C2_globally|frozenElliptic_bounded|frozenElliptic_deriv_bounded|V_eq_frozenElliptic|Remark_5_2_frozen_monotone_trap_direct' ShenWork/Paper1/StatementAssembly.lean ShenWork/Paper1/Statements.lean ShenWork/Paper1/Lemma25Helpers.lean
```

## 2. Minimal mathematically valid route

Let

```lean
κ := kappa c
```

For `2 < c`, `κ` is the slow positive spatial decay root. The target is equivalent to

```text
U x = exp(-κ x) + o(exp(-κ₁ x))    as x → +∞
```

for every admissible `κ₁` in the open interval

```text
κ < κ₁ < min ((1 + α)κ) (min (mκ + 1/2) 1).
```

The upper bound

```text
0 < U x < exp(-κx)
```

is only a one-sided envelope. It does not fix the leading coefficient. The correct proof has to use the stationary equation and the construction normalization.

The honest route is:

1. **Produce the stationary profile.** Use the existing positive Rothe/Schauder route, most likely the `b1_chiPos_existence_profileClean_stationary_floor_rootPin` branch or a nearby specialization, to get the constructed `U` with `FrozenStationaryWaveProfile p c U` and the trap/floor data needed for normalization.

2. **Produce the strict positive upper bound.** Prove or carry a separate positive-side strict bound theorem for the produced `U`:

   ```lean
   ShenUpperBoundPositive p c U
   ```

   Existing logistic-profile theorems are not enough because they apply to the explicit barrier profile, not the fixed point. This bound gives positivity, boundedness, and `U = O(exp(-κx))` on the right.

3. **Identify the elliptic signal.** Use the `FrozenStationaryWaveProfile` to pass to `IsTravelingWave` and then use the existing resolvent/regularity infrastructure to identify

   ```lean
   V = frozenElliptic p U
   ```

   The useful search targets here are `IsTravelingWave.V_eq_frozenElliptic_full`, `V_eq_frozenElliptic_strong`, and the `frozenElliptic_*` estimates.

4. **Get elliptic right-tail estimates.** From `U = O(exp(-κx))`, get `U^γ = O(exp(-γκx))`. Passing through the whole-line resolvent for `1 - ∂xx` gives right-tail estimates for `V`, `V'`, and, if needed, `V''`. The branch bound uses a safe `1/2` margin, so the needed committed target can be phrased as a half-rate estimate for the elliptic derivatives. Existing Lemma 2.5 and Lemma 5.3 APIs are relevant here, but they currently stop at weighted signal/derivative estimates and do not by themselves provide the sharp `U` coefficient.

5. **Rewrite the stationary equation as a linearized equation at zero.** Schematic sign convention, to be checked by unfolding `frozenWaveOperator` before coding:

   ```text
   L_c U = F,
   L_c U := U'' + c U' + U,
   F := U^(1+α) + χ ∂x(U^m V').
   ```

   The exact signs are not important for the size estimate, but they are important when committing the Lean theorem.

6. **Prove forcing decay.** The three upper bounds in the branch statement match the three forcing mechanisms:

   ```text
   κ₁ < (1+α)κ       from U^(1+α),
   κ₁ < mκ + 1/2    from U^m times elliptic derivative decay,
   κ₁ < 1           from the elliptic/resolvent fast scale.
   ```

   This should be committed as a theorem producing a `LinearizedForcingLittleO` residual, not as `HasWaveRightTailAsymptotic` itself.

7. **Use variation of constants for the scalar linear ODE.** For

   ```text
   L_c w = f,
   ```

   the homogeneous right-tail modes are `exp(-κx)` and the faster root. Variation of constants gives

   ```text
   U x = A exp(-κx) + O(exp(-κ₁x))
   ```

   for every admissible `κ₁` once the forcing has the decay above.

8. **Prove the leading coefficient is exactly one.** This is the main normalization point. Stationarity plus a strict upper bound can at best give `U x ~ A exp(-κx)` with `0 ≤ A ≤ 1`. The target requires `A = 1`. That must come from the specific construction: lower pin, floor, root pin, or a barrier contact/normalization argument. It cannot be inferred from `HasWaveUpperTailBound` or `ShenUpperBoundPositive` alone.

9. **Convert additive error to the current predicate.** This last step is pure algebra:

   ```text
   exp((κ₁-κ)x) * (U x / exp(-κx) - 1)
   = exp(κ₁x) * (U x - exp(-κx)).
   ```

   Therefore the proof should naturally produce an additive little-o error first, then wrap it into `HasWaveRightTailAsymptotic`.

## 3. Proposed smaller residual and pure wrapper

I would not replace the positive branch by another branch that carries the exact current `HasWaveRightTailAsymptotic` family. The smaller honest residual should name the linearization data. The final route theorem then converts the linearization data into the current asymptotic.

Proposed API skeleton:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRothePos
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Additive form of the sharp right-tail error.
This is algebraically equivalent to `HasWaveRightTailAsymptotic`, but it is the
natural output of variation of constants. -/
def RightTailAdditiveError (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp (κ₁ * x) *
      (U x - Real.exp (-(kappa c) * x)))
    atTop (𝓝 0)

/-- Leading coefficient normalization for the slow mode. -/
def RightTailLeadingCoefficientOne (c : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => U x / Real.exp (-(kappa c) * x))
    atTop (𝓝 1)

/-- A deliberately small elliptic tail residual. The exact committed version may
split this into fields for `V`, `V'`, and `V''`; the important point is that it is
about `frozenElliptic p U`, not about the final `HasWaveRightTailAsymptotic`. -/
def FrozenEllipticHalfTail (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  ∃ C R : ℝ, 0 < C ∧ ∀ x : ℝ, R ≤ x →
    |frozenElliptic p U x| + |deriv (frozenElliptic p U) x| ≤
      C * Real.exp (-(1 / 2 : ℝ) * x)

/-- Schematic nonlinear forcing in the linearized right-tail equation.
Before committing this definition, unfold `frozenWaveOperator` and fix the exact
sign convention. The sign does not affect the decay route, but it matters in Lean. -/
def stationaryTailForcing (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : ℝ → ℝ :=
  fun x =>
    (U x) ^ (1 + p.α) +
      p.χ * deriv (fun y => (U y) ^ p.m * deriv (frozenElliptic p U) y) x

/-- Forcing is little-o at every admissible right-tail rate. -/
def LinearizedForcingLittleO
    (p : CMParams) (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp (κ₁ * x) * stationaryTailForcing p c U x)
    atTop (𝓝 0)

/-- The residual that should replace carrying the full asymptotic family in the
positive branch. It names the linearization inputs and normalization needed to
prove the tail, but does not itself assert `HasWaveRightTailAsymptotic`. -/
structure PositiveTailLinearizationData
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  kappa_pos : 0 < kappa c
  stationary : ∀ x, frozenWaveOperator p c U U x = 0
  strict_upper : ShenUpperBoundPositive p c U
  leading_one : RightTailLeadingCoefficientOne c U
  elliptic_tail : FrozenEllipticHalfTail p c U
  forcing_decay :
    ∀ κ₁, kappa c < κ₁ →
      κ₁ < min ((1 + p.α) * kappa c)
        (min (p.m * kappa c + 1 / 2) 1) →
      LinearizedForcingLittleO p c κ₁ U

/-- The theorem to prove by linearized ODE plus variation of constants. -/
def PositiveTailLinearizationProducesAsymptotic : Prop :=
  ∀ {p : CMParams} {c κ₁ : ℝ} {U : ℝ → ℝ},
    PositiveTailLinearizationData p c U →
    kappa c < κ₁ →
    κ₁ < min ((1 + p.α) * kappa c)
      (min (p.m * kappa c + 1 / 2) 1) →
    HasWaveRightTailAsymptotic c κ₁ U

/-- Positive branch with the sharp tail replaced by linearization data. -/
structure Paper1PositiveCriticalFrozenStationaryBranchLinearized : Prop where
  produce :
    ∀ p : CMParams, p.α = p.m + p.γ - 1 →
      0 ≤ p.χ → p.χ < min (1 / 2 : ℝ) (chiStar p) →
      ∀ c : ℝ, 2 < c →
        ∃ U : ℝ → ℝ,
          FrozenStationaryWaveProfile p c U ∧
            ShenUpperBoundPositive p c U ∧
            PositiveTailLinearizationData p c U

/-- Pure wrapper from the smaller residual branch to the current branch. -/
theorem Paper1PositiveCriticalFrozenStationaryBranchLinearized.to_current
    (hlin : PositiveTailLinearizationProducesAsymptotic)
    (hbranch : Paper1PositiveCriticalFrozenStationaryBranchLinearized) :
    Paper1PositiveCriticalFrozenStationaryBranch := by
  intro p hpα hχ_nonneg hχ_lt c hc
  rcases hbranch.produce p hpα hχ_nonneg hχ_lt c hc with
    ⟨U, hprofile, hupper, htailData⟩
  refine ⟨U, hprofile, hupper, ?_⟩
  intro κ₁ hκ₁lo hκ₁hi
  exact hlin htailData hκ₁lo hκ₁hi

end

end ShenWork.Paper1
```

The residual above is smaller than carrying the current tail family because the branch only carries the ingredients of the linearization argument: stationarity, strict upper bound, leading coefficient one, elliptic half-tail, and nonlinear forcing decay. The actual `HasWaveRightTailAsymptotic` statement is produced once, in `PositiveTailLinearizationProducesAsymptotic`.

A slightly more incremental first step is to introduce the additive-error wrapper. This is less ambitious than the full linearization data, but still better than propagating the ratio predicate everywhere:

```lean
import ShenWork.Paper1.StatementAssembly

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

def RightTailAdditiveError (c κ₁ : ℝ) (U : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => Real.exp (κ₁ * x) *
      (U x - Real.exp (-(kappa c) * x)))
    atTop (𝓝 0)

/-- Pure algebra target: additive little-o implies the existing ratio form. -/
theorem RightTailAdditiveError.to_hasWaveRightTailAsymptotic
    {c κ₁ : ℝ} {U : ℝ → ℝ}
    (h : RightTailAdditiveError c κ₁ U) :
    HasWaveRightTailAsymptotic c κ₁ U := by
  -- Expected proof shape:
  --   unfold RightTailAdditiveError HasWaveRightTailAsymptotic at h ⊢
  --   convert h using 1
  --   ext x
  --   field_simp [Real.exp_ne_zero]
  --   rw [← Real.exp_add]
  --   ring_nf
  -- The only content is the identity
  --   exp((κ₁-κ)x) * (U/exp(-κx)-1)
  --     = exp(κ₁x) * (U-exp(-κx)).
  admit

end

end ShenWork.Paper1
```

The `admit` in the display above is not a suggested commit. It marks a tiny algebra proof obligation. The branch-level route should not use an axiom for this lemma.

## 4. APIs that are too weak, too strong, or misleading

### `HasWaveRightTailAsymptotic_of_stationary` is misleading

The name suggests a producer from stationarity. The theorem is actually:

```lean
... → (htail : HasWaveRightTailAsymptotic c κ₁ U) → HasWaveRightTailAsymptotic c κ₁ U
```

It should either be renamed to something like

```lean
HasWaveRightTailAsymptotic.of_stationary_of_tail
```

or removed from any producer route. Keeping the current name invites accidental circular proof plans.

### `Paper1PositiveCriticalFrozenStationaryBranch` is too coarse as a frontier

The branch currently hides three different analytic tasks under one existential:

```lean
FrozenStationaryWaveProfile p c U
ShenUpperBoundPositive p c U
∀ κ₁, ... → HasWaveRightTailAsymptotic c κ₁ U
```

The first is a Rothe/Schauder construction. The second is a strict maximum-principle or invariant-region statement. The third is a linearized asymptotic theorem. They should be split so that the tail proof has named residuals.

### `HasWaveUpperTailBound` is too weak for asymptotics

No theorem of the following shape should be expected:

```lean
HasWaveUpperTailBound p c U → HasWaveRightTailAsymptotic c κ₁ U
```

This is mathematically false. The upper bound only gives an envelope such as `U = O(exp(-κx))`. It does not imply

```text
U x / exp(-κx) → 1.
```

A simple model obstruction is `U_a x = a * exp(-κx)` with `0 < a < 1`. It has the same upper decay scale, but

```text
U_a x / exp(-κx) → a ≠ 1.
```

For any `κ₁ > κ`, the target expression behaves like

```text
exp((κ₁-κ)x) * (a - 1),
```

which does not tend to zero. Strict upper bounds do not fix this coefficient either.

### Stationarity plus upper bound still does not automatically fix coefficient one

The linearized ODE route gives

```text
U x = A exp(-κx) + lower order terms.
```

The current target demands `A = 1`. That is a construction normalization issue, not a generic consequence of stationarity. The proof must use the lower pin, floor, root pin, or a comparable normalization from the positive construction.

### Lemma 5.1 and Lemma 5.3 are necessary but not sufficient

The derivative and signal estimates around Lemma 5.1/Lemma 5.3 are relevant for bounding the elliptic contribution and the chemotaxis forcing. They do not by themselves prove the additive remainder

```text
U x - exp(-κx) = o(exp(-κ₁x)).
```

In particular, a derivative exponential estimate such as

```lean
|deriv U x| ≤ B1 * exp(-(kappa c) * x) + B2 * exp(-(kappa c) * p.γ * x)
```

is still only an upper estimate. It does not prove the coefficient `1` or the sharper cancellation against `exp(-κx)`.

### Explicit logistic profile APIs are non-routes for the constructed wave

The theorems in `ShenWork/PDE/TravelingWaveConstruction.lean` for

```lean
logisticProfile (kappa c)
```

are useful barriers and examples. They cannot be used to conclude the constructed stationary profile has the same sharp tail unless the construction is proved to select that exact profile, which it does not.

## Recommended implementation order

1. Add a new file, for example:

   ```text
   ShenWork/Paper1/PositiveRightTail.lean
   ```

2. First commit the pure algebra lemma:

   ```lean
   RightTailAdditiveError.to_hasWaveRightTailAsymptotic
   ```

3. Add `PositiveTailLinearizationData` and the pure branch wrapper shown above.

4. Prove elliptic half-tail estimates for `frozenElliptic p U` from `ShenUpperBoundPositive p c U` and existing resolvent APIs.

5. Define the exact `stationaryTailForcing` by unfolding `frozenWaveOperator`; do not guess signs in a committed theorem.

6. Prove `LinearizedForcingLittleO` for each admissible `κ₁`, using the three rate restrictions already present in the branch statement.

7. Prove the scalar variation-of-constants theorem for `L_c` with forcing little-o.

8. Prove `RightTailLeadingCoefficientOne` from the specific positive construction normalization. This is the critical non-generic step.

9. Only then replace the current carried `∀ κ₁, ... → HasWaveRightTailAsymptotic` obligation in the positive branch by the smaller linearization residual and route it through the pure wrapper.

## Final audit answer

The current code has many relevant consumers and estimates, but no producer of the positive branch sharp right-tail asymptotic. The smallest honest proof route is:

```text
constructed frozen stationary profile
+ strict positive upper bound
+ elliptic V tail estimates
+ nonlinear forcing decay in the linearized equation
+ variation of constants
+ leading coefficient one from construction normalization
⇒ additive sharp tail error
⇒ HasWaveRightTailAsymptotic
```

The no-go is absolute: `HasWaveUpperTailBound` alone, and even `HasStrictWaveUpperTailBound` alone, cannot imply the branch tail asymptotic because they do not determine the leading coefficient of the slow exponential mode.
