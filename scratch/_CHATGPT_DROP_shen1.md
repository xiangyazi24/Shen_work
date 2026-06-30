# Q2300 shen1 — Paper1 positive upper-contact audit

Repo audited: `xiangyazi24/Shen_work` on `main`.

Scope note: the new local `UpperBarrierContact.lean` names mentioned in the prompt (`PositiveUpperBarrierSmoothBranchResidual`, `Paper1PositiveLowerRawCapRouteAParamData`, etc.) do not appear on committed `main` yet.  This audit is therefore anchored to committed APIs and to the intended local definitions from the prompt.

## Executive conclusion

There is a split answer.

* `exp_operator_compare_at_contact` looks **plausibly provable now** from committed local-calculus/max-principle ingredients, but not by a single existing theorem.  It should be the next short Lean proof target, not a long-term analytic residual.
* `exp_strict_super_at_contact` should **remain an honest analytic residual** for now.  Current superbarrier APIs prove only `≤ 0`, not `< 0`, and Route-A/raw lower pin data does not currently provide the strict elliptic/chemotactic slack needed to upgrade the exponential branch.
* `no_const_left_plateau` can be discharged for positive branch profiles once you have both a left limit `Tendsto U atBot (𝓝 1)` and `MChi p ≠ 1`.  In the standard positive assumptions currently used in the statement layer, `0 ≤ p.χ` is not enough because `p.χ = 0` is allowed and then `MChi p = 1` is expected.  Minimal extra scalar assumption: either carry `MChi p ≠ 1`, or carry `0 < p.χ` plus the existing `MChi_eq_rpow_of_chi_nonneg_lt_one` normalization and `p.χ < 1`.

## Committed API facts that matter

### Upper barrier and smooth regions

The upper barrier is still the raw min barrier:

```lean
def upperBarrier (κ M : ℝ) : ℝ → ℝ :=
  fun x => min M (Real.exp (-κ * x))
```

The key branch-local rewrites/projections are committed:

```lean
upperBarrier_eq_M_of_le_exp
upperBarrier_eq_exp_of_exp_le
upperBarrier_eventuallyEq_const_of_lt
upperBarrier_eventuallyEq_exp_of_lt
upperBarrier_deriv_eq_zero_of_const_lt
upperBarrier_deriv_eq_exp_of_lt
upperBarrier_iteratedDeriv_two_eq_zero_of_const_lt
upperBarrier_iteratedDeriv_two_eq_exp_of_lt
upperBarrier_contDiffAt_two_of_ne_interface
```

So at an exponential-branch point

```lean
hx : Real.exp (-(kappa c) * x) < MChi p
```

you can get, with `κ := kappa c` and `M := MChi p`, all of:

```lean
upperBarrier (kappa c) (MChi p) x = Real.exp (-(kappa c) * x)
upperBarrier (kappa c) (MChi p) =ᶠ[𝓝 x] expDecay (kappa c)
ContDiffAt ℝ 2 (upperBarrier (kappa c) (MChi p)) x
```

The first comes from `upperBarrier_eq_exp_of_exp_le hx.le`; the local smoothness comes from `upperBarrier_contDiffAt_two_of_ne_interface` with `ne_of_lt hx`.

### Positive superbarrier APIs

Committed positive whole-line superbarrier:

```lean
theorem whole_line_super_barrier_pos
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hmκ : p.m * κ ≤ 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hc : c = κ + κ⁻¹) :
    InWaveTrapSet κ M u →
    ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

Its exponential branch internally calls:

```lean
frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
```

and its constant branch internally calls:

```lean
frozenWaveOperator_upperBarrier_const_region_nonpos_pos
```

There is also the away-from-interface wrapper:

```lean
theorem Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
    (p : CMParams) {c κ M : ℝ} {u : ℝ → ℝ}
    (hκ : 0 < κ) (hκ1 : κ < 1) (hc : c = κ + κ⁻¹)
    (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
    (hα : p.α = p.m + p.γ - 1)
    (hmκ : p.m * κ ≤ 1)
    (hM : 1 ≤ M)
    (hMchi : (1 / (1 - p.χ)) ^ (1 / p.α) ≤ M)
    (hu : InWaveTrapSet κ M u) :
    ∀ x, Real.exp (-κ * x) ≠ M →
      frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

Important: every one of these is non-strict.  There is no committed `... < 0` version of the positive exponential region.

The committed exponential formula is:

```lean
theorem frozenWaveOperator_exp_eq
    (p : CMParams) {c κ : ℝ} {u : ℝ → ℝ}
    (hc : 2 ≤ c) (hκ : κ = kappa c)
    (_hu : IsCUnifBdd u) (_hu_nonneg : ∀ x, 0 ≤ u x) (x : ℝ) :
    frozenWaveOperator p c u (expDecay κ) x =
      -(expDecay κ x) * (expDecay κ x) ^ p.α
      - p.χ * deriv (fun y => (expDecay κ y) ^ p.m *
          deriv (frozenElliptic p u) y) x
```

This formula shows exactly why strictness is delicate: the logistic part is strictly negative, but the chemotactic term can be positive and is only bounded non-strictly by the committed positive-superbarrier estimates.

### Stationary regularity and SMP APIs

The exact regularity frontier is:

```lean
def StationaryC2RegularityFromEquation
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        Differentiable ℝ U ∧ Differentiable ℝ (deriv U)
```

This is enough for first derivatives and for a direct second-derivative-at-a-local-max bridge, but it is not literally the `ContDiffAt ℝ 2 U x` input expected by the existing `iteratedDeriv2_le_of_isLocalMax_sub` helper.

The committed strong maximum principle is only a positivity theorem:

```lean
def StationaryStrongMaxPrinciple
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        ProfileNontrivial U →
          ∀ x, 0 < U x
```

It does not compare `U` with the upper barrier.  It cannot prove either smooth upper-contact field by itself.

### One-sided max-estimate / comparison APIs

The key committed local estimate is:

```lean
theorem implicitStep_oneSided_max_estimate
    (p : CMParams) {c M C_chem : ℝ} {u W B : ℝ → ℝ} {x₀ : ℝ}
    (hM : 0 ≤ M)
    (hWmem : W x₀ ∈ Set.Icc (0 : ℝ) M)
    (hBmem : B x₀ ∈ Set.Icc (0 : ℝ) M)
    (hBW : B x₀ ≤ W x₀)
    (hderiv1 : deriv W x₀ = deriv B x₀)
    (hderiv2 : iteratedDeriv 2 W x₀ ≤ iteratedDeriv 2 B x₀)
    (hchem : -p.χ * (deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀)
        ≤ C_chem * (W x₀ - B x₀)) :
    frozenWaveOperator p c u W x₀ - frozenWaveOperator p c u B x₀
      ≤ (reactionLip p.α M + C_chem) * (W x₀ - B x₀)
```

The key flux split is:

```lean
theorem chemFlux_increment_split
    (p : CMParams) {u W B : ℝ → ℝ} {x₀ : ℝ}
    (hu : IsCUnifBdd u) (hu_nonneg : ∀ y, 0 ≤ u y)
    (hWdiff : DifferentiableAt ℝ W x₀) (hBdiff : DifferentiableAt ℝ B x₀)
    (hderiv1 : deriv W x₀ = deriv B x₀) :
    deriv (chemFlux p u W) x₀ - deriv (chemFlux p u B) x₀
      = p.m * deriv (frozenElliptic p u) x₀
          * ((W x₀) ^ (p.m - 1) - (B x₀) ^ (p.m - 1)) * deriv W x₀
        + ((W x₀) ^ p.m - (B x₀) ^ p.m) * deriv (deriv (frozenElliptic p u)) x₀
```

This is exactly the right shape for the exponential contact operator comparison: at contact `W x₀ = B x₀`, both power differences vanish, so the chem increment is `0` once the derivative equality is available.

## Field 2: `exp_operator_compare_at_contact`

### Verdict

This field is likely provable from the current committed APIs with a small local bridge theorem.  It should not be treated as a deep Route-A analytic residual.

### Proof route

Let:

```lean
κ := kappa c
M := MChi p
B := upperBarrier κ M
```

At an exponential-branch contact:

```lean
hx  : Real.exp (-(kappa c) * x) < MChi p
hUx : U x = Real.exp (-(kappa c) * x)
```

1. Trap gives global nonpositivity of `φ := U - B`:

```lean
∀ y, U y - B y ≤ 0
```

because `htrap.le_upperBarrier y`.

2. The exponential branch rewrite gives:

```lean
B x = Real.exp (-(kappa c) * x)
```

so `hUx` gives `φ x = 0`.  Hence `x` is a local maximum of `φ`.

3. From `StationaryC2RegularityFromEquation`:

```lean
rcases hreg U htrap hstat with ⟨hUdiff, hUd_diff⟩
```

so `U` is differentiable and `deriv U` is differentiable.

4. The barrier is smooth at `x` by:

```lean
upperBarrier_contDiffAt_two_of_ne_interface (ne_of_lt hx)
```

5. At the local max, get first derivative equality:

```lean
deriv U x = deriv B x
```

6. Prove a missing local bridge for the second derivative inequality:

```lean
-- target bridge, no new analytic assumption:
-- from hloc, hUdiff, hUd_diff, and hBC2:
--   iteratedDeriv 2 U x ≤ iteratedDeriv 2 B x
```

The committed helper

```lean
iteratedDeriv2_le_of_isLocalMax_sub
```

already proves this if both sides are `ContDiffAt ℝ 2`.  Since `hreg` gives `Differentiable ℝ U ∧ Differentiable ℝ (deriv U)`, the narrow missing bridge should avoid demanding global `ContDiffAt` and instead prove the needed pointwise linearity/second-derivative inequality directly from differentiability of `deriv U` at the point.

A good name would be:

```lean
iteratedDeriv2_le_of_isLocalMax_sub_of_deriv_differentiable
```

7. Use `chemFlux_increment_split` with `W := U`, `B := upperBarrier κ M`, `u := U`.  Because `U x = B x`, the two power differences are zero, so the chem increment is zero.  This discharges `hchem` in `implicitStep_oneSided_max_estimate` with `C_chem := 0`.

8. Range hypotheses for `implicitStep_oneSided_max_estimate` are routine from:

```lean
htrap.nonneg x
htrap.le_M x
upperBarrier_nonneg
upperBarrier_le_M
```

9. `implicitStep_oneSided_max_estimate` then gives:

```lean
frozenWaveOperator p c U U x -
  frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x ≤ 0
```

which is the desired `exp_operator_compare_at_contact` after rearranging.

### Recommendation

Prove this next as a local theorem, independent of Route-A raw/plateau lower pins.  Route-A data is not needed here; trap + stationarity + regularity + branch contact are enough.

Suggested target name:

```lean
positiveUpperBarrier_expOperatorCompareAtContact_of_regular_stationary
```

The only missing Lean bridge is the pointwise second-derivative inequality from `StationaryC2RegularityFromEquation`; the chem part is already essentially contained in `chemFlux_increment_split`.

## Field 3: `exp_strict_super_at_contact`

### Verdict

This should remain an honest analytic residual.

The committed APIs give:

```lean
frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x ≤ 0
```

but not:

```lean
frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0
```

at exponential-branch contact.

### Why current APIs do not prove it

On the exponential branch, `upperBarrier` is locally `expDecay`, and the committed formula is:

```lean
frozenWaveOperator p c U (expDecay (kappa c)) x =
  -(expDecay (kappa c) x) * (expDecay (kappa c) x) ^ p.α
  - p.χ * deriv (fun y => (expDecay (kappa c) y) ^ p.m *
      deriv (frozenElliptic p U) y) x
```

The first term is strictly negative, but for `p.χ ≥ 0` the chemotactic term can have the opposite sign.  The positive superbarrier proof controls that term only non-strictly.  The proof of `whole_line_super_barrier_pos` explicitly routes the exponential case through the non-strict regional theorem:

```lean
frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
```

There is no committed theorem named like any of the following:

```lean
frozenWaveOperator_upperBarrier_exp_region_neg_of_chi_nonneg
frozenWaveOperator_upperBarrier_exp_region_strict_neg_of_chi_nonneg
whole_line_super_barrier_pos_strict
```

or any theorem that turns Route-A lower-pinning into strict slack in the frozen elliptic/chemotaxis bound.

### Why Route-A/raw cap data does not currently close it

The Route-A/raw lower pin is excellent for right-tail squeeze; committed APIs include:

```lean
HasWaveRightTailAsymptotic_of_lowerPinnedRawMonotoneTrap
```

which produces the sharp right-tail family from raw lower-pinned trap membership.  But the strict superbarrier residual is a pointwise statement about the cross-frozen operator of the upper barrier at a contact point.  It depends on the frozen elliptic field and its derivative through the chemotaxis term.  Current lower-pin/tail theorems do not provide a strict pointwise estimate of:

```lean
deriv (fun y => (expDecay (kappa c) y) ^ p.m * deriv (frozenElliptic p U) y) x
```

or a strict version of the positive regional superbarrier inequality.

Thus a direct proof of `exp_strict_super_at_contact` would require a new analytic theorem, for example one of:

```lean
-- strict regional superbarrier, probably the cleanest formulation
-- ∀ x, Real.exp (-κ * x) < M ->
--   frozenWaveOperator p c u (upperBarrier κ M) x < 0

-- or a contact-specific strict theorem
-- ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
--   U x = Real.exp (-(kappa c) * x) ->
--   frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0
```

The first global strict regional theorem may be too strong unless the proof extracts genuine slack from `p.χ < chiStar p` and the chemotaxis estimates.  The second contact-specific theorem is safer and better aligned with the local no-contact route.

### Likely false / too-strong assumptions to avoid

Do not assume any of these without a new proof:

```lean
whole_line_super_barrier_pos ... -> F(B) x < 0
Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa ... -> F(B) x < 0
StationaryStrongMaxPrinciple ... -> U x < upperBarrier ... x
RouteA raw lower pin -> strict exp-branch superbarrier at contact
```

They are not consequences of the committed statements.  The first two are only non-strict.  The strong maximum principle only gives `0 < U`.  The raw lower pin currently feeds the right-tail squeeze, not a strict local elliptic flux estimate.

## Constant branch: `no_const_left_plateau`

### What is already provable

For a monotone trapped profile, contact with the constant branch forces a whole left plateau.  This is purely order-theoretic and uses only:

```lean
htrap.le_M
htrap.antitone
```

Proof shape:

```lean
-- If U x = M and y ≤ x, then antitonicity gives U x ≤ U y,
-- while trap gives U y ≤ M.  Hence U y = M.
```

For the canonical positive branch:

```lean
M := MChi p
```

this reduces constant-branch no-contact to `no_const_left_plateau` exactly as your local residual intends.

### When `no_const_left_plateau` is discharged

If you have:

```lean
hlim : Tendsto U atBot (𝓝 (1 : ℝ))
hMne : MChi p ≠ 1
```

then a left plateau at `MChi p` is impossible, because the plateau gives:

```lean
Tendsto U atBot (𝓝 (MChi p))
```

and uniqueness of limits gives `MChi p = 1`.

This is the narrowest useful discharge lemma:

```lean
-- theorem no_const_left_plateau_of_tendsto_atBot_one
--     (hlim : Tendsto U atBot (𝓝 (1 : ℝ)))
--     (hMne : MChi p ≠ 1) :
--     ∀ x, MChi p < Real.exp (-(kappa c) * x) ->
--       (∀ y, y ≤ x -> U y = MChi p) -> False
```

### Are the needed hypotheses currently present?

The left limit is present whenever the local route packages a `FrozenStationaryWaveProfile p c U`, because that structure carries the left-end convergence to `1`.  The existing statement-layer positive branch explicitly asks for:

```lean
FrozenStationaryWaveProfile p c U
```

in `Paper1PositiveCriticalFrozenStationaryBranch`.

The scalar `MChi p ≠ 1` is **not** supplied by the current standard positive-branch assumptions alone:

```lean
0 ≤ p.χ
p.χ < min (1 / 2 : ℝ) (chiStar p)
```

because `p.χ = 0` is allowed.  Existing normalization lemmas include:

```lean
MChi_eq_rpow_of_chi_nonneg_lt_one
one_le_MChi_of_chi_nonneg_lt_one
```

These give the right normalization/weak lower bound, but not strict inequality when `χ = 0` is included.

Minimal extra scalar assumption:

```lean
hMne : MChi p ≠ 1
```

or, semantically cleaner for the positive-only strict branch:

```lean
hχ_pos : 0 < p.χ
```

with the already available `p.χ < 1`.  From `0 < p.χ`, one should prove a small scalar lemma:

```lean
-- theorem MChi_ne_one_of_chi_pos_lt_one
--     (hχ_pos : 0 < p.χ) (hχ_lt : p.χ < 1) :
--     MChi p ≠ 1
```

using `MChi_eq_rpow_of_chi_nonneg_lt_one` and positivity of `1 / p.α`.

If the intended positive branch continues to include `χ = 0`, then `hlim : U → 1` at `-∞` cannot rule out a left plateau at level `1`; a different unique-continuation/no-flat-halfline theorem would be needed, and I do not see such a committed theorem for this upper contact problem.

## Recommended next Paper1 steps

### Step 1: prove the operator-compare field and remove it from the residual

Add a theorem with target shape:

```lean
-- target shape only
-- theorem positiveUpperBarrier_expOperatorCompareAtContact_of_regular_stationary
--     {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
--     (hM0 : 0 ≤ MChi p)
--     (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
--     (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
--     (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
--     ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
--       U x = Real.exp (-(kappa c) * x) ->
--         frozenWaveOperator p c U U x ≤
--           frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x
```

Do it by proving the small local bridges described above.  This is a realistic direct path from committed APIs.

### Step 2: discharge constant branch when `χ > 0` is available

For branch wrappers that really target positive sensitivity (`0 < p.χ`), add:

```lean
-- target scalar helper
-- theorem MChi_ne_one_of_chi_pos_lt_one ... : MChi p ≠ 1
```

then use `FrozenStationaryWaveProfile.lim_neg_inf.1` and the left-plateau contradiction to discharge `no_const_left_plateau`.

If the wrapper intentionally keeps `0 ≤ p.χ`, continue carrying `no_const_left_plateau`, or split off the `χ = 0` case with a separate argument.

### Step 3: keep only strict exponential superbarrier as analytic frontier

After Step 1, the residual can be narrowed to:

```lean
structure PositiveUpperBarrierRemainingContactResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) ->
      (∀ y, y ≤ x -> U y = MChi p) -> False
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0
```

And if Step 2 applies (`FrozenStationaryWaveProfile` plus `MChi p ≠ 1`), it can be narrowed further to just:

```lean
structure PositiveUpperBarrierExpStrictContactResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0
```

This is the honest remaining mathematical obstacle.

## Final answer

For Route-A/fixed-point profiles, the next committed Lean work should be:

1. **Prove `exp_operator_compare_at_contact`** from local contact calculus using `implicitStep_oneSided_max_estimate`, `chemFlux_increment_split`, and a new pointwise second-derivative bridge from `StationaryC2RegularityFromEquation`.  This is plausible and should not remain a long-term residual.
2. **Do not claim `exp_strict_super_at_contact` from the current superbarrier APIs.**  It is not a consequence of `whole_line_super_barrier_pos` or the regional non-strict lemmas.  Keep it as the analytic residual unless a strict positive exponential-region superbarrier theorem is added.
3. **Discharge the constant residual only under `Tendsto U atBot (𝓝 1)` and `MChi p ≠ 1`.**  In the current branch assumptions, add `0 < p.χ` or carry `MChi p ≠ 1`; `0 ≤ p.χ` is too weak because it admits `χ = 0`.

No `sorry`/`admit` Lean patch is recommended for the strict exponential field at this stage.
