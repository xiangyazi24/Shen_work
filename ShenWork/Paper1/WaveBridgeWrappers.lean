import ShenWork.Paper1.Statements
import ShenWork.Paper1.WaveEllipticMono

/-!
# B1 negative-branch bridge property-functions

This file produces the bridge "property-functions" consumed by
`Theorem_1_1.of_assumed_fixed_point_construction_branches`
(`ShenWork/Paper1/Statements.lean:16600`) via
`NegativeSensitivityWaveFixedPointConstruction.exists_fixed_limit_with_speed_bridge_data`
(`ShenWork/Paper1/Statements.lean:9879`).

For the negative branch, with
* `trap U := InMonotoneWaveTrapSet (kappa c) 1 U`
* `aux U := FrozenAuxiliaryLimitOutput p c (kappa c) 1 (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U`

the five property-functions are (exact shape verbatim from line 16609-16620):

1. `hstat`    : `∀ U, trap U → aux U → ∀ x, frozenWaveOperator p c U U x = 0`
2. `hlim_bot` : `∀ U, trap U → aux U → Tendsto U atBot (𝓝 1)`
3. `hVmono`   : `∀ U, trap U → aux U → ∀ x, deriv (frozenElliptic p U) x ≤ 0`
4. `hupper`   : `∀ U, trap U → aux U → ShenUpperBoundNegative c U`
5. `htail`    : `∀ U, trap U → aux U → ∀ κ₁, kappa c < κ₁ →
                  κ₁ < min ((1+p.α)*kappa c) (min (p.m*kappa c + 1/2) 1) →
                  HasWaveRightTailAsymptotic c κ₁ U`

PROVED here: `b1_neg_hVmono` (property-function 3).
STALLED (precise reports as block comments below): hstat (1), hlim_bot (2),
hupper (4), htail (5).
-/

open Filter Topology

namespace ShenWork.Paper1

/-- **Property-function 3 (`hVmono`).**  On a monotone wave trap the frozen
elliptic field's derivative is nonpositive everywhere.  The `aux` hypothesis is
not needed: monotonicity of `U` (carried by `InMonotoneWaveTrapSet`) already
forces `frozenElliptic p U` to be antitone, hence `deriv ≤ 0`.  This is exactly
the committed `frozenElliptic_deriv_nonpos_of_monotone_trap` (with `M = 1`). -/
theorem b1_neg_hVmono (p : CMParams) (c : ℝ) :
    ∀ U : ℝ → ℝ,
      InMonotoneWaveTrapSet (kappa c) 1 U →
        FrozenAuxiliaryLimitOutput p c (kappa c) 1
          (fun u => InMonotoneWaveTrapSet (kappa c) 1 u) U U →
          ∀ x, deriv (frozenElliptic p U) x ≤ 0 :=
  fun U hU _haux x =>
    frozenElliptic_deriv_nonpos_of_monotone_trap p (kappa c) 1 U hU x

/-
================================================================================
STALL REPORTS for the remaining four property-functions.
================================================================================

The four stalled property-functions all bottom out in ONE missing ingredient:
the fixed-point / orbit-limit identification is NOT exposed by `trap U` or
`aux U`.  Concretely:

  * `trap U = InMonotoneWaveTrapSet (kappa c) 1 U`
      = `InWaveTrapSet (kappa c) 1 U ∧ NonincreasingProfile U`
      = `IsCUnifBdd U ∧ (∀ x, 0 ≤ U x ∧ U x ≤ upperBarrier (kappa c) 1 x)
          ∧ Antitone U`.
    (defs: Statements.lean:4371 `InWaveTrapSet`, 4377 `InMonotoneWaveTrapSet`,
     3450 `upperBarrier κ M = min M (exp (-κ x))`.)
    Trap gives only NON-strict `0 ≤ U x` and `U x ≤ min 1 (exp(-κc x))`,
    plus antitonicity and CUnif-boundedness.  No lower barrier, no strict
    positivity, no equation.

  * `aux U = FrozenAuxiliaryLimitOutput p c (kappa c) 1 trap U U`
      (def Statements.lean:5380)
      = ∃ z, FrozenAuxiliarySolutionFrom p c U (upperBarrier (kappa c) 1) z
          ∧ (∀ t≥0, trap (z t)) ∧ (∀ x, Antitone (t ↦ z t x))
          ∧ ∀ x, Tendsto (t ↦ z t x) atTop (𝓝 (U x)).
    So `aux U` supplies a PARABOLIC ORBIT `z` (def `FrozenAuxiliarySolutionFrom`
    Statements.lean:5353: `z 0 = upperBarrier` and
    `∂_t z = frozenWaveOperator p c U (z t)`) that is trapped, antitone in time,
    and converges pointwise to `U`.  It does NOT supply that `U` itself is a
    fixed point of the auxiliary map, a Green identity at `U`, nor any
    stationarity statement.

--------------------------------------------------------------------------------
(1) hstat  —  ∀ U, trap U → aux U → ∀ x, frozenWaveOperator p c U U x = 0
--------------------------------------------------------------------------------
GOAL after `intro U hU haux x`:  `frozenWaveOperator p c U U x = 0`
  (target shape: Statements.lean:16610).

Closest committed lemma:
  `fixedPoint_stationary` (WaveAuxMap.lean:279):
      (hgreen : GreenIdentity p c lam U) → (hfix : auxMap p c lam U = U) →
        ∀ x, frozenWaveOperator p c U U x = 0.

MISSING HYPOTHESES:  both inputs of `fixedPoint_stationary`.
  - `GreenIdentity p c lam U`  — the analytic Green identity at the limit `U`.
  - `auxMap p c lam U = U`      — that `U` is a FIXED POINT of the auxiliary map.
Neither is derivable from `trap U` or `aux U`.  `aux U` only gives a parabolic
ORBIT `z` with `z t → U` pointwise and `∂_t z = frozenWaveOperator p c U (z t)`;
it does NOT give `∂_t z → 0` along the orbit, nor that the pointwise limit `U`
is a stationary point of the flow (orbit-limit ≠ fixed-point of `auxMap`; this
requires a compactness / continuity-of-the-map passage to the limit that is not
committed).  A grep for any committed bridge
`FrozenAuxiliaryLimitOutput → (GreenIdentity ∨ auxMap…=U ∨ frozenWaveOperator…=0)`
returns nothing (verified).  This is the genuine FP-identification gap
(orbit-limit vs. the stationary equation).

STALL: missing a committed theorem of the form
  `FrozenAuxiliaryLimitOutput … U U → auxMap p c lam U = U`
  (or directly `… → GreenIdentity p c lam U`), for the appropriate `lam`.

--------------------------------------------------------------------------------
(2) hlim_bot  —  ∀ U, trap U → aux U → Tendsto U atBot (𝓝 1)
--------------------------------------------------------------------------------
GOAL after `intro U hU haux`:  `Tendsto U atBot (𝓝 1)`
  (target shape: Statements.lean:16611).

Partial progress available from `trap U` alone:
  `InMonotoneWaveTrapSet.antitone hU : Antitone U` and
  `InMonotoneWaveTrapSet.nonneg hU : 0 ≤ U x`, and
  `InMonotoneWaveTrapSet.le_M hU : U x ≤ 1`.
So `U` is antitone and bounded in `[0,1]`; hence a left limit
`ℓ := lim_{x→-∞} U x ∈ [0,1]` EXISTS (monotone bounded).  But pinning `ℓ = 1`
needs:
  (a) strict positivity `ℓ > 0`  — would come from a LOWER barrier, which lives
      only inside `NegativeSensitivityWaveFixedPointConstruction` and is NOT
      exposed by `trap`/`aux`; and
  (b) the stationary equation at `x → -∞`, i.e. passing hstat through the limit
      to force `ℓ(1 - ℓ^a) = 0`, hence (with ℓ>0) `ℓ = 1`.

DEPENDENCY: (b) requires hstat (property-function 1), which is itself stalled
on the FP-identification gap above.  Therefore hlim_bot stalls on the SAME
gap, plus the additional un-exposed lower-barrier positivity.

STALL: depends on hstat (1) [FP-identification gap] AND on a strict-positivity
input (lower barrier) not carried by `trap`/`aux`.

--------------------------------------------------------------------------------
(4) hupper  —  ∀ U, trap U → aux U → ShenUpperBoundNegative c U
--------------------------------------------------------------------------------
GOAL after `intro U hU haux x`:
  `0 < U x ∧ U x < max 1 (Real.exp (-(kappa c) * x))`
  (def `ShenUpperBoundNegative` Statements.lean:382; target 16614).

What `trap U` provides (non-strict, from `InWaveTrapSet`/`upperBarrier`):
  `0 ≤ U x`                                 (InMonotoneWaveTrapSet.nonneg)
  `U x ≤ upperBarrier (kappa c) 1 x = min 1 (exp(-κc x)) ≤ max 1 (exp(-κc x))`.

MISSING:  BOTH inequalities must be STRICT, and the trap gives only `≤`:
  - strict positivity `0 < U x`:  needs a LOWER barrier `0 < lowerBarrier … x ≤ U x`.
    The lower barrier (`lowerBarrierPlateau_pos`, Statements.lean:4249) lives
    inside `NegativeSensitivityWaveFixedPointConstruction`, NOT in `trap`/`aux`.
  - strict upper `U x < max 1 (exp)`:  at `x = 0`, `min 1 (exp 0) = max 1 (exp 0) = 1`
    and trap only gives `U 0 ≤ 1`, NOT `U 0 < 1`.  Strictness here also needs the
    fixed-point structure (a stationary profile is `< 1` for finite `x`), again
    not exposed by `trap`/`aux`.

Closest committed lemmas: none produce `ShenUpperBoundNegative` from trap/aux —
grep shows `ShenUpperBoundNegative` appears in the codebase ONLY as a hypothesis
or as an explicit fixed-point obligation, never as a conclusion derived from
`InWaveTrapSet`/`InMonotoneWaveTrapSet`/`FrozenAuxiliaryLimitOutput` (verified).
(Contrast the positive branch, where `ShenUpperBoundPositive.inWaveTrapSet`
goes trap→tailbound, the OPPOSITE direction.)

STALL: missing strict lower bound (lower barrier, in the construction `h`, not
exposed by trap/aux) and strict upper bound at `x=0` (fixed-point structure).
`ShenUpperBoundNegative` is genuinely a carried fixed-point obligation, not a
trap consequence.

--------------------------------------------------------------------------------
(5) htail  —  ∀ U, trap U → aux U → ∀ κ₁, kappa c < κ₁ →
              κ₁ < min ((1+p.α)*kappa c) (min (p.m*kappa c + 1/2) 1) →
              HasWaveRightTailAsymptotic c κ₁ U
--------------------------------------------------------------------------------
GOAL after `intro U hU haux κ₁ hκ₁_lo hκ₁_hi`:
  `HasWaveRightTailAsymptotic c κ₁ U`
  (def Statements.lean:153:
     `Tendsto (x ↦ exp((κ₁-κc)x)·(U x / exp(-κc x) - 1)) atTop (𝓝 0)`;
   target 16615-16620).

This is a SHARP right-tail asymptotic: `U x = exp(-κc x)(1 + o(exp(-(κ₁-κc)x)))`
as `x → +∞`.  `trap U` gives only the crude two-sided envelope
`0 ≤ U x ≤ min 1 (exp(-κc x))` (upper barrier), which is NOT enough to pin the
RATIO `U x / exp(-κc x) → 1` with the required rate.  The sharp asymptotic is a
property of the STATIONARY solution of the frozen ODE (linearisation at the
right end), proved in the paper from the equation — it cannot follow from trap
membership plus the orbit data alone.

Closest committed lemmas: `HasWaveRightTailAsymptotic.*` in Lemma25Helpers.lean
and Statements.lean (159, 185, …) only CONSUME `HasWaveRightTailAsymptotic`
(extract `ratio_tendsto_one`, `tendsto_atTop_zero`); none PRODUCE it from
`trap`/`aux`.  Grep finds no `HasWaveRightTailAsymptotic …_of_inWaveTrapSet`
or `…_of_FrozenAuxiliaryLimitOutput` (verified).

STALL: the sharp tail asymptotic is a fixed-point/equation property, not a trap
consequence; depends on hstat (1) [the equation] plus a linearisation argument
at `+∞` that is not committed.  Missing: a committed theorem producing
`HasWaveRightTailAsymptotic` from the stationary equation `frozenWaveOperator
p c U U = 0` (which itself is stalled, property-function 1).

================================================================================
SUMMARY
  PROVED:  b1_neg_hVmono            (property-function 3) — clean, aux unused.
  STALLED: hstat (1), hlim_bot (2), hupper (4), htail (5).
  Root cause: trap+aux expose only a trapped, antitone, pointwise-converging
  parabolic ORBIT.  They do NOT expose (i) the stationary equation / Green
  identity / auxMap fixed-point [blocks hstat, and via hstat blocks hlim_bot &
  htail], nor (ii) the lower barrier / strict bounds carried by the construction
  `NegativeSensitivityWaveFixedPointConstruction` [blocks hupper, and the ℓ>0
  half of hlim_bot].
================================================================================
-/

end ShenWork.Paper1
