# PAPER1-POSITIVE-STRICT-BARRIER-PRODUCER-ROUTE

Repo: `xiangyazi24/Shen_work`  
Source inspected: current `main` around `7dcd04a3`, including the later `StatementAssembly.lean` split after `5cde97f2`.

Question answered: the smallest honest route to **produce**

```lean
∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

for the lower-pinned positive stationary profile, without merely carrying `ShenUpperBoundPositive p c U`.

## Executive route

Do **not** start with a global comparison theorem for

```lean
fun x => upperBarrier (kappa c) (MChi p) x - U x
```

as if it were a smooth `C²` gap.  The barrier is

```lean
upperBarrier κ M x = min M (Real.exp (-κ * x))
```

and is nonsmooth at the unique interface `Real.exp (-κ * x) = M`.  Current source even has the formal obstruction

```lean
not_differentiableAt_upperBarrier_of_interface
```

so a global classical maximum principle for `upperBarrier - U` is the wrong first API.

The smallest honest API is:

1. keep the produced object in the lower-pinned trap,
2. prove **local contact contradictions** on the constant branch, exponential branch, and interface,
3. assemble these contradictions with the non-strict trap bound into the strict barrier comparison, and
4. feed that into the already-committed pure wrapper

```lean
ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
```

This keeps the residual strictly smaller than `ShenUpperBoundPositive`: the producer proves no-contact with the construction barrier, not positivity or the paper-facing `MChi` normalization.

## 1. Current theorem names/files that nearly imply strict upper-barrier

### Pure strict-barrier-to-Shen wiring already exists

File: `ShenWork/Paper1/StatementAssembly.lean`

```lean
ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
```

Statement shape:

```lean
(hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
(hpos : ∀ x, 0 < U x)
(hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x) :
ShenUpperBoundPositive p c U
```

This is exactly the pure wrapper we want to consume after no-contact is proved.  The same file also defines:

```lean
Paper1PositiveCriticalFrozenStationaryStrictBarrierBranch
paper1_positiveCriticalBranch_of_strictBarrier
Paper1MainStatementStrictBarrierData
```

These are good final wiring interfaces; they intentionally do **not** produce the strict comparison.

### Positive upper-barrier supersolution facts

File: `ShenWork/Paper1/WaveSuperBarrierPos.lean`

Main grep targets:

```lean
whole_line_super_barrier_pos
chemFlux_deriv_neg_chi_le_at_interface_pos
frozenWaveOperator_upperBarrier_interface_nonpos_pos
```

`whole_line_super_barrier_pos` proves, for a trapped old profile `u`, that the barrier is a weak whole-line frozen supersolution:

```lean
InWaveTrapSet κ M u →
∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

under the positive-sensitivity regime, `α = m + γ - 1`, `0 < κ`, `κ < 1`, `p.m * κ ≤ 1`, `1 ≤ M`, the `MChi` budget, and `c = κ + κ⁻¹`.

Away from the interface, the file’s header points to the branch facts in `Statements.lean`:

```lean
frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
frozenWaveOperator_upperBarrier_const_region_nonpos_pos
Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
```

Mismatch: these are weak supersolution inequalities for the barrier.  They do not, by themselves, prove that a stationary subprofile cannot touch the barrier.

### Upper-barrier branch and interface calculus

File: `ShenWork/Paper1/Statements.lean`

Useful exact names:

```lean
upperBarrier
upperBarrier_eq_M_of_le_exp
upperBarrier_eq_exp_of_exp_le
upperBarrier_eventuallyEq_const_of_lt
upperBarrier_eventuallyEq_exp_of_lt
upperBarrier_deriv_eq_zero_of_const_lt
upperBarrier_deriv_eq_exp_of_lt
upperBarrier_iteratedDeriv_two_eq_zero_of_const_lt
upperBarrier_iteratedDeriv_two_eq_exp_of_lt
upperBarrier_eventuallyEq_const_left_of_interface
upperBarrier_eventuallyEq_exp_right_of_interface
upperBarrier_derivWithin_left_eq_zero_of_interface
upperBarrier_derivWithin_right_eq_exp_of_interface
not_differentiableAt_upperBarrier_of_interface
frozenWaveOperator_upperBarrier_const_region_eq
```

These are the exact tools for avoiding a fake global `C²` barrier proof.  The interface facts should be used for a one-sided contradiction if contact occurs at the kink.

### Produced-object facts from lower-pinned construction

File: `ShenWork/Paper1/WaveRotheSchauder.lean`

Useful exact names:

```lean
InLowerPinnedMonotoneTrap
InLowerPinnedMonotoneTrap.bare
InLowerPinnedMonotoneTrap.lower
InLowerPinnedMonotoneTrap.profileNontrivial
InLowerPinnedMonotoneTrap.pos
b1_chiNeg_existence_of_lowerPinnedSchauderData_stationary_rootPin
b1_chiNeg_existence_of_lowerBarrierPinnedSchauderData_stationary_rootPin
```

Despite the historical `chiNeg` prefix, the lower-pinned Schauder wrapper is sign-agnostic at this layer.  Its conclusion is exactly the shape the positive branch should preserve:

```lean
∃ U, InLowerPinnedMonotoneTrap κ M φ U ∧
  FrozenStationaryWaveProfile p c U
```

Mismatch: the current positive wrappers in `WaveRothePos.lean` generally erase the lower pin and return only

```lean
∃ U, InMonotoneWaveTrapSet κ M U ∧ FrozenStationaryWaveProfile p c U
```

For the strict upper-barrier producer, keep the lower-pinned witness.

### Existing maximum-principle infrastructure

File: `ShenWork/Paper1/WaveTrapProps.lean`

Useful names:

```lean
StationaryStrongMaxPrinciple
StationaryLinearGronwallData
stationaryJet_zero_of_gronwall_right
stationaryLinearGronwallData_of_trap
stationaryStrongMaxPrinciple_of_linearGronwall
stationaryStrongMaxPrinciple_of_trap_regularity
stationaryStrongMaxPrinciple_of_trap
stationaryStrongMaxPrinciple_of_odeUniqueness
```

Mismatch: these prove positivity/no-zero-contact for a nonnegative stationary profile `U`.  They do not directly prove no-contact for `upperBarrier - U`, because that gap is not packaged as a stationary trapped profile and the barrier is nonsmooth at the interface.

File: `ShenWork/Paper1/NoSmallLeftPocket.lean`

Reusable maximum-principle pieces:

```lean
deriv_deriv_nonneg_of_isLocalMin
exists_interior_min_left
noSmallInteriorMin
strictlyPositiveAtLeft_of_noSmallInteriorMin
```

Mismatch: this is left-floor/small-density machinery, not an upper-barrier comparison theorem.  But `deriv_deriv_nonneg_of_isLocalMin` and the style of packaging a local contradiction are exactly the right pattern for the new no-contact API.

### Explicit logistic profile facts are not producers for the constructed profile

File: `ShenWork/PDE/TravelingWaveConstruction.lean`

Names:

```lean
logisticProfile_shenUpperBoundPositive
logisticProfile_hasWaveRightTailAsymptotic
logisticProfile_positive_construction_seed_data
logisticProfile_positive_construction_seed_data_of_chi_lt_half_chiStar
```

Mismatch: all concern `logisticProfile (kappa c)`, not the non-explicit fixed point `U`.  They should not be used to close this residual unless a theorem proves the constructed `U` is that logistic profile.

## 2. Is a strong maximum/comparison route mathematically valid?

Yes, but the valid route is **branchwise plus one-sided interface**, not a single smooth global comparison against `upperBarrier`.

The comparison should be against the local smooth branches:

```lean
B_const x = MChi p
B_exp x   = Real.exp (-(kappa c) * x)
```

and then against the one-sided interface data.  The global theorem should be only an assembler.

### Required sub-obligations

For the produced positive profile:

```lean
hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
       (lowerBarrierPlateau (kappa c) κtilde D) U
hprofile : FrozenStationaryWaveProfile p c U
```

we need the following non-circular inputs, all satisfiable from current routes or from local comparison lemmas.

#### Common data

* `hU.bare` gives non-strict trap membership:

  ```lean
  U x ≤ upperBarrier (kappa c) (MChi p) x
  ```

* `hU.pos (lowerBarrierPlateau_pos ...)` or `hprofile.U_pos` gives positivity.
* `hprofile.stationary_eq` gives stationarity:

  ```lean
  ∀ x, frozenWaveOperator p c U U x = 0
  ```

* regularity for local comparison: at minimum, differentiability of `U` and `deriv U` on the branch.  The already-existing C² producers in `WaveTrapProps.lean` and `WavePaperStationaryFloor.lean` are the right source.
* superbarrier inequalities from `whole_line_super_barrier_pos` and the away-from-interface branch theorems.

#### Constant branch no-contact

Branch condition:

```lean
MChi p < Real.exp (-(kappa c) * x)
```

Here `upperBarrier = MChi p` locally.  Need to show contact

```lean
U x = MChi p
```

is impossible.

Recommended split:

* If `0 < p.χ`, then prove `1 < MChi p`; combine monotonicity plus `U → 1` at `-∞` to get `U x ≤ 1`, hence `U x < MChi p`.  This is mostly order/limit wiring once `MChi` strictness is proved.
* If `p.χ = 0`, then `MChi p = 1`, and this becomes the classical no-finite-contact with the left equilibrium `1`.  This needs a real strong maximum/unique-continuation lemma: if a nonconstant stationary profile with right decay touches `1` at a finite point in the plateau branch, it cannot remain a valid wave.  Do not claim this from trap membership alone.

#### Exponential branch no-contact

Branch condition:

```lean
Real.exp (-(kappa c) * x) < MChi p
```

Here `upperBarrier = expDecay (kappa c)` locally.  Contact means

```lean
U x = Real.exp (-(kappa c) * x)
```

At such an interior contact, the gap `B_exp - U` has a local minimum zero.  The local proof should consume:

* stationarity of `U`,
* the exponential-region barrier inequality from `whole_line_super_barrier_pos` / `frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg`,
* C² regularity of `U`, and
* a one-dimensional strong comparison or contact contradiction for the smooth branch.

This is the main new comparison lemma.  It is smaller than `ShenUpperBoundPositive` because it only rules out equality on the smooth exponential branch.

#### Interface no-contact

Interface condition:

```lean
Real.exp (-(kappa c) * x) = MChi p
```

At the interface, a very small and honest theorem should rule out contact by one-sided derivatives, without stationarity.

If `U ≤ upperBarrier`, `U x = MChi p`, and `U` is differentiable at `x`, then the one-sided gap derivatives force contradictory inequalities:

* from the left, `upperBarrier` has derivative `0`, so contact gives a constraint on `deriv U x`;
* from the right, `upperBarrier` has derivative `-kappa c * MChi p`, so contact gives the opposite strict constraint.

The existing facts

```lean
upperBarrier_derivWithin_left_eq_zero_of_interface
upperBarrier_derivWithin_right_eq_exp_of_interface
not_differentiableAt_upperBarrier_of_interface
```

are exactly the right API.  This interface theorem is strictly smaller than any PDE comparison theorem and should be proved first.

## 3. Minimal honest Lean decomposition

### 3.1 Local contact-contradiction API

Do not make a package field named `ShenUpperBoundPositive`.  If a temporary API package is useful, make it a package of local **contact contradictions**.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps
import ShenWork.Paper1.NoSmallLeftPocket

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Local no-contact facts for the canonical positive upper barrier.

This is intentionally not `ShenUpperBoundPositive` and not even the global strict
barrier statement.  It only says that equality is impossible on each local
piece of `upperBarrier`. -/
structure PositiveUpperBarrierContactContradictions
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  const_branch :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) →
      U x = MChi p → False
  exp_branch :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) → False
  interface :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p →
      U x = MChi p → False

/-- Pure assembly: non-strict trap bound plus local no-contact gives strict
comparison with the nonsmooth barrier. -/
theorem strict_upperBarrier_MChi_of_contactContradictions
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hno : PositiveUpperBarrierContactContradictions p c U) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x := by
  intro x
  -- sketch:
  -- have hle : U x ≤ upperBarrier (kappa c) (MChi p) x := by
  --   exact htrap.trap.upper x   -- unfold/accessor as available
  -- rcases lt_or_eq_of_le hle with hlt | heq
  -- · exact hlt
  -- · rcases lt_trichotomy (Real.exp (-(kappa c) * x)) (MChi p) with hExpLt | hEq | hMLt
  --   · have hB : upperBarrier (kappa c) (MChi p) x = Real.exp (-(kappa c) * x) :=
  --       upperBarrier_eq_exp_of_exp_le hExpLt.le
  --     exact False.elim (hno.exp_branch x hExpLt (by simpa [hB] using heq))
  --   · have hB : upperBarrier (kappa c) (MChi p) x = MChi p :=
  --       upperBarrier_eq_M_of_le_exp hEq.ge
  --     exact False.elim (hno.interface x hEq (by simpa [hB] using heq))
  --   · have hB : upperBarrier (kappa c) (MChi p) x = MChi p :=
  --       upperBarrier_eq_M_of_le_exp hMLt.le
  --     exact False.elim (hno.const_branch x hMLt (by simpa [hB] using heq))
  sorry

end ShenWork.Paper1
```

The `sorry` above marks the intended proof body only; do not commit it as code.  It should be a short proof once the exact `InWaveTrapSet` upper-bound accessor is selected.

### 3.2 Interface contact theorem: prove this first

```lean
import ShenWork.Paper1.Statements

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Interface contact is impossible for any differentiable profile lying below
`upperBarrier`.

This is a one-sided calculus lemma, not a PDE lemma.  It is the cleanest way to
handle the nonsmooth kink. -/
theorem upperBarrier_interface_contact_absurd_of_differentiable
    {κ M : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M)
    (hbelow : ∀ y, U y ≤ upperBarrier κ M y)
    (hUdiff : DifferentiableAt ℝ U x)
    (hx : Real.exp (-κ * x) = M)
    (hcontact : U x = M) :
    False := by
  -- proof route:
  -- left side: `upperBarrier = M`, so the gap `M - U` has one-sided minimum 0.
  -- right side: `upperBarrier = expDecay κ`, whose one-sided derivative is `-κ*M`.
  -- differentiability of U forces incompatible one-sided derivative inequalities.
  -- consume:
  --   upperBarrier_derivWithin_left_eq_zero_of_interface
  --   upperBarrier_derivWithin_right_eq_exp_of_interface
  --   hUdiff.derivWithin uniqueDiffWithinAt_Iio/Ioi
  sorry

end ShenWork.Paper1
```

This theorem is satisfiable and non-circular: it assumes only non-strict barrier membership, differentiability of `U`, and actual equality at the kink, then derives contradiction from one-sided slopes.

### 3.3 Constant branch contact theorem

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Constant-branch contact contradiction for the positive stationary profile.

This is local to the branch `MChi p < exp(-(kappa c)*x)`.  It should be proved
by a case split on `p.χ = 0` versus `0 < p.χ`:
* if `0 < p.χ`, prove `1 < MChi p` and use monotonicity plus `U → 1` at `-∞`;
* if `p.χ = 0`, use a stationary strong maximum/unique-continuation argument
  ruling out finite contact with the equilibrium `1`. -/
theorem positive_constBranch_contact_absurd_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hbranch : MChi p < Real.exp (-(kappa c) * x))
    (hcontact : U x = MChi p) :
    False := by
  -- real residual, not pure wiring
  -- suggested sublemmas:
  --   one_lt_MChi_of_chi_pos_lt_one
  --   antitone_le_of_tendsto_atBot_one
  --   chiZero_no_finite_contact_one_of_stationary
  sorry

end ShenWork.Paper1
```

This theorem is smaller than `ShenUpperBoundPositive`: it rules out one equality case on one branch.

### 3.4 Exponential branch contact theorem

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Exponential-branch contact contradiction for the positive stationary profile.

This is the main smooth-branch comparison lemma.  It should use the exponential
branch of the positive upper-barrier supersolution plus stationarity of `U`. -/
theorem positive_expBranch_contact_absurd_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ} {x : ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hbranch : Real.exp (-(kappa c) * x) < MChi p)
    (hcontact : U x = Real.exp (-(kappa c) * x)) :
    False := by
  -- real residual, not pure wiring
  -- consume/derive:
  --   hprofile.stationary_eq
  --   hU.bare.trap
  --   frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
  --   or whole_line_super_barrier_pos specialized to the branch
  --   C² regularity from the stationary Green/Rothe regularity route
  --   a one-dimensional strong comparison/contact contradiction for
  --     gap = expDecay (kappa c) - U
  sorry

end ShenWork.Paper1
```

This is the hardest part of the strict upper-bound producer.

### 3.5 Produce all contact contradictions and assemble strict barrier

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheSchauder
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.WaveTrapProps

open Filter Topology Real Set

namespace ShenWork.Paper1

/-- Producer of the local contact-contradiction API from the actual positive
lower-pinned stationary object. -/
theorem positiveUpperBarrier_contactContradictions_of_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    -- either derive this from the profile's regularity field, or carry the exact
    -- C¹ fact if `FrozenStationaryWaveProfile` does not expose it directly:
    (hUdiff : ∀ x, DifferentiableAt ℝ U x) :
    PositiveUpperBarrierContactContradictions p c U := by
  refine
    { const_branch := ?_
      exp_branch := ?_
      interface := ?_ }
  · intro x hbranch hcontact
    exact positive_constBranch_contact_absurd_of_lowerPinnedStationary
      hα hχ_nonneg hχ_small hc hgap hD hU hprofile hbranch hcontact
  · intro x hbranch hcontact
    exact positive_expBranch_contact_absurd_of_lowerPinnedStationary
      hα hχ_nonneg hχ_small hc hgap hD hU hprofile hbranch hcontact
  · intro x hinterface hcontact
    have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hχ_small (min_le_left _ _)
    have hχ_lt_one : p.χ < 1 := by linarith
    have hMpos : 0 < MChi p := by
      -- from one_le_MChi_of_chi_nonneg_lt_one or direct positivity
      exact lt_of_lt_of_le zero_lt_one
        (one_le_MChi_of_chi_nonneg_lt_one p hχ_nonneg hχ_lt_one)
    exact upperBarrier_interface_contact_absurd_of_differentiable
      (κ := kappa c) (M := MChi p) (U := U) (x := x)
      (kappa_pos_of_two_lt hc) hMpos
      (by
        intro y
        -- exact trap upper-bound accessor from `hU.bare`
        -- e.g. `exact hU.bare.trap.upper y`
        sorry)
      (hUdiff x) hinterface hcontact

/-- Strict upper-barrier producer.  This is the main theorem to feed into
`ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi`. -/
theorem strict_upperBarrier_MChi_of_positive_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hUdiff : ∀ x, DifferentiableAt ℝ U x) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x := by
  exact strict_upperBarrier_MChi_of_contactContradictions hU.bare
    (positiveUpperBarrier_contactContradictions_of_lowerPinnedStationary
      hα hχ_nonneg hχ_small hc hgap hD hU hprofile hUdiff)

/-- Final upper-bound producer, still smaller than the whole positive branch
because it produces only `ShenUpperBoundPositive`, not the tail asymptotic. -/
theorem ShenUpperBoundPositive_of_positive_lowerPinnedStationary
    {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
    (hα : p.α = p.m + p.γ - 1)
    (hχ_nonneg : 0 ≤ p.χ)
    (hχ_small : p.χ < min (1 / 2 : ℝ) (chiStar p))
    (hc : 2 < c)
    (hgap : 0 < κtilde - kappa c) (hD : 0 < D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (hprofile : FrozenStationaryWaveProfile p c U)
    (hUdiff : ∀ x, DifferentiableAt ℝ U x) :
    ShenUpperBoundPositive p c U := by
  have hχ_lt_half : p.χ < (1 / 2 : ℝ) :=
    lt_of_lt_of_le hχ_small (min_le_left _ _)
  have hχ_lt_one : p.χ < 1 := by linarith
  exact ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
    hχ_nonneg hχ_lt_one hprofile.U_pos
    (strict_upperBarrier_MChi_of_positive_lowerPinnedStationary
      hα hχ_nonneg hχ_small hc hgap hD hU hprofile hUdiff)

end ShenWork.Paper1
```

Again, the `sorry` markers are proposal placeholders only; the committed Lean should introduce these theorem statements only when their proofs are being supplied or when the exact remaining hypothesis is explicitly exposed.

## 4. Recommended proof order

1. **Pure assembly first**: prove `strict_upperBarrier_MChi_of_contactContradictions`.  This is just `lt_or_eq_of_le`, `lt_trichotomy`, and the existing `upperBarrier_eq_*` lemmas.
2. **Interface no-contact second**: prove `upperBarrier_interface_contact_absurd_of_differentiable`.  This is one-sided calculus and avoids the PDE.
3. **Constant branch third**: prove the easy `0 < χ` case using `1 < MChi p`; isolate the `χ = 0` no-finite-contact theorem separately.
4. **Exponential branch last**: prove the smooth-branch comparison theorem using the positive exponential-region supersolution and stationarity.  This is the real PDE comparison step.
5. **Only then expose `ShenUpperBoundPositive_of_positive_lowerPinnedStationary`** and feed it into the existing strict-barrier branch wrapper.

## 5. False or vacuous routes to avoid

* Do not derive strictness from `InMonotoneWaveTrapSet` alone.  The trap carries only non-strict `U ≤ upperBarrier`.
* Do not use a global classical maximum principle on `upperBarrier - U` without handling the interface.  `upperBarrier` is not differentiable at the kink.
* Do not introduce a field

  ```lean
  strict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x
  ```

  and then call that a producer.  If a package is used, make it local contact contradictions or lower-level comparison data.
* Do not use `StationaryStrongMaxPrinciple` as if it directly applies to `upperBarrier - U`.  It is for positivity/no-zero-contact of stationary trapped profiles, not for a nonsmooth gap against the upper barrier.
* Do not replace the constructed profile by `logisticProfile (kappa c)`.  Existing logistic lemmas are useful checks/examples, but they are not facts about the Route-A fixed point `U`.
* Do not erase the lower pin too early.  The lower-pinned object supplies positivity/nontriviality and is the correct input to comparison and later tail-squeeze arguments.
