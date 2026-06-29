# Q2282 shen2: positive upper-barrier contact audit

Repo target: `xiangyazi24/Shen_work`, current `main` plus the visible `StatementAssembly.lean` contact/cap wrappers.

## Verdict

`PositiveUpperBarrierContactContradictions p c U` is **still a genuine residual as a whole**.

Current repo lemmas get very close:

* the lower-pinned cap route now closes the sharp right tail by pure squeeze;
* `whole_line_super_barrier_pos` proves the nonsmooth `upperBarrier (kappa c) (MChi p)` is a weak frozen supersolution for positive sensitivity;
* `StationaryC2RegularityFromEquation` / `stationaryStrongMaxPrinciple_of_trap` can provide C²-type regularity and lower positivity machinery;
* the upper-barrier branch lemmas compute the constant branch, exponential branch, and interface behavior.

But none of these gives the missing **upper strong-comparison / no-contact** principle.  The existing stationary strong maximum principle is a lower-zero principle for a stationary nonnegative profile; it does not apply to `upperBarrier - U`, and no theorem currently proves that a stationary solution strictly stays below a weak supersolution after contact is ruled out.

One piece is small and should be closed now: the **interface** no-contact follows from differentiability of `U` plus the one-sided slopes of `upperBarrier`.  The **constant** and **exponential** branch no-contact facts remain the real analytic atoms.

## Current contact split in `StatementAssembly.lean`

Relevant names already present:

```lean
import ShenWork.Paper1.StatementAssembly

namespace ShenWork.Paper1

#check PositiveUpperBarrierContactContradictions
#check strict_upperBarrier_MChi_of_contactContradictions
#check ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
#check Paper1PositiveCriticalFrozenStationaryContactBranch
#check paper1_positiveStrictBarrierBranch_of_contactBranch
#check paper1_positiveCriticalBranch_of_strictBarrier

end ShenWork.Paper1
```

Current record shape:

```lean
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
```

Current pure assembly already closed:

```lean
theorem strict_upperBarrier_MChi_of_contactContradictions
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hno : PositiveUpperBarrierContactContradictions p c U) :
    ∀ x, U x < upperBarrier (kappa c) (MChi p) x
```

Then:

```lean
theorem ShenUpperBoundPositive.of_pos_strict_upperBarrier_MChi
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hχ_nonneg : 0 ≤ p.χ) (hχ_lt : p.χ < 1)
    (hpos : ∀ x, 0 < U x)
    (hstrict : ∀ x, U x < upperBarrier (kappa c) (MChi p) x) :
    ShenUpperBoundPositive p c U
```

So the only upper-bound problem is producing the three no-contact fields.

## Existing lower-pinned tail route is closed

Relevant names in `StationaryUpperTail.lean`:

```lean
import ShenWork.Paper1.StationaryUpperTail

namespace ShenWork.Paper1

#check HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
#check lowerPinnedMonotoneTrap_tail_family_for_branch
#check HasWaveRightTailAsymptotic_of_stationary

end ShenWork.Paper1
```

Closed pure squeeze theorem:

```lean
theorem HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap
    {c κtilde D M κ₁ : ℝ} {U : ℝ → ℝ}
    (hD : 0 ≤ D)
    (hU : InLowerPinnedMonotoneTrap (kappa c) M
      (lowerBarrierPlateau (kappa c) κtilde D) U)
    (_hκ₁lo : kappa c < κ₁) (hκ₁hi : κ₁ < κtilde) :
    HasWaveRightTailAsymptotic c κ₁ U
```

Branch-rate wrapper:

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

`HasWaveRightTailAsymptotic_of_stationary` is still explicitly a carried wrapper for routes that do not preserve the lower pin.

## Existing strong-max / C² facts do not prove upper no-contact

Relevant names in `WaveTrapProps.lean`:

```lean
import ShenWork.Paper1.WaveTrapProps

namespace ShenWork.Paper1

#check StationaryStrongMaxPrinciple
#check StationaryLinearGronwallData
#check stationaryStrongMaxPrinciple_of_linearGronwall
#check StationaryC2RegularityFromEquation
#check StationaryGreenRepresentationFromEquation
#check stationaryC2RegularityFromEquation_of_trap
#check stationaryLinearGronwallData_of_trap
#check stationaryStrongMaxPrinciple_of_trap_regularity
#check stationaryStrongMaxPrinciple_of_trap

end ShenWork.Paper1
```

The important existing shapes are:

```lean
def StationaryStrongMaxPrinciple
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        ProfileNontrivial U →
          ∀ x, 0 < U x
```

and:

```lean
def StationaryC2RegularityFromEquation
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        Differentiable ℝ U ∧ Differentiable ℝ (deriv U)
```

These do **not** imply `PositiveUpperBarrierContactContradictions`:

* `StationaryStrongMaxPrinciple` only says a nontrivial nonnegative stationary trapped profile cannot touch `0`.  It does not compare `U` to a supersolution `W`.
* Applying it to `upperBarrier - U` is not available: `upperBarrier - U` is not known to be in a monotone trap, and it does not satisfy an equation of the form `frozenWaveOperator p c Z Z = 0`.
* `StationaryC2RegularityFromEquation` gives differentiability of `U`; it does not give a strong comparison or Hopf lemma against `upperBarrier`.

## Existing positive super-barrier facts are weak supersolution facts only

Relevant names in `WaveSuperBarrierPos.lean`:

```lean
import ShenWork.Paper1.WaveSuperBarrierPos

namespace ShenWork.Paper1

#check chemFlux_deriv_neg_chi_le_at_interface_pos
#check frozenWaveOperator_upperBarrier_interface_nonpos_pos
#check whole_line_super_barrier_pos

end ShenWork.Paper1
```

Main positive supersolution theorem:

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

For the positive branch this can be instantiated with:

```lean
κ := kappa c
M := MChi p
u := U
```

using existing side-condition names:

```lean
#check kappa_pos_of_two_lt
#check kappa_lt_one_of_two_lt
#check kappa_add_inv_eq_of_two_lt
#check one_le_MChi_of_chi_nonneg_lt_one
#check MChi_eq_rpow_of_chi_nonneg_lt_one
#check chiStar_le_one
```

But `whole_line_super_barrier_pos` is only:

```lean
frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x ≤ 0
```

It does not say strict `< 0`, and it does not include any theorem that converts weak supersolution + stationary solution + pointwise order into no-contact.

Relevant regional facts in `Statements.lean`:

```lean
import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

#check frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
#check frozenWaveOperator_upperBarrier_const_region_nonpos_pos
#check Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
#check Lemma_4_1_strengthened_away_from_interface_direct

end ShenWork.Paper1
```

Again: all are non-strict supersolution/region facts, not contact contradictions.

## Existing upper-barrier branch lemmas

Relevant names in `Statements.lean`:

```lean
import ShenWork.Paper1.Statements

namespace ShenWork.Paper1

#check upperBarrier
#check upperBarrier_eq_M_of_le_exp
#check upperBarrier_eq_exp_of_exp_le
#check upperBarrier_eventuallyEq_const_of_lt
#check upperBarrier_eventuallyEq_exp_of_lt
#check upperBarrier_deriv_eq_zero_of_const_lt
#check upperBarrier_deriv_eq_exp_of_lt
#check upperBarrier_iteratedDeriv_two_eq_zero_of_const_lt
#check upperBarrier_iteratedDeriv_two_eq_exp_of_lt
#check upperBarrier_eventuallyEq_const_left_of_interface
#check upperBarrier_eventuallyEq_exp_right_of_interface
#check upperBarrier_derivWithin_left_eq_zero_of_interface
#check upperBarrier_derivWithin_right_eq_exp_of_interface
#check not_differentiableAt_upperBarrier_of_interface

end ShenWork.Paper1
```

These prove the local shape and one-sided derivative behavior of the barrier.  They are enough to close the **interface** contact by a small calculus lemma, but not the smooth branch no-contact.

## What can be closed immediately: interface no-contact

The interface field should not remain an analytic residual.  Add this pure theorem and prove it from one-sided derivative estimates/order.

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveTrapProps
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Pure upper-barrier kink no-contact.
If a differentiable profile lies below `upperBarrier κ M`, it cannot touch the
barrier at the interface `exp (-κ x) = M`, because the left and right slopes of
the barrier are `0` and `-κ*M`. -/
-- theorem upperBarrier_interface_noContact_of_differentiableAt
--     {κ M : ℝ} {U : ℝ → ℝ} {x : ℝ}
--     (hκ : 0 < κ) (hM : 0 < M)
--     (hUdiff : DifferentiableAt ℝ U x)
--     (hle : ∀ y, U y ≤ upperBarrier κ M y)
--     (hx : Real.exp (-κ * x) = M)
--     (hcontact : U x = M) :
--     False

/-- Specialized interface no-contact for the positive `MChi` barrier, using the
C² regularity frontier to get differentiability of `U`. -/
-- theorem positiveUpperBarrier_interface_noContact_of_regular_stationary
--     {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
--     (hκ : 0 < kappa c) (hM : 0 < MChi p)
--     (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
--     (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
--     (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
--     ∀ x, Real.exp (-(kappa c) * x) = MChi p →
--       U x = MChi p → False

end

end ShenWork.Paper1
```

Proof sketch for `upperBarrier_interface_noContact_of_differentiableAt`:

* from `hle`, `U x = M`, and `upperBarrier_eventuallyEq_const_left_of_interface`, get left slopes forcing `deriv U x ≥ 0`;
* from `hle`, `U x = M`, and `upperBarrier_eventuallyEq_exp_right_of_interface`, get right slopes forcing `deriv U x ≤ -κ*M`;
* since `0 < κ` and `0 < M`, `-κ*M < 0`, contradiction.

This is pure local calculus.  It should be proved, not carried.

## What remains missing: smooth branch no-contact

The two real residual fields are:

```lean
const_branch :
  ∀ x, MChi p < Real.exp (-(kappa c) * x) →
    U x = MChi p → False

exp_branch :
  ∀ x, Real.exp (-(kappa c) * x) < MChi p →
    U x = Real.exp (-(kappa c) * x) → False
```

They require an upper strong-comparison principle for a stationary solution touching a weak supersolution on a smooth branch.  Current lemmas do not provide this.

A good residual to add is narrower than the full contact record:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveTrapProps
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- The remaining analytic atom for the positive branch after the interface kink
is closed by differentiability.  This is the upper strong-comparison/no-contact
principle on the two smooth branches of `upperBarrier (kappa c) (MChi p)`. -/
def PositiveUpperBarrierSmoothBranchNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  (∀ x, MChi p < Real.exp (-(kappa c) * x) →
      U x = MChi p → False) ∧
  (∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) → False)

/-- Assembly once the two smooth-branch no-contact facts and the pure interface
fact are available. -/
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hinterface :
      ∀ x, Real.exp (-(kappa c) * x) = MChi p →
        U x = MChi p → False) :
    PositiveUpperBarrierContactContradictions p c U :=
  { const_branch := hsmooth.1
    exp_branch := hsmooth.2
    interface := hinterface }

end

end ShenWork.Paper1
```

If you want the residual as a theorem-shaped analytic target with all positive-branch hypotheses exposed, use this shape:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveTrapProps
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Missing analytic target: strong no-contact on smooth branches of the positive
`MChi` upper barrier for the lower-pinned stationary profile. -/
-- theorem positiveUpperBarrier_smoothBranchNoContact_of_lowerPinned_stationary
--     {p : CMParams} {c κtilde D : ℝ} {U : ℝ → ℝ}
--     (hα : p.α = p.m + p.γ - 1)
--     (hχ_nonneg : 0 ≤ p.χ) (hχ : p.χ < chiStar p)
--     (hc : 2 < c)
--     (hmκ : p.m * kappa c ≤ 1)
--     (hD : 0 < D)
--     (htrap : InLowerPinnedMonotoneTrap (kappa c) (MChi p)
--       (lowerBarrierPlateau (kappa c) κtilde D) U)
--     (hprofile : FrozenStationaryWaveProfile p c U)
--     (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
--     PositiveUpperBarrierSmoothBranchNoContact p c U

end

end ShenWork.Paper1
```

That theorem is not presently derivable from named repo lemmas.  Its proof would need a real upper comparison/Hopf argument for the frozen nonlocal stationary equation, using:

```lean
whole_line_super_barrier_pos
frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
frozenWaveOperator_upperBarrier_const_region_nonpos_pos
StationaryC2RegularityFromEquation
```

plus a new comparison lemma for `upperBarrier - U` on a smooth branch.  That comparison lemma is the missing analytic atom.

## Why weak supersolution is insufficient

At a smooth contact point with `W := upperBarrier (kappa c) (MChi p)` and `U ≤ W`, one gets `Z := W - U ≥ 0`, `Z x = 0`, and, if smooth, `Z' x = 0`, `Z'' x ≥ 0`.  Since `W x = U x` and `W' x = U' x` at a smooth tangency, the nonlinear reaction and chemotaxis first-derivative terms cancel at the contact, so the operator comparison only gives a non-strict inequality consistent with `Z'' x = 0`.  The committed super-barrier theorem gives `frozenWaveOperator p c U W x ≤ 0`, while stationarity gives `frozenWaveOperator p c U U x = 0`; without a strong comparison principle, this does not yield `False`.

So the repo has a weak super-barrier, not a strict anti-contact theorem.

## Recommended next additions

Add these in a small file or near the existing contact wrappers:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveTrapProps
import ShenWork.Paper1.WaveSuperBarrierPos
import ShenWork.Paper1.StationaryUpperTail

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

-- Pure, should be proved immediately.
-- theorem upperBarrier_interface_noContact_of_differentiableAt
--     {κ M : ℝ} {U : ℝ → ℝ} {x : ℝ}
--     (hκ : 0 < κ) (hM : 0 < M)
--     (hUdiff : DifferentiableAt ℝ U x)
--     (hle : ∀ y, U y ≤ upperBarrier κ M y)
--     (hx : Real.exp (-κ * x) = M)
--     (hcontact : U x = M) :
--     False

-- Residual container: the actual remaining upper strong-comparison atom.
def PositiveUpperBarrierSmoothBranchNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  (∀ x, MChi p < Real.exp (-(kappa c) * x) →
      U x = MChi p → False) ∧
  (∀ x, Real.exp (-(kappa c) * x) < MChi p →
      U x = Real.exp (-(kappa c) * x) → False)

-- Pure assembly from the residual plus the interface theorem.
theorem PositiveUpperBarrierContactContradictions.of_smoothBranchNoContact
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hsmooth : PositiveUpperBarrierSmoothBranchNoContact p c U)
    (hinterface :
      ∀ x, Real.exp (-(kappa c) * x) = MChi p →
        U x = MChi p → False) :
    PositiveUpperBarrierContactContradictions p c U :=
  { const_branch := hsmooth.1
    exp_branch := hsmooth.2
    interface := hinterface }

end

end ShenWork.Paper1
```

## Final route answer

Do **not** try to derive `PositiveUpperBarrierContactContradictions` directly from `stationaryStrongMaxPrinciple_of_trap`, C² regularity, and `whole_line_super_barrier_pos`.  Those APIs do not expose upper strong comparison.

The honest decomposition is:

1. keep the lower-pinned cap route for `HasWaveRightTailAsymptotic`; it is already closed by `HasWaveRightTailAsymptotic_of_lowerPinnedMonotoneTrap` / `lowerPinnedMonotoneTrap_tail_family_for_branch`;
2. prove the pure interface no-contact lemma from differentiability and one-sided upper-barrier slopes;
3. carry or prove the new analytic atom `PositiveUpperBarrierSmoothBranchNoContact` for the constant and exponential smooth branches;
4. assemble `PositiveUpperBarrierContactContradictions` and then use the already-built wrappers to get `ShenUpperBoundPositive` and the current positive branch.
