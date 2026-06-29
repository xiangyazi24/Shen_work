# Q2289 shen1 — audit of positive upper smooth-branch no-contact

Repo: `xiangyazi24/Shen_work`  
Branch written: `chatgpt-scratch`  
Question: can the positive upper-barrier **smooth branch** no-contact fields be proved from current committed Lean APIs, or should they be decomposed into a smaller frontier?

## Bottom line

I do **not** see a committed proof of either smooth-branch no-contact field from the current APIs.

The interface field is special and is already provable from the committed kink theorem:

```lean
maxSub_upperBarrier_ne_interface
```

because a contact at the kink gives a local maximum of `U - upperBarrier`, and the concave corner forbids a local maximum for differentiable `U`.

For the two smooth branches, the same local-maximum argument only gives a **zero** maximum of `U - upperBarrier`, not a positive maximum and not a kink contradiction.  The committed Rothe maximum-principle closers rule out a **positive overshoot**; they do not rule out zero contact.

The honest recommendation is:

* keep the interface theorem as already proved from `maxSub_upperBarrier_ne_interface`;
* replace the raw smooth no-contact pair by a smaller residual:
  * constant branch: carry only a **no-left-plateau** residual, because constant-branch contact is provably equivalent to a left plateau using only antitonicity and `U ≤ M`;
  * exponential branch: carry a **contact operator-comparison residual** plus a **strict exp-branch superbarrier-at-contact residual**.  These are narrower and more diagnostic than raw no-contact, and align with the available one-sided max-estimate API.

## API audit

### 1. Superbarrier APIs

Relevant committed names:

```lean
whole_line_super_barrier_pos
Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa
frozenWaveOperator_upperBarrier_const_region_nonpos_pos
frozenWaveOperator_upperBarrier_exp_region_nonpos_of_chi_nonneg
frozenWaveOperator_upperBarrier_const_region_eq
frozenWaveOperator_exp_eq
upperBarrier_eventuallyEq_const_of_lt
upperBarrier_eventuallyEq_exp_of_lt
upperBarrier_contDiffAt_two_of_ne_interface
```

What they give:

```lean
whole_line_super_barrier_pos ... :
  InWaveTrapSet κ M u →
  ∀ x, frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

and, away from the kink,

```lean
Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa ... :
  ∀ x, Real.exp (-κ * x) ≠ M →
    frozenWaveOperator p c u (upperBarrier κ M) x ≤ 0
```

The regional ingredients are only non-strict.  They do **not** imply contact is impossible, because contact with a non-strict super-solution is compatible with `F(B) = 0` unless a strong comparison/Hopf-type input is present.

This matters especially on the constant branch.  In the limiting case `χ = 0`, the canonical `MChi p` is expected to be `1`, and the constant barrier `B ≡ 1` has zero logistic residual.  So a blanket strict constant-branch superbarrier residual would be false or at least too strong for the full positive-branch interface.

### 2. Stationary regularity / strong maximum principle APIs

Relevant committed names:

```lean
StationaryC2RegularityFromEquation
stationaryC2RegularityFromEquation_of_trap
stationaryStrongMaxPrinciple_of_trap_regularity
stationaryStrongMaxPrinciple_of_trap
StationaryStrongMaxPrinciple
```

Exact regularity frontier:

```lean
def StationaryC2RegularityFromEquation
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        Differentiable ℝ U ∧ Differentiable ℝ (deriv U)
```

Despite the name, this returns `Differentiable ℝ U ∧ Differentiable ℝ (deriv U)`, not a direct `ContDiffAt ℝ 2 U x` field.  That is enough for the interface theorem because `maxSub_upperBarrier_ne_interface` only needs `DifferentiableAt ℝ U x`.  It is not immediately the exact shape consumed by the Rothe max-principle closers, which use `ContDiffAt ℝ 2` for the second-derivative test.

The strong maximum principle currently proves positivity:

```lean
def StationaryStrongMaxPrinciple
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        ProfileNontrivial U →
          ∀ x, 0 < U x
```

This is a lower-bound strong maximum principle for `U = 0`.  It does not give a strong comparison principle for `U` against `MChi p` or `exp (-(kappa c) * x)`.

### 3. Max-principle / one-sided comparison APIs

Relevant committed names:

```lean
implicitStep_oneSided_max_estimate
implicitStep_le_of_barrier_maxPrinciple
implicitStep_le_of_barrier_maxPrinciple_clean
iteratedDeriv2_le_of_isLocalMax_sub
chemFlux_increment_split
exists_isMaxOn_pos_of_tendsto_nonpos
```

These are excellent for proving **non-overshoot** `W ≤ B` for an implicit step.  The clean theorem explicitly argues by contradiction from a positive value of `W - B` and then finds a positive global maximum.  In a smooth-branch contact situation, however, the trap already gives

```lean
U y - upperBarrier (kappa c) (MChi p) y ≤ 0
```

for every `y`, and contact gives equality at `x`.  That is a zero maximum, not a positive maximum.  The existing max-principle closers therefore reprove `U ≤ B`; they do not rule out equality.

The one-sided estimate can still be useful in a future proof.  At a smooth contact point, it is natural to aim for

```lean
frozenWaveOperator p c U U x ≤
  frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x
```

and combine it with stationarity `F(U) x = 0` and a strict superbarrier residual `F(B) x < 0`.  But the strict residual is not currently committed, and the constant branch cannot honestly be handled by a blanket strict-superbarrier field.

## Provable piece: constant contact forces a left plateau

This is the clean committed-API reduction I would add immediately.  It uses only `InMonotoneWaveTrapSet.le_M` and `InMonotoneWaveTrapSet.antitone`.

```lean
import ShenWork.Paper1.StatementAssembly

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- A contact with the constant upper level of a monotone trap forces a whole
left plateau.  No stationarity or regularity is needed. -/
theorem constBranch_contact_forces_left_plateau
    {κ M : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet κ M U)
    {x : ℝ} (hUx : U x = M) :
    ∀ y, y ≤ x -> U y = M := by
  intro y hy
  exact le_antisymm
    (htrap.le_M y)
    (by
      have hmono : U x ≤ U y := htrap.antitone hy
      simpa [hUx] using hmono)

/-- If a profile tending to `1` at `-∞` had a left plateau at level `MChi p`,
then `MChi p = 1`.  Thus for `MChi p ≠ 1`, the left plateau is impossible. -/
theorem no_const_left_plateau_of_tendsto_atBot_one
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hlim : Tendsto U atBot (𝓝 (1 : ℝ)))
    (hMne : MChi p ≠ 1) :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) ->
      (∀ y, y ≤ x -> U y = MChi p) -> False := by
  intro x _hx hplateau
  have hev : U =ᶠ[atBot] fun _ : ℝ => MChi p := by
    exact eventually_atBot.2 ⟨x, fun y hy => hplateau y hy⟩
  have hlimM : Tendsto U atBot (𝓝 (MChi p)) :=
    tendsto_const_nhds.congr' (hev.mono fun y hy => hy.symm)
  have hEq : (1 : ℝ) = MChi p := tendsto_nhds_unique hlim hlimM
  exact hMne hEq.symm

end
end ShenWork.Paper1
```

For the positive branch, this gives a very useful route when the constructed profile has `U → 1` at `-∞` and one has, or can prove, `MChi p ≠ 1` under the intended `χ > 0` assumptions.  It is much narrower than carrying constant-branch no-contact directly.

## Recommended replacement frontier

If the local file currently defines:

```lean
def PositiveUpperBarrierSmoothBranchNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  (∀ x, MChi p < Real.exp (-(kappa c) * x) ->
    U x = MChi p -> False) ∧
  (∀ x, Real.exp (-(kappa c) * x) < MChi p ->
    U x = Real.exp (-(kappa c) * x) -> False)
```

then I recommend carrying this smaller frontier instead:

```lean
/-- Smaller smooth-branch frontier for the positive upper barrier.

* `no_const_left_plateau` replaces constant-branch no-contact.  This is weaker and
  more structural: actual constant-branch contact is reduced to this field by
  monotonicity and the trap bound.
* `exp_operator_compare_at_contact` is the strong-comparison inequality at an
  exponential-branch contact point.
* `exp_strict_super_at_contact` is the strict exp-branch barrier residual at such
  a contact point.

Together with stationarity, these assemble the old smooth no-contact pair. -/
structure PositiveUpperBarrierSmoothBranchResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) ->
      (∀ y, y ≤ x -> U y = MChi p) -> False
  exp_operator_compare_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U U x ≤
          frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0
```

The assembly wrapper is small and should be robust:

```lean
import ShenWork.Paper1.StatementAssembly

open Filter Topology

namespace ShenWork.Paper1

noncomputable section

/-- Existing local intended interface, included here for completeness.  If your
`UpperBarrierContact.lean` already defines this, omit this definition. -/
def PositiveUpperBarrierSmoothBranchNoContact
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop :=
  (∀ x, MChi p < Real.exp (-(kappa c) * x) ->
    U x = MChi p -> False) ∧
  (∀ x, Real.exp (-(kappa c) * x) < MChi p ->
    U x = Real.exp (-(kappa c) * x) -> False)

/-- A contact with the constant upper level of a monotone trap forces a whole
left plateau. -/
theorem constBranch_contact_forces_left_plateau
    {κ M : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet κ M U)
    {x : ℝ} (hUx : U x = M) :
    ∀ y, y ≤ x -> U y = M := by
  intro y hy
  exact le_antisymm
    (htrap.le_M y)
    (by
      have hmono : U x ≤ U y := htrap.antitone hy
      simpa [hUx] using hmono)

/-- Smaller smooth-branch frontier for the positive upper barrier. -/
structure PositiveUpperBarrierSmoothBranchResidual
    (p : CMParams) (c : ℝ) (U : ℝ → ℝ) : Prop where
  no_const_left_plateau :
    ∀ x, MChi p < Real.exp (-(kappa c) * x) ->
      (∀ y, y ≤ x -> U y = MChi p) -> False
  exp_operator_compare_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U U x ≤
          frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x
  exp_strict_super_at_contact :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x < 0

/-- The smaller residual assembles the original smooth-branch no-contact pair. -/
theorem positiveUpperBarrierSmoothBranchNoContact_of_residual
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hres : PositiveUpperBarrierSmoothBranchResidual p c U) :
    PositiveUpperBarrierSmoothBranchNoContact p c U := by
  constructor
  · intro x hx hUx
    exact hres.no_const_left_plateau x hx
      (constBranch_contact_forces_left_plateau htrap hUx)
  · intro x hx hUx
    have hcmp := hres.exp_operator_compare_at_contact x hx hUx
    have hstrict := hres.exp_strict_super_at_contact x hx hUx
    have hnonneg :
        0 ≤ frozenWaveOperator p c U
          (upperBarrier (kappa c) (MChi p)) x := by
      simpa [hstat x] using hcmp
    exact (not_lt_of_ge hnonneg) hstrict

end
end ShenWork.Paper1
```

This is the wrapper I would use in `UpperBarrierContact.lean` rather than carrying the raw pair.

## Why the exp residual is the right narrow target

At an exponential-branch contact, the natural proof target is not raw `False`; it is the operator comparison

```lean
frozenWaveOperator p c U U x ≤
  frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x
```

plus strict negativity of the barrier residual at that contact.  The existing one-sided max-estimate API is designed around exactly this kind of statement.

A future theorem skeleton should look like this:

```lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheMaxPrincipleClosers
import ShenWork.Paper1.WaveRotheResidualClose

open Filter Topology Set Real

namespace ShenWork.Paper1

noncomputable section

/-- Future target: derive the exp-branch operator comparison at a contact point
from the local maximum of `U - upperBarrier` and the one-sided max-estimate
calculus.  This is not currently a one-line consequence of committed APIs because
`StationaryC2RegularityFromEquation` returns differentiability of `U` and `deriv U`,
while the existing second-derivative-test closer is packaged for `ContDiffAt ℝ 2`. -/
theorem expBranch_operator_compare_at_contact_of_smooth_max_estimate
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hM0 : 0 ≤ MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p))
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0) :
    ∀ x, Real.exp (-(kappa c) * x) < MChi p ->
      U x = Real.exp (-(kappa c) * x) ->
        frozenWaveOperator p c U U x ≤
          frozenWaveOperator p c U (upperBarrier (kappa c) (MChi p)) x := by
  intro x hx hUx
  -- Proof route:
  -- 1. Let `B := upperBarrier (kappa c) (MChi p)`.
  -- 2. From `hx`, get `B =ᶠ[𝓝 x] expDecay (kappa c)` and
  --    `ContDiffAt ℝ 2 B x` via `upperBarrier_contDiffAt_two_of_ne_interface`.
  -- 3. From trap + contact, get `IsLocalMax (fun y => U y - B y) x`.
  -- 4. At the local max, get `deriv U x = deriv B x`.
  -- 5. Get the second-derivative inequality `iteratedDeriv 2 U x ≤ iteratedDeriv 2 B x`.
  --    Existing closer: `iteratedDeriv2_le_of_isLocalMax_sub`, but it wants
  --    `ContDiffAt ℝ 2 U x`; bridge this from `hreg`, or prove the inequality
  --    directly from `Differentiable ℝ U ∧ Differentiable ℝ (deriv U)`.
  -- 6. Use `chemFlux_increment_split`; at contact `U x = B x`, so both rpow
  --    differences vanish, giving chem increment `≤ 0` with `C_chem := 0`.
  -- 7. Use `implicitStep_oneSided_max_estimate` with `C_chem := 0`.
  --
  -- This is the exact missing smooth strong-comparison calculus, not currently
  -- committed as a theorem.
  admit

end
end ShenWork.Paper1
```

Do **not** commit the skeleton with `admit`; it is documentation of the next theorem to prove.  The recommended residual above lets the file stay axiom-clean while identifying exactly what remains.

## Why the current APIs do not close the smooth fields

### Constant branch

At a constant-branch contact:

```lean
MChi p < Real.exp (-(kappa c) * x)
U x = MChi p
```

trap membership gives `U y ≤ MChi p` for every `y`, and antitonicity gives `MChi p ≤ U y` for every `y ≤ x`.  Hence the profile is exactly flat at level `MChi p` on the whole left half-line.  Existing APIs do not currently include the theorem that such a stationary left plateau is impossible for the positive branch.

This is why `no_const_left_plateau` is the right smaller residual.  It is strictly more informative than raw no-contact and can be discharged from left-tail data when available.

### Exponential branch

At an exponential-branch contact:

```lean
Real.exp (-(kappa c) * x) < MChi p
U x = Real.exp (-(kappa c) * x)
```

`upperBarrier` is smooth near `x`, so the obstruction is not the kink.  The available proof route is a smooth strong-comparison argument.  The committed APIs provide many ingredients, but not the final stationary strong-comparison theorem:

* `whole_line_super_barrier_pos` gives only `F(B) ≤ 0`.
* `Lemma_4_1_pos_frozen_holds_away_from_interface_at_kappa` gives only away-from-interface `F(B) ≤ 0`.
* `implicitStep_le_of_barrier_maxPrinciple_clean` rules out positive overshoot, not zero contact.
* `StationaryStrongMaxPrinciple` gives `0 < U`, not `U < B`.

So the exp field should be carried as the two comparison residuals above until the smooth strong-comparison theorem is committed.

## Practical patch recommendation

For the local intended `UpperBarrierContact.lean`:

1. Keep the interface theorem from `maxSub_upperBarrier_ne_interface`.
2. Add `constBranch_contact_forces_left_plateau`.
3. Replace `PositiveUpperBarrierSmoothBranchNoContact` as a carried input with `PositiveUpperBarrierSmoothBranchResidual`.
4. Use `positiveUpperBarrierSmoothBranchNoContact_of_residual` to recover the old shape for existing wrappers.
5. If the branch has `FrozenStationaryWaveProfile p c U`, use `hprofile.lim_neg_inf.1` plus `MChi p ≠ 1` to discharge the constant residual via `no_const_left_plateau_of_tendsto_atBot_one`.
6. Leave the exp residual as the narrow analytic frontier until a stationary smooth strong-comparison theorem is committed.

## Validation note

This is a connector-only audit/drop.  I did not run `lake build`.  All theorem and projection names above were checked against the repository through the GitHub connector; the code snippets are intended to be copied into Lean and may need minor local adjustments if `UpperBarrierContact.lean` already defines one of the displayed names.
