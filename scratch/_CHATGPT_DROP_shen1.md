# Q2286 shen1 — positive upper-barrier interface no-contact

## Code patch

Preferred placement: `ShenWork/Paper1/StatementAssembly.lean`, because that is where the positive upper-barrier contact wrappers already live.

Add the `WaveRotheResidualClose` import to expose the existing kink/no-local-max theorem:

```lean
import ShenWork.Paper1.Lemma25Helpers
import ShenWork.Paper1.StationaryUpperTail
import ShenWork.Paper1.WaveRotheResidualClose
```

Then insert the theorem after `PositiveUpperBarrierContactContradictions` and before `strict_upperBarrier_MChi_of_contactContradictions`:

```lean
/-- At the nonsmooth interface of the canonical positive upper barrier,
a regular stationary trapped profile cannot touch the barrier.

The proof is deliberately local.  At a contact point on the interface, trap
membership makes `U - upperBarrier` globally nonpositive, while the contact
identity makes its value at the interface equal to `0`; hence that point is a
local maximum.  The committed kink lemma
`maxSub_upperBarrier_ne_interface` then forbids the interface because `U` is
differentiable there by the regularity frontier. -/
theorem positiveUpperBarrier_interfaceNoContact_of_regular_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p -> U x = MChi p -> False := by
  intro x hx hUx
  rcases hreg U htrap hstat with ⟨hUdiff, _hUd_diff⟩
  have hbar_x : upperBarrier (kappa c) (MChi p) x = MChi p :=
    upperBarrier_eq_M_of_le_exp hx.ge
  have hloc :
      IsLocalMax
        (fun y => U y - upperBarrier (kappa c) (MChi p) y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    exact Filter.Eventually.of_forall fun y => by
      have hy_le :
          U y - upperBarrier (kappa c) (MChi p) y ≤ 0 := by
        exact sub_nonpos.mpr (htrap.le_upperBarrier y)
      have hx_zero :
          U x - upperBarrier (kappa c) (MChi p) x = 0 := by
        rw [hUx, hbar_x]
        ring
      simpa [hx_zero] using hy_le
  have hne : Real.exp (-(kappa c) * x) ≠ MChi p :=
    maxSub_upperBarrier_ne_interface
      (κ := kappa c) (M := MChi p) (W := U) (x := x)
      hκ hM (hUdiff x) hloc
  exact hne hx
```

This is the exact goal shape requested.  It uses no axioms and no `sorry`.

## Exact field/projection names verified

The trap projections are theorem projections, not structure fields, because the trap is defined as a pair of propositions:

```lean
def InWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  IsCUnifBdd u ∧ ∀ x, 0 ≤ u x ∧ u x ≤ upperBarrier κ M x

def InMonotoneWaveTrapSet (κ M : ℝ) (u : ℝ → ℝ) : Prop :=
  InWaveTrapSet κ M u ∧ NonincreasingProfile u
```

The existing projection names in `Statements.lean` are:

```lean
InMonotoneWaveTrapSet.trap
InMonotoneWaveTrapSet.antitone
InMonotoneWaveTrapSet.deriv_nonpos
InMonotoneWaveTrapSet.nonneg
InMonotoneWaveTrapSet.le_upperBarrier
InMonotoneWaveTrapSet.le_M
InMonotoneWaveTrapSet.le_exp
InMonotoneWaveTrapSet.tendsto_atTop_zero
```

So the relevant upper-bound line is exactly:

```lean
htrap.le_upperBarrier y
```

not `htrap.le_upper`.

## Existing theorem reused

The proof calls the committed theorem from `ShenWork/Paper1/WaveRotheResidualClose.lean`:

```lean
theorem maxSub_upperBarrier_ne_interface {κ M : ℝ} {W : ℝ → ℝ} {x : ℝ}
    (hκ : 0 < κ) (hM : 0 < M)
    (hWdiff : DifferentiableAt ℝ W x)
    (hmax : IsLocalMax (fun y => W y - upperBarrier κ M y) x) :
    Real.exp (-κ * x) ≠ M
```

In this new wrapper, instantiate it with:

```lean
κ := kappa c
M := MChi p
W := U
```

The differentiability hypothesis comes from:

```lean
rcases hreg U htrap hstat with ⟨hUdiff, _hUd_diff⟩
```

because `StationaryC2RegularityFromEquation` is exactly:

```lean
def StationaryC2RegularityFromEquation
    (p : CMParams) (c κ M : ℝ) : Prop :=
  ∀ U : ℝ → ℝ,
    InMonotoneWaveTrapSet κ M U →
      (∀ x, frozenWaveOperator p c U U x = 0) →
        Differentiable ℝ U ∧ Differentiable ℝ (deriv U)
```

## Why the local maximum proof closes

At an interface point `hx : Real.exp (-(kappa c) * x) = MChi p`, the barrier value is on the constant branch:

```lean
upperBarrier (kappa c) (MChi p) x = MChi p
```

by:

```lean
upperBarrier_eq_M_of_le_exp hx.ge
```

At a contact point `hUx : U x = MChi p`, this gives:

```lean
U x - upperBarrier (kappa c) (MChi p) x = 0
```

For every `y`, trap membership gives:

```lean
U y ≤ upperBarrier (kappa c) (MChi p) y
```

hence:

```lean
U y - upperBarrier (kappa c) (MChi p) y ≤ 0
```

Therefore `x` is a global, hence local, maximum of `U - upperBarrier`.  But `maxSub_upperBarrier_ne_interface` says no differentiable `U` can have such a local maximum at the kink/interface.  This contradicts `hx`.

## Import-cycle note

I do not see an import cycle for the preferred placement.  Current `StatementAssembly.lean` imports `Lemma25Helpers` and `StationaryUpperTail`; `WaveRotheResidualClose.lean` imports lower-level Rothe/super-barrier files, not `StatementAssembly.lean`.  Existing code search showed `StatementAssembly` being imported only by top-level/audit files, not by `WaveRotheResidualClose`.

If Lean nevertheless reports a cycle in your local dependency graph, put the same theorem in a new leaf file instead of importing it back into `StatementAssembly.lean`:

```lean
-- ShenWork/Paper1/PositiveUpperBarrierNoContact.lean
import ShenWork.Paper1.StatementAssembly
import ShenWork.Paper1.WaveRotheResidualClose

namespace ShenWork.Paper1

noncomputable section

/-- At the nonsmooth interface of the canonical positive upper barrier,
a regular stationary trapped profile cannot touch the barrier. -/
theorem positiveUpperBarrier_interfaceNoContact_of_regular_stationary
    {p : CMParams} {c : ℝ} {U : ℝ → ℝ}
    (hκ : 0 < kappa c) (hM : 0 < MChi p)
    (htrap : InMonotoneWaveTrapSet (kappa c) (MChi p) U)
    (hstat : ∀ x, frozenWaveOperator p c U U x = 0)
    (hreg : StationaryC2RegularityFromEquation p c (kappa c) (MChi p)) :
    ∀ x, Real.exp (-(kappa c) * x) = MChi p -> U x = MChi p -> False := by
  intro x hx hUx
  rcases hreg U htrap hstat with ⟨hUdiff, _hUd_diff⟩
  have hbar_x : upperBarrier (kappa c) (MChi p) x = MChi p :=
    upperBarrier_eq_M_of_le_exp hx.ge
  have hloc :
      IsLocalMax
        (fun y => U y - upperBarrier (kappa c) (MChi p) y) x := by
    dsimp [IsLocalMax, IsMaxFilter]
    exact Filter.Eventually.of_forall fun y => by
      have hy_le :
          U y - upperBarrier (kappa c) (MChi p) y ≤ 0 := by
        exact sub_nonpos.mpr (htrap.le_upperBarrier y)
      have hx_zero :
          U x - upperBarrier (kappa c) (MChi p) x = 0 := by
        rw [hUx, hbar_x]
        ring
      simpa [hx_zero] using hy_le
  have hne : Real.exp (-(kappa c) * x) ≠ MChi p :=
    maxSub_upperBarrier_ne_interface
      (κ := kappa c) (M := MChi p) (W := U) (x := x)
      hκ hM (hUdiff x) hloc
  exact hne hx

end
end ShenWork.Paper1
```

Then import that new file from the downstream consumer or top-level `ShenWork.lean`, rather than from `StatementAssembly.lean`.

## Validation note

This connector-only git drop did not run `lake build`.  The patch is assembled from the exact declarations currently present in the repository and should elaborate against those names.
