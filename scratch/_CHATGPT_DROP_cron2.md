# Q697 (cron2): exact signatures for `PhysicalResolverJointC2Data` and htime-discharged factor producer

Static repo inspection only; I did not run a Lean build or `#print axioms`.

Files inspected:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean
```

## 1. Exact `PhysicalResolverJointC2Data` signature

Defined in namespace:

```lean
namespace ShenWork.IntervalResolverJointC2PhysicalConcrete
```

The exact structure is:

```lean
/-- **The honest physical joint-`C²` hypothesis** for the coupled resolver: the
time-coefficient family is `ContDiff ℝ 2` in `t`, with three-time-order bounds
`Bt` whose bounded-weight value/gradient joint majorants are summable.  This is
the 3-time-order source `ℓ¹`/`C²`-in-`x` data, with the elliptic weight already
folded into `(v̂_k).re`.  It does NOT mention `DuhamelSourceTimeC2Coeff` nor any
`λ²`/`λ³` eigenvalue summability. -/
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  /-- Each coefficient is `C²` in time. -/
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  /-- Three-time-order coefficient bounds. -/
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  /-- The bounded-weight **value** joint majorant is summable (orders `0,1,2`). -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  /-- The bounded-weight **gradient** joint majorant is summable. -/
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

The coefficient family appearing here is immediately above it:

```lean
/-- The concrete resolver time-coefficient family `c k t = (v̂_k(t)).re`. -/
def resolverTimeCoeff (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => (intervalNeumannResolverCoeff p (u t) k).re
```

So the four fields mean:

1. every resolver coefficient is `C²` in time;
2. each time derivative order `i = 0,1,2` is bounded by `Bt i k`;
3. the bounded-weight value joint majorant is summable;
4. the bounded-weight gradient joint majorant is summable.

## 2. Exact `ChemDivMixedTimeDerivClosedRepr` signature

Important correction: this is **not** a `structure`; it is a `def` of an existential `Prop`.

Defined in namespace:

```lean
namespace ShenWork.IntervalCoupledRegularityBootstrap
```

Exact definition:

```lean
/-- **Closed-slab spectral representative of the mixed time-derivative.**

`Gmix` is the globally jointly continuous flux mixed time-derivative built from
the bounded-weight sin/cos series; `agree` records that it equals the committed
`coupledChemDivTimeDerivativeLift` lift on the closed spatial domain throughout
the time window `Ioo (τ-δ) (τ+δ)`.  No outer-commute atom, no resolver `C²`
field, and no FAC conclusion is assumed. -/
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

The existential components are:

```lean
Gmix : ℝ × ℝ → ℝ
Continuous Gmix
∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
  coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

The consumer immediately below it is:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

This theorem extracts `Gmix`, its global continuity, and slab agreement, then transfers `ContinuousOn` to the committed `coupledChemDivTimeDerivativeLift`.

## 3. Exact `coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged` signature

Defined in namespace:

```lean
namespace ShenWork.IntervalCoupledRegularityBootstrap
```

Exact theorem:

```lean
/-- **χ₀<0 FAC factor inputs with `htime_cont` discharged.**

Assembles the full FAC factor joint-`C²` inputs from the resolver physical joint
`C²` data, the `u`-side positivity/continuity, the source/Picard-`C²` slab data,
and — in place of the previously-open `htime_cont` field — the closed-slab
spectral representative `ChemDivMixedTimeDerivClosedRepr`.  The mixed
time-derivative continuity is now produced internally by
`chemDivMixedTimeDeriv_jointContinuousOn_closed`, so `htime_cont` is no longer a
slab hypothesis. -/
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_cont : ∀ s : ℝ, Continuous (u s))
    (hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x)
    (other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
      (∀ᶠ s in 𝓝 τ,
        ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
        ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
      ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
    H hu_cont hu_nonneg (fun τ => by
      rcases other τ with ⟨δ, hδ, hsrc, hu_c2, hrepr⟩
      exact ⟨δ, hδ, hsrc, hu_c2,
        chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr⟩)
```

This theorem requires exactly four inputs:

```lean
H : PhysicalResolverJointC2Data p u Bt
hu_cont : ∀ s : ℝ, Continuous (u s)
hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x
other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
  (∀ᶠ s in 𝓝 τ,
    ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
  (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

and returns:

```lean
CoupledChemDivFluxFactorJointC2Inputs p u
```

It internally supplies the old `htime_cont` field by calling:

```lean
chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

and delegates the rest to:

```lean
coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

## 4. Sorry/admit status of these declarations

Based on direct inspection of the fetched declarations and exact-name searches for `sorry`/`admit`:

```text
PhysicalResolverJointC2Data
ChemDivMixedTimeDerivClosedRepr
chemDivMixedTimeDeriv_jointContinuousOn_closed
coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
```

these declarations themselves are **not sorry'd** and are **not admit'd**.

More precise status:

- `PhysicalResolverJointC2Data` is a `structure`, so it has no proof body and no `sorry`.
- `ChemDivMixedTimeDerivClosedRepr` is a `def` of an existential `Prop`, so it has no proof body and no `sorry`.
- `chemDivMixedTimeDeriv_jointContinuousOn_closed` has an explicit proof body; no `sorry`/`admit` was found in the declaration.
- `coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged` is an explicit theorem term delegating to `_physical_commuteDischarged`; no `sorry`/`admit` was found in the declaration.

I did not run Lean or `#print axioms`, so this is a syntactic placeholder audit of the relevant declarations, not a transitive axiom audit of every dependency.

## 5. Practical takeaway for the heat-semigroup route

For a heat-level proof, this route reduces the target to building:

```lean
H : PhysicalResolverJointC2Data p u Bt
hu_cont : ∀ s : ℝ, Continuous (u s)
hu_nonneg : ∀ s : ℝ, ∀ x : intervalDomainPoint, 0 ≤ u s x
other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
  (∀ᶠ s in 𝓝 τ,
    ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
  (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
  ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Then the call is simply:

```lean
have Hfac : CoupledChemDivFluxFactorJointC2Inputs p u :=
  coupledChemDivFluxFactorJointC2Inputs_of_physical_htimeDischarged
    H hu_cont hu_nonneg other
```

This is the shortest mature path I found that also discharges the flux time-bridge and `htime_cont` internally.
