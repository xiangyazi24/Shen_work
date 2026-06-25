# Q579 (cron2): joint continuity of `coupledChemDivTimeDerivativeLift` without `ResolverHasSpectralAgreement`

## Executive verdict

Yes: the repo **does** have a non-`ResolverHasSpectralAgreement` route to

```lean
ContinuousOn
  (Function.uncurry
    (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

but it is not a one-line `ContDiff` theorem specialized to the heat semigroup.  The best existing route is:

```text
ChemDivMixedReprWitnessData
  → ChemDivMixedReprData
  → ChemDivMixedTimeDerivClosedRepr
  → ContinuousOn (uncurry coupledChemDivTimeDerivativeLift) on the closed slab
```

This route bypasses `ResolverHasSpectralAgreement`.  It asks instead for a globally continuous closed-slab representative `Gmix` of the mixed time-derivative field, or for the more structured witness bundle of ten continuous slice representatives

```text
U, U_t, U_tx, U_x, v, v_x, v_xx, v_t, v_tx, v_txx.
```

For the heat semigroup level-0 case, this is probably the clean route: build the witness data directly from heat-series representatives for the `U` fields and elliptic-resolver/series representatives for the `V` fields on the positive time window.  It is simpler than manufacturing `ResolverHasSpectralAgreement`, because `ResolverHasSpectralAgreement` is a Duhamel/restart spectral package and carries a `DuhamelSourceTimeC1` datum.

I found **no theorem** already specialized to

```lean
coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)
```

and no direct theorem saying “`ContDiff` of the heat/resolver composition implies joint continuity of `coupledChemDivTimeDerivativeLift`.”  The existing “composition” theorem is the `mixedAlgebra`/representative route.

## 1. The existing `ResolverHasSpectralAgreement` route

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:50` gives only the resolver time-derivative field `v_t`, not the full chemDiv mixed derivative:

```lean
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

The underlying structure is in `ShenWork/Paper2/IntervalResolverTimeRegularity.lean:38`:

```lean
structure ResolverHasSpectralAgreement
    (T : ℝ) (v : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_data : ∀ t₀, 0 < t₀ → t₀ < T →
    ∃ (a₀ : ℕ → ℝ) (M : ℝ) (_ : 0 ≤ M) (_ : ∀ n, |a₀ n| ≤ M)
      (a : ℝ → ℕ → ℝ) (_ : DuhamelSourceTimeC1 a) (offset : ℝ),
      (0 < t₀ - offset) ∧
      (∀ᶠ s in 𝓝 t₀, ∀ x : intervalDomainPoint,
        v s x = ∑' n, localRestartCoeff a₀ a (s - offset) n *
          cosineMode n x.1)
```

The closed-slab theorem it feeds is in `IntervalResolverTimeRegularity.lean:97`:

```lean
theorem resolver_timeDeriv_jointContinuousOn_closed
    {T : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement T v) :
    ContinuousOn
      (Function.uncurry
        (fun (t : ℝ) (x : ℝ) =>
          deriv (fun s => intervalDomainLift (v s) x) t))
      (Ioo (0 : ℝ) T ×ˢ Icc (0 : ℝ) 1)
```

Search for a heat-specific construction of

```lean
ResolverHasSpectralAgreement U (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0))
```

found no direct theorem.  More importantly, constructing it is not “simple”: the structure demands local restart cosine data plus `DuhamelSourceTimeC1` for the coefficient family.  For level 0, direct heat/resolver smoothness is likely a shorter proof obligation than building this restart/Duhamel spectral agreement package.

## 2. Non-`ResolverHasSpectralAgreement` route: closed-slab representative

The main alternative is in `ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean`.

### 2.1 Closed-slab representative structure

`IntervalChemDivTimeDerivClosed.lean:43`:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

### 2.2 Joint continuity theorem

`IntervalChemDivTimeDerivClosed.lean:54`:

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

This theorem is exactly the target shape, except centered as `Icc (τ-δ) (τ+δ)` instead of arbitrary `Icc c T`.  For a fixed positive window `[c,T]`, one can choose e.g.

```lean
τ := (c + T) / 2
δ := (T - c) / 2
```

when `c ≤ T`, and then rewrite `Icc (τ-δ) (τ+δ)` to `Icc c T` (or choose any slightly larger slab around `[c,T]` and use `.mono`).

This theorem uses no `ResolverHasSpectralAgreement`; all it needs is the continuous representative `Gmix` and the equality on the closed slab.

## 3. Constructing the closed representative by composition: `mixedAlgebra`

The composition route is in `ShenWork/PDE/IntervalChemDivMixedReprConstruct.lean`.

### 3.1 Explicit algebra for the mixed derivative

`IntervalChemDivMixedReprConstruct.lean:49`:

```lean
def mixedAlgebra (β : ℝ)
    (Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ) :
    ℝ × ℝ → ℝ :=
  fun q =>
    let U := Uc q; let Ut := Utc q; let Utx := Utxc q; let Ux := Uxc q
    let V := Vc q; let Vx := Vxc q; let Vxx := Vxxc q
    let Vt := Vtc q; let Vtx := Vtxc q; let Vtxx := Vtxxc q
    let B := 1 + V
    ((Utx * Vx + Ut * Vxx) / B ^ β - β * Ut * Vx * Vx / B ^ (β + 1)) +
    ((Ux * Vtx + U * Vtxx) / B ^ β - β * U * Vtx * Vx / B ^ (β + 1)) -
    (β * (Ux * Vx * Vt + U * Vxx * Vt + U * Vx * Vtx) / B ^ (β + 1)
      - β * (β + 1) * U * Vx * Vt * Vx / B ^ (β + 2))
```

This is the “smooth functional of `u`, `v`, and derivatives” made explicit.

### 3.2 Representative data bundle

`IntervalChemDivMixedReprConstruct.lean:70`:

```lean
structure ChemDivMixedReprData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc : ℝ × ℝ → ℝ
  Utc : ℝ × ℝ → ℝ
  Utxc : ℝ × ℝ → ℝ
  Uxc : ℝ × ℝ → ℝ
  Vc : ℝ × ℝ → ℝ
  Vxc : ℝ × ℝ → ℝ
  Vxxc : ℝ × ℝ → ℝ
  Vtc : ℝ × ℝ → ℝ
  Vtxc : ℝ × ℝ → ℝ
  Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

### 3.3 Data → closed representative

`IntervalChemDivMixedReprConstruct.lean:102`:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_data
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (D : ChemDivMixedReprData p u τ δ) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ
```

This theorem proves that `mixedAlgebra` of the continuous representatives is itself continuous, using the positivity floor for the `rpow` denominators.

So the clean non-spectral proof chain is:

```lean
have D : ChemDivMixedReprData p u τ δ := ...
have Hrepr : ChemDivMixedTimeDerivClosedRepr p u τ δ :=
  chemDivMixedTimeDerivClosedRepr_of_data D
exact chemDivMixedTimeDeriv_jointContinuousOn_closed Hrepr
```

## 4. Even more structured witness bundle

`ShenWork/PDE/IntervalChemDivMixedReprWitness.lean` gives a larger witness structure that derives the `agree` field by the spatial chain rule.

`IntervalChemDivMixedReprWitness.lean:178`:

```lean
structure ChemDivMixedReprWitnessData
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) where
  Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc : ℝ × ℝ → ℝ
  cont_Uc : Continuous Uc
  cont_Utc : Continuous Utc
  cont_Utxc : Continuous Utxc
  cont_Uxc : Continuous Uxc
  cont_Vc : Continuous Vc
  cont_Vxc : Continuous Vxc
  cont_Vxxc : Continuous Vxxc
  cont_Vtc : Continuous Vtc
  cont_Vtxc : Continuous Vtxc
  cont_Vtxxc : Continuous Vtxxc
  floor : ∀ q : ℝ × ℝ, 0 < 1 + Vc q
  Uc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Uc (t, x) = intervalDomainLift (u t) x
  Utc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Utc (t, x) = ShenWork.Paper2.PicardLimitK1.slopeSlice u t x
  Vc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Vc (t, x) = intervalDomainLift (coupledChemicalConcentration p u t) x
  Vtc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
    Vtc (t, x) = coupledChemicalTimeDerivativeLift p u t x
  hUx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => intervalDomainLift (u t) y) (Uxc (t, x)) x
  hUtx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => ShenWork.Paper2.PicardLimitK1.slopeSlice u t y)
      (Utxc (t, x)) x
  hVx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => intervalDomainLift (coupledChemicalConcentration p u t) y)
      (Vxc (t, x)) x
  hVxx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt
      (fun y => deriv (intervalDomainLift (coupledChemicalConcentration p u t)) y)
      (Vxxc (t, x)) x
  hVtx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => coupledChemicalTimeDerivativeLift p u t y) (Vtxc (t, x)) x
  hVtxx : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun y => deriv (coupledChemicalTimeDerivativeLift p u t) y)
      (Vtxxc (t, x)) x
  Vxc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    Vxc (t, x) = deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x
  Vtxc_eq : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Ioo (0 : ℝ) 1,
    Vtxc (t, x) = deriv (coupledChemicalTimeDerivativeLift p u t) x
  boundary_agree : ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ ({0, 1} : Set ℝ),
    coupledChemDivTimeDerivativeLift p u t x =
      mixedAlgebra p.β Uc Utc Utxc Uxc Vc Vxc Vxxc Vtc Vtxc Vtxxc (t, x)
```

The theorem deriving the closed representative is `IntervalChemDivMixedReprWitness.lean:326`:

```lean
theorem chemDivMixedTimeDerivClosedRepr_of_witness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (W : ChemDivMixedReprWitnessData p u τ δ) :
    ShenWork.IntervalCoupledRegularityBootstrap.ChemDivMixedTimeDerivClosedRepr
      p u τ δ
```

This is the most explicit route if you want Lean to verify that the committed `coupledChemDivTimeDerivativeLift` equals the smooth composition on the closed slab.

## 5. Factor-`C²` packages do not by themselves remove `htime_cont`

A tempting route is `CoupledChemDivFluxFactorJointC2Inputs`, but note that it still **contains** the desired continuity field as a hypothesis.

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean:79`:

```lean
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ...
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

So proving “`u`, `v`, `v_x` are joint `C²`” is not enough to use this structure unless you also supply the `ContinuousOn` field.  The explicit way to supply that field is the `ChemDivMixedTimeDerivClosedRepr` route above.

There is a helper in `IntervalChemDivTimeDerivClosed.lean:87` that plugs this representative route into the physical resolver chain:

```lean
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
    CoupledChemDivFluxFactorJointC2Inputs p u
```

This again confirms that `ChemDivMixedTimeDerivClosedRepr` is the intended non-spectral discharge of `htime_cont`.

## 6. Physical resolver C² data is another alternative to `ResolverHasSpectralAgreement`

The v-side smoothness route can avoid `ResolverHasSpectralAgreement` by using `PhysicalResolverJointC2Data`.

`ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean:83`:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

It gives joint `C²` of `v` and `v_x`:

`IntervalResolverJointC2PhysicalConcrete.lean:115`:

```lean
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

and joint `C²` of `v_x`:

`IntervalResolverJointC2PhysicalConcrete.lean:137`:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

This is not the full `coupledChemDivTimeDerivativeLift` continuity theorem, but it supplies major v-side pieces for the representative/witness route.  For heat level 0, constructing `PhysicalResolverJointC2Data` from heat-smooth source coefficients may be more natural than constructing `ResolverHasSpectralAgreement`.

## 7. Practical recommendation for `[c,T]`

For the positive heat window, avoid `ResolverHasSpectralAgreement`.  Add a windowed theorem of the following shape:

```lean
theorem chemDivTimeDerivative_jointContinuousOn_of_mixedRepr_on
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c T τ δ : ℝ}
    (hsub : Icc c T ⊆ Icc (τ - δ) (τ + δ))
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
  (chemDivMixedTimeDeriv_jointContinuousOn_closed H).mono
    (by intro q hq; exact ⟨hsub hq.1, hq.2⟩)
```

Then prove the heat-specific representative:

```lean
∃ τ δ, Icc c T ⊆ Icc (τ - δ) (τ + δ) ∧
  ChemDivMixedTimeDerivClosedRepr
    p (conjugatePicardIter p u₀ 0) τ δ
```

or directly construct `ChemDivMixedReprWitnessData` for the level-0 heat semigroup.  This is the committed non-spectral route and lines up with the mathematical statement “the field is a smooth composition of smooth heat/resolver factors.”

No direct heat-specialized theorem was found.