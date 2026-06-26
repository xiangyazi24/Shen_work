# Q741 (cron2): per-slice agreement for `coupledChemDivSourceLift`

Static repo inspection only; I did not run a Lean build.

## Executive answer

I did **not** find a ready-made theorem with the exact Level0 `2A-agree` shape:

```lean
∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x =
    deriv (chemFluxFun p.β U_cos_s V_cos_s) x
```

The closest coupled-specific theorem is:

```lean
coupledChemDivSourceLift_eq_deriv_fluxLift_interior
```

in:

```text
ShenWork/PDE/IntervalChemDivOuterCommute.lean
```

but it is only an **interior** statement and only identifies the source with the derivative of the built-in coupled flux:

```lean
theorem coupledChemDivSourceLift_eq_deriv_fluxLift_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    coupledChemDivSourceLift p u s x =
      deriv (coupledChemDivFluxLift p u s) x := by
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  unfold coupledChemDivSourceLift intervalDomainChemotaxisDiv
    coupledChemDivFluxLift
  simp only [intervalDomainLift, hxIcc, dif_pos]
```

Searches for:

```text
coupledChemDivSourceLift_eq
chemDivSourceLift agree
chemDivSource Icc
```

did not turn up an exact closed-interval/cosine-representative agreement lemma.  So for `2A-agree`, you probably need to unfold manually or add a small helper lemma.

## Current `2A-agree` target is still a sorry

In:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

there is already the exact pending target:

```lean
have hF_agree : ∀ q ∈ Icc c T ×ˢ Icc (0 : ℝ) 1,
    Function.uncurry
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0)) q =
    deriv
      (ShenWork.Paper2.ChemDivSpatialC2.chemFluxFun p.β
        (fun x => ∑' k, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
          heatCoeff u₀ k) * cosineMode k x)
        (intervalResolverLiftR p (conjugatePicardIter p u₀ 0 q.1)))
      q.2 := by
  sorry -- [SUB-SORRY 2A-agree: per-slice agreement ...]
```

So the repo itself confirms this exact agreement has not yet been packaged.

## Relevant definitions

### `coupledChemDivSourceLift`

File:

```text
ShenWork/PDE/IntervalCoupledSourceTimeC1.lean
```

```lean
/-- Lifted chemotaxis-divergence source with the elliptic resolver substituted. -/
def coupledChemDivSourceLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) : ℝ → ℝ :=
  intervalDomainLift
    (fun x => intervalDomainChemotaxisDiv p (u s)
      (coupledChemicalConcentration p u s) x)
```

### `coupledChemDivFluxLift`

File:

```text
ShenWork/PDE/IntervalChemDivFluxChain.lean
```

```lean
/-- Lifted chemotactic flux before the outer spatial derivative. -/
def coupledChemDivFluxLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  intervalDomainLift (u s) y * deriv v y / (1 + v y) ^ p.β
```

### `chemFluxFun`

File:

```text
ShenWork/Paper2/IntervalChemDivSpatialC2.lean
```

```lean
/-- The chemotaxis flux function whose spatial derivative is the chemDiv source.
`φ(y) = lift(u)(y) · deriv(lift(v))(y) / (1 + lift(v)(y))^β` -/
def chemFluxFun (β : ℝ) (u v : ℝ → ℝ) (y : ℝ) : ℝ :=
  u y * deriv v y / (1 + v y) ^ β
```

So after unfolding, `coupledChemDivFluxLift p u s` is definitionally the same flux shape as

```lean
chemFluxFun p.β
  (intervalDomainLift (u s))
  (intervalDomainLift (coupledChemicalConcentration p u s))
```

## Existing pattern: `IntervalChemDivSpatialC2.lean`

The pattern you cited is real and useful, but it is for the non-coupled `chemDivLift`, not directly for `coupledChemDivSourceLift`:

```lean
theorem chemDivLift_contDiffOn_two_of_global
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu : ContDiff ℝ 4 (intervalDomainLift u))
    (hv : ContDiff ℝ 4 (intervalDomainLift v))
    (hv_pos : ∀ x, (0 : ℝ) < 1 + intervalDomainLift v x) :
    ContDiffOn ℝ 2 (chemDivLift p u v) (Icc (0 : ℝ) 1) := by
  have hglobal := chemFluxDeriv_contDiff_two hu hv hv_pos p.hβ
  have h_eq : ∀ x ∈ Icc (0 : ℝ) 1,
      chemDivLift p u v x =
        deriv (chemFluxFun p.β (intervalDomainLift u) (intervalDomainLift v)) x := by
    intro x hx
    unfold chemDivLift intervalDomainLift
    rw [dif_pos hx]
    unfold intervalDomainChemotaxisDiv
    unfold chemFluxFun
    rfl
  exact hglobal.contDiffOn.congr h_eq
```

This is the right manual-unfolding style to copy for the coupled version.

## Another nearby theorem: EWA eval agreement

There is also a stronger-looking but different theorem in:

```text
ShenWork/Wiener/EWA/ChemDivEval.lean
```

```lean
theorem evalST_chemDivEWA_eq_coupledChemDivSourceLift ...
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    ... :
    evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
      = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ)
```

This theorem is not the Level0 `U_cos/V_cos` agreement.  It is an EWA synthesis/eval bridge, interior-only, and it requires `hgrad`, `h_flux_nbhd`, and `h_flux_diff` hypotheses.  However, its comments and final proof step are useful: it explicitly documents that

```lean
coupledChemicalConcentration p u s = intervalNeumannResolverR p (u s)
```

is definitional, and its final step is:

```lean
rw [coupledChemDivSourceLift, intervalDomainLift, dif_pos hxIcc]
rfl
```

So again, the route is unfolding, not a prepackaged Level0 agreement lemma.

## Suggested proof strategy for `2A-agree`

For each `q = (s,x)` with `s ∈ Icc c T` and `x ∈ Icc 0 1`:

1. Set
   ```lean
   u := conjugatePicardIter p u₀ 0
   w := u s
   V := coupledChemicalConcentration p u s
   ```
2. Unfold the left-hand side:
   ```lean
   rw [coupledChemDivSourceLift, intervalDomainLift, dif_pos hx]
   unfold intervalDomainChemotaxisDiv
   ```
   This should expose the derivative of the flux built from
   ```lean
   intervalDomainLift w
   intervalDomainLift V
   ```
3. Unfold the flux side:
   ```lean
   unfold ShenWork.Paper2.ChemDivSpatialC2.chemFluxFun
   ```
4. Use the heat agreement and resolver agreement to replace the lifted fields with the smooth representatives.

Important caveat: replacing inside `deriv` is not justified by mere pointwise equality at `x`.  For interior points `x ∈ Ioo 0 1`, agreement on `Icc 0 1` gives agreement on a neighborhood of `x`, so `Filter.EventuallyEq.deriv_eq` is the clean way to rewrite under `deriv`:

```lean
have hflux_ev :
    (chemFluxFun p.β (intervalDomainLift w) (intervalDomainLift V))
      =ᶠ[𝓝 x]
    (chemFluxFun p.β U_cos V_cos) := by
  filter_upwards [Ioo_mem_nhds hx_interior] with y hy
  -- use hU_agree y (Ioo_subset_Icc_self hy)
  -- use hV_agree y (Ioo_subset_Icc_self hy)

rw [Filter.EventuallyEq.deriv_eq hflux_ev]
```

For endpoints `x = 0` or `x = 1`, agreement only on `Icc 0 1` is not enough to rewrite a full derivative under `deriv`; Lean’s `deriv` is two-sided.  To close the stated `Icc` target at endpoints, you need one of:

* a stronger global/neighborhood agreement between `intervalDomainLift ...` and the cosine representatives near the endpoints;
* an endpoint-specific lemma using the even/reflection extension machinery;
* or prove the agreement on `Ioo 0 1` first and extend to endpoints by continuity, if both sides are already known continuous on `Icc 0 1`.

The existing `chemDivLift_contDiffOn_two_of_global` avoids this endpoint issue because it does **not** replace `intervalDomainLift u/v` by a different representative under `deriv`; it unfolds to the exact same functions.

## Bottom line

There is no exact landed `coupledChemDivSourceLift` agreement lemma for your `U_cos/V_cos` representative.  Use manual unfolding, with `coupledChemDivSourceLift_eq_deriv_fluxLift_interior` as a helpful interior shortcut.  For the closed-interval endpoint cases in the current `Icc` statement, be careful: rewriting inside `deriv` needs neighborhood/eventual agreement, not just pointwise agreement on `[0,1]`.
