# Q752 (cron2): windowed chem-div chain rule / FluxJointC2Hyp search

Static repository inspection only; I did not run a Lean build.

## Search verdict

Requested searches:

- `CoupledChemDivLocalChainRuleOn` — no hit.
- `FluxJointC2HypOn` — no hit.
- `chainRule.*window` / `chainRule window` — hits only nearby/global chem-div files and generic windowed infrastructure, not a chem-div `On` structure.
- `chainRule.*Icc` / `chainRule Icc` — same: global chem-div structures plus endpoint/windowed coefficient-time lemmas.

## Answers

### 1. Windowed/`On` version of `CoupledChemDivLocalChainRule`?

**No, not as a named chem-div structure.**

The committed chem-div chain-rule package is global:

```lean
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ...
```

Location:

```text
ShenWork/PDE/IntervalChemDivTimeDerivative.lean
```

The pointwise wrapper is also global:

```lean
theorem coupledChemDivLocalChainRule_of_pointwiseChainAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivPointwiseChainAtoms p u) :
    CoupledChemDivLocalChainRule p u
```

Location:

```text
ShenWork/PDE/IntervalChemDivLocalChainRule.lean
```

I did not find `CoupledChemDivLocalChainRuleOn`, nor a variant parameterized by `lo hi` / `Icc lo hi`.

### 2. Windowed version of `CoupledChemDivFluxJointC2Hyp`?

**No, not as a named chem-div structure.**

The primitive flux joint-`C²` package is also global:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ...
```

Location:

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

The factor input structure feeding it is global too:

```lean
structure CoupledChemDivFluxFactorJointC2Inputs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ...
```

Location:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

The residual wrapper in the window-discharge file also keeps a global field:

```lean
other : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
  ...
```

Location:

```text
ShenWork/Paper2/IntervalChemDivWinDischarge.lean
```

So the current committed chem-div route is: global factor inputs → global `CoupledChemDivFluxJointC2Hyp` → global `CoupledChemDivOuterCommuteAtoms` → global `CoupledChemDivLocalChainRule` → global `DuhamelSourceTimeC1`, then optionally forget/restrict to `DuhamelSourceTimeC1On`.

### 3. Pattern where the chain rule is used directly without going through global `FluxJointC2Hyp`?

**Yes.** The cleanest pattern is in:

```text
ShenWork/Wiener/EWA/ChemDivAdot.lean
```

It consumes `hchain : CoupledChemDivLocalChainRule p u` directly, without requiring a `CoupledChemDivFluxJointC2Hyp` argument:

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s := by
  rcases hchain.exists_local_slab s with
    ⟨δ, hδ, hf_cont, hdiff, hcont_deriv⟩
  exact
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
      (f := coupledChemDivSourceLift p u)
      (f' := coupledChemDivTimeDerivativeLift p u)
      (τ := s) (δ := δ) (n := n) hδ hf_cont hdiff hcont_deriv
```

The same file then derives the window-within form needed by final consumers:

```lean
theorem chemDivAdot_hasDerivWithinAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s
```

and packages the derivative + continuity legs as:

```lean
theorem chemDivAdot_deriv_legs_of_smoothness
    (hchain : CoupledChemDivLocalChainRule p u)
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ...
```

That is a real direct-chain-rule pattern. It still assumes the **global** `CoupledChemDivLocalChainRule`, but it does not go through `FluxJointC2Hyp` at the use site.

There is also an inline use in:

```text
ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean
```

After building

```lean
have hchain : CoupledChemDivLocalChainRule
    p (conjugatePicardIter p u₀ 0) :=
  coupledChemDivLocalChainRule_of_fluxJointC2 hfluxC2
```

it directly calls `hchain.exists_local_slab s` to produce coefficient `HasDerivAt` via `cosineCoeffs_hasDerivAt_of_smooth_param`. However, that local inline pattern still obtains `hchain` from the global `hfluxC2` route.

## Important nearby windowed infrastructure

There **is** a generic endpoint/windowed cosine-coefficient chain-rule lemma:

```text
ShenWork/Paper2/IntervalMildPicardRegularityEndpoint2.lean
```

```lean
theorem cosineCoeffs_hasDerivWithinAt_of_smooth_param
    {f f' : ℝ → ℝ → ℝ} {a' W : ℝ} {n : ℕ} (ha'W : a' ≤ W)
    {σ : ℝ} (hσ : σ ∈ Set.Icc a' W)
    (hf_cont : ∀ s ∈ Set.Icc a' W,
      ContinuousOn (f s) (Set.Icc (0 : ℝ) 1))
    (h_diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc a' W,
      HasDerivWithinAt (fun r => f r x) (f' s x) (Set.Icc a' W) s)
    (h_cont_deriv : ContinuousOn (Function.uncurry f')
      (Set.Icc a' W ×ˢ Set.Icc (0 : ℝ) 1)) :
    HasDerivWithinAt (fun s => cosineCoeffs (f s) n)
      (cosineCoeffs (f' σ) n) (Set.Icc a' W) σ
```

This is almost exactly the coefficient-level engine a hypothetical `CoupledChemDivLocalChainRuleOn` should use.

A concrete use pattern is in:

```text
ShenWork/Paper2/IntervalPicardLevel0SourceTimeC1On.lean
```

The theorem `heatSourceCoeff_hasDerivWithinAt` builds window-local coefficient derivatives by supplying:

- per-slice source continuity on `Icc c T`,
- pointwise `HasDerivWithinAt` on `Icc c T`,
- joint continuity of the derivative field on `Icc c T ×ˢ Icc 0 1`,

then calls `IntervalMildPicardRegularityEndpoint2.cosineCoeffs_hasDerivWithinAt_of_smooth_param`.

This is the best existing template for a chem-div windowed chain-rule path.

## Practical recommendation

The repo does **not** already contain the requested chem-div windowed structures. If the goal is to avoid proving anything at `τ ≤ 0`, the clean new abstraction would be a small direct package, not necessarily a full `FluxJointC2HypOn`:

```lean
structure CoupledChemDivLocalChainRuleOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (lo hi : ℝ) : Prop where
  hlohi : lo ≤ hi
  source_cont : ∀ s ∈ Set.Icc lo hi,
    ContinuousOn (coupledChemDivSourceLift p u s) (Set.Icc (0 : ℝ) 1)
  diff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ Set.Icc lo hi,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceLift p u r x)
      (coupledChemDivTimeDerivativeLift p u s x)
      (Set.Icc lo hi) s
  deriv_cont : ContinuousOn
    (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
    (Set.Icc lo hi ×ˢ Set.Icc (0 : ℝ) 1)
```

Then prove:

```lean
theorem coupledChemDivCoeff_hasDerivWithinAt_of_chainRuleOn
    (hchain : CoupledChemDivLocalChainRuleOn p u lo hi) :
    ∀ s ∈ Set.Icc lo hi, ∀ n,
      HasDerivWithinAt
        (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n)
        (Set.Icc lo hi) s := by
  -- call IntervalMildPicardRegularityEndpoint2.cosineCoeffs_hasDerivWithinAt_of_smooth_param
```

That would match the existing `DuhamelSourceTimeC1On` endpoint design and avoid the global `τ ≤ 0` obligations entirely.

If the objective is minimal disruption to the current code, your fallback is valid: keep the existing global `CoupledChemDivFluxJointC2Hyp` target and split `τ`:

```lean
by_cases hτ : 0 < τ
· -- real positive-time proof; choose δ small enough, e.g. δ ≤ τ / 2, so the slab stays in `Ioi 0`
  ...
· -- τ ≤ 0 branch
  sorry
```

This is syntactically the shortest way to preserve the current global pipeline. The nonpositive branch is not degenerate or vacuous, though; it is a real placeholder for behavior outside the positive time window.
