# Q518 / cron1: chemDiv `adot` on a positive window

## Executive verdict

For the desired heat-semigroup statement on `[c,T]`, the repo has a **generic, proved bridge** from the local chem-div chain rule to coefficient `HasDerivAt` with derivative exactly

```lean
coupledChemDivAdot p u s n
```

and therefore `HasDerivWithinAt` on any closed window follows immediately by `.hasDerivWithinAt`.

What I did **not** find on the target `chatgpt-scratch` branch is a closed, heat-semigroup-specialized producer of the full package

```lean
∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
  hderiv_on_Icc ∧ hadotcont_on_Icc ∧ hMdot_on_Icc
```

for `u = conjugatePicardIter p u₀ 0`.  The missing part is not the formal coefficient derivative bridge; it is the analytic input for the heat level: local chain rule/joint-continuity of the explicit time-derivative field, plus a **uniform-in-mode** bound for `coupledChemDivAdot`.

Code search on `main` does show newer roadmap/prototype files for exactly this level-0 heat-semigroup package, but several of them are not present on `chatgpt-scratch` at the time of this report.  In particular, `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, `ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean`, `ShenWork/Paper2/IntervalChemDivSpatialC2.lean`, and `ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean` were found by repo code search/default-branch fetches, while `fetch_file(..., ref := "chatgpt-scratch")` returned 404 for them.  Treat them as useful roadmap unless merged into the target branch.

## 1. Existing derivative theorem for `coupledChemDivAdot`

The canonical candidate is already fixed in

```lean
-- ShenWork/PDE/IntervalChemDivTimeDerivative.lean
noncomputable def coupledChemDivAdot (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n
```

and `coupledChemDivTimeDerivativeLift` is the pointwise chain-rule field using `slopeSlice u` and `coupledChemicalTimeDerivativeLift` for the elliptic concentration time derivative.

The main proved branch-local bridge is in `ShenWork/Wiener/EWA/ChemDivAdot.lean`:

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s
```

There is also the packaged window form on `[0,T]`:

```lean
theorem chemDivAdot_hasDerivWithinAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s
```

For the requested positive window `[c,T]`, do not need a new theorem.  Use the global `HasDerivAt` theorem and restrict to the desired set:

```lean
let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0

have hderiv_Icc_cT :
    ∀ s ∈ Set.Icc c T, ∀ n,
      HasDerivWithinAt
        (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n)
        (Set.Icc c T) s := by
  intro s hs n
  have hAt :
      HasDerivAt
        (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) s := by
    simpa [coupledChemDivSourceCoeffs] using
      coupledChemDivCoeff_hasDerivAt_of_chainRule
        (p := p) (u := u) hchain s n
  exact hAt.hasDerivWithinAt
```

So the answer to question (1) is: **yes, for arbitrary `u`, provided you have `CoupledChemDivLocalChainRule p u`; no heat-specialized closed theorem is needed for the formal `HasDerivWithinAt` step.**

## 2. Infrastructure for `adot` continuity and boundedness

### Continuity

The branch-local generic theorem is:

```lean
theorem chemDivAdot_continuousOn_of_jointCont
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n) (Set.Icc (0 : ℝ) T)
```

It is just the compact dominated-convergence lemma for cosine coefficients.  For `[c,T]`, use the underlying lemma directly:

```lean
ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
  .cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

whose shape is:

```lean
theorem cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
    {f : ℝ → ℝ → ℝ} {c T : ℝ} (k : ℕ)
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun σ => cosineCoeffs (f σ) k) (Set.Icc c T)
```

Thus, for the heat semigroup level:

```lean
have hadotcont :
    ∀ n, ContinuousOn
      (fun s => coupledChemDivAdot p (conjugatePicardIter p u₀ 0) s n)
      (Set.Icc c T) := by
  intro n
  simpa [coupledChemDivAdot] using
    ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
      .cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (f := coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0))
        (c := c) (T := T) n hjoint
```

The remaining obligation is therefore the slab continuity

```lean
ContinuousOn
  (Function.uncurry
    (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
  (Icc c T ×ˢ Icc 0 1)
```

not the cosine-coefficient continuity step.

### Boundedness

There are two levels.

On `chatgpt-scratch`, `ShenWork/Wiener/EWA/ChemDivAdot.lean` isolates the honest residual:

```lean
theorem chemDivAdot_Mdot_residual
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (env : ℕ → ℝ) (henvnn : ∀ n, 0 ≤ env n) (henvsum : Summable env)
    (henv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ env n) :
    ∃ Mdot : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

For `[c,T]`, the same proof pattern works with the window changed, or you can provide an envelope on `[0,T]` and restrict.  The important point is: **per-mode continuity on compact `[c,T]` only gives a bound depending on `n`; it does not give one uniform `Mdot` for all modes.**

On `main`/default, the file `ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean` goes further and supplies a concrete producer from quadratic decay of the `adot` coefficients:

```lean
theorem chemDivAdot_Mdot_of_quadratic_decay
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {Cdot : ℝ} (hC : 0 ≤ Cdot)
    (hzero : ∀ s ∈ Icc (0 : ℝ) T,
      |coupledChemDivAdot p u s 0| ≤ Cdot)
    (hdecay : ∀ s ∈ Icc (0 : ℝ) T, ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ Cdot / ((n : ℝ) * Real.pi) ^ 2) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

and also a spatial-H² style wrapper:

```lean
theorem chemDivAdot_Mdot_of_spatial_H2
    ...
    (hcont : ∀ s ∈ Icc (0 : ℝ) T,
      ContinuousOn (coupledChemDivTimeDerivativeLift p u s) (Icc 0 1))
    (hbd : ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc 0 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup)
    (hdecay_raw : ∀ s ∈ Icc (0 : ℝ) T, ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ 2 * B_H2 / ((n : ℝ) * Real.pi) ^ 2) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

This is exactly the right shape for the positive heat window: prove the time-derivative field has uniform spatial H²/Neumann control on `[c,T]`, then apply the quadratic envelope argument.

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean` confirms that the currently landed windowed consumer still treats `hadotcont`, `MchemDot`, and `hMdot` as part of the regularity residual.  It does not derive them from a bare `GradientMildSolutionData`.

## 3. Is `ResolverHasSpectralAgreement` needed?

For the **generic coupled solution route**, yes: existing branch-local facts use `ResolverHasSpectralAgreement` to get the `v_t` factor for

```lean
v = coupledChemicalConcentration p u
```

The relevant proved wrappers are in `IntervalChemDivTimeDerivative.lean` and `IntervalChemDivLocalChainRule.lean`:

```lean
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

```lean
theorem coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T)
```

and

```lean
theorem chemDiv_v_hasDerivAt_factor
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hs0 : 0 < s) (hsU : s < U) (hy : y ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)
      (coupledChemicalTimeDerivativeLift p u s y) s
```

For the **level-0 heat semigroup**, `ResolverHasSpectralAgreement` is probably not mathematically necessary and may be the wrong bottom.  A more direct proof should use the explicit heat series:

1. `conjugatePicardIter p u₀ 0` is definitionally
   ```lean
   fun t x => intervalFullSemigroupOperator t (intervalDomainLift u₀) x.1
   ```
   from `IntervalConjugatePicard.lean`.
2. On `main`, `IntervalHeatSemigroupHighRegularity.lean` proves `heatSemigroup_contDiff_four` from bounded initial cosine coefficients and `t > 0`.
3. On `main`, `IntervalChemDivSpatialC2.lean` contains the spatial C²/H² route for `chemDivLift` from global C⁴ cosine representatives.
4. The remaining heat-level time step should prove the direct chain rule for
   ```lean
   s ↦ coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) s n
   ```
   using `∂ₜ S(t)u₀ = Δ S(t)u₀` and the differentiated elliptic resolver source, then feed the already-landed coefficient bridge.

The default-branch file `IntervalConjugateLevel0BFormSourceOn.lean` states exactly the requested theorem as

```lean
theorem level0_chemDiv_timeDerivData ... :
  ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
    (∀ s ∈ Icc c T, ∀ n,
      HasDerivWithinAt
        (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
        (adot s n) (Icc c T) s) ∧
    (∀ n, ContinuousOn (fun s => adot s n) (Icc c T)) ∧
    (∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot)
```

but it is currently `sorry` there.  The comment says the intended proof is direct from heat-semigroup regularity, not from resolver spectral agreement.

## Minimal route I would implement

Use the branch-local bridge and specialize only the analytic hypotheses to the heat level:

```lean
let u : ℝ → intervalDomainPoint → ℝ := conjugatePicardIter p u₀ 0
let adot : ℝ → ℕ → ℝ := coupledChemDivAdot p u

-- analytic heat-level obligations:
hchain : CoupledChemDivLocalChainRule p u
hjoint : ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc c T ×ˢ Icc 0 1)
henv : ∃ env, Summable env ∧ (∀ n, 0 ≤ env n) ∧
  ∀ s ∈ Icc c T, ∀ n, |coupledChemDivAdot p u s n| ≤ env n
```

Then:

* `hderiv` is `coupledChemDivCoeff_hasDerivAt_of_chainRule hchain` plus `.hasDerivWithinAt`;
* `hadotcont` is `cosineCoeffs_continuousOn_of_jointContinuousOn_Icc` applied to `coupledChemDivTimeDerivativeLift`;
* `Mdot` is `chemDivAdot_Mdot_residual` or the default-branch quadratic-envelope producer after merging/importing it.

So the practical answer is:

* **Yes**, the coefficient `HasDerivAt`/`HasDerivWithinAt` bridge exists and is already in terms of `coupledChemDivAdot`.
* **Continuity** is reduced to joint continuity of `coupledChemDivTimeDerivativeLift` on the compact slab.
* **Boundedness** requires a summable/quadratic envelope for the `adot` coefficients; compactness plus per-mode continuity is insufficient.
* **ResolverHasSpectralAgreement** is the existing generic way to get `v_t` regularity, but for `u = S(t)u₀` on `[c,T]`, a direct heat-series/elliptic-resolver proof should avoid it.  That direct proof is not fully landed on `chatgpt-scratch`.