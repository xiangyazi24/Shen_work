# Q527 (cron2): chemDiv `adot` infrastructure for heat semigroup level 0

## Executive verdict

The repo already has the coefficient derivative theorem you need.  For the heat semigroup target on `[c,T]`, the derivative and continuity legs should be filled with the canonical

```lean
adot := coupledChemDivAdot p (conjugatePicardIter p u₀ 0)
```

and then:

1. `h_deriv` comes from `CoupledChemDivLocalChainRule` via the committed `HasDerivAt` theorem and `.hasDerivWithinAt`.
2. `h_adotcont` comes from joint continuity of `coupledChemDivTimeDerivativeLift` on `[c,T] × [0,1]` plus `cosineCoeffs_continuousOn_of_jointContinuousOn_Icc`.
3. `Mdot` is not produced by smoothness/continuity.  It requires a uniform summable envelope or a quadratic-decay/H² bound for the time-derivative field.

Important branch note: `ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean` is present in the current indexed/default branch, but `fetch_file(..., ref="chatgpt-scratch")` returned 404 for that path.  If the active implementation branch is `chatgpt-scratch`, either port that file or copy/generalize its proofs locally.

## Target sorry location

The target theorem is in:

`ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean:335`

```lean
theorem level0_chemDiv_timeDerivData
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (_hcT : c ≤ T)
    (_hu₀_cont : Continuous u₀)
    (_hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (_hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (_hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ (adot : ℝ → ℕ → ℝ) (Mdot : ℝ),
      (∀ s ∈ Icc c T, ∀ n,
        HasDerivWithinAt
          (fun r => coupledChemDivSourceCoeffs p (conjugatePicardIter p u₀ 0) r n)
          (adot s n) (Icc c T) s) ∧
      (∀ n, ContinuousOn (fun s => adot s n) (Icc c T)) ∧
      (∀ s ∈ Icc c T, ∀ n, |adot s n| ≤ Mdot)
```

Inside it, the current skeleton already has the right structure:

- `hchain : CoupledChemDivLocalChainRule p (conjugatePicardIter p u₀ 0)` at `IntervalConjugateLevel0BFormSourceOn.lean:359`, currently sorry at line `361`.
- `hjointcont : ContinuousOn (Function.uncurry (coupledChemDivTimeDerivativeLift p ...)) (Icc c T ×ˢ Icc 0 1)` at line `372`, currently sorry at line `376`.
- `hderiv_global` is then derived at line `384`; `hderiv` on `[c,T]` at line `399` uses `.hasDerivWithinAt`.
- `hadotcont` is derived at line `406` using `cosineCoeffs_continuousOn_of_jointContinuousOn_Icc`.
- the remaining true residual is `hMdot` at line `422`, currently sorry at line `423`.

## 1. `HasDerivAt` / `HasDerivWithinAt` theorems for `coupledChemDivSourceCoeffs`

### Candidate derivative definition

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:45`

```lean
def coupledChemDivAdot (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n
```

### Original full-field `HasDerivAt` theorem

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:114`

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_fields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (F : CoupledChemDivTimeC1Fields p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s
```

Hypotheses hidden inside `F : CoupledChemDivTimeC1Fields p u` are at `IntervalChemDivTimeDerivative.lean:96`:

```lean
structure CoupledChemDivTimeC1Fields
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  Cchem : ℝ
  hCchem : 0 ≤ Cchem
  hH2 : ∀ s, 0 ≤ s →
    IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)
  hdecay : ∀ s, 0 ≤ s → ∀ k : ℕ, 1 ≤ k →
    |cosineCoeffs (coupledChemDivSourceLift p u s) k|
      ≤ Cchem / ((k : ℝ) * Real.pi) ^ 2
  hzero : ∀ s, 0 ≤ s →
    |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ Cchem
  hchain : CoupledChemDivLocalChainRule p u
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot
```

But the theorem body only uses `F.hchain`.

### Slim `HasDerivAt` theorem consuming only the chain-rule package

`ShenWork/Wiener/EWA/ChemDivAdot.lean:79`

```lean
theorem coupledChemDivCoeff_hasDerivAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) (s : ℝ) (n : ℕ) :
    HasDerivAt
      (fun r => cosineCoeffs (coupledChemDivSourceLift p u r) n)
      (coupledChemDivAdot p u s n) s
```

This is the cleanest theorem for your `[c,T]` target, because once you have global `HasDerivAt`, Lean can restrict it to any set:

```lean
exact (coupledChemDivCoeff_hasDerivAt_of_chainRule hchain s n).hasDerivWithinAt
```

You may need the `simpa [coupledChemDivSourceCoeffs]` wrapper because the theorem is stated for `cosineCoeffs (coupledChemDivSourceLift ...)`, while your target is stated with `coupledChemDivSourceCoeffs`.

### Existing `[0,T]` `HasDerivWithinAt` theorem

`ShenWork/Wiener/EWA/ChemDivAdot.lean:100`

```lean
theorem chemDivAdot_hasDerivWithinAt_of_chainRule
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
        (coupledChemDivAdot p u s n) (Set.Icc 0 T) s
```

This is useful for consumers shaped as `[0,T]`, but it is not directly the target `[c,T]` theorem.  For the heat semigroup positive window, use the global `HasDerivAt` theorem above and restrict to `Icc c T`; this is exactly what the current target file does around `IntervalConjugateLevel0BFormSourceOn.lean:384-404`.

### Chain-rule package required by the `HasDerivAt` theorem

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:78`

```lean
structure CoupledChemDivLocalChainRule
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt
        (fun r => coupledChemDivSourceLift p u r x)
        (coupledChemDivTimeDerivativeLift p u s x) s) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

There is a pointwise-atom wrapper in `ShenWork/PDE/IntervalChemDivLocalChainRule.lean:33`:

```lean
theorem coupledChemDivLocalChainRule_of_pointwiseChainAtoms
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (A : CoupledChemDivPointwiseChainAtoms p u) :
    CoupledChemDivLocalChainRule p u
```

## 2. Continuity theorem for `coupledChemDivAdot`

### Direct theorem, `[0,T]` shape

`ShenWork/Wiener/EWA/ChemDivAdot.lean:125`

```lean
theorem chemDivAdot_continuousOn_of_jointCont
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n) (Set.Icc (0 : ℝ) T)
```

Again, this is `[0,T]`-shaped.  For the actual positive window `[c,T]`, use the lower-level compact dominated-convergence lemma directly.

### Generic coefficient-continuity lemma, arbitrary `[c,T]`

`ShenWork/Paper2/IntervalDomainPositiveWindowK1OnEndpoint.lean:31`

```lean
theorem cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
    {f : ℝ → ℝ → ℝ} {c T : ℝ} (k : ℕ)
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun σ => cosineCoeffs (f σ) k) (Set.Icc c T)
```

This is exactly what the target skeleton uses at `IntervalConjugateLevel0BFormSourceOn.lean:406-417`:

```lean
have key :=
  cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
    (f := coupledChemDivTimeDerivativeLift
      p (conjugatePicardIter p u₀ 0))
    (c := c) (T := T) n hjointcont
simpa only [hadot_def, coupledChemDivAdot] using key
```

So `hadotcont` needs precisely:

```lean
hjointcont : ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

### Combined derivative+continuity package

`ShenWork/Wiener/EWA/ChemDivAdot.lean:149`

```lean
theorem chemDivAdot_deriv_legs_of_smoothness
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hchain : CoupledChemDivLocalChainRule p u)
    (hjointcont : ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Set.Icc (0 : ℝ) T ×ˢ Set.Icc (0 : ℝ) 1)) :
    (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (coupledChemDivAdot p u s n) (Set.Icc 0 T) s)
      ∧ (∀ n, ContinuousOn (fun s => coupledChemDivAdot p u s n)
          (Set.Icc (0 : ℝ) T))
```

This is a good reference theorem, but for the target `[c,T]` it is better to inline/use the two lower-level facts as above.

## 3. Resolver time-derivative continuity facts and their hypotheses

The resolver-side hypothesis is:

`ShenWork/Paper2/IntervalResolverTimeRegularity.lean:38`

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

It gives joint continuity of `v_t` (not of the full chemDiv time derivative):

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:50`

```lean
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

and fixed-space closed-window continuity:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:60`

```lean
theorem coupledChemicalTimeDerivative_continuousOn_Icc_of_lt_horizon
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {U T c x : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u))
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => coupledChemicalTimeDerivativeLift p u s x)
      (Icc c T)
```

The lower-level endpoint theorem is in `ShenWork/Paper2/IntervalResolverTimeEndpoint.lean:39`:

```lean
theorem resolver_lift_timeDeriv_continuousOn_Icc_of_lt_horizon
    {U T c x : ℝ} {v : ℝ → intervalDomainPoint → ℝ}
    (H : ResolverHasSpectralAgreement U v)
    (hc : 0 < c) (hTU : T < U) (hx : x ∈ Icc (0 : ℝ) 1) :
    ContinuousOn
      (fun s => deriv (fun r => intervalDomainLift (v r) x) s)
      (Icc c T)
```

There are convenience wrappers in `ShenWork/PDE/IntervalChemDivLocalChainRule.lean`:

- `chemDiv_vt_jointContinuous_factor` at line `40`, requiring only `H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)` and returning joint continuity of `coupledChemicalTimeDerivativeLift` on `Ioo 0 U × [0,1]`.
- `chemDiv_vt_continuousOn_factor` at line `50`, requiring `H`, `hc : 0 < c`, `hTU : T < U`, and `hx : x ∈ Icc 0 1`, returning fixed-`x` continuity on `Icc c T`.
- `chemDiv_v_hasDerivAt_factor` at line `72`, requiring `H`, `hs0 : 0 < s`, `hsU : s < U`, `hy : y ∈ Icc 0 1`, returning pointwise `HasDerivAt` for `v` with derivative `coupledChemicalTimeDerivativeLift`.

Crucial distinction: these resolver facts only control `coupledChemicalTimeDerivativeLift` (`v_t`).  They do not by themselves prove

```lean
ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
  (Icc c T ×ˢ Icc (0 : ℝ) 1)
```

because `coupledChemDivTimeDerivativeLift` also contains `slopeSlice u`, `deriv v`, `deriv vt`, products, powers, and an outer spatial derivative.  You need an additional chemDiv mixed-time-derivative continuity/closed representative fact.

One such abstraction exists:

`ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:43`

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

and it produces:

`ShenWork/PDE/IntervalChemDivTimeDerivClosed.lean:54`

```lean
theorem chemDivMixedTimeDeriv_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {τ δ : ℝ}
    (H : ChemDivMixedTimeDerivClosedRepr p u τ δ) :
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

For the heat-semigroup positive window, the missing analytic step is to produce the analogous closed representative/joint continuity on `[c,T] × [0,1]`.

## 4. Bound theorem for `coupledChemDivAdot`

### General residual: summable envelope implies `Mdot`

`ShenWork/Wiener/EWA/ChemDivAdot.lean:185`

```lean
theorem chemDivAdot_Mdot_residual
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (env : ℕ → ℝ) (henvnn : ∀ n, 0 ≤ env n) (henvsum : Summable env)
    (henv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |coupledChemDivAdot p u s n| ≤ env n) :
    ∃ Mdot : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

This isolates the exact missing ingredient: a nonnegative summable envelope `env` dominating all time-derivative coefficients uniformly in time and mode.

However, this theorem is `[0,T]`-shaped.  Your target is `[c,T]`.  If you only have heat-semigroup smoothing for `c > 0`, clone/generalize this theorem to arbitrary `Icc c T`; its proof should be identical.

### Quadratic-decay producer on current default branch

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:135` (current default branch; absent from `chatgpt-scratch` when fetched by ref)

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

### H²/sup-bound producer on current default branch

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:161` (current default branch; absent from `chatgpt-scratch` when fetched by ref)

```lean
theorem chemDivAdot_Mdot_of_spatial_H2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {B_sup B_H2 : ℝ} (hBs : 0 ≤ B_sup) (hBh : 0 ≤ B_H2)
    (hcont : ∀ s ∈ Icc (0 : ℝ) T, ContinuousOn
      (coupledChemDivTimeDerivativeLift p u s) (Icc (0 : ℝ) 1))
    (hbd : ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B_sup)
    (hdecay_raw : ∀ s ∈ Icc (0 : ℝ) T, ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ 2 * B_H2 / ((n : ℝ) * Real.pi) ^ 2) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

For your `[c,T]` heat-window theorem, the natural local replacement is:

```lean
∃ Cdot, 0 ≤ Cdot ∧
  (∀ s ∈ Icc c T, |coupledChemDivAdot p u s 0| ≤ Cdot) ∧
  (∀ s ∈ Icc c T, ∀ n, 1 ≤ n →
    |coupledChemDivAdot p u s n| ≤ Cdot / ((n : ℝ) * Real.pi)^2)
```

then use the same `adotEnvelope` proof with `Icc c T` instead of `Icc 0 T`.

## Practical fill strategy for `level0_chemDiv_timeDerivData`

Use this shape:

```lean
set u := conjugatePicardIter p u₀ 0
set adot := coupledChemDivAdot p u with hadot_def

have hderiv : ∀ s ∈ Icc c T, ∀ n,
    HasDerivWithinAt
      (fun r => coupledChemDivSourceCoeffs p u r n)
      (adot s n) (Icc c T) s := by
  intro s hs n
  have hAt : HasDerivAt
      (fun r => coupledChemDivSourceCoeffs p u r n)
      (adot s n) s := by
    simpa [coupledChemDivSourceCoeffs, hadot_def] using
      coupledChemDivCoeff_hasDerivAt_of_chainRule
        (p := p) (u := u) hchain s n
  exact hAt.hasDerivWithinAt

have hadotcont : ∀ n, ContinuousOn (fun s => adot s n) (Icc c T) := by
  intro n
  have key :=
    ShenWork.IntervalDomainPositiveWindowK1OnEndpoint
      .cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
        (f := coupledChemDivTimeDerivativeLift p u) (c := c) (T := T) n hjointcont
  simpa [hadot_def, coupledChemDivAdot] using key
```

For `hMdot`, do not try to get it from `ResolverHasSpectralAgreement` or `hadotcont`.  You need one of:

1. a windowed version of `chemDivAdot_Mdot_residual` plus a summable envelope on `[c,T]`, or
2. a windowed version of `chemDivAdot_Mdot_of_quadratic_decay`, or
3. a windowed version of `chemDivAdot_Mdot_of_spatial_H2` once you have H²/sup bounds for `coupledChemDivTimeDerivativeLift` on `[c,T] × [0,1]`.

Bottom line: the derivative/continuity sorries are reducible to `hchain` and `hjointcont`; the real analytic content for `adot` is the uniform coefficient envelope for `coupledChemDivTimeDerivativeLift` on the positive window.