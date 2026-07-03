# Codex Spec: Replace `dotMaj` with direct Duhamel semigroup estimate

## Goal

In `ShenWork/Wiener/EWA/SourceReducedCoreWire.lean`, replace the term-by-term
derivative majorant `dotMaj` (which uses `derivBound` from `DuhamelSourceTimeC1On`)
with a new majorant that uses only the **direct Duhamel semigroup estimate**:

    λ_n * |∫₀ᵗ e^{-λ_n(t-s)} a(s,n) ds| ≤ envelope(n)

This eliminates the dependency on `derivBound` / `hderivBound`, which is the
hardest field to produce for the EWA Picard fixed point.

## Mathematical key estimate

For a source coefficient family `a : ℝ → ℕ → ℝ` with summable envelope
`env(n)` satisfying `|a(s,n)| ≤ env(n)` for all `s ∈ [0,T]`:

```
|duhamelSpectralCoeff a t n| = |∫₀ᵗ e^{-λ_n(t-s)} a(s,n) ds|
  ≤ ∫₀ᵗ e^{-λ_n(t-s)} |a(s,n)| ds
  ≤ env(n) ∫₀ᵗ e^{-λ_n(t-s)} ds
  = env(n) · (1 - e^{-λ_n t}) / λ_n       (for λ_n > 0)
```

Therefore:
```
λ_n · |duhamelSpectralCoeff a t n| ≤ env(n) · (1 - e^{-λ_n t}) ≤ env(n)
```

And the fullSourceCoeffDot has the spectral ODE form:
```
fullSourceCoeffDot(s,n) = -λ_n · e^{-sλ_n} · u₀(n)
  + (-χ₀) · (chemSource(s,n) - λ_n · duhamelCoeff(chem, s, n))
  + (logSource(s,n) - λ_n · duhamelCoeff(log, s, n))
```

Bound each term using triangle inequality:
```
|chemSource(s,n) - λ_n · duhamelCoeff(chem, s, n)|
  ≤ |chemSource(s,n)| + λ_n · |duhamelCoeff(chem, s, n)|
  ≤ chemEnv(n) + chemEnv(n) = 2 · chemEnv(n)
```

So:
```
|fullSourceCoeffDot(s,n)| ≤ Mu0 · λ_n · e^{-cλ_n}
  + 2|χ₀| · chemEnv(n) + 2 · logEnv(n)
```

This is **summable** (heat term by super-exponential decay for c > 0, source
terms by envelope summability), and **does not use `derivBound`**.

## Concrete changes in SourceReducedCoreWire.lean

### Step 1: Add the direct Duhamel eigenvalue estimate

Add after line ~225 (after `duhamel_deriv_bound_on`):

```lean
/-- Direct Duhamel semigroup bound: λ_n * |duhamelCoeff| ≤ envelope. -/
private theorem eigenvalue_mul_abs_duhamelCoeff_le_env {a : ℝ → ℕ → ℝ}
    {env : ℕ → ℝ}
    (henv_nn : ∀ n, 0 ≤ env n)
    (henv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |a s n| ≤ env n)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) (n : ℕ) :
    unitIntervalCosineEigenvalue n * |duhamelSpectralCoeff a t n| ≤ env n
```

The proof uses: factor out the absolute value, bound `|a(s,n)|` by `env(n)`,
compute the integral ∫₀ᵗ e^{-λ(t-s)} ds = (1-e^{-λt})/λ, multiply by λ.
Use `ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one` for the
`λ · (1-e^{-λt})/λ = 1 - e^{-λt} ≤ 1` step.

Also add the corollary for the "difference" form:
```lean
private theorem source_minus_eigenvalue_duhamel_le_two_env {a : ℝ → ℕ → ℝ}
    {env : ℕ → ℝ}
    (henv_nn : ∀ n, 0 ≤ env n)
    (henv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |a s n| ≤ env n)
    {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) (n : ℕ) :
    |a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n|
      ≤ 2 * env n
```

Proof: triangle inequality + the above.

### Step 2: Define new majorant `dotMajDirect`

```lean
private noncomputable def dotMajDirect (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (Mu0 c : ℝ)
    (chemEnv logEnv : ℕ → ℝ) (n : ℕ) : ℝ :=
  Mu0 * (unitIntervalCosineEigenvalue n *
      Real.exp (-c * unitIntervalCosineEigenvalue n))
    + 2 * |(-p.χ₀)| * chemEnv n + 2 * logEnv n
```

### Step 3: Prove summability and bound for `dotMajDirect`

```lean
private theorem dotMajDirect_summable (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (Mu0 : ℝ) {c : ℝ} (hc : 0 < c)
    (chemEnv logEnv : ℕ → ℝ)
    (hchemSum : Summable chemEnv) (hlogSum : Summable logEnv) :
    Summable (dotMajDirect p u Mu0 c chemEnv logEnv)
```

```lean
private theorem dotMajDirect_bound (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {Mu0 : ℝ}
    (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (chemEnv logEnv : ℕ → ℝ)
    (hchemNN : ∀ n, 0 ≤ chemEnv n)
    (hlogNN : ∀ n, 0 ≤ logEnv n)
    (hchemBd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivSourceCoeffs p u s n| ≤ chemEnv n)
    (hlogBd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledLogisticSourceCoeffs p u s n| ≤ logEnv n)
    {c : ℝ} (hc : 0 < c) (hcT : c < T) (x : ℝ) (n : ℕ)
    (s : ℝ) (hs : s ∈ Ioo c T) :
    ‖fullSourceCoeffDot p u u₀cos s n * cosineMode n x‖ ≤
      dotMajDirect p u Mu0 c chemEnv logEnv n
```

### Step 4: New synthesis theorem

Write `synthesis_hasDerivAt_direct` using `dotMajDirect` instead of `dotMaj`.
It takes:
- Source coefficients continuous on [0,T] (for each mode)
- Source envelopes summable + bounding

It does NOT take DuhamelSourceTimeC1On.

The proof structure is identical to `synthesis_hasDerivAt_on`, using
`hasDerivAt_tsum_of_isPreconnected` with `dotMajDirect` as the domination.

For `fullSourceCoeff_hasDerivAt_on`, we need `duhamelSpectralCoeff_hasDerivAt_of_on`.
Currently this takes `DuhamelSourceTimeC1On`, but only uses it for
ContinuousOn of the source coefficients (line 14-16 of IntervalDuhamelSpectralDerivOn.lean).

Write a new version `duhamelSpectralCoeff_hasDerivAt_of_cont` that takes
ContinuousOn directly:

In a new file `ShenWork/PDE/IntervalDuhamelSpectralDerivCont.lean`:
```lean
theorem duhamelSpectralCoeff_hasDerivAt_of_cont {a : ℝ → ℕ → ℝ} {T : ℝ}
    (hcont : ContinuousOn (fun s => a s n) (Icc 0 T))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasDerivAt (fun r => duhamelSpectralCoeff a r n)
      (a t n - unitIntervalCosineEigenvalue n * duhamelSpectralCoeff a t n) t
```

The proof is IDENTICAL to `duhamelSpectralCoeff_hasDerivAt_of_on` but
takes `hcont` directly instead of deriving it from `DuhamelSourceTimeC1On`.

### Step 5: New `realSlice_reducedCore_wired_v2`

Write `realSlice_reducedCore_wired_v2` with the same signature as
`realSlice_reducedCore_wired` BUT replacing:
```
(hchem_on : DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 T)
(hlog_on : DuhamelSourceTimeC1On (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T)
```
with:
```
(hchem_cont : ∀ n, ContinuousOn
    (fun s => coupledChemDivSourceCoeffs p (realSlice u_star) s n) (Set.Icc 0 T))
(hlog_cont : ∀ n, ContinuousOn
    (fun s => coupledLogisticSourceCoeffs p (realSlice u_star) s n) (Set.Icc 0 T))
(chemEnv logEnv : ℕ → ℝ)
(hchemEnvNN : ∀ n, 0 ≤ chemEnv n)
(hlogEnvNN : ∀ n, 0 ≤ logEnv n)
(hchemEnvSum : Summable chemEnv)
(hlogEnvSum : Summable logEnv)
(hchemEnvBd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
    |coupledChemDivSourceCoeffs p (realSlice u_star) s n| ≤ chemEnv n)
(hlogEnvBd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
    |coupledLogisticSourceCoeffs p (realSlice u_star) s n| ≤ logEnv n)
```

## Verification

```bash
cd ~/repos/Shen_work
lake env lean ShenWork/PDE/IntervalDuhamelSpectralDerivCont.lean
lake env lean ShenWork/Wiener/EWA/SourceReducedCoreWire.lean
```

Both must exit 0 with no `sorry`, no `axiom`, no `native_decide`.

## Key definitions to import

- `duhamelSpectralCoeff`: `ShenWork.IntervalDuhamelClosedC2`
- `unitIntervalCosineEigenvalue`: search the tree for its definition
- `reciprocalSquareTerm`: used in the old bound, NOT needed for the new one
- `fullSourceCoeffDot`, `fullSourceCoeff`: already imported in SourceReducedCoreWire
- `ShenWork.IntervalDuhamelRegularity.parabolicGain_le_one`: for 1-e^{-λt} ≤ 1

## What NOT to do

- Do NOT modify `dotMaj`, `dotMaj_summable`, `dotMaj_bound`, `duhamel_deriv_bound_on`,
  `synthesis_hasDerivAt_on`, or `realSlice_reducedCore_wired` — keep them intact
- Add the new versions ALONGSIDE the existing ones (v2 pattern)
- Do NOT introduce `sorry`, `axiom`, `native_decide`, or `admit`
- Keep line length ≤ 100 chars
