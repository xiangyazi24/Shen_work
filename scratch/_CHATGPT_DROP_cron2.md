# Q570 (cron2): uniform-in-`n` bounds for `coupledChemDivAdot`

## Executive verdict

On `chatgpt-scratch`, I found **no unconditional heat-level0 theorem** and no theorem specialized to

```lean
u = conjugatePicardIter p u₀ 0
```

that proves

```lean
∃ Mdot, ∀ s ∈ Icc c T, ∀ n,
  |coupledChemDivAdot p u s n| ≤ Mdot
```

or even the `[0,T]` version without additional analytic inputs.

What exists on `chatgpt-scratch` is only the **residual converter**:

```lean
chemDivAdot_Mdot_residual
```

It turns a supplied nonnegative summable envelope for `|coupledChemDivAdot p u s n|` into a single uniform `Mdot`.  It does **not** construct that envelope.

There is a stronger file, `ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean`, visible in the repository's indexed/default branch, that provides conditional producers from quadratic decay / spatial H² data.  But `fetch_file(..., ref="chatgpt-scratch")` returns **404** for that file, so it is **not currently present on `chatgpt-scratch`**.  Porting or recreating that file would give useful conditional Mdot producers, but still not an unconditional heat-level0 bound: it requires H²/quadratic-decay inputs for the time-derivative field.

Bottom line: the genuine residual is real.  The repo has the abstract envelope-to-Mdot theorem on `chatgpt-scratch`; default has conditional H²/quadratic-decay producers; neither branch has a ready-made heat-semigroup-level0 uniform `Mdot` theorem.

## 1. `ChemDivAdot.lean` on `chatgpt-scratch`: envelope residual only

`ShenWork/Wiener/EWA/ChemDivAdot.lean:165` states explicitly that per-mode continuity does **not** imply a uniform-in-`n` bound:

```lean
The uniform bound `Mdot` is a SINGLE real with `|coupledChemDivAdot p u s n| ≤ Mdot`
for ALL `n` and all `s ∈ [0,T]`.  Per-mode smoothness gives continuity of each
`s ↦ coupledChemDivAdot p u s n` on the compact `[0,T]`, hence a per-`n` bound — but the
constant depends on `n` and there is no uniform control as `n → ∞` from smoothness alone.
```

The only Mdot theorem in this file is the residual converter:

`ShenWork/Wiener/EWA/ChemDivAdot.lean:185`

```lean
theorem chemDivAdot_Mdot_residual
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (env : ℕ → ℝ) (henvnn : ∀ n, 0 ≤ env n) (henvsum : Summable env)
    (henv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |coupledChemDivAdot p u s n| ≤ env n) :
    ∃ Mdot : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

Interpretation: this is useful once you prove an envelope, but it does not prove any pointwise coefficient decay or H² regularity by itself.

## 2. `CoupledChemDivTimeC1Fields`: Mdot is an input field, not produced

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:96`

```lean
structure CoupledChemDivTimeC1Fields
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  ...
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot
```

`hMdot` is then passed through when constructing the source time-C¹ package:

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean:130`

```lean
noncomputable def coupledChemDivSource_timeC1_of_fields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (F : CoupledChemDivTimeC1Fields p u) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u)
```

with the call ending in:

```lean
... (Mdot := F.MchemDot) F.hMdot
```

So this structure does not solve the residual; it requires it.

## 3. `IntervalChemDivWinDischarge.lean`: residual bundle also carries `hMdot`

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:79`

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  ...
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot
```

The residual is wired into the global source package:

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:122`

```lean
theorem fluxJointC2Hyp_of_residual {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    CoupledChemDivFluxJointC2Hyp p u
```

and then:

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:131`

```lean
noncomputable def coupledChemDivSource_duhamelSourceTimeC1_of_residual
    {u : ℝ → intervalDomainPoint → ℝ}
    (R : ChemDivSolutionRegularityResidual p u) :
    DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u)
```

The call passes `R.hadotcont R.MchemDot R.hMdot`, so again the uniform adot bound is assumed in the residual bundle, not generated there.

## 4. `ChemDivAdotEnvelope.lean`: useful conditional producers, but absent on `chatgpt-scratch`

Attempted branch fetch:

```text
fetch_file(path = "ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean", ref = "chatgpt-scratch")
→ 404 Not Found
```

The file exists on the repository's indexed/default branch.  It is exactly the missing conditional envelope/Mdot producer.

### Envelope definition and lemmas

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:62` on default/indexed branch:

```lean
noncomputable def adotEnvelope (Cdot : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then Cdot else Cdot / ((n : ℝ) * Real.pi) ^ 2
```

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:67`

```lean
theorem adotEnvelope_nonneg {Cdot : ℝ} (hC : 0 ≤ Cdot) :
    ∀ n, 0 ≤ adotEnvelope Cdot n
```

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:82`

```lean
theorem adotEnvelope_summable {Cdot : ℝ} (hC : 0 ≤ Cdot) :
    Summable (adotEnvelope Cdot)
```

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:109`

```lean
theorem adotEnvelope_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {Cdot : ℝ} {s : ℝ}
    (hzero : |coupledChemDivAdot p u s 0| ≤ Cdot)
    (hdecay : ∀ n : ℕ, 1 ≤ n →
      |coupledChemDivAdot p u s n| ≤ Cdot / ((n : ℝ) * Real.pi) ^ 2) :
    ∀ n, |coupledChemDivAdot p u s n| ≤ adotEnvelope Cdot n
```

### Uniform Mdot from quadratic decay

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:137` on default/indexed branch:

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

This is exactly the desired output shape, but the hypotheses are still the genuine analytic work: mode-0 bound plus uniform quadratic decay for all `n ≥ 1`.

### Uniform Mdot from spatial H²/sup bounds

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:163` on default/indexed branch:

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

This is the more practical theorem to port/adapt for level 0.  It still requires a uniform sup bound for the time-derivative field and a raw quadratic coefficient-decay estimate, i.e. the H² regularity of `coupledChemDivTimeDerivativeLift` on the time window.

## 5. Search conclusion

Searches for:

```text
coupledChemDivAdot Mdot bound hMdot
chemDivAdot_Mdot adotEnvelope chemDivAdot_Mdot_of_quadratic_decay
"|coupledChemDivAdot" "≤"
MchemDot hMdot coupledChemDivAdot
```

found no additional unconditional/specialized bound theorem.  The only relevant results are:

1. `chemDivAdot_Mdot_residual` on `chatgpt-scratch`, requiring a summable envelope.
2. `hMdot` fields in `CoupledChemDivTimeC1Fields` and `ChemDivSolutionRegularityResidual`, which are assumptions.
3. `ChemDivAdotEnvelope.lean` on the default/indexed branch, containing conditional producers from quadratic decay / spatial H² inputs, but missing from `chatgpt-scratch`.

## Practical recommendation

For the Level0 heat-semigroup chain, the next target should be a windowed version of the default-branch theorem, probably:

```lean
theorem level0_chemDivAdot_Mdot_of_spatial_H2_on
    ...
    (hcont : ∀ s ∈ Icc c T, ContinuousOn
      (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s) (Icc 0 1))
    (hbd : ∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1,
      |coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s x| ≤ B_sup)
    (hdecay_raw : ∀ s ∈ Icc c T, ∀ n, 1 ≤ n →
      |coupledChemDivAdot p (conjugatePicardIter p u₀ 0) s n|
        ≤ 2 * B_H2 / ((n : ℝ) * Real.pi)^2) :
    ∃ Mdot, ∀ s ∈ Icc c T, ∀ n,
      |coupledChemDivAdot p (conjugatePicardIter p u₀ 0) s n| ≤ Mdot
```

The proof should be a direct port of `ChemDivAdotEnvelope.lean`, but with `Icc c T` instead of `Icc 0 T`.  The remaining analytic payload is proving `hbd` and `hdecay_raw` for the heat semigroup time-derivative field.