# Q571 (cron2): sup/L∞ bound route for `coupledChemDivAdot`

## Executive verdict

There is **no existing bound theorem** on `chatgpt-scratch` proving a uniform sup/L∞ bound of the form

```lean
∀ s ∈ Icc c T, ∀ x ∈ Icc (0:ℝ) 1,
  |coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s x| ≤ B
```

nor a general sufficient-regularity theorem that bounds

```lean
|coupledChemDivTimeDerivativeLift p u s x|.
```

Searches for `coupledChemDivTimeDerivativeLift bound/sup/L∞/Linfty/B_sup/hbd` found no producer on `chatgpt-scratch`.  The only match with a `B_sup` field is `ChemDivAdotEnvelope.lean` on the indexed/default branch, and that file is **absent** on `chatgpt-scratch` (`fetch_file(..., ref = "chatgpt-scratch")` returns 404).

However, your proposed shortcut is absolutely the right shape: the repo already has the generic coefficient estimate

```lean
|cosineCoeffs f n| ≤ 2 * B
```

for every mode `n`, assuming `f` is continuous on `[0,1]` and `|f| ≤ B`.  Therefore the Level0 `Mdot` residual can be reduced to exactly two analytic facts:

```lean
hcont : ∀ s ∈ Icc c T,
  ContinuousOn (coupledChemDivTimeDerivativeLift p u s) (Icc (0:ℝ) 1)

hbd : ∀ s ∈ Icc c T, ∀ x ∈ Icc (0:ℝ) 1,
  |coupledChemDivTimeDerivativeLift p u s x| ≤ B
```

Then `Mdot := 2 * B` works for all modes, with no H²/quadratic-decay requirement.

## 1. Existing generic cosine-coefficient sup bound

`ShenWork/Paper2/IntervalMildPicardRegularity.lean:837` on `chatgpt-scratch`:

```lean
/-- Cosine coefficients of a bounded continuous function on `[0,1]` are uniformly bounded. -/
theorem cosineCoeffs_abs_le_of_continuous_bounded
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n, |cosineCoeffs f n| ≤ 2 * B
```

This theorem is already used for heat/Picard C² base data immediately below it (`picardIterateHasC2Slices_zero`) to uniformly bound cosine coefficients of bounded continuous initial data.

For `adot`, since

```lean
coupledChemDivAdot p u s n = cosineCoeffs (coupledChemDivTimeDerivativeLift p u s) n
```

by definition, the missing bridge should be very small:

```lean
theorem chemDivAdot_Mdot_of_timeDeriv_sup_on
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c T B : ℝ} (hB : 0 ≤ B)
    (hcont : ∀ s ∈ Icc c T,
      ContinuousOn (coupledChemDivTimeDerivativeLift p u s) (Icc (0:ℝ) 1))
    (hbd : ∀ s ∈ Icc c T, ∀ x ∈ Icc (0:ℝ) 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B) :
    ∃ Mdot : ℝ, ∀ s ∈ Icc c T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot := by
  refine ⟨2 * B, ?_⟩
  intro s hs n
  simpa [coupledChemDivAdot] using
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (hcont s hs) hB (hbd s hs) n
```

This is strictly easier than the H²/quadratic-decay route if all you need is a uniform-in-mode bound.

## 2. Full `coupledChemDivTimeDerivativeLift` bound: not found

The definition of the field to be bounded is in `ShenWork/PDE/IntervalChemDivTimeDerivative.lean:31`:

```lean
def coupledChemDivTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s x : ℝ) : ℝ :=
  deriv
    (fun y : ℝ =>
      let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
      let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
      ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
          (1 + v y) ^ p.β +
        intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
        p.β * intervalDomainLift (u s) y * deriv v y * vt y /
          (1 + v y) ^ (p.β + 1))
    x
```

Searches for these patterns found no producer:

```text
coupledChemDivTimeDerivativeLift bound sup L∞ Linfty
coupledChemDivTimeDerivativeLift B_sup hbd |coupledChemDivTimeDerivativeLift|
"|coupledChemDivTimeDerivativeLift"
"coupledChemDivTimeDerivativeLift p u s x" "≤"
"B_sup" "coupledChemDivTimeDerivativeLift"
```

The only theorem mentioning an explicit sup bound for this field is the default-branch `ChemDivAdotEnvelope.lean` theorem below, where the bound is a hypothesis.

## 3. `ChemDivAdotEnvelope.lean`: conditional hbd consumer, not a bound producer

On `chatgpt-scratch`, this path is missing:

```text
ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean  -- 404 on ref=chatgpt-scratch
```

On the indexed/default branch, it contains:

`ShenWork/Wiener/EWA/ChemDivAdotEnvelope.lean:163`:

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

This theorem confirms the intended interface: a uniform sup bound `hbd` on `coupledChemDivTimeDerivativeLift` is recognized as useful.  But the theorem does **not** prove `hbd`; it consumes it.  Also, it includes an extra H²/quadratic-decay input for positive modes, which is unnecessary for the simpler all-mode `2*B_sup` argument above.

## 4. Individual terms: no full numerical bound found

The expression for `coupledChemDivTimeDerivativeLift` needs bounds on the spatial derivative of a three-term flux-time expression involving:

- `intervalDomainLift (u s)`
- `slopeSlice u s` / `u_t`
- `v = coupledChemicalConcentration p u s`
- `deriv v`
- `vt = coupledChemicalTimeDerivativeLift p u s`
- `deriv vt`
- one more outer spatial derivative of the whole expression
- denominator floors `(1 + v)^β`, `(1 + v)^(β+1)`

I found continuity/joint-C²/repr infrastructure for these factors, but not a packaged numerical sup bound.

### Resolver time derivative

`ShenWork/PDE/IntervalChemDivTimeDerivative.lean` gives continuity/differentiability facts for `coupledChemicalTimeDerivativeLift`, not bounds:

```lean
theorem coupledChemicalTimeDerivative_jointContinuousOn_closed
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {U : ℝ}
    (H : ResolverHasSpectralAgreement U (coupledChemicalConcentration p u)) :
    ContinuousOn
      (Function.uncurry (coupledChemicalTimeDerivativeLift p u))
      (Ioo (0 : ℝ) U ×ˢ Icc (0 : ℝ) 1)
```

and

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

Searches for `|coupledChemicalTimeDerivativeLift|` and `coupledChemicalTimeDerivativeLift ≤ ...` found no norm estimate.

### Heat trajectory sup bound exists, but only for `u`, not for chemDiv time derivative

`ShenWork/Paper2/IntervalHsupNormHeat.lean:65` proves the pure heat trajectory remains bounded by the initial sup bound:

```lean
theorem heat_supNorm_le_initial
    {u₀ : intervalDomainPoint → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ y, |intervalDomainLift u₀ y| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    intervalDomainSupNorm (heatTrajectory u₀ t) ≤ B
```

This is useful for the `U` factor, but it does not bound `u_t`, `v_t`, `∂ₓv`, `∂ₓv_t`, or the outer spatial derivative defining `coupledChemDivTimeDerivativeLift`.

### Residual bundle still assumes the time-derivative coefficient bound

`ShenWork/Paper2/IntervalChemDivWinDischarge.lean:79` has the residual bundle:

```lean
structure ChemDivSolutionRegularityResidual
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) where
  ...
  hadotcont : ∀ n, Continuous (fun s => coupledChemDivAdot p u s n)
  MchemDot : ℝ
  hMdot : ∀ s, 0 ≤ s → ∀ n, |coupledChemDivAdot p u s n| ≤ MchemDot
```

This confirms the bound remains a residual assumption in that route.

## 5. Recommended next Lean target

Add the simple sup-bound-to-Mdot lemma first.  It should build on the existing `cosineCoeffs_abs_le_of_continuous_bounded` and avoid H²/quadratic decay entirely:

```lean
theorem chemDivAdot_Mdot_of_timeDeriv_sup_on
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c T B : ℝ} (hB : 0 ≤ B)
    (hcont : ∀ s ∈ Icc c T,
      ContinuousOn (coupledChemDivTimeDerivativeLift p u s) (Icc (0:ℝ) 1))
    (hbd : ∀ s ∈ Icc c T, ∀ x ∈ Icc (0:ℝ) 1,
      |coupledChemDivTimeDerivativeLift p u s x| ≤ B) :
    ∃ Mdot, ∀ s ∈ Icc c T, ∀ n,
      |coupledChemDivAdot p u s n| ≤ Mdot
```

Then the genuine heat-semigroup analytic target becomes sharply named:

```lean
level0_coupledChemDivTimeDerivativeLift_sup_bound
```

with conclusion roughly:

```lean
∃ B, 0 ≤ B ∧
  ∀ s ∈ Icc c T, ∀ x ∈ Icc (0:ℝ) 1,
    |coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s x| ≤ B
```

I did not find this theorem, or any equivalent bound on all the necessary component factors, in the current repo.