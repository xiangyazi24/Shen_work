# Q834 (cron2) — exact use of `hSup` and whether `cosineCoeffs_abs_le_of_continuous_bounded` needs continuity

Static repo inspection only; I did not run a local Lean build.

## Short answer

In `level0_chemDiv_envelope_summable`, the `hSup` result is used only for the **zeroth-mode coefficient bound** in the final envelope construction.

After

```lean
obtain ⟨Msup, hMsupnn, hcont_slices, hsup_slices⟩ := hSup
```

these fields are used here:

```lean
by_cases hn : n = 0
· -- mode 0
  subst hn
  ...
  exact le_trans
    (cosineCoeffs_abs_le_of_continuous_bounded
      (hcont_slices s hs) hMsupnn
      (hsup_slices s hs) 0)
    hCenv_ge_2Msup
· -- mode k ≥ 1
  ...
  intervalWeakH2Neumann_cosineCoeff_quadratic_decay_of_bound h2s hBs n hk
```

The positive-mode branch uses only the `hH2_data` / `h2s hBs` quadratic-decay route.  It does **not** use `hSup`.

So `hSup` contributes exactly:

```lean
hMsupnn     : 0 ≤ Msup
hcont_slices : ∀ s ∈ Icc c T,
  ContinuousOn (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s) (Icc 0 1)
hsup_slices : ∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1,
  |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup
```

and all three are passed to `cosineCoeffs_abs_le_of_continuous_bounded` for `n = 0`.

## Signature found

In `ShenWork/Paper2/IntervalMildPicardRegularity.lean`:

```lean
theorem cosineCoeffs_abs_le_of_continuous_bounded
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n, |cosineCoeffs f n| ≤ 2 * B
```

So the committed theorem **does** require `ContinuousOn`, by signature.

But in its proof, continuity is used only to prove interval integrability:

```lean
have hint : IntervalIntegrable (fun x : ℝ => (f x : ℂ)) volume (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable
  rwa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
```

After that, the proof uses the coefficient estimate by an integral norm and the pointwise bound.  Thus, mathematically and proof-theoretically, continuity is stronger than necessary.

## Existing weaker ingredients

The file already has a weaker-looking zeroth-mode lemma chain:

```lean
theorem cosineCoeffs_zero_abs_le_integral_abs
    (f : ℝ → ℝ) :
    |cosineCoeffs f 0| ≤ ∫ x in (0 : ℝ)..1, |f x|
```

and then:

```lean
theorem cosineCoeffs_zero_abs_le_of_bound
    {f : ℝ → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    |cosineCoeffs f 0| ≤ B
```

Again, `cosineCoeffs_zero_abs_le_of_bound` uses `ContinuousOn` only to obtain `IntervalIntegrable f volume 0 1`.

## Recommended weaker replacement

For the actual mode-0 use in `level0_chemDiv_envelope_summable`, you only need a zeroth-mode lemma, not the all-mode `≤ 2 * B` lemma.  A good replacement is:

```lean
theorem cosineCoeffs_zero_abs_le_of_intervalIntegrable_bound
    {f : ℝ → ℝ} {B : ℝ}
    (hf_int : IntervalIntegrable f volume (0 : ℝ) 1)
    (_hB : 0 ≤ B)
    (hbd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    |cosineCoeffs f 0| ≤ B := by
  calc
    |cosineCoeffs f 0|
        ≤ ∫ x in (0 : ℝ)..1, |f x| :=
          cosineCoeffs_zero_abs_le_integral_abs f
    _ ≤ ∫ _ in (0 : ℝ)..1, B := by
        apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
          (hf_int.norm) intervalIntegrable_const
        intro x hx
        exact hbd x (by
          simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
    _ = B := by simp
```

Then the mode-0 branch can become:

```lean
have hzero := cosineCoeffs_zero_abs_le_of_intervalIntegrable_bound
  (hf_int s hs) hMsupnn (hsup_slices s hs)
-- gives |cosineCoeffs source 0| ≤ Msup
exact le_trans hzero ?_
```

Since your envelope has `Cenv = 2 * max B Msup`, this is even stronger than the current `≤ 2 * Msup` route.

If you want to keep the same `2 * B` shape for all modes, the all-mode weaker version is also straightforward:

```lean
theorem cosineCoeffs_abs_le_of_intervalIntegrable_bounded
    {f : ℝ → ℝ} (hf_int : IntervalIntegrable (fun x : ℝ => (f x : ℂ)) volume (0 : ℝ) 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n, |cosineCoeffs f n| ≤ 2 * B := by
  -- same proof as `cosineCoeffs_abs_le_of_continuous_bounded`, replacing
  -- the `ContinuousOn.intervalIntegrable` block by `hf_int`.
```

## If the bound is only on `Ioo 0 1`

A pure `∀ x ∈ Ioo 0 1, |f x| ≤ B` bound is not directly accepted by the current proof because `intervalIntegral.integral_mono_on` asks for a pointwise bound on `Set.uIcc 0 1`.  But endpoints are measure zero, so there are two clean options:

1. Prove endpoint bounds separately and upgrade to an `Icc` bound.  In this file’s zero-extension situation, endpoint values are often `0`, so `0 ≤ B` suffices.

2. Prove an a.e. version using a.e. domination on the interval; then an `Ioo` bound is enough because `{0,1}` is null.  This is slightly more measure-theoretic but conceptually the weakest statement.

For your stated replacement — “L∞ bound on `Ioo 0 1` + integrability” — the Lean-friendly version is probably: integrability plus an a.e. bound on `(0,1)`/`[0,1]`.  If you also have endpoint-zero facts, converting to an `Icc` pointwise bound is simpler.

## What this means for `hSup`

If you keep the current lemma, `hSup` must provide `ContinuousOn` because the theorem demands it.

If you add the weaker interval-integrable/L∞ zeroth-mode lemma, then the `ContinuousOn` component of `hSup` is unnecessary for the final envelope construction.  You would only need:

```lean
∃ Msup, 0 ≤ Msup ∧
  (∀ s ∈ Icc c T, IntervalIntegrable
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s) volume 0 1) ∧
  (∀ s ∈ Icc c T, ∀ x ∈ Icc 0 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup)
```

or, with an a.e. version, integrability plus an a.e. bound.

However, note that the current construction of `hSup` obtains the bound from compactness of a jointly continuous source on `[c,T]×[0,1]`.  If you remove continuity from `hSup`, you still need some other way to produce the uniform `Msup` and integrability.  The positive-mode envelope does not need it; only the zeroth mode does.

## Verdict

`cosineCoeffs_abs_le_of_continuous_bounded` requires `ContinuousOn` syntactically, but not essentially.  Continuity is only a convenient way to get interval integrability.  For sub-sorry 2A / `hSup`, you can weaken the zeroth-mode path to `IntervalIntegrable + L∞ bound` and avoid proving per-slice `ContinuousOn` solely for `cosineCoeffs_abs_le_of_continuous_bounded`.
