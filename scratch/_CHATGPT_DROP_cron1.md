# Q835 / cron1: boundary-bypass plan for chem-div `hSup`

Repo inspected: `xiangyazi24/Shen_work`

Source ref inspected: `main`

Branch written: `chatgpt-scratch`

## Verdict

Yes — this is the right approach.

The important correction is: do **not** ask for `ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)` just to bound the zeroth coefficient.  That is exactly the false/brittle endpoint requirement.  Instead, ask for a smooth representative `smoothRep s : ℝ → ℝ` which:

1. agrees with the actual source on `Ioo 0 1`,
2. is `ContinuousOn` on `Icc 0 1`, and
3. is uniformly bounded on `Icc 0 1`.

Then transfer the coefficient by `cosineCoeffs_congr_on_Ioo` and apply the existing bounded-continuous coefficient estimate to `smoothRep s`.

## Why this matches the current repo

The current zero-mode discharge is the theorem

```lean
theorem coupledChemDivSource_zeroCoeff_of_uniformSup
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (B Msup : ℝ) (hMsup : 0 ≤ Msup)
    (hcont : ∀ s, 0 ≤ s →
      ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1))
    (hsup : ∀ s, 0 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p u s x| ≤ Msup) :
    ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ 2 * max B Msup
```

in

```text
ShenWork/PDE/IntervalChemDivFluxFACSourceDecay.lean
```

It calls

```lean
cosineCoeffs_abs_le_of_continuous_bounded
```

on the **actual** `coupledChemDivSourceLift`.  That is the part to replace.

The bound lemma itself is fine.  It only needs `ContinuousOn f (Icc 0 1)` and a pointwise `Icc` bound for whatever `f` you feed it:

```lean
theorem cosineCoeffs_abs_le_of_continuous_bounded
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    {B : ℝ} (hB : 0 ≤ B)
    (hfb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ B) :
    ∀ n, |cosineCoeffs f n| ≤ 2 * B
```

So feed it `smoothRep s`, not `coupledChemDivSourceLift p u s`.

## Suggested replacement theorem shape

Something like this is the right local helper:

```lean
theorem coupledChemDivSource_zeroCoeff_of_uniformSmoothRepSup
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (B Msup : ℝ) (hMsup : 0 ≤ Msup)
    (smoothRep : ℝ → ℝ → ℝ)
    (hrep_cont : ∀ s, 0 ≤ s →
      ContinuousOn (smoothRep s) (Icc (0 : ℝ) 1))
    (hrep_sup : ∀ s, 0 ≤ s → ∀ x ∈ Icc (0 : ℝ) 1,
      |smoothRep s x| ≤ Msup)
    (hrep_agree : ∀ s, 0 ≤ s → ∀ x ∈ Ioo (0 : ℝ) 1,
      coupledChemDivSourceLift p u s x = smoothRep s x) :
    ∀ s, 0 ≤ s →
      |cosineCoeffs (coupledChemDivSourceLift p u s) 0| ≤ 2 * max B Msup := by
  intro s hs
  have hcoeff :
      cosineCoeffs (coupledChemDivSourceLift p u s) 0 =
        cosineCoeffs (smoothRep s) 0 :=
    ShenWork.EWA.cosineCoeffs_congr_on_Ioo
      (fun x hx => hrep_agree s hs x hx) 0
  rw [hcoeff]
  have hzero : |cosineCoeffs (smoothRep s) 0| ≤ 2 * Msup :=
    ShenWork.IntervalMildPicardRegularity.cosineCoeffs_abs_le_of_continuous_bounded
      (hrep_cont s hs) hMsup (hrep_sup s hs) 0
  refine le_trans hzero ?_
  have hmax : Msup ≤ max B Msup := le_max_right B Msup
  nlinarith
```

If the target constant can be sharpened, replace the last use of
`cosineCoeffs_abs_le_of_continuous_bounded` with `cosineCoeffs_zero_abs_le_of_bound`; that gives `≤ Msup` for mode `0`.  But the existing consumer target is already `≤ 2 * max B Msup`, so the all-modes bounded-continuous lemma is enough and matches the current code style.

## How to get `hrep_agree`

`coupledChemDivSourceLift_eq_deriv_fluxLift_interior` already gives the first half:

```lean
coupledChemDivSourceLift p u s x = deriv (coupledChemDivFluxLift p u s) x
```

for `x ∈ Ioo 0 1`.

So if your `smoothRep s` is the smooth representative for

```lean
deriv (coupledChemDivFluxLift p u s)
```

then `hrep_agree` should be only the interior derivative-identification lemma.  Crucially, you no longer need to extend this agreement to endpoints for coefficient purposes.

## Positive modes

For `k ≥ 1`, keep using the existing H²/quadratic-decay route.  The current theorem

```lean
coupledChemDivSource_quadraticDecay_of_uniformH2
```

already outputs

```lean
|cosineCoeffs (coupledChemDivSourceLift p u s) k| ≤
  2 * max B Msup / ((k : ℝ) * Real.pi) ^ 2
```

from `IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)` plus the second-derivative `L¹` bound.  If in a refactor the H² certificate is instead built for `smoothRep s`, then use the same `cosineCoeffs_congr_on_Ioo` transfer for positive modes too.  But with the theorem as currently written, only the zero-mode/sup-bound leg needs the smooth-representative replacement.

## Dependency caveat

`cosineCoeffs_congr_on_Ioo` currently lives in

```text
ShenWork/Wiener/EWA/NonCircularCoeffBridge.lean
```

under namespace `ShenWork.EWA`.  That file is EWA-facing and imports a lot.  If importing it from the PDE/Paper2 source-decay layer creates dependency-direction trouble, do **not** force that import.  Move or duplicate just the small lemma into a lower-level coefficient utility file near

```lean
cosineCoeffs_eq_factor_mul_integral
```

in `IntervalMildPicardRegularity.lean`, or create a tiny low-level file such as `IntervalCosineCoeffCongr.lean`.  The proof is only the already-proved endpoint-null `intervalIntegral.integral_congr_ae` argument.

## Bottom line

Change `hSup`/zero-mode input from:

```lean
ContinuousOn (coupledChemDivSourceLift p u s) (Icc 0 1)
∧ ∀ x ∈ Icc 0 1, |coupledChemDivSourceLift p u s x| ≤ Msup
```

to:

```lean
ContinuousOn (smoothRep s) (Icc 0 1)
∧ ∀ x ∈ Icc 0 1, |smoothRep s x| ≤ Msup
∧ EqOn (coupledChemDivSourceLift p u s) (smoothRep s) (Ioo 0 1)
```

Then the actual source coefficient bound follows by congruence, and the endpoint obstruction disappears rather than being pushed elsewhere.
