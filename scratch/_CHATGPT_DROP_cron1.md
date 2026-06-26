# Q874 / cron1: rpow `HasDerivAt` chain rule for the heat-source derivative

Repo inspected: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Ref inspected: `main`

## Answer

Yes.  The repo uses the Mathlib method

```lean
HasDerivAt.rpow_const
```

for exactly this chain rule.  I did **not** find a repo-defined theorem named

```lean
rpow_const_hasDerivAt
Real.hasDerivAt_rpow_const
```

but the method `.rpow_const` is used directly in repo proofs.

The closest already-packaged theorem for your source shape is:

```lean
ShenWork.EWA.hasDerivAt_powerLiftSlice
```

File:

```text
ShenWork/Wiener/EWA/SourcePowerCoeffDeriv.lean
```

Line: `83` in the fetched file region.

Exact local theorem shape:

```lean
theorem hasDerivAt_powerLiftSlice {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {x : ℝ} {r : ℝ}
    (hslice : HasDerivAt (fun s => intervalDomainLift (v s) x) (vdotL r x) r)
    (hpos : 0 < intervalDomainLift (v r) x) :
    HasDerivAt (fun s => p.ν * (intervalDomainLift (v s) x) ^ p.γ)
      (p.ν * p.γ * (intervalDomainLift (v r) x) ^ (p.γ - 1) * vdotL r x) r := by
  -- d/dr (lift v r x)^γ = vdotL · γ · (lift v r x)^{γ−1}  (exponent EXPLICIT).
  have hpow : HasDerivAt (fun s => (intervalDomainLift (v s) x) ^ p.γ)
      (vdotL r x * p.γ * (intervalDomainLift (v r) x) ^ (p.γ - 1)) r :=
    hslice.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))
  have hmul := hpow.const_mul p.ν
  refine hmul.congr_deriv ?_
  ring
```

This is exactly your first time-derivative formula with

```lean
v     := conjugatePicardIter p u₀ 0
vdotL := fun s x => ∂ₜ S(s)u₀(x)
```

modulo supplying the heat semigroup pointwise derivative as `hslice` and positivity as `hpos`.

## Raw Mathlib pattern

The core line is:

```lean
hslice.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))
```

In scalar form, the repo also uses:

```lean
have hpow : HasDerivAt (fun r => (f r) ^ α)
    (f' * α * (f σ) ^ (α - 1)) σ :=
  hf_deriv.rpow_const (Or.inl hf_ne)
```

inside:

```lean
ShenWork.IntervalMildPicardRegularity.logisticSourceFun_hasDerivAt_time
```

File:

```text
ShenWork/Paper2/IntervalMildPicardRegularity.lean
```

Line: `607` in the fetched file region.

## How to use it for heat semigroup source

For your integrand

```lean
f s x := p.ν * (S(s)u₀ x) ^ p.γ
```

prove a pointwise slice derivative:

```lean
hslice : HasDerivAt
  (fun r => intervalDomainLift (conjugatePicardIter p u₀ 0 r) x)
  (heatTimeDeriv p u₀ s x) s
```

and positivity:

```lean
hpos : 0 < intervalDomainLift (conjugatePicardIter p u₀ 0 s) x
```

Then either call the packaged theorem:

```lean
ShenWork.EWA.hasDerivAt_powerLiftSlice
  (p := p)
  (v := conjugatePicardIter p u₀ 0)
  (vdotL := heatTimeDeriv p u₀)
  (x := x) (r := s)
  hslice hpos
```

or inline the same proof:

```lean
have hpow : HasDerivAt
    (fun r => (intervalDomainLift (conjugatePicardIter p u₀ 0 r) x) ^ p.γ)
    (heatTimeDeriv p u₀ s x * p.γ *
      (intervalDomainLift (conjugatePicardIter p u₀ 0 s) x) ^ (p.γ - 1)) s :=
  hslice.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))

have hsrc : HasDerivAt
    (fun r => p.ν * (intervalDomainLift (conjugatePicardIter p u₀ 0 r) x) ^ p.γ)
    (p.ν * (heatTimeDeriv p u₀ s x * p.γ *
      (intervalDomainLift (conjugatePicardIter p u₀ 0 s) x) ^ (p.γ - 1))) s :=
  hpow.const_mul p.ν
```

Then `ring` or `ring_nf` can rearrange the derivative into your preferred form:

```lean
p.ν * p.γ * (S(s)u₀ x) ^ (p.γ - 1) * ∂ₜS(s)u₀ x
```

## Important Lean detail

Use the positivity branch explicitly:

```lean
(Or.inl (ne_of_gt hpos))
```

and pass the exponent explicitly if elaboration struggles:

```lean
hslice.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))
```

This is exactly how `SourcePowerCoeffDeriv.lean` avoids implicit-exponent/unification pain.

## Bottom line

For item (2) in `cosineCoeffs_hasDerivAt_of_smooth_param`, the repo already has the right rpow chain-rule pattern:

```lean
hslice.rpow_const (p := p.γ) (Or.inl (ne_of_gt hpos))
```

and the already-packaged theorem:

```lean
ShenWork.EWA.hasDerivAt_powerLiftSlice
```

is the closest reusable statement for the chemotaxis power source `ν · u^γ`.