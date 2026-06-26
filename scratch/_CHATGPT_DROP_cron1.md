# Q767 / cron1: verify `coupledChemical_grad_jointContDiffAt_two`

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

Yes. `sub-sorry 3D` has an existing producer:

```lean
coupledChemical_grad_jointContDiffAt_two
```

It is defined in:

```text
ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean
```

and it **does require**:

```lean
H : PhysicalResolverJointC2Data p u Bt
```

plus the interior spatial-point hypothesis:

```lean
hx : x ∈ Ioo (0 : ℝ) 1
```

It does **not** require `DuhamelSourceTimeC2Coeff`; it uses the bounded-weight physical resolver data.

## Exact theorem statement

```lean
/-- **Physical producer of `hgradv_c2`** — joint `ContDiffAt ℝ 2` of the spatial
 derivative `∂ₓ v` of the lifted coupled concentration, via the bounded-weight
 gradient assembler. -/
theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x) := by
  ...
```

## Hypotheses

The theorem has these explicit hypotheses/parameters:

```lean
{p : CM2Params}
{u : ℝ → intervalDomainPoint → ℝ}
{Bt : ℕ → ℕ → ℝ}
(H : PhysicalResolverJointC2Data p u Bt)
{s x : ℝ}
(hx : x ∈ Ioo (0 : ℝ) 1)
```

The output is:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
  (s, x)
```

This is exactly the factor-Joint-C² field for the resolver gradient:

```lean
hgradv_c2 :
  ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

Modulo the unused slab membership, it can be supplied as:

```lean
fun x hx s _hs => coupledChemical_grad_jointContDiffAt_two H hx
```

## What `PhysicalResolverJointC2Data` contains

In the same file, `PhysicalResolverJointC2Data` is the bounded-weight resolver regularity package:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  /-- Each coefficient is `C²` in time. -/
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  /-- Three-time-order coefficient bounds. -/
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  /-- The bounded-weight **value** joint majorant is summable. -/
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  /-- The bounded-weight **gradient** joint majorant is summable. -/
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

`coupledChemical_grad_jointContDiffAt_two` uses especially:

```lean
H.coeff_contDiff
H.coeff_bound
H.grad_summable
```

via:

```lean
boundedWeightJointGradSeries_contDiff_two H.coeff_contDiff
  (fun i k t hi => H.coeff_bound i k t hi) H.grad_summable
```

It also uses `H.value_summable 2 le_rfl` internally to justify the termwise spatial derivative equality by obtaining eigenvalue-weighted summability of the value coefficients.

## Where it is used

`coupledChemical_grad_jointContDiffAt_two` is used in:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

inside the time-bridge proof:

```lean
coupledChemDivFlux_timeBridge_of_physicalJointC2
```

where it supplies the eventual-near-`x` `hgradv` input:

```lean
filter_upwards [hopen] with y hy using coupledChemical_grad_jointContDiffAt_two H hy
```

This confirms the graph correction: `3D` is a direct child of `PhysicalResolverJointC2Data`, parallel to `3C`, not something that has to be manually derived by differentiating `3C`.

## Practical close for sub-sorry 3D

If the local context contains:

```lean
H : PhysicalResolverJointC2Data p u Bt
```

then a slab-shaped `3D` goal closes with:

```lean
intro x hx s hs
exact coupledChemical_grad_jointContDiffAt_two H hx
```

or point-free:

```lean
fun x hx s _hs => coupledChemical_grad_jointContDiffAt_two H hx
```

The `s ∈ Metric.ball τ δ` hypothesis is unused by this theorem.
