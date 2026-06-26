# Q745 / cron1: flux time fderiv bridge search

Repo inspected: `xiangyazi24/Shen_work`.
Scratch write target: branch `chatgpt-scratch`, file `scratch/_CHATGPT_DROP_cron1.md`.

## Verdict

Yes. The repo already has the relevant flux time-derivative definition, a committed time bridge theorem with exactly the target eventual-equality shape, and a generic Clairaut/commutation lemma that is instantiated for the flux in the outer-commute producer.

The most directly relevant theorem for sub-sorry 3F is:

```lean
theorem coupledChemDivFlux_timeBridge_of_physicalJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt)
    (hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : ∀ s : ℝ, ∀ x : ℝ,
      0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y : ℝ =>
        fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))
```

Location:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

This theorem has the exact conclusion needed by sub-sorry 3F, except it is pointwise in `{s x}` and takes `hx`; the slab-shaped field is obtained by:

```lean
fun x hx s _hs =>
  coupledChemDivFlux_timeBridge_of_physicalJointC2 H hu_c2 hbase hx
```

That exact pattern is already used in the same file inside:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

## 1. Definition of `coupledChemDivFluxTimeDerivativeLift`

Defined in:

```text
ShenWork/PDE/IntervalChemDivFluxChain.lean
```

Definition:

```lean
def coupledChemDivFluxTimeDerivativeLift (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (s y : ℝ) : ℝ :=
  let v : ℝ → ℝ := intervalDomainLift (coupledChemicalConcentration p u s)
  let vt : ℝ → ℝ := coupledChemicalTimeDerivativeLift p u s
  ShenWork.Paper2.PicardLimitK1.slopeSlice u s y * deriv v y /
      (1 + v y) ^ p.β +
    intervalDomainLift (u s) y * deriv vt y / (1 + v y) ^ p.β -
    p.β * intervalDomainLift (u s) y * deriv v y * vt y /
      (1 + v y) ^ (p.β + 1)
```

Same file also proves the pointwise chain-rule lemma:

```lean
theorem coupledChemDivFlux_hasDerivAt_time
    ... :
    HasDerivAt (fun r => coupledChemDivFluxLift p u r y)
      (coupledChemDivFluxTimeDerivativeLift p u s y) s
```

Hypotheses for `coupledChemDivFlux_hasDerivAt_time`:

```lean
hu : HasDerivAt (fun r => intervalDomainLift (u r) y)
  (ShenWork.Paper2.PicardLimitK1.slopeSlice u s y) s

hgv : HasDerivAt
  (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
  (deriv (coupledChemicalTimeDerivativeLift p u s) y) s

hv : HasDerivAt
  (fun r => intervalDomainLift (coupledChemicalConcentration p u r) y)
  (coupledChemicalTimeDerivativeLift p u s y) s

hbase : 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) y
```

So the explicit flux time derivative is already the algebraic derivative candidate, and the repo already has the product/quotient/rpow `HasDerivAt` proof that this candidate differentiates the fixed-space flux slice.

## 2. Existing Clairaut / commutation lemmas for the flux

### Generic time partial bridge

Located in:

```text
ShenWork/PDE/IntervalChemDivFluxTimeBridge.lean
```

```lean
theorem real_twoVar_time_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun r : ℝ => F (r, x)) s =
      fderiv ℝ F (s, x) (1, 0)
```

This is the direct `∂ₜ` slice = Fréchet directional derivative bridge.

### Generic spatial bridge

Located in:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

```lean
theorem real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun y : ℝ => F (s, y)) x =
      fderiv ℝ F (s, x) (0, 1)
```

### Generic Clairaut bridge

Located in:

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

```lean
theorem real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
    {F Ft : ℝ → ℝ → ℝ} {s x : ℝ}
    (hF : ContDiffAt ℝ 2 (Function.uncurry F) (s, x))
    (hspatial :
      (fun r : ℝ => deriv (F r) x) =ᶠ[𝓝 s]
        (fun r : ℝ => fderiv ℝ (Function.uncurry F) (r, x) (0, 1)))
    (htime :
      (fun y : ℝ => Ft s y) =ᶠ[𝓝 x]
        (fun y : ℝ => fderiv ℝ (Function.uncurry F) (s, y) (1, 0))) :
    HasDerivAt (fun r : ℝ => deriv (F r) x) (deriv (Ft s) x) s
```

This lemma uses `hF.isSymmSndFDerivAt` from `Mathlib.Analysis.Calculus.FDeriv.Symmetric` to identify the two second Fréchet derivatives.

### Flux instantiation of the Clairaut bridge

Also in:

```text
ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean
```

```lean
theorem coupledChemDivOuterCommuteAtoms_of_fluxJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (H : CoupledChemDivFluxJointC2Hyp p u) :
    CoupledChemDivOuterCommuteAtoms p u
```

Inside this theorem, the generic Clairaut bridge is instantiated as:

```lean
real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
  (F := coupledChemDivFluxLift p u)
  (Ft := coupledChemDivFluxTimeDerivativeLift p u)
  (hflux_c2 x hx s hs) (hspatial x hx s hs) (htime x hx s hs)
```

and it produces:

```lean
HasDerivAt
  (fun r => deriv (coupledChemDivFluxLift p u r) x)
  (deriv (coupledChemDivFluxTimeDerivativeLift p u s) x) s
```

So: there is no theorem named literally `Clairaut.*flux`, but the flux Clairaut/commutation route is committed under `coupledChemDivOuterCommuteAtoms_of_fluxJointC2`, using the generic `real_twoVar_clairaut_hasDerivAt_of_fderiv_partials`.

## 3. The FactorJointC2Inputs / resolver time-bridge pattern

The factor pipeline currently has two relevant layers.

### A. The older factor package still contains the bridge as a field

In:

```text
ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean
```

`CoupledChemDivFluxFactorJointC2Inputs.exists_local_slab` has this field:

```lean
∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
  (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
    (fun y : ℝ =>
      fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
        (s, y) (1, 0))
```

The producer `coupledChemDivFluxJointC2Hyp_of_factorJointC2Inputs` just names this field as `htime_deriv_fderiv_bridge := htime` and passes it into `CoupledChemDivFluxJointC2Hyp`.

Likewise, in:

```text
ShenWork/PDE/IntervalChemDivFluxFactorFAC.lean
```

`FACLocalSlabInputs` still has the same time-bridge field explicitly, and `coupledChemDivFluxFactorJointC2Inputs_of_FACInputs` passes it through as `htime_bridge`.

### B. The newer physical discharge removes this bridge hypothesis

In:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

The theorem:

```lean
theorem coupledChemDivFluxFactorJointC2Inputs_of_physical_commuteDischarged
```

has an `other` hypothesis that no longer includes the flux time bridge. Its `other` fields are only:

```lean
∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
  (∀ᶠ s in 𝓝 τ,
    ContinuousOn (coupledChemDivSourceLift p u s) (Icc (0 : ℝ) 1)) ∧
  (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)) ∧
  ContinuousOn
    (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
    (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Then it fills the missing time-bridge field by:

```lean
exact coupledChemDivFlux_timeBridge_of_physicalJointC2 H hu_c2 hbase hx
```

This is the pattern to reuse for sub-sorry 3F.

### C. How the resolver supplies the residual inner commute `hgv`

Also in:

```text
ShenWork/PDE/IntervalChemDivFACCommuteDischarge.lean
```

The theorem:

```lean
theorem coupledChemical_innerCommute_of_physicalJointC2
```

produces:

```lean
HasDerivAt
  (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
  (deriv (coupledChemicalTimeDerivativeLift p u s) y) s
```

from physical resolver joint C²:

```lean
H : PhysicalResolverJointC2Data p u Bt
```

It sets:

```lean
F : ℝ → ℝ → ℝ := fun r => intervalDomainLift (coupledChemicalConcentration p u r)
```

then uses:

```lean
coupledChemical_jointContDiffAt_two H hy
real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
real_twoVar_time_deriv_eq_fderiv_of_differentiableAt
real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
```

So the resolver time bridge pattern is:

1. Use `coupledChemical_jointContDiffAt_two H hy` for joint C² of `v`.
2. Use `coupledChemical_grad_jointContDiffAt_two H hy` for joint C² of `∂ₓ v` when proving flux C².
3. Convert time and spatial slice derivatives to Fréchet partials using the two `real_twoVar_*_eq_fderiv_of_differentiableAt` lemmas.
4. Apply `real_twoVar_clairaut_hasDerivAt_of_fderiv_partials` to produce the inner commute `hgv`.
5. Feed `hgv` plus `hu`, `hv`, `hgradv`, and positivity into `coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt`.
6. For the FAC slab, use `coupledChemDivFlux_timeBridge_of_physicalJointC2` directly.

## Practical closure route for sub-sorry 3F

If the local context contains:

```lean
H : PhysicalResolverJointC2Data p u Bt
hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
  ContDiffAt ℝ 2 (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x)
hbase : ∀ s : ℝ, ∀ x : ℝ,
  0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x
```

then the sub-sorry shape

```lean
∀ x ∈ Ioo 0 1, ∀ s ∈ Metric.ball τ δ,
  (fun y => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[nhds x]
  (fun y => fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0))
```

should close with:

```lean
intro x hx s hs
exact coupledChemDivFlux_timeBridge_of_physicalJointC2
  (p := p) (u := u) (H := H) hu_c2 hbase hx
```

The `hs` ball membership is unused by this theorem.

If the context does **not** have global `hu_c2`/`hbase` in exactly that shape, use the lower-level theorem:

```lean
coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
```

and supply eventual-near-`x` versions of:

```lean
hu      : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 lifted-u at (s,y)
hv      : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 lifted-v at (s,y)
hgradv  : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 lifted-∂ₓv at (s,y)
hbase   : ∀ᶠ y in 𝓝 x, 0 < 1 + v(s,y)
hgv     : ∀ᶠ y in 𝓝 x, HasDerivAt (fun r => ∂ₓv(r,y)) (∂ₓ∂ₜv(s,y)) s
```

The physical resolver theorem `coupledChemical_innerCommute_of_physicalJointC2` is the committed way to build `hgv`.
