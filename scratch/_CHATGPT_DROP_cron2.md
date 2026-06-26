# Q866 (cron2) — Level0 `1A` / `2A-sup` from heat resolver joint C²?

Static repo inspection only; I did **not** run Lean.

## Short answer

Yes, dispatch an opus subagent, but do **not** give it the prompt exactly as written.

The proposed chain is the right lane for **`2A-sup`** / the current `2A-core` uniform source sup bound, and much of the product/quotient/rpow algebra is already committed. But the same chain, as stated, is **not enough for `1A`**.

Reason: current `1A` is not bounding the chemDiv source itself. It is bounding

```lean
|(hH2_per_slice s hs).secondDeriv x|
```

where `hH2_per_slice s hs : IntervalWeakH2Neumann (coupledChemDivSourceLift ... s)`.
That is the **second spatial derivative of the chemDiv source**. Since the chemDiv source is already `∂ₓ flux`, `1A` needs a uniform bound on roughly `∂ₓ²(∂ₓ flux) = ∂ₓ³ flux` (or an equivalent uniform H²/second-derivative representative). A joint `ContDiffAt ℝ 2` theorem for the uncurried flux only gives the source `∂ₓ flux` as joint `C¹`; it does not give continuity/boundedness of the source’s second derivative.

So the correct dispatch is:

1. **Wire `2A-sup` now** from the existing factor-joint-C² / heat-resolver route.
2. **For `1A`, either upgrade the target to a joint `C²` theorem for the chemDiv source representative, or prove a separate uniform H² second-derivative majorant.** Do not expect flux joint `C²` alone to close it.

## What already exists and should be reused

### 1. Heat joint C²

`ShenWork/Paper2/IntervalHeatSemigroupHighRegularity.lean` has:

```lean
theorem heatSemigroup_jointContDiffAt_two
    {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    {c : ℝ} (hc : 0 < c) {s₀ x₀ : ℝ} (hs₀ : c < s₀) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, (Real.exp (-q.1 * unitIntervalCosineEigenvalue k) *
        cosineCoeffs (intervalDomainLift u₀) k) * cosineMode k q.2) (s₀, x₀)
```

This is a **cosine-series representative** theorem, not directly a theorem about the zero-extended `intervalDomainLift (conjugatePicardIter ...)` at the boundary.

### 2. Heat resolver joint C², with upstream sorry

The same file has:

```lean
theorem heatSemigroup_level0_resolverJointC2Data
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  sorry
```

and then the wrapper:

```lean
theorem heatResolverJointContDiffAt_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (_hc : 0 < c) {s₀ x₀ : ℝ} (_hs₀ : c < s₀)
    (hx₀ : x₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 (fun q : ℝ × ℝ =>
      intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1) q.2) (s₀, x₀)
```

This wrapper is useful for interior points. For compact bounds on the closed slab `[c,T] × [0,1]`, the subagent should be careful: the lifted concentration/source has zero-extension boundary behavior, so the clean compactness object should be a **smooth cosine-series representative**, not necessarily `coupledChemDivSourceLift` itself on the closed slab.

### 3. Resolver value and resolver-gradient joint C² from `PhysicalResolverJointC2Data`

`ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean` has:

```lean
structure PhysicalResolverJointC2Data
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (Bt : ℕ → ℕ → ℝ) : Prop where
  coeff_contDiff : ∀ k, ContDiff ℝ (2 : ℕ∞) (resolverTimeCoeff p u k)
  coeff_bound : ∀ (i k : ℕ) (t : ℝ), i ≤ 2 →
    ‖iteratedFDeriv ℝ i (resolverTimeCoeff p u k) t‖ ≤ Bt i k
  value_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointMajorant Bt m)
  grad_summable : ∀ m : ℕ, (m : ℕ∞) ≤ (2 : ℕ∞) →
    Summable (boundedWeightJointGradMajorant Bt m)
```

with producers:

```lean
theorem coupledChemical_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2) (s, x)
```

and:

```lean
theorem coupledChemical_grad_jointContDiffAt_two
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {Bt : ℕ → ℕ → ℝ}
    (H : PhysicalResolverJointC2Data p u Bt) {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1)) q.2)
      (s, x)
```

These are exactly the resolver facts needed for the flux product/quotient/rpow step, at least on the interior.

### 4. The product/quotient/rpow flux lemma already exists

`ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean` already contains the algebraic step the proposed route describes:

```lean
theorem coupledChemDivFlux_contDiffAt_of_factorJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {s x : ℝ}
    (hu : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (u q.1) q.2) (s, x))
    (hv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift (coupledChemicalConcentration p u q.1) q.2)
      (s, x))
    (hgradv : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p u q.1))
          q.2)
      (s, x))
    (hbase : 0 <
      1 + intervalDomainLift (coupledChemicalConcentration p u s) x) :
    ContDiffAt ℝ 2
      (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

It also has the bridge:

```lean
theorem real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt
    {F : ℝ × ℝ → ℝ} {s x : ℝ}
    (hF : DifferentiableAt ℝ F (s, x)) :
    deriv (fun y : ℝ => F (s, y)) x =
      fderiv ℝ F (s, x) (0, 1)
```

So the opus subagent should **not** re-prove this algebra. It should reuse it.

## How I would scope the opus subagent

### Deliverable A: close `2A-sup` / current `2A-core`

Ask it to replace the current uniform sup sorry in `hSup` with a helper along this shape:

```lean
-- Suggested helper shape, not guaranteed exact syntax.
theorem level0_chemDivSourceLift_uniform_sup_of_smooth_flux_rep
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ Msup : ℝ, 0 ≤ Msup ∧
      ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
        |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup := by
  -- Build/use smooth cosine representatives U, V, Vx.
  -- Prove the representative source G(s,x) = ∂ₓ flux_s(x) is ContinuousOn on
  -- `Icc c T ×ˢ Icc 0 1`.
  -- Compactness gives C for |G|.
  -- On `x ∈ Ioo 0 1`, show source lift = G.
  -- At `x = 0` or `x = 1`, reuse/prove boundary zero, so the same bound holds.
  sorry
```

Important details for this deliverable:

* Do **not** try to prove `ContinuousOn (coupledChemDivSourceLift ...) (Icc 0 1)`. The current Level0 comments correctly say this is false/problematic because of zero-extension boundary behavior.
* Use a smooth representative on the closed slab for compactness.
* Use the boundary-zero helper already being developed in the `hSup` block for endpoint values.
* Use the existing `coupledChemDivFlux_contDiffAt_of_factorJointC2` for the product/rpow/division step.
* If the current `heatResolverJointContDiffAt_two` interior wrapper is too weak at endpoints for compactness, extract the raw series regularity from `PhysicalResolverJointC2Data` instead of going through the lifted `coupledChemical...` theorem. The proof of `coupledChemical_jointContDiffAt_two` already internally constructs the global bounded-weight series and only uses the `Ioo` hypothesis for congruence to `intervalDomainLift`.

A minimal local source-continuity skeleton after obtaining flux `C²` is:

```lean
-- F : ℝ × ℝ → ℝ is the smooth flux representative.
-- G q := fderiv ℝ F q (0, 1), the spatial derivative/source representative.
have hF_c2 : ContDiffAt ℝ 2 F (s, x) := ...
have hG_c1 : ContDiffAt ℝ 1 (fun q => fderiv ℝ F q (0, 1)) (s, x) := by
  -- use hF_c2.fderiv_right, then apply the continuous linear evaluation at `(0,1)`
  sorry
have hG_cont : ContinuousAt (fun q => fderiv ℝ F q (0, 1)) (s, x) :=
  hG_c1.continuousAt
```

Then assemble `ContinuousOn G (Icc c T ×ˢ Icc 0 1)` pointwise and apply compactness.

### Deliverable B: do **not** claim `1A` is solved by the same flux C² lemma

For `1A`, ask the subagent to either:

#### Option B1: prove a stronger representative theorem

Target a clean theorem saying the **second derivative of the chemDiv source representative** is continuous on the compact slab:

```lean
-- Suggested abstraction for the compactness part.
theorem uniform_bound_of_secondDeriv_rep_continuous
    {c T : ℝ}
    (hcT : c ≤ T)
    {G : ℝ × ℝ → ℝ}
    (hGcont : ContinuousOn G (Icc c T ×ˢ Icc (0 : ℝ) 1))
    (hagrees : ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
      (hH2_per_slice s hs).secondDeriv x = G (s, x)) :
    ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
      |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  -- compactness of `Icc c T ×ˢ Icc 0 1`
  sorry
```

The analytic hard part is then just the production of `G` and `hGcont`.

But this requires stronger regularity than flux joint `C²`: it needs joint continuity of the source’s second spatial derivative. In terms of flux, that is a third spatial derivative of the flux. In terms of factor data, it likely requires more than the current `PhysicalResolverJointC2Data` value/gradient C² package.

#### Option B2: bypass joint continuity and prove a uniform H² majorant directly

Instead of compactness of the pointwise second derivative, prove the desired L¹ bound by coefficient/IBP majorants directly:

```lean
∃ B, 0 ≤ B ∧ ∀ s ∈ Icc c T,
  (∫ x in (0 : ℝ)..1, |(hH2_per_slice s hs).secondDeriv x|) ≤ B
```

This may be closer to the existing `IntervalWeakH2Neumann` / cosine-decay infrastructure, but it is a different task from wiring flux joint `C²`.

## Recommended opus prompt

I would send something like:

> In `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, use the existing heat/resolver joint C² pipeline to close the `hSup` uniform bound (`SUB-SORRY 2A-sup` / current `2A-core`) for Level0. Reuse `coupledChemDivFlux_contDiffAt_of_factorJointC2`, `real_twoVar_spatial_deriv_eq_fderiv_of_differentiableAt`, `heatSemigroup_jointContDiffAt_two`, `heatResolverJointContDiffAt_two`, and `coupledChemical_grad_jointContDiffAt_two`; do not re-prove product/rpow/division calculus. Prove compact boundedness for a smooth cosine-series source representative, then transfer to `coupledChemDivSourceLift` on `Ioo 0 1` and use boundary-zero at `0,1`. Do not try to prove `ContinuousOn (coupledChemDivSourceLift ...) (Icc 0 1)`. For `SUB-SORRY 1A`, only add a compactness skeleton if needed; flag that flux joint `C²` alone is insufficient for the second-derivative bound, which needs joint continuity of the chemDiv source’s second derivative or a separate uniform H² majorant.

## Bottom line

Dispatch the subagent, but phrase the task as **“close `2A-sup` and isolate the remaining `1A` derivative-order gap”**, not as **“the same flux `ContDiffAt ℝ 2` chain closes both `1A` and `2A-sup`.”**

That avoids wasting time on an impossible derivative-order mismatch while still getting a real Level0 sorry reduction from the existing `heatResolverJointContDiffAt_two` / `PhysicalResolverJointC2Data` route.
