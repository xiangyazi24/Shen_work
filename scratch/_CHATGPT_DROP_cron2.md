# Q1336 (cron2/cron3) — gradient version of `heatResolver_jointContDiffAt_two`

Static GitHub-connector inspection only. I did **not** run Lean locally.

## Short answer

Route **A** is the right route.  Route **B** is too weak for the theorem as stated.

The theorem goal is:

```lean
ContDiffAt ℝ 2
  (fun q : ℝ × ℝ =>
    deriv (intervalDomainLift (coupledChemicalConcentration p
      (conjugatePicardIter p u₀ 0) q.1)) q.2)
  (s₀, x₀)
```

If you start from the value theorem

```lean
heatResolver_jointContDiffAt_two :
  ContDiffAt ℝ 2 (fun q => intervalDomainLift (v q.1) q.2) (s₀, x₀)
```

then applying `ContDiffAt.fderiv` loses one derivative.  At best it gives `ContDiffAt ℝ 1` of the full Fréchet derivative, hence `ContDiffAt ℝ 1` of the spatial component of the derivative.  It does **not** give `ContDiffAt ℝ 2` of the spatial derivative.

So Route B can prove a downgraded theorem:

```lean
ContDiffAt ℝ 1
  (fun q => deriv (intervalDomainLift (v q.1)) q.2)
  (s₀, x₀)
```

but not the current `ContDiffAt ℝ 2` goal.  To prove the current goal without losing an order, you need a direct gradient series proof: cutoff + `contDiff_tsum` for the gradient terms.

## Existing infrastructure found

### 1. Current direct cutoff value route

In `ShenWork/Paper2/IntervalHeatResolverJointC2.lean`, the value route already has:

```lean
def resolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p u k q.1 * cosineMode k q.2


def cutoffResolverTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * cosineMode k q.2)
```

and:

```lean
theorem cutoffResolverSeries_contDiff_two :
  ContDiff ℝ 2 (fun q : ℝ × ℝ =>
    ∑' k : ℕ, cutoffResolverTerm p (conjugatePicardIter p u₀ 0) c k q)
```

Then `heatResolver_jointContDiffAt_two` transfers this cutoff series to the actual lifted resolver value by eventual equality.

### 2. Current gradient theorem is only a placeholder

The gradient theorem currently says:

```lean
theorem heatResolver_grad_jointContDiffAt_two ... :
  ContDiffAt ℝ 2
    (fun q : ℝ × ℝ =>
      deriv (intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1)) q.2)
    (s₀, x₀) := by
  -- comments...
  sorry
```

The comments already point to the true remaining work:

```lean
-- The full proof needs the interchange of tsum and deriv (from summability
-- of the gradient series) and the cutoff+contDiff_tsum on the gradient series.
```

That is Route A.

### 3. Generic gradient assembler already exists

The repo already has generic gradient-series infrastructure in

```lean
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

The key definitions/theorems are:

```lean
def boundedWeightJointGradTerm (c : ℕ → ℝ → ℝ) (n : ℕ) : ℝ × ℝ → ℝ :=
  fun q => c n q.1 * deriv (cosineMode n) q.2


def boundedWeightJointGradMajorant (Bt : ℕ → ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Bt i n * gradCosWeight (k - i) n


theorem boundedWeightJointGradTerm_contDiff
    {c : ℕ → ℝ → ℝ} (n : ℕ) (hc : ContDiff ℝ (2 : ℕ∞) (c n)) :
    ContDiff ℝ (2 : ℕ∞) (boundedWeightJointGradTerm c n)


theorem boundedWeightJointGradSeries_contDiff_two
    {c : ℕ → ℝ → ℝ} {Bt : ℕ → ℕ → ℝ}
    (hc : ∀ n, ContDiff ℝ (2 : ℕ∞) (c n))
    (hBt : ∀ (i n : ℕ) (t : ℝ), i ≤ 2 → ‖iteratedFDeriv ℝ i (c n) t‖ ≤ Bt i n)
    (hsumm : ∀ k : ℕ, (k : ℕ∞) ≤ (2 : ℕ∞) →
      Summable (boundedWeightJointGradMajorant Bt k)) :
    ContDiff ℝ (2 : ℕ∞)
      (fun q : ℝ × ℝ => ∑' n : ℕ, boundedWeightJointGradTerm c n q)
```

This is exactly the gradient analogue of the value assembler.

### 4. The physical route already proves the eventual-equality pattern for gradients

In `ShenWork/PDE/IntervalResolverJointC2PhysicalConcrete.lean`, the theorem

```lean
coupledChemical_grad_jointContDiffAt_two
```

uses:

```lean
boundedWeightJointGradSeries_contDiff_two
```

then proves that the actual spatial derivative equals the gradient series near interior points.  Its key local bridge is:

```lean
have hval : (fun y : ℝ =>
      intervalDomainLift (coupledChemicalConcentration p u q.1) y) =ᶠ[𝓝 q.2]
    fun y : ℝ =>
      ∑' k : ℕ, boundedWeightJointTerm (resolverTimeCoeff p u) k (q.1, y) := by
  filter_upwards [hopen] with y hy
  exact coupledChemical_lift_eq_series (Ioo_subset_Icc_self hy)

rw [Filter.EventuallyEq.deriv_eq hval]

have hgrad := cosineCoeffSeries_grad_hasDerivAt heig q.2
...
rw [hrw, hgrad.deriv]
exact tsum_congr (fun k => by simp [boundedWeightJointGradTerm, hb, cosineMode_deriv])
```

This is the proof pattern to copy for the direct cutoff theorem.

## Recommended direct cutoff implementation

Add a gradient cutoff term, its majorant, and a gradient cutoff series theorem.

### 1. Define the raw/cutoff gradient terms

Use the existing direct file’s `resolverTerm` shape, but replace `cosineMode` by `deriv cosineMode`:

```lean
/-- The `k`-th spatial-gradient resolver term:
`(t,x) ↦ resolverTimeCoeff_k(t) · ∂ₓ cos(kπx)`. -/
def resolverGradTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => resolverTimeCoeff p u k q.1 * deriv (cosineMode k) q.2

/-- The cutoff spatial-gradient resolver term. -/
def cutoffResolverGradTerm (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (c : ℝ) (k : ℕ) : ℝ × ℝ → ℝ :=
  fun q => smoothRightCutoff (c / 2) c q.1 *
    (resolverTimeCoeff p u k q.1 * deriv (cosineMode k) q.2)
```

### 2. Prove each cutoff gradient term is C²

This is mechanically parallel to `cutoffResolverTerm_contDiff_two`.  You can avoid re-proving coefficient regularity by reusing:

```lean
cutoffResolverCoeff_contDiff_two
```

from the current file, because

```lean
fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff ... k t
```

is already globally `ContDiff ℝ 2`.  Then multiply by `deriv (cosineMode k)` composed with `snd`.

Skeleton:

```lean
private theorem cosineModeDeriv_contDiff_two (k : ℕ) :
    ContDiff ℝ (2 : ℕ∞) (fun x : ℝ => deriv (cosineMode k) x) := by
  have hEq : (fun x : ℝ => deriv (cosineMode k) x) =
      fun x : ℝ => -((k : ℝ) * Real.pi) * Real.sin ((k : ℝ) * Real.pi * x) := by
    funext x
    rw [cosineMode_deriv]
  rw [hEq]
  fun_prop

 theorem cutoffResolverGradTerm_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ContDiff ℝ 2
      (cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k) := by
  have hcoef := cutoffResolverCoeff_contDiff_two
    (p := p) (u₀ := u₀) (M₀ := M₀) hu₀_bound hu₀_cont hc k
  have hcoef_q : ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      smoothRightCutoff (c / 2) c q.1 *
        resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1) :=
    hcoef.comp contDiff_fst
  have hgradcos_q : ContDiff ℝ 2 (fun q : ℝ × ℝ => deriv (cosineMode k) q.2) :=
    (cosineModeDeriv_contDiff_two k).comp contDiff_snd
  show ContDiff ℝ 2 (fun q =>
    smoothRightCutoff (c / 2) c q.1 *
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k q.1 *
        deriv (cosineMode k) q.2))
  conv => ext q; ring
  exact hcoef_q.mul hgradcos_q
```

### 3. Add gradient majorants

You need gradient weights, not merely the value weights.  Either add separate gradient majorants or replace the existing value majorant by something large enough to dominate both value and gradient terms.

Cleanest:

```lean
noncomputable def cutoffResolverGradMajorant
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ) (M₀ c : ℝ) (hc : 0 < c)
    (j k : ℕ) : ℝ :=
  -- analytic majorant using gradCosWeight instead of valueCosWeight
  Classical.choice inferInstance

 theorem cutoffResolverGradMajorant_nonneg ... : 0 ≤ cutoffResolverGradMajorant ... := by
  sorry

 theorem cutoffResolverGradMajorant_summable ... :
    Summable (cutoffResolverGradMajorant p u₀ M₀ c hc j) := by
  sorry

 theorem cutoffResolverGradTerm_iteratedFDeriv_bound ... :
    ‖iteratedFDeriv ℝ j
      (cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k) q‖ ≤
      cutoffResolverGradMajorant p u₀ M₀ c hc j k := by
  sorry
```

These are the same analytic obligations as the value majorant, except with `gradCosWeight` / derivatives of `deriv cosineMode`.

### 4. Prove global C² of the cutoff gradient series

```lean
theorem cutoffResolverGradSeries_contDiff_two
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k ≤ M₀) -- typo fixed below
    (hu₀_cont : Continuous u₀)
    {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 2 (fun q : ℝ × ℝ =>
      ∑' k : ℕ, cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) := by
  apply contDiff_tsum
    (𝕜 := ℝ)
    (f := cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c)
    (v := fun j k => cutoffResolverGradMajorant p u₀ M₀ c hc j k)
  · intro k
    exact cutoffResolverGradTerm_contDiff_two hu₀_bound hu₀_cont hc k
  · intro j hj
    exact cutoffResolverGradMajorant_summable hc hu₀_bound hu₀_cont hj
  · intro j k q hj
    exact cutoffResolverGradTerm_iteratedFDeriv_bound hu₀_bound hu₀_cont hc j k q hj
```

Correct the typo in the first hypothesis:

```lean
(hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
```

### 5. Eventual equality to the actual gradient

Use the physical-route pattern.  At an interior point, first show locally in `x` that the lift equals the value series, then take `deriv` of that eventual equality, then rewrite derivative of the series as the gradient series using `cosineCoeffSeries_grad_hasDerivAt`.

For the raw gradient series:

```lean
theorem resolverGradSeries_eq_lift_deriv_on_interior
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {t x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (heig : Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k * |resolverTimeCoeff p u k t|)) :
    deriv (intervalDomainLift (coupledChemicalConcentration p u t)) x =
      ∑' k : ℕ, resolverGradTerm p u k (t, x) := by
  have hopen : Ioo (0 : ℝ) 1 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  have hval : (fun y : ℝ => intervalDomainLift (coupledChemicalConcentration p u t) y)
      =ᶠ[𝓝 x]
      fun y : ℝ => ∑' k : ℕ, resolverTerm p u k (t, y) := by
    filter_upwards [hopen] with y hy
    exact resolverSeries_eq_lift_on_interior (Set.Ioo_subset_Icc_self hy)
  rw [Filter.EventuallyEq.deriv_eq hval]
  set b : ℕ → ℝ := fun k => resolverTimeCoeff p u k t with hb
  have hgrad := cosineCoeffSeries_grad_hasDerivAt heig x
  have hrw : (fun y : ℝ => ∑' k : ℕ, resolverTerm p u k (t, y)) =
      fun y : ℝ => ∑' k : ℕ, b k * cosineMode k y := by
    funext y
    exact tsum_congr (fun k => by simp [resolverTerm, hb])
  rw [hrw, hgrad.deriv]
  exact tsum_congr (fun k => by simp [resolverGradTerm, hb, cosineMode_deriv])
```

You still need the `heig` summability.  In the physical route this is derived from `H.value_summable 2 le_rfl`.  In the direct route, make it one of the analytic consequences of the same coefficient estimates used by the cutoff majorant, e.g.:

```lean
theorem resolverCoeff_eigen_summable_at_positive_time
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ : ℝ}
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀)
    {t : ℝ} (ht : 0 < t) :
    Summable (fun k : ℕ =>
      unitIntervalCosineEigenvalue k *
        |resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k t|) := by
  -- same elliptic-weight + source coefficient H4/IBP route as the value/grad majorants
  sorry
```

Then the final theorem is:

```lean
theorem heatResolver_grad_jointContDiffAt_two ... :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift (coupledChemicalConcentration p
          (conjugatePicardIter p u₀ 0) q.1)) q.2)
      (s₀, x₀) := by
  -- 1. cutoff gradient series globally C²
  have hCutoff :=
    (cutoffResolverGradSeries_contDiff_two (p := p)
      hu₀_bound hu₀_cont hc).contDiffAt (x := (s₀, x₀))

  -- 2. actual gradient = raw gradient series near interior points
  have hmem : {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) 1 ∧ c < q.1} ∈ 𝓝 (s₀, x₀) := by
    -- product neighborhood from `hx₀` and `hs₀`
    -- use `(isOpen_Ioo.preimage continuous_snd)` and `Ioi_mem_nhds hs₀`
    sorry

  have hEqGradRaw :
      (fun q : ℝ × ℝ => deriv (intervalDomainLift (coupledChemicalConcentration p
        (conjugatePicardIter p u₀ 0) q.1)) q.2)
      =ᶠ[𝓝 (s₀, x₀)]
      (fun q : ℝ × ℝ =>
        ∑' k : ℕ, resolverGradTerm p (conjugatePicardIter p u₀ 0) k q) := by
    filter_upwards [hmem] with q hq
    exact resolverGradSeries_eq_lift_deriv_on_interior hq.1
      (resolverCoeff_eigen_summable_at_positive_time
        hu₀_bound hu₀_cont (lt_trans hs₀ hq.2))

  -- 3. raw gradient series = cutoff gradient series near `s₀` because cutoff = 1
  have hEqCutoffGrad :
      (fun q : ℝ × ℝ =>
        ∑' k : ℕ, resolverGradTerm p (conjugatePicardIter p u₀ 0) k q)
      =ᶠ[𝓝 (s₀, x₀)]
      (fun q : ℝ × ℝ =>
        ∑' k : ℕ, cutoffResolverGradTerm p (conjugatePicardIter p u₀ 0) c k q) := by
    have hc'c : c / 2 < c := by linarith
    have hφ_one : smoothRightCutoff (c / 2) c =ᶠ[𝓝 s₀] fun _ => (1 : ℝ) :=
      smoothRightCutoff_eventually_eq_one hc'c hs₀
    have hφ_prod :
        (fun q : ℝ × ℝ => smoothRightCutoff (c / 2) c q.1) =ᶠ[𝓝 (s₀, x₀)]
          fun _ : ℝ × ℝ => (1 : ℝ) :=
      hφ_one.comp_tendsto continuous_fst.continuousAt
    filter_upwards [hφ_prod] with q hq
    congr 1
    ext k
    simp [cutoffResolverGradTerm, resolverGradTerm, hq]

  exact hCutoff.congr_of_eventuallyEq (hEqGradRaw.trans hEqCutoffGrad)
```

## Why Route B is tempting but wrong for the current theorem

The value function is

```lean
F q = intervalDomainLift (v q.1) q.2
```

If

```lean
hF : ContDiffAt ℝ 2 F q₀
```

then

```lean
hF.fderiv : ContDiffAt ℝ 1 (fderiv ℝ F) q₀
```

up to the exact Mathlib spelling.  The spatial derivative is the second component of `fderiv ℝ F q`, so after composing with a continuous linear projection you get only:

```lean
ContDiffAt ℝ 1 (fun q => fderiv ℝ F q (0,1)) q₀
```

and after proving

```lean
fderiv ℝ F q (0,1) = deriv (fun x => intervalDomainLift (v q.1) x) q.2
```

locally, you still have only `ContDiffAt ℝ 1` for the gradient.

To get `ContDiffAt ℝ 2` of the gradient from a value theorem, you would need a value theorem at order `3`:

```lean
ContDiffAt ℝ 3 F q₀
```

not the current order `2` theorem.

## Final recommendation

Use Route A.

Reuse the existing generic gradient infrastructure:

```lean
boundedWeightJointGradTerm
boundedWeightJointGradMajorant
boundedWeightJointGradSeries_contDiff_two
```

and the existing physical-route bridge pattern in

```lean
coupledChemical_grad_jointContDiffAt_two
```

Do **not** try to obtain the current `ContDiffAt ℝ 2` gradient theorem from the value `ContDiffAt ℝ 2` theorem.  That loses one derivative and can only prove a `ContDiffAt ℝ 1` gradient theorem unless you first upgrade the value theorem to `ContDiffAt ℝ 3`.
