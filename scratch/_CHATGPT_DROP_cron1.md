# Q1552 (cron1) -- half-line source coefficient boundedness for iSup majorant

Repository: `xiangyazi24/Shen_work`  
Branch: `chatgpt-scratch`  
Target file: `scratch/_CHATGPT_DROP_cron1.md`

## Short answer

I did **not** find an existing theorem that directly states:

```lean
BddAbove ((fun t : ℝ => |cosineCoeffs (srcSlice p (conjugatePicardIter p u₀ 0) t) k|) '' Set.Ici c)
```

or a direct half-line bound for

```lean
|cosineCoeffs (fun x => p.ν * (S(t)u₀(x)) ^ p.γ) k|
```

on `[c, ∞)`.

What exists is close but not exactly this:

1. **Closed-window compactness templates**: prove a coefficient bound on `Set.Icc a b` from joint continuity on `Set.Icc a b ×ˢ Set.Icc 0 1`.
2. **Cosine coefficient absolute-value bound**: `cosineCoeffs_abs_le_of_continuous_bounded` is used as the final step once a spatial slice is continuous and uniformly bounded.
3. **Heat semigroup L∞ contraction**: `intervalFullSemigroupOperator_Linfty_bound` gives a direct all-positive-time spatial sup bound for `S(t)u₀` from an initial sup bound.
4. **Positive-time continuity of `srcTimeCoeff`**: the `FlooredSourceTimeData`/direct route gives local positive-time continuity/ContDiff, not half-line boundedness.

So for the iSup majorant BddAbove proof, the best route is probably **not** “continuity + decay to infinity” as the first attack. The simpler route for the zeroth source coefficient is:

```text
L∞ contraction of S(t)u₀ for all t > 0
→ uniform bound on ν*(S(t)u₀)^γ for all t ≥ c/2
→ cosineCoeffs_abs_le_of_continuous_bounded
→ coefficient is uniformly bounded on [c/2,∞)
```

For time derivatives of the coefficient (`j = 1,2`), use the analogous positive-time heat smoothing estimates on `[c/2,∞)`: `du` and `d2u` have uniform bounds there because the heat multipliers are bounded by the same exponential at `c/2`.  That is the real analytic content needed for the derivative part of the cutoff majorant.

## Search results / relevant files

### No direct half-line source coefficient theorem found

Search queries tried:

```text
cosineCoeffs source t >= c infinity bound srcTimeCoeff Ici Ioi
srcTimeCoeff_bound srcTimeCoeff_contDiff cosineCoeffs srcSlice bound
Ici infinity BddAbove cosineCoeffs
BddAbove cosineCoeffs source
ν u^γ cosineCoeffs chem source bound p.ν p.γ
```

These did not return a theorem with the needed half-line shape.

### The source coefficient identity exists

`ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean:58-66`:

```lean
/-- The concrete chemotaxis source slice `x ↦ p.ν · u(t,x)^γ` at time `t`. -/
def srcSlice (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (t x : ℝ) : ℝ :=
  p.ν * intervalDomainLift (u t) x ^ p.γ

/-- The committed identity `srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k`. -/
theorem srcTimeCoeff_eq_cosineCoeffs
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (k : ℕ) (t : ℝ) :
    srcTimeCoeff p u k t = cosineCoeffs (srcSlice p u t) k := by
```

This is the rewrite needed to move from `resolverTimeCoeff = w_k * srcTimeCoeff` to a source cosine coefficient.

### Heat semigroup L∞ contraction exists

`ShenWork/PDE/IntervalFullKernelSupBound.lean:52-56`:

```lean
/-- **Full-kernel `L∞→L∞` (sup) bound.**  `|intervalFullSemigroupOperator t f x| ≤ M`
whenever `|f| ≤ M`. -/
theorem intervalFullSemigroupOperator_Linfty_bound {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hf : ∀ y, |f y| ≤ M) (x : ℝ) :
    |intervalFullSemigroupOperator t f x| ≤ M := by
```

This is likely the shortest path for bounding the **zeroth** source coefficient uniformly for all `t ≥ c/2`.

### Existing compact-window coefficient-bound template

`ShenWork/Wiener/EWA/SourcePowerCoeffDerivComplete.lean:190-205` proves a window-uniform bound from compactness:

```lean
theorem powerCoeff_bound_of_inputs {p : CM2Params}
    {v : ℝ → intervalDomainPoint → ℝ} {vdotL : ℝ → ℝ → ℝ} {a' b' : ℝ}
    (hslabcont : ContinuousOn (Function.uncurry (gPow p v vdotL))
      (Set.Icc a' b' ×ˢ Set.Icc (0 : ℝ) 1)) :
    ∃ Mdot, ∀ σ ∈ Set.Icc a' b', ∀ k, |adotPow p v vdotL σ k| ≤ Mdot := by
  set K := Set.Icc a' b' ×ˢ Set.Icc (0 : ℝ) 1 with hKdef
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B, hB⟩ := hKcompact.bddAbove_image hslabcont.norm
  set B' := max B 0 with hB'def
  ...
  exact cosineCoeffs_abs_le_of_continuous_bounded hsec hB'nn ... k
```

This is **not half-line**, but it is the right closed-window compactness pattern.

### Existing coefficient continuity on closed windows

`ShenWork/Paper2/IntervalDomainPositiveWindowK1OnEndpoint.lean:32-37`:

```lean
theorem cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
    {f : ℝ → ℝ → ℝ} {c T : ℝ} (k : ℕ)
    (hf : ContinuousOn (Function.uncurry f)
      (Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1)) :
    ContinuousOn (fun σ => cosineCoeffs (f σ) k) (Set.Icc c T) := by
```

Again: closed-window, not half-line.

### Existing positive-time coefficient regularity, but not half-line boundedness

`IntervalHeatResolverJointC2.lean` proves/uses positive-time local regularity of `srcTimeCoeff` and `resolverTimeCoeff`; this is local, not a half-line bound. The key theorem shape is:

```lean
theorem heatLevel0_srcTimeCoeff_contDiffAt_two ... {t : ℝ} (ht : 0 < t) (k : ℕ) :
  ContDiffAt ℝ (2 : ℕ∞)
    (srcTimeCoeff p (conjugatePicardIter p u₀ 0) k) t
```

and then

```lean
theorem heatLevel0_resolverTimeCoeff_contDiffAt_two ... {t : ℝ} (ht : 0 < t) (k : ℕ) :
  ContDiffAt ℝ (2 : ℕ∞)
    (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t
```

These are enough for local continuity on every positive point, but not enough alone for `BddAbove` on `[c/2,∞)`.

## Does continuity plus decay at infinity imply boundedness?

Mathematically: **yes**.

Lean route:

```lean
lemma bddAbove_image_Ici_of_continuousOn_tendsto
    {f : ℝ → ℝ} {c L : ℝ}
    (hf : ContinuousOn f (Set.Ici c))
    (hlim : Tendsto f atTop (𝓝 L)) :
    BddAbove (f '' Set.Ici c) := by
  -- choose R ≥ c such that for t ≥ R, |f t - L| ≤ 1
  -- tail bound: f t ≤ |L| + 1
  -- compact part: f '' Icc c R is BddAbove by compactness
  -- union the two bounds
  sorry
```

For norm-valued nonnegative target:

```lean
lemma bddAbove_norm_image_Ici_of_continuousOn_tendsto
    {f : ℝ → E} [NormedAddCommGroup E] {c : ℝ}
    (hf : ContinuousOn f (Set.Ici c))
    (hlim : Tendsto f atTop (𝓝 0)) :
    BddAbove ((fun t => ‖f t‖) '' Set.Ici c) := by
  -- same split; tail bound ≤ 1, compact part by continuity of norm ∘ f
  sorry
```

But two warnings:

1. `FlooredSourceTimeData.d0`/the local direct route gives local continuity/ContDiffAt at positive times. It does **not** by itself give a `Tendsto` statement as `t → ∞`.
2. For `k = 0`, the source coefficient does not necessarily decay to `0`; it tends to a finite constant if `S(t)u₀` tends to its mean. Finite limit is still enough for boundedness.

So the statement “continuity + decay” is correct only after proving the missing `atTop` limit. The repo search did not reveal that theorem for this source coefficient.

## Better route for this BddAbove proof

For the iSup majorant, avoid requiring an `atTop` source-coefficient limit if possible.

### Zeroth source coefficient (`r = 0`)

Use L∞ contraction:

```text
|u₀| ≤ U0
⇒ |S(t)u₀(x)| ≤ U0                      for all t > 0, x
⇒ 0 ≤ S(t)u₀(x) ≤ U0                    using positivity
⇒ |p.ν * (S(t)u₀(x))^p.γ| ≤ p.ν * U0^p.γ
⇒ |cosineCoeffs (srcSlice p u t) k| ≤ 2 * p.ν * U0^p.γ
```

This gives a uniform bound for all `t ≥ c/2` immediately, no compactness-at-infinity needed.

Relevant available theorem:

```lean
intervalFullSemigroupOperator_Linfty_bound
```

Relevant coefficient endpoint:

```lean
cosineCoeffs_abs_le_of_continuous_bounded
```

### First and second time derivatives (`r = 1,2`)

Use heat smoothing on the half-line:

```text
for t ≥ c/2:
λ^m exp(-t λ) ≤ λ^m exp(-(c/2) λ)
```

So `du`, `d2u`, and the source derivative slices have uniform spatial sup/H4/coeff bounds on `[c/2,∞)`. This is the half-line analogue of the cutoff estimates already used in the heat regularity file.

This is better than compactness plus decay because it directly gives explicit mode-wise summable majorants.

## Recommended theorem to add

Add a simple half-line coefficient boundedness lemma for any jointly bounded source slice:

```lean
theorem cosineCoeffs_bddAbove_Ici_of_uniform_spatial_bound
    {f : ℝ → ℝ → ℝ} {c B : ℝ} (hB : 0 ≤ B)
    (hcont : ∀ t ∈ Set.Ici c, ContinuousOn (f t) (Set.Icc (0 : ℝ) 1))
    (hbd : ∀ t ∈ Set.Ici c, ∀ x ∈ Set.Icc (0 : ℝ) 1, |f t x| ≤ B)
    (k : ℕ) :
    BddAbove ((fun t : ℝ => |cosineCoeffs (f t) k|) '' Set.Ici c) := by
  refine ⟨2 * B, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact cosineCoeffs_abs_le_of_continuous_bounded (hcont t ht) hB (hbd t ht) k
```

Then instantiate `f t = srcSlice p (conjugatePicardIter p u₀ 0) t` using L∞ contraction.

For the resolver coefficient:

```lean
theorem resolverTimeCoeff_bddAbove_Ici_of_src_bound
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {c B : ℝ}
    (hB : 0 ≤ B)
    (hsrc : ∀ t ∈ Set.Ici c, |srcTimeCoeff p u k t| ≤ B) :
    BddAbove ((fun t : ℝ => |resolverTimeCoeff p u k t|) '' Set.Ici c) := by
  refine ⟨|ShenWork.PDE.intervalNeumannResolverWeight p k| * B, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  rw [resolverTimeCoeff_eq_weight_smul]
  -- abs_mul + hsrc
  sorry
```

## For the original set over `q : ℝ × ℝ`

The target is:

```lean
BddAbove
  ((fun q : ℝ × ℝ =>
    ‖iteratedFDeriv ℝ j (cutoffResolverTerm p u c k) q‖) '' Set.univ)
```

For `q.1 < c/2`, the cutoff term is locally zero, so the norm is `0`.

For `q.1 ≥ c/2`, use the finite Leibniz majorant from Q1541. The needed coefficient envelopes should be stated over `Set.Ici (c/2)`:

```lean
∀ r ≤ 2, BddAbove
  ((fun t : ℝ =>
    ‖iteratedFDeriv ℝ r
      (resolverTimeCoeff p (conjugatePicardIter p u₀ 0) k) t‖) '' Set.Ici (c/2))
```

Then the product/cosine finite sum gives the desired `BddAbove` over all `q`.

## Final verdict

* I did not find a direct existing half-line theorem bounding the source cosine coefficients on `[c,∞)`.
* The repo has strong closed-window compactness templates and the needed coefficient-boundedness lemma.
* `FlooredSourceTimeData.d0`/local ContDiff gives continuity at positive times, but continuity alone does not give half-line boundedness.
* Continuity plus a proven finite limit at infinity would give boundedness by compact `[c,R]` plus tail `[R,∞)`, but the source `atTop` limit theorem appears absent.
* The most direct route is to prove uniform spatial bounds on `[c/2,∞)` using `intervalFullSemigroupOperator_Linfty_bound`, then apply `cosineCoeffs_abs_le_of_continuous_bounded`. For derivative coefficients, use the standard heat multiplier estimate with lower time cutoff `c/2`.
