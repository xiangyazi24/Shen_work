# Q987 (cron2) — cutoff resolver coefficients without full `FlooredSourceTimeData`?

Static repo inspection only; I did **not** run Lean.

## Short answer

There is a **partial shortcut**, but not the one suggested by the phrase “the
cutoff kills the blow-up region.”

For the single mode

```lean
fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t
```

you can avoid the full six-field `FlooredSourceTimeData`.  But you **cannot** avoid
proving a local positive-time two-derivative theorem for `srcTimeCoeff` (or an
exact equivalent).  The cutoff only removes the obligations at times
`t < c / 2`.  At every time `t ≥ c / 2`, and in particular at the transition time
`t = c / 2`, Lean still needs a `ContDiffAt ℝ 2` proof for
`resolverTimeCoeff p u k`, hence for `srcTimeCoeff p u k`, because `c / 2 > 0`.

So the right split is:

```text
full FlooredSourceTimeData      = d0 + d1 + sliceC2 + sliceNeumann + zerothBound + laplBound
coefficient ContDiff only       = d0 + d1 + continuity of second derivative coefficient
coefficient bounds for tsum     = derivative bounds/envelopes, but can be local/cutoff-specific
```

Thus:

* **Yes**, you can bypass full `FlooredSourceTimeData` for the **term
  `ContDiff` premise** of `contDiff_tsum`.
* **No**, the cutoff does not by itself prove `ContDiff`; you still need a local
  positive-time `srcTimeCoeff` C² lemma.
* For the **majorant premises** of `contDiff_tsum`, you still need bounded
  derivative envelopes.  Those can be proved directly on the cutoff support, but
  they are separate from the term-C² proof.

The simplest existing route remains the restart route from Q931:
`resolverSpectralJointC2At_of_restartSmoothCutoff`, because it already proves the
cutoff coefficient C² and bounds for `localRestartCoeff`.  If you insist on the
physical coefficient `resolverTimeCoeff p u k`, use the lightweight local lemma
below instead of full `FlooredSourceTimeData`.

## Relevant committed theorem names

### Coefficient factorization

File:

```text
ShenWork/PDE/IntervalPhysicalResolverDataConcrete.lean
```

Names:

```lean
ShenWork.IntervalPhysicalResolverDataConcrete.srcTimeCoeff
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_weight_smul
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_eq_smul
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_iteratedFDeriv_eq
ShenWork.IntervalPhysicalResolverDataConcrete.resolverTimeCoeff_bound
```

The key identity is:

```lean
resolverTimeCoeff p u k t =
  intervalNeumannResolverWeight p k * srcTimeCoeff p u k t
```

### Source coefficient identity and existing full-data producer

File:

```text
ShenWork/PDE/IntervalPhysicalSourceTimeC2Concrete.lean
```

Names:

```lean
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcSlice
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_eq_cosineCoeffs
ShenWork.IntervalPhysicalSourceTimeC2Concrete.FlooredSourceTimeData
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_contDiff
ShenWork.IntervalPhysicalSourceTimeC2Concrete.srcTimeCoeff_bound
ShenWork.IntervalPhysicalSourceTimeC2Concrete.physicalSourceTimeC2_of_floored
```

This file confirms that `srcTimeCoeff_contDiff` is currently obtained from
`FlooredSourceTimeData`, by two uses of
`cosineCoeffs_hasDerivAt_of_smooth_param` plus `contDiff_succ_iff_deriv`.
That is exactly the part we can factor out into a smaller local lemma.

### Parametric cosine coefficient derivative

Imported/opened in `IntervalPhysicalSourceTimeC2Concrete.lean`:

```lean
ShenWork.IntervalMildPicardRegularity.cosineCoeffs_hasDerivAt_of_smooth_param
ShenWork.IntervalDomainPositiveWindowK1OnEndpoint.cosineCoeffs_continuousOn_of_jointContinuousOn_Icc
```

These are the right primitives for the local coefficient-C² lemma.

### Cutoff infrastructure

File:

```text
ShenWork/PDE/IntervalResolverSpectralJointC2Cutoff.lean
```

Names:

```lean
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_contDiff
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eq_zero_of_le
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eq_one_of_ge
ShenWork.IntervalResolverSpectralJointC2Cutoff.smoothRightCutoff_eventually_eq_one
```

### Existing bounded-weight `contDiff_tsum` assembler

File:

```text
ShenWork/PDE/IntervalResolverJointC2Physical.lean
```

Names:

```lean
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointTerm
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradTerm
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointMajorant
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradMajorant
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointSeries_contDiff_two
ShenWork.IntervalResolverJointC2Physical.boundedWeightJointGradSeries_contDiff_two
```

This assembler works for any coefficient family `c : ℕ → ℝ → ℝ`.  So you can feed
it a cutoff family

```lean
def cutoffResolverCoeff
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c : ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t
```

instead of feeding it raw `resolverTimeCoeff`.

## Minimal shortcut theorem for the cutoff coefficient

The clean theorem to add is not a theorem about the source slices directly; it is
an adapter theorem saying: once `srcTimeCoeff` is known to be C² at positive times
where the cutoff may be nonzero, the cutoff resolver coefficient is globally C².

```lean
import ShenWork.PDE.IntervalPhysicalResolverDataConcrete
import ShenWork.PDE.IntervalResolverSpectralJointC2Cutoff

open Filter Topology Set
open ShenWork.IntervalDomain
open ShenWork.PDE
open ShenWork.IntervalResolverSpectralJointC2Cutoff
open ShenWork.IntervalResolverJointC2PhysicalConcrete (resolverTimeCoeff)
open ShenWork.IntervalPhysicalResolverDataConcrete

noncomputable section

namespace ShenWork.Paper2.Cron2CutoffResolverCoeff

/-- Cut off the resolver coefficient in time, killing the nonpositive/near-zero
region before feeding the coefficient family to `contDiff_tsum`. -/
def cutoffResolverCoeff
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c : ℝ)
    (k : ℕ) : ℝ → ℝ :=
  fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t

/-- Adapter: local positive-time C² of `srcTimeCoeff` on `[c/2,∞)` is enough to
make the cutoff resolver coefficient globally C².  The branch `t < c/2` is
locally zero; the branch `t ≥ c/2` uses the constant-weight identity
`resolverTimeCoeff = wₖ • srcTimeCoeff`. -/
theorem cutoffResolverCoeff_contDiff_two_of_srcTimeCoeff_contDiffAt
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hsrc : ∀ τ : ℝ, c / 2 ≤ τ →
      ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) τ) :
    ContDiff ℝ (2 : ℕ∞) (cutoffResolverCoeff p u c k) := by
  -- Skeleton; exact names for the final `congr_of_eventuallyEq` direction may need
  -- minor adjustment.
  rw [contDiff_iff_contDiffAt]
  intro τ
  by_cases hτlt : τ < c / 2
  · -- Locally left of `c/2`, the cutoff is identically zero.
    have hzero : cutoffResolverCoeff p u c k =ᶠ[𝓝 τ] fun _ : ℝ => 0 := by
      filter_upwards [Iio_mem_nhds hτlt] with t ht
      have hφ : smoothRightCutoff (c / 2) c t = 0 := by
        exact smoothRightCutoff_eq_zero_of_le (by linarith) (le_of_lt ht)
      simp [cutoffResolverCoeff, hφ]
    -- `fun _ => 0` is C², transfer by eventual equality.
    exact (contDiffAt_const : ContDiffAt ℝ (2 : ℕ∞) (fun _ : ℝ => (0 : ℝ)) τ)
      |>.congr_of_eventuallyEq hzero.symm
  · -- At and to the right of `c/2`, `τ` is positive and the source coefficient is C².
    have hτle : c / 2 ≤ τ := le_of_not_gt hτlt
    have hres : ContDiffAt ℝ (2 : ℕ∞) (resolverTimeCoeff p u k) τ := by
      rw [resolverTimeCoeff_eq_smul]
      exact (hsrc τ hτle).const_smul (intervalNeumannResolverWeight p k)
    have hφ : ContDiffAt ℝ (2 : ℕ∞) (smoothRightCutoff (c / 2) c) τ :=
      smoothRightCutoff_contDiff.contDiffAt
    simpa [cutoffResolverCoeff] using hφ.mul hres

end ShenWork.Paper2.Cron2CutoffResolverCoeff
```

This theorem is the actual shortcut for the **term ContDiff** part.  It avoids
constructing the full `PhysicalResolverJointC2Data` and avoids full
`FlooredSourceTimeData`.  It does **not** avoid local source-coefficient C².

## Minimal local source-coefficient C² lemma

The missing hypothesis `hsrc` above should be supplied by a lightweight local
positive-time lemma.  It should not require the full six fields of
`FlooredSourceTimeData`; only the first two derivative-slice fields and continuity
of the second derivative slice are needed.

Recommended target:

```lean
structure LocalSourceTimeC2At
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (s₁ s₂ : ℝ → ℝ → ℝ) (τ : ℝ) : Prop where
  d0 : ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (srcSlice p u s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => srcSlice p u r x) (s₁ s x) s) ∧
    ContinuousOn (Function.uncurry s₁)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
  d1 : ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ, ContinuousOn (s₁ s) (Icc (0 : ℝ) 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      HasDerivAt (fun r => s₁ r x) (s₂ s x) s) ∧
    ContinuousOn (Function.uncurry s₂)
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Then prove:

```lean
theorem srcTimeCoeff_contDiffAt_two_of_localSourceTimeC2At
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {s₁ s₂ : ℝ → ℝ → ℝ} {τ : ℝ}
    (H : LocalSourceTimeC2At p u s₁ s₂ τ) (k : ℕ) :
    ContDiffAt ℝ (2 : ℕ∞) (srcTimeCoeff p u k) τ := by
  -- Proof route:
  -- 1. From `H.d0`, use `cosineCoeffs_hasDerivAt_of_smooth_param` to show
  --      HasDerivAt (srcTimeCoeff p u k) (cosineCoeffs (s₁ τ) k) τ.
  --    More generally, get the derivative formula locally near τ.
  -- 2. From `H.d1`, use the same primitive for
  --      HasDerivAt (fun t => cosineCoeffs (s₁ t) k)
  --        (cosineCoeffs (s₂ τ) k) τ.
  -- 3. Use `cosineCoeffs_continuousOn_of_jointContinuousOn_Icc` on the `s₂` slab
  --    to get continuity at τ of `fun t => cosineCoeffs (s₂ t) k`.
  -- 4. Assemble via the same pattern already committed in
  --    `srcTimeCoeff_contDiff`:
  --      `contDiff_one_iff_deriv`
  --      then `contDiff_succ_iff_deriv` / local `ContDiffAt` analogue.
  sorry
```

If the local `ContDiffAt` assembly lemmas are awkward, prove a slightly stronger
open-neighborhood version:

```lean
theorem srcTimeCoeff_contDiffOn_Ioo_of_sourceTimeC2On
    ... :
    ContDiffOn ℝ (2 : ℕ∞) (srcTimeCoeff p u k) (Ioo a b)
```

then use `.contDiffAt` with `IsOpen.mem_nhds` when `τ ∈ Ioo a b`.  This is often
less painful than using `ContDiffAt` derivative-recursion lemmas directly.

For the heat semigroup level-0 case, choose the slices already documented in
`IntervalHeatSemigroupFlooredSourceTimeData.lean`:

```lean
s₁ := srcSlice1 p (conjugatePicardIter p u₀ 0) (heatDu u₀)
s₂ := srcSlice2 p (conjugatePicardIter p u₀ 0) (heatDu u₀) (heatD2u u₀)
```

and prove the local data only for `τ ≥ c/2`.  Since `0 < c`, every such `τ` is
positive, and the local ball can be chosen inside `(0,∞)`.  This avoids all the
`t ≤ 0` obligations that make global `FlooredSourceTimeData` annoying.

## How this plugs into `contDiff_tsum`

Define the cutoff coefficient family:

```lean
def cutoffResolverCoeffFamily
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c : ℝ) :
    ℕ → ℝ → ℝ :=
  fun k t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t
```

Then feed it to the existing bounded-weight assemblers:

```lean
have hValueSeries : ContDiff ℝ (2 : ℕ∞)
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ,
        boundedWeightJointTerm (cutoffResolverCoeffFamily p u c) k q) :=
  boundedWeightJointSeries_contDiff_two
    (hc := fun k => cutoffResolverCoeff_contDiff_two_of_srcTimeCoeff_contDiffAt
      (p := p) (u := u) (c := c) hc k hsrc)
    hBt_cut
    hBt_cut_summable

have hGradSeries : ContDiff ℝ (2 : ℕ∞)
    (fun q : ℝ × ℝ =>
      ∑' k : ℕ,
        boundedWeightJointGradTerm (cutoffResolverCoeffFamily p u c) k q) :=
  boundedWeightJointGradSeries_contDiff_two
    (hc := fun k => cutoffResolverCoeff_contDiff_two_of_srcTimeCoeff_contDiffAt
      (p := p) (u := u) (c := c) hc k hsrc)
    hBt_cut
    hBt_cut_grad_summable
```

Near any target `s₀ > c`, use:

```lean
smoothRightCutoff_eventually_eq_one (by linarith : c / 2 < c) hs₀
```

to transfer the cutoff series back to the original resolver series by eventual
equality, exactly like `heatSeries_eventuallyEq_cutoff` and
`heatSemigroup_jointContDiffAt_two` do.

## Important caveat: term C² is not enough for `contDiff_tsum`

`contDiff_tsum` needs three things:

```lean
1. ∀ k, ContDiff ℝ 2 (cutoff term k)
2. ∀ derivative order i ≤ 2, a summable majorant
3. pointwise derivative bounds by that majorant
```

The shortcut above only solves item 1.  Items 2 and 3 still need cutoff-specific
bounds for

```lean
iteratedFDeriv ℝ i
  (fun t => smoothRightCutoff (c / 2) c t * resolverTimeCoeff p u k t)
```

For those bounds, you again need formulas or estimates for the first two time
derivatives of `srcTimeCoeff` on the support where the cutoff is nonzero.  You do
not need full `FlooredSourceTimeData`, but you do need a bound package equivalent
to the `src_bound` part of `PhysicalSourceTimeC2` restricted to the positive
cutoff region.

If using the one-sided `smoothRightCutoff (c/2) c`, the support is unbounded to
`+∞`; your majorants must be uniform for all `t ≥ c/2`.  For local-at-`s₀`
regularity, a two-sided compact restart cutoff is often easier because all bounds
are only needed on a compact positive slab.  This is exactly why the existing
restart theorem is attractive.

## Best practical recommendation

For the direct physical coefficient lane:

1. Add `LocalSourceTimeC2At` or `PositiveSourceTimeC2On` with only `d0`, `d1`, and
   continuity of the second derivative slice.
2. Prove `srcTimeCoeff_contDiffAt_two_of_localSourceTimeC2At` by copying the
   coefficient part of `srcTimeCoeff_contDiff`, not the whole `FlooredSourceTimeData`.
3. Prove `cutoffResolverCoeff_contDiff_two_of_srcTimeCoeff_contDiffAt` as the
   zero-left/product-right adapter.
4. Separately prove cutoff derivative bounds/envelopes for `hBt_cut`.
5. Feed `cutoffResolverCoeffFamily` to
   `boundedWeightJointSeries_contDiff_two` and
   `boundedWeightJointGradSeries_contDiff_two`.
6. Transfer back near `s₀ > c` using `smoothRightCutoff_eventually_eq_one`.

For the fastest route to close the resolver joint-C² target, do not build this
new lane unless you specifically need the physical coefficient family.  Use the
already committed restart path:

```lean
coupledChemicalConcentration_resolver_jointC2At_c2Data
  HRc2 hs0 hsU hx
  (by
    intro a₀ M _hM ha₀ a src offset hτoffset _hagree
    exact resolverSpectralJointC2At_of_restartSmoothCutoff
      (a₀ := a₀) (M := M) (a := a)
      (offset := offset) (s := s) (x := x)
      hτoffset ha₀ src)
```

That path already has the coefficient C² and `contDiff_tsum` bounds for the
cutoff/restart coefficients.  It is the real shortcut.  The physical cutoff lane
is a smaller refactor of `FlooredSourceTimeData`, not a complete replacement for
the two time-derivative source calculus.
