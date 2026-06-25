# Q464 (cron2): Neumann BC for `chemDivLift`

## Executive verdict

For the theorem exactly as stated,

```lean
deriv (chemDivLift p u v) 0 = 0 ∧ deriv (chemDivLift p u v) 1 = 0
```

the cleanest proof is **not** direct flux algebra and not cosine parity. It is the **zero-extension endpoint-derivative convention**.

`chemDivLift p u v` is defined as

```lean
intervalDomainLift (fun pt => intervalDomainChemotaxisDiv p u v pt)
```

and `intervalDomainLift` is identically `0` off `[0,1]`. Therefore at the left endpoint it is zero on the whole left side, and at the right endpoint it is zero on the whole right side. For the ordinary two-sided Mathlib `deriv`, this forces the endpoint derivative to be `0` for any zero-extension: if the function is differentiable at the endpoint, the derivative must agree with the derivative of the constant zero side; if it is not differentiable, Mathlib's `deriv` is the junk value `0`.

So the strongest useful lemma is:

```lean
theorem intervalDomainLift_deriv_left_endpoint_zero
    (w : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift w) 0 = 0

theorem intervalDomainLift_deriv_right_endpoint_zero
    (w : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift w) 1 = 0
```

Then `chemDivLift_neumann_bc` is a one-line specialization:

```lean
simpa [chemDivLift] using
  ⟨intervalDomainLift_deriv_left_endpoint_zero
      (fun pt => intervalDomainChemotaxisDiv p u v pt),
   intervalDomainLift_deriv_right_endpoint_zero
      (fun pt => intervalDomainChemotaxisDiv p u v pt)⟩
```

This proof uses none of `hu_C2`, `hv_C2`, `hu_N0`, `hv_N0`, etc. Those hypotheses are irrelevant for the **two-sided zero-extension endpoint derivative**.

However, this is an important warning: the theorem as stated proves only the **junk-value endpoint derivative** of a zero-extension. It does **not** prove the genuine one-sided Neumann boundary condition needed for integration by parts / `IntervalWeakH2Neumann`. For the genuine source regularity, you still need:

```lean
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 0 (Ioi 0)) (nhds 0)
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 1 (Iio 1)) (nhds 0)
```

and those are not consequences of only `u,v ∈ C²` plus `u' = v' = 0` at endpoints. The repo already records that the chem source needs higher regularity: roughly `u ∈ C³` and `v ∈ C⁴`, or a cosine/even-reflection package giving the required odd-derivative vanishings.

Thus:

* For the exact theorem with `deriv ... 0 = 0`: use **(c)**, the zero-extension/junk-value route, and prove a general lemma for all `intervalDomainLift` functions.
* For the mathematically meaningful chem source Neumann condition: use **(b)**/spectral parity or stronger cosine-series regularity, not the weak `C² + first Neumann` hypotheses.
* **(a)** direct flux computation is the wrong local target for the two-sided `deriv`; it computes interior/right-hand flux derivatives, while the Lean endpoint `deriv` of a zero-extension is governed by the outside-zero side and junk-value convention.

## Files checked

### `IntervalDomain.lean`: definitions

`intervalDomainChemotaxisDiv` is the derivative of the chemotaxis flux:

```lean
def intervalDomainChemotaxisDiv (p : CM2Params)
    (u v : intervalDomainPoint → ℝ) (x : intervalDomainPoint) : ℝ :=
  deriv
    (fun y : ℝ =>
      intervalDomainLift u y * deriv (intervalDomainLift v) y /
        (1 + intervalDomainLift v y) ^ p.β)
    x.1
```

`intervalDomainLift` zero-extends a subtype function:

```lean
def intervalDomainPoint : Type := Subtype (Set.Icc (0 : ℝ) 1)

def intervalDomainLift (f : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  fun x => if hx : x ∈ Set.Icc (0 : ℝ) 1 then f ⟨x, hx⟩ else 0
```

`chemDivLift` in `IntervalBFormSpectralHchem.lean` is just:

```lean
def chemDivLift (p : CM2Params) (u v : intervalDomainPoint → ℝ) : ℝ → ℝ :=
  intervalDomainLift (fun x => intervalDomainChemotaxisDiv p u v x)
```

Therefore the endpoint derivative in your theorem is the endpoint derivative of a zero-extension.

### `IntervalCosineSliceRegularity.lean`: existing template

The repo already says the two-sided endpoint derivative is the junk-value endpoint convention:

```lean
/-- **Junk-value endpoint derivative at the left endpoint.**  If the lift of a
slice is nonzero at `0`, then — since `intervalDomainLift` zero-extends to the
left of `0` — the lift is discontinuous at `0`, hence not differentiable, hence
`deriv = 0` by the Mathlib junk-value convention. -/
theorem intervalDomainLift_deriv_left_endpoint_zero_of_ne
    {w : intervalDomainPoint → ℝ} (hne : intervalDomainLift w 0 ≠ 0) :
    deriv (intervalDomainLift w) 0 = 0

/-- **Junk-value endpoint derivative at the right endpoint.**  Symmetric to
`intervalDomainLift_deriv_left_endpoint_zero_of_ne`. -/
theorem intervalDomainLift_deriv_right_endpoint_zero_of_ne
    {w : intervalDomainPoint → ℝ} (hne : intervalDomainLift w 1 ≠ 0) :
    deriv (intervalDomainLift w) 1 = 0
```

The current lemma requires endpoint nonvanishing because it proves non-differentiability via a jump. For `chemDivLift`, endpoint nonvanishing is usually the wrong hypothesis: often the endpoint value is `0`, but the zero-extension still has ordinary two-sided derivative `0` either by differentiability with zero slope or by non-differentiability/junk.

So the useful generalization is to remove the `hne` hypothesis entirely.

### `SourceSliceC2Neumann.lean`: logistic-source template

The logistic source proof separates two notions:

1. genuine one-sided Neumann limits, proved by comparison with a smooth/cosine-series interior representative:

```lean
Tendsto (deriv (intervalDomainLift (intervalLogisticSource ...)))
  (nhdsWithin 0 (Ioi 0)) (nhds 0)
```

2. endpoint point-derivatives of the zero-extension, proved by the junk-value route:

```lean
intervalDomainLift_deriv_left_endpoint_zero_of_ne
intervalDomainLift_deriv_right_endpoint_zero_of_ne
```

This is exactly the template to follow conceptually: do not confuse the two-sided point derivative with the genuine one-sided normal derivative.

### `IntervalChemDivSpatialC2.lean`: current chem-div residual

The file already has the target theorem as a `sorry`:

```lean
theorem chemDivLift_neumann_bc
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu_C2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv_C2 : ContDiffOn ℝ 2 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    (hu_N0 : deriv (intervalDomainLift u) 0 = 0)
    (hu_N1 : deriv (intervalDomainLift u) 1 = 0)
    (hv_N0 : deriv (intervalDomainLift v) 0 = 0)
    (hv_N1 : deriv (intervalDomainLift v) 1 = 0) :
    deriv (chemDivLift p u v) 0 = 0 ∧
    deriv (chemDivLift p u v) 1 = 0 := by
  sorry
```

The comments there suggest a symmetry/flux computation route. For this exact statement, that is overkill and potentially misleading. The theorem follows from zero-extension alone. The higher-regularity residual in the same file is still real for the C²/weak-H² source data; the endpoint point-derivative theorem is not the hard part.

## Recommended Lean lemma

Add this near `IntervalCosineSliceRegularity.lean`, next to the existing `_of_ne` junk-value lemmas, or in a small zero-extension helper file imported by `IntervalChemDivSpatialC2.lean`.

```lean
import ShenWork.PDE.IntervalCosineSliceRegularity

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)

namespace ShenWork.IntervalCosineSliceRegularity

/-- The ordinary two-sided derivative at the left endpoint of any zero-extension
`intervalDomainLift w` is `0`.

If the zero-extension is differentiable at `0`, the left-side constant-zero branch
forces derivative `0`; if it is not differentiable, Mathlib's `deriv` is the junk
value `0`. -/
theorem intervalDomainLift_deriv_left_endpoint_zero
    (w : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift w) 0 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift w) 0
  · -- Since `intervalDomainLift w = 0` on `Iio 0`, the within-derivative along
    -- `Iio 0` is zero.  The global derivative restricts to the same within-derivative,
    -- and uniqueness on the left neighbourhood gives the global derivative is zero.
    have hleft : (intervalDomainLift w) =ᶠ[nhdsWithin (0 : ℝ) (Set.Iio 0)] (fun _ : ℝ => 0) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
      refine ⟨Set.Iio (0 : ℝ), self_mem_nhdsWithin, ?_⟩
      intro y hy
      have hnot : y ∉ Set.Icc (0 : ℝ) 1 := fun hyIcc => (not_le.mpr hy) hyIcc.1
      simp [intervalDomainLift, hnot]
    -- Implementation detail: use `HasDerivAt.hasDerivWithinAt`,
    -- `(hasDerivWithinAt_const ...).congr_of_eventuallyEq`, and uniqueness for
    -- `UniqueDiffWithinAt ℝ (Set.Iio 0) 0`.
    -- One possible proof shape:
    --   have hglob : HasDerivAt (intervalDomainLift w)
    --       (deriv (intervalDomainLift w) 0) 0 := hdiff.hasDerivAt
    --   have hwithin_glob := hglob.hasDerivWithinAt
    --   have hwithin_zero : HasDerivWithinAt (intervalDomainLift w) 0 (Set.Iio 0) 0 := ...
    --   exact (hwithin_zero.unique hwithin_glob uniqueDiffWithinAt_Iio).symm
    sorry
  · exact deriv_zero_of_not_differentiableAt hdiff

/-- The ordinary two-sided derivative at the right endpoint of any zero-extension
`intervalDomainLift w` is `0`. -/
theorem intervalDomainLift_deriv_right_endpoint_zero
    (w : intervalDomainPoint → ℝ) :
    deriv (intervalDomainLift w) 1 = 0 := by
  by_cases hdiff : DifferentiableAt ℝ (intervalDomainLift w) 1
  · have hright : (intervalDomainLift w) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => 0) := by
      refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
      refine ⟨Set.Ioi (1 : ℝ), self_mem_nhdsWithin, ?_⟩
      intro y hy
      have hnot : y ∉ Set.Icc (0 : ℝ) 1 := fun hyIcc => (not_le.mpr hy) hyIcc.2
      simp [intervalDomainLift, hnot]
    -- Same proof shape, using uniqueness on `Set.Ioi 1`.
    sorry
  · exact deriv_zero_of_not_differentiableAt hdiff

end ShenWork.IntervalCosineSliceRegularity
```

I left the uniqueness sub-proof schematic because the exact Mathlib lemma names around `UniqueDiffWithinAt` for `Iio/Ioi` may vary. If those names are awkward in v4.29.1, an alternative is to use `HasDerivAtFilter` uniqueness directly on `nhdsWithin 0 (Iio 0)` / `nhdsWithin 1 (Ioi 1)`.

The key point: this lemma is general and independent of `chemDiv`.

## Final `chemDivLift_neumann_bc` proof shape

Once the two general zero-extension lemmas are available:

```lean
import ShenWork.Paper2.IntervalChemDivSpatialC2
import ShenWork.PDE.IntervalCosineSliceRegularity

open Set
open ShenWork.IntervalDomain
  (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.IntervalBFormSpectral (chemDivLift)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainLift_deriv_left_endpoint_zero
   intervalDomainLift_deriv_right_endpoint_zero)

namespace ShenWork.Paper2.ChemDivSpatialC2

theorem chemDivLift_neumann_bc_clean
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu_C2 : ContDiffOn ℝ 2 (intervalDomainLift u) (Icc (0 : ℝ) 1))
    (hv_C2 : ContDiffOn ℝ 2 (intervalDomainLift v) (Icc (0 : ℝ) 1))
    (hu_N0 : deriv (intervalDomainLift u) 0 = 0)
    (hu_N1 : deriv (intervalDomainLift u) 1 = 0)
    (hv_N0 : deriv (intervalDomainLift v) 0 = 0)
    (hv_N1 : deriv (intervalDomainLift v) 1 = 0) :
    deriv (chemDivLift p u v) 0 = 0 ∧
    deriv (chemDivLift p u v) 1 = 0 := by
  constructor
  · simpa [chemDivLift] using
      intervalDomainLift_deriv_left_endpoint_zero
        (fun x : intervalDomainPoint => intervalDomainChemotaxisDiv p u v x)
  · simpa [chemDivLift] using
      intervalDomainLift_deriv_right_endpoint_zero
        (fun x : intervalDomainPoint => intervalDomainChemotaxisDiv p u v x)

end ShenWork.Paper2.ChemDivSpatialC2
```

All six assumptions are unused. You may keep them in the theorem for compatibility with `chemDivSource_weakH2_of_uv_C4`, but they should not appear in the proof.

## What if you need the real Neumann BC?

If the goal is the real boundary condition for source inversion / weak-H², the endpoint point-derivative is not enough. `IntervalWeakH2Neumann` requires both the endpoint point derivatives and the one-sided endpoint derivative limits:

```lean
noncomputable def intervalWeakH2Neumann_of_contDiffOn
    {g : ℝ → ℝ}
    (hgC2 : ContDiffOn ℝ 2 g (Set.Icc (0 : ℝ) 1))
    (htend0 : Filter.Tendsto (deriv g) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htend1 : Filter.Tendsto (deriv g) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0))
    (hbc0 : deriv g 0 = 0) (hbc1 : deriv g 1 = 0) :
    IntervalWeakH2Neumann g
```

For `g = chemDivLift p u v`, the `hbc0/hbc1` part is the easy zero-extension lemma above. The hard part is:

```lean
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 0 (Ioi 0)) (nhds 0)
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 1 (Iio 1)) (nhds 0)
```

Those are statements about the interior behavior of `flux''` at the endpoints. They require higher parity/regularity assumptions, not just `C²` and first Neumann data.

A meaningful theorem should look like one of these:

### Spectral/even-reflection route

```lean
/-- If the chem-div source has an even cosine-series representative with enough
weighted summability, then the genuine one-sided Neumann limits hold. -/
theorem chemDivLift_neumann_limits_of_cosineSeries
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    {b : ℕ → ℝ}
    (hb : Summable (fun n => unitIntervalCosineEigenvalue n * |b n|))
    (hagree : Set.EqOn (chemDivLift p u v)
      (fun x => ∑' n, b n * cosineMode n x) (Set.Icc (0 : ℝ) 1)) :
    Tendsto (deriv (chemDivLift p u v)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
    Tendsto (deriv (chemDivLift p u v)) (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
  -- same pattern as `intervalDomainCosineSlice_neumann_limit_left/right`
  sorry
```

This is the clean parity route. If you can represent the chem-div source as a cosine series with `∑ λₙ |bₙ| < ∞`, the endpoint derivative limits follow exactly like the existing cosine-slice Neumann lemmas.

### Direct flux route, but with the right hypotheses

To prove `flux'' → 0` at endpoints directly, you need enough derivatives and endpoint compatibility. Schematically at `0`:

```text
F = U * V' * (1+V)^(-β)
chemDiv = F'
deriv(chemDiv) interior = F''
```

`F''(0)` contains terms involving `U'(0)`, `V'(0)`, `V'''(0)`, and products of lower derivatives. `U'(0)=V'(0)=0` kills many terms, but you still need a condition killing the relevant odd derivative term, e.g. `V'''(0)=0` in the even-reflection case. That is why merely `U,V ∈ C²` plus first Neumann data is not enough for the real one-sided Neumann limit.

The right direct theorem would require something like:

```lean
theorem chemDivLift_neumann_limits_of_flux_parity
    {p : CM2Params} {u v : intervalDomainPoint → ℝ}
    (hu_C3 : ContDiffOn ℝ 3 (intervalDomainLift u) (Icc 0 1))
    (hv_C4 : ContDiffOn ℝ 4 (intervalDomainLift v) (Icc 0 1))
    (hu_N0 : deriv (intervalDomainLift u) 0 = 0)
    (hu_N1 : deriv (intervalDomainLift u) 1 = 0)
    (hv_N0 : deriv (intervalDomainLift v) 0 = 0)
    (hv_N1 : deriv (intervalDomainLift v) 1 = 0)
    -- plus odd-derivative/parity conditions, e.g. V''' endpoint vanish and U''' as needed
    :
    Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 0 (Ioi 0)) (nhds 0) ∧
    Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 1 (Iio 1)) (nhds 0) := by
  sorry
```

But I would avoid this direct route unless you already have the endpoint parity lemmas. The cosine-series route is cleaner.

## Answer to the three options

### (a) Direct computation

Not the clean proof for the stated theorem. Direct computation is useful only for the genuine one-sided limit. For the two-sided zero-extension `deriv`, the endpoint value is dominated by the outside-zero branch and Mathlib's junk convention.

### (b) Symmetry / cosine parity

This is the clean proof for **genuine Neumann limits**. If the chem-div source has an even cosine-series representative with enough weighted summability, then the derivative is a sine series and the one-sided endpoint limits vanish. This is the right mathematical proof for weak-H² / source inversion.

### (c) Zero-extension

This is the clean proof for the theorem exactly as written. It proves the pointwise endpoint equations for ordinary `deriv` with no assumptions. It should be factored as a general lemma for `intervalDomainLift`.

## Recommendation

1. Replace the body of `chemDivLift_neumann_bc` with the zero-extension lemma proof. Keep the current assumptions only if downstream theorem signatures expect them.
2. Do **not** treat this as closing the chem-div source Neumann problem. The genuine source problem is the one-sided `Tendsto` pair needed by `intervalWeakH2Neumann_of_contDiffOn`.
3. For the real chem-div source tower, prefer a cosine/spectral theorem giving both:

```lean
ContDiffOn ℝ 2 (chemDivLift p u v) (Icc 0 1)
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 0 (Ioi 0)) (nhds 0)
Tendsto (deriv (chemDivLift p u v)) (nhdsWithin 1 (Iio 1)) (nhds 0)
```

The endpoint `deriv = 0` conjunct can then be discharged mechanically by zero-extension.
