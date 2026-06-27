# Q1035 (cron2/cron3) — can 1A and 2A-sup be proved directly from `hlocal_slab`?

Static repo inspection only; I did **not** run Lean.

I read `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean` at ref `9dd3a4b`, focusing on:

- the 1A block inside `hL1_uniform`, around the `hunif_ptwise` sorry;
- the 2A-sup block inside `hSup`, around `hbdry_zero` and `hsup_bound`;
- the new positive-window `hlocal_slab` inside `level0_chemDiv_timeDerivData`.

## Executive verdict

No.  The new `hlocal_slab` is the right replacement for the old global `CoupledChemDivFluxJointC2Hyp` in the **time-C¹ coefficient chain**.  It avoids the impossible `τ ≤ 0` branch and gives exactly what `cosineCoeffs_hasDerivAt_of_smooth_param` needs later.

But `hlocal_slab` does **not** directly close 1A or 2A-sup.

The reason is simple: `hlocal_slab` packages local **time-chain-rule** data for the chemDiv source and closed-slab continuity of the **time derivative field**

```lean
coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)
```

whereas 1A and 2A-sup need closed-slab boundedness of either:

```lean
coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0)
```

or the weak-H² `secondDeriv` selected by `hH2_per_slice`.

The compactness/Mathlib part is not the problem; it is already present.  The missing piece is still a closed-slab continuous **source representative** and, for 1A, a closed-slab continuous **H² second-derivative representative**.

## What `hlocal_slab` gives after `9dd3a4b`

In `level0_chemDiv_timeDerivData`, the new local package is:

```lean
have hlocal_slab : ∀ s, s ∈ Icc c T → ∃ δ : ℝ, 0 < δ ∧
  (∀ᶠ r in 𝓝 s,
    MeasureTheory.IntervalIntegrable
      (coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r)
      MeasureTheory.volume (0 : ℝ) 1) ∧
  (∀ x ∈ Ioo (0 : ℝ) 1, ∀ r ∈ Metric.ball s δ,
    HasDerivAt
      (fun t => coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) t x)
      (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) r x) r) ∧
  ContinuousOn
    (Function.uncurry
      (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
    (Icc (s - δ) (s + δ) ×ˢ Icc (0 : ℝ) 1)
```

The file then derives a global-window continuity fact from this:

```lean
have hjointcont : ContinuousOn
    (Function.uncurry (coupledChemDivTimeDerivativeLift
      p (conjugatePicardIter p u₀ 0)))
    (Icc c T ×ˢ Icc (0 : ℝ) 1) := by
  ...
```

That `hjointcont` is for the **time derivative field**.  It is later used exactly where it belongs: to prove `ContinuousOn (fun s => adot s n)` and a uniform coefficient derivative bound `hMdot` by compactness of the time-derivative field.

It does not assert that the source itself is jointly continuous on the closed slab, nor that the H² second derivative is jointly continuous.

## Q1. Does `hlocal_slab` directly imply joint continuity on `[c,T] × [0,1]`?

Only for the field it explicitly carries:

```lean
Function.uncurry (coupledChemDivTimeDerivativeLift p u)
```

The file already derives this as `hjointcont`.

It does **not** directly imply joint continuity of:

```lean
Function.uncurry (fun s x => coupledChemDivSourceLift p u s x)
```

or of a smooth representative of that source.

The second field of `hlocal_slab`,

```lean
HasDerivAt
  (fun t => coupledChemDivSourceLift p u t x)
  (coupledChemDivTimeDerivativeLift p u r x) r
```

is only time differentiability at each fixed interior `x`.  It gives time-continuity pointwise in `x` for interior `x`, but it gives neither spatial continuity nor joint continuity on the closed set.  It also does not address endpoint behavior of `intervalDomainLift`.

So the answer is: **no, not directly**.  It proves the right `hjointcont` for coefficient time-C¹; it does not give the source closed-slab continuity needed for 2A-sup.

## Q2. Can 1A be proved from `hlocal_slab` alone?

No.

1A bounds:

```lean
|(hH2_per_slice s hs).secondDeriv x|
```

where `hH2_per_slice s hs` is an `IntervalWeakH2Neumann` certificate for the chemDiv source.  In `IntervalChemDivSpatialC2.lean`, the per-slice H² datum is built by the cosine-representative route:

```lean
set F := deriv (chemFluxFun p.β U_cos V_cos)
...
secondDeriv := hF_H2.secondDeriv
```

So this `secondDeriv` is the second spatial derivative of the chemDiv source representative `F`, equivalently a third spatial derivative of the flux representative.

`hlocal_slab` only gives:

1. eventual interval integrability of the source;
2. time `HasDerivAt` of the source at interior points;
3. closed-slab continuity of the source's time derivative.

It gives no closed-slab representative for the selected `secondDeriv`, and it gives no higher spatial regularity field from which to derive it.  The 1A comments in the file are still accurate: one needs joint-in-time control of the smooth cosine representative and its relevant spatial derivatives, e.g.

```lean
∃ G2 : ℝ × ℝ → ℝ,
  ContinuousOn G2 (Icc c T ×ˢ Icc (0 : ℝ) 1) ∧
  ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
    (hH2_per_slice s hs).secondDeriv x = G2 (s, x)
```

Once such a `G2` exists, 1A is compactness-only.  But `hlocal_slab` alone does not construct `G2`.

## Q3. Does `hlocal_slab + hbdry_zero` suffice for 2A-sup?

Still no.

The existing `hbdry_zero` is useful and removes the endpoint-value problem:

```lean
have hbdry_zero : ∀ s, ∀ endpoint ∈ ({0, 1} : Set ℝ),
  coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s endpoint = 0
```

But for a uniform bound on all of

```lean
Icc c T ×ˢ Icc 0 1
```

one still needs a uniform interior bound.  `hlocal_slab` gives time differentiability of the source at each interior point, not a compact-domain continuous source representative.

The right missing lemma is a closed-slab source representative, for example:

```lean
structure ChemDivSourceClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c T : ℝ) : Prop where
  Gsrc : ℝ × ℝ → ℝ
  cont : ContinuousOn Gsrc (Icc c T ×ˢ Icc (0 : ℝ) 1)
  agree_int : ∀ s ∈ Icc c T, ∀ x ∈ Ioo (0 : ℝ) 1,
    coupledChemDivSourceLift p u s x = Gsrc (s, x)
  bdry_zero : ∀ s ∈ Icc c T, ∀ x ∈ ({0, 1} : Set ℝ),
    coupledChemDivSourceLift p u s x = 0
```

For heat Level0, `Gsrc` should be the smooth cosine-series representative

```lean
Gsrc (s, x) = deriv (chemFluxFun p.β U_cos(s, ·) V_cos(s, ·)) x
```

or a `mixedAlgebra`-style explicit representative for the source.  It should be proved continuous on the closed positive-time slab from joint smoothness of heat and resolver representatives.  Then:

- interior bound transfers by `agree_int`;
- boundary bound transfers by `bdry_zero`;
- compactness gives the uniform `Msup`.

So `hlocal_slab + hbdry_zero` is not enough; it lacks the `Gsrc` closed representative and agreement theorem.

## Q4. Existing Mathlib infrastructure for compact boundedness

Yes.  This part is already available and already used in the repo.

### Pattern A: `IsCompact.bddAbove_image`

The current file already uses this pattern in the `hMdot` proof:

```lean
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
have hFcont_norm : ContinuousOn (fun p => ‖Function.uncurry F p‖) K :=
  hjointcont.norm
obtain ⟨B_sup, hB_sup⟩ := hKcompact.bddAbove_image hFcont_norm
```

Then pointwise extraction is:

```lean
have hmem : (s, x) ∈ K := ⟨hs, hx⟩
have : ‖Function.uncurry F (s, x)‖ ≤ B_sup :=
  hB_sup (Set.mem_image_of_mem _ hmem)
```

This works directly for `Gsrc` or `G2` once those continuous representatives exist.

### Pattern B: `IsCompact.exists_isMaxOn`

The repo also uses:

```lean
hcompact.exists_isMaxOn hnonempty hcont
```

for example in `IntervalPicardIterateBddProducer.exists_datum_source_coeff_bound`, where it bounds a continuous source on `Icc 0 1`.

For a product slab, the pattern is:

```lean
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
have hKnonempty : K.Nonempty := by
  refine ⟨(c, 0), ?_⟩
  exact ⟨left_mem_Icc.mpr hcT, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩

have hAbsCont : ContinuousOn (fun q => |G q|) K := hGcont.abs
obtain ⟨q₀, hq₀K, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty hAbsCont
refine ⟨|G q₀|, abs_nonneg _, ?_⟩
intro s hs x hx
exact hmax ⟨hs, hx⟩
```

## Compactness-only code for 2A-sup after `Gsrc`

Once a source representative exists, the 2A-sup core should look like this:

```lean
-- Suppose:
-- Hsrc.Gsrc      : ℝ × ℝ → ℝ
-- Hsrc.cont      : ContinuousOn Hsrc.Gsrc K
-- Hsrc.agree_int : source = Gsrc on interior
-- Hsrc.bdry_zero : source = 0 at x = 0,1

set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
have hGabs_cont : ContinuousOn (fun q : ℝ × ℝ => |Hsrc.Gsrc q|) K :=
  Hsrc.cont.abs

obtain ⟨B, hB_upper⟩ := hKcompact.bddAbove_image hGabs_cont

have hB_nonneg : 0 ≤ B := by
  have hmem : (c, (0 : ℝ)) ∈ K :=
    ⟨left_mem_Icc.mpr hcT, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩
  exact le_trans (abs_nonneg (Hsrc.Gsrc (c, 0)))
    (hB_upper (Set.mem_image_of_mem _ hmem))

refine ⟨B, hB_nonneg, ?_⟩
intro s hs x hx
rcases eq_or_lt_of_le hx.1 with hx0 | hx0
· subst x
  rw [Hsrc.bdry_zero s hs 0 (by simp)]
  exact hB_nonneg
rcases eq_or_lt_of_le hx.2 with hx1 | hx1
· subst x
  rw [Hsrc.bdry_zero s hs 1 (by simp)]
  exact hB_nonneg
· have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  rw [Hsrc.agree_int s hs x hxIoo]
  exact hB_upper (Set.mem_image_of_mem _ ⟨hs, hx⟩)
```

## Compactness-only code for 1A after `G2`

Once the H² second-derivative representative exists:

```lean
-- Suppose:
-- H2repr.G2    : ℝ × ℝ → ℝ
-- H2repr.cont  : ContinuousOn H2repr.G2 K
-- H2repr.agree : (hH2_per_slice s hs).secondDeriv x = H2repr.G2 (s,x)

set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
have hAbsCont : ContinuousOn (fun q : ℝ × ℝ => |H2repr.G2 q|) K :=
  H2repr.cont.abs
have hKnonempty : K.Nonempty := by
  refine ⟨(c, 0), ?_⟩
  exact ⟨left_mem_Icc.mpr hcT, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩

obtain ⟨q₀, hq₀K, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty hAbsCont
refine ⟨|H2repr.G2 q₀|, abs_nonneg _, ?_⟩
intro s hs x hx
rw [H2repr.agree s hs x hx]
exact hmax ⟨hs, hx⟩
```

## Direct answers

### 1. Does `hlocal_slab` directly imply joint continuity on the closed compact set?

No.  It directly implies joint continuity on the closed compact set only for

```lean
coupledChemDivTimeDerivativeLift
```

and the file already derives `hjointcont` for that.  It does not imply joint continuity of the source or of the H² second derivative.

### 2. Can 1A be proved from `hlocal_slab` alone?

No.  1A needs a closed-slab continuous representative for `(hH2_per_slice s hs).secondDeriv`.  `hlocal_slab` has no field identifying or controlling this `secondDeriv`, and it does not carry the higher spatial regularity needed to build it.

### 3. Does `hlocal_slab + hbdry_zero` suffice for 2A-sup?

No.  `hbdry_zero` handles endpoints, but the interior still needs a uniform bound.  `hlocal_slab` gives time differentiability at each interior point, not closed-slab source continuity or boundedness.  Add a closed-slab source representative `Gsrc`; then `hbdry_zero + Gsrc + compactness` suffices.

### 4. Is there existing Mathlib infrastructure for continuous-on-compact implies bounded?

Yes.  Use either `IsCompact.bddAbove_image` or `IsCompact.exists_isMaxOn`.  Both patterns are already present in the repo.  The current file already uses `isCompact_Icc.prod isCompact_Icc` plus `hKcompact.bddAbove_image` in the `hMdot` block; `IntervalPicardIterateBddProducer.lean` uses `exists_isMaxOn`.

## Bottom line

`hlocal_slab` is sufficient for the time-coefficient derivative route (`hderiv`, `hadotcont`, and `hMdot`).  It is not sufficient for 1A or 2A-sup.  Those should be closed by adding two representative lemmas:

1. `ChemDivSourceClosedRepr` for the source itself;
2. `ChemDivH2SecondClosedRepr` for the chosen weak-H² `secondDeriv`.

After those are available, 1A and 2A-sup are compactness exercises using existing Mathlib/repo patterns.
