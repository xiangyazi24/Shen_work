# Q1032 (cron2/cron3) — audit of 1A and 2A-sup after `hfluxC2`

Static repo inspection only; I did **not** run Lean.

I read:

- `ShenWork/Paper2/IntervalConjugateLevel0BFormSourceOn.lean`, especially the block around the 1A and 2A-sup sorries.
- `ShenWork/PDE/IntervalChemDivOuterCommuteProducer.lean` for `CoupledChemDivFluxJointC2Hyp`.
- `ShenWork/PDE/IntervalChemDivFluxJointC2Producer.lean` for the factor-input shape.
- `ShenWork/Paper2/IntervalChemDivSpatialC2.lean` for how the per-slice `IntervalWeakH2Neumann.secondDeriv` is actually built.
- Existing compact-boundedness patterns in the repo, especially `IntervalConjugateLevel0BFormSourceOn.lean`'s `hMdot` block and `IntervalPicardIterateBddProducer.lean`.

## Executive verdict

No: proving `hfluxC2 : CoupledChemDivFluxJointC2Hyp p u` is **not by itself all the infrastructure needed** for 1A and 2A-sup.

The Mathlib compactness/boundedness part is already available and already used in the repo.  The real missing piece is an analytic bridge:

```text
local/interior flux joint C²
  ⟹ closed-slab continuous representative for the chemDiv source
  ⟹ closed-slab continuous representative for the weak-H² secondDeriv
```

For 2A-sup, `hfluxC2` gets close but still does not directly close the goal because compactness needs a continuous function on a compact **closed** slab, while the raw lift has endpoint/junk-derivative behavior.  The existing `hbdry_zero` solves endpoint values, but one still needs an interior agreement + closed representative theorem.

For 1A, the gap is larger: `hfluxC2` gives joint `C²` of the **flux**

```lean
Function.uncurry (coupledChemDivFluxLift p u)
```

on the interior.  But the weak-H² `secondDeriv` in 1A is the second derivative of the **source** `chemDiv = ∂ₓ flux`, i.e. it corresponds to a third spatial derivative of the flux representative.  So flux joint `C²` is not enough to bound `secondDeriv`; one needs the per-slice C⁴/cosine-representative route already used in `IntervalChemDivSpatialC2.lean`, plus joint-in-time continuity of that representative.

## Current shape of the relevant goals

In `IntervalConjugateLevel0BFormSourceOn.lean`, 1A is inside the uniform L¹ bound for the weak-H² second derivative:

```lean
have hunif_ptwise : ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
    ∀ x ∈ Icc (0 : ℝ) 1, |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  sorry -- [SUB-SORRY 1A: joint continuity + compactness → ptwise bound]
```

2A-sup is the uniform source sup bound:

```lean
have hsup_bound : ∃ (Msup : ℝ), 0 ≤ Msup ∧
    ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup := by
  ...
  have hbdry_zero : ∀ s, ∀ endpoint ∈ ({0, 1} : Set ℝ),
      coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s endpoint = 0 := by
    ...
  sorry -- [SUB-SORRY 2A-core]
```

After 2A-sup, the file already has the integrability bridge:

```lean
apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := Msup))
...
```

so for 2A, the only real issue is the sup bound.

## What `hfluxC2` actually gives

`CoupledChemDivFluxJointC2Hyp` currently has this shape:

```lean
structure CoupledChemDivFluxJointC2Hyp
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) : Prop where
  exists_local_slab : ∀ τ : ℝ, ∃ δ : ℝ, 0 < δ ∧
    (∀ᶠ s in 𝓝 τ,
      MeasureTheory.IntervalIntegrable (coupledChemDivSourceLift p u s)
        MeasureTheory.volume (0 : ℝ) 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      ContDiffAt ℝ 2
        (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun r : ℝ => deriv (coupledChemDivFluxLift p u r) x) =ᶠ[𝓝 s]
        (fun r : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (r, x) (0, 1))) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
      (fun y : ℝ => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
        (fun y : ℝ =>
          fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u))
            (s, y) (1, 0))) ∧
    ContinuousOn
      (Function.uncurry (coupledChemDivTimeDerivativeLift p u))
      (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

This is designed for the **time chain rule** and outer-commute step, not for the weak-H² envelope bound.  It provides:

1. source interval integrability near each `τ`,
2. interior joint `C²` of the flux,
3. spatial/time bridge fields for Clairaut,
4. closed-slab continuity of the **time derivative** field `coupledChemDivTimeDerivativeLift`.

It does **not** directly provide:

```lean
ContinuousOn (fun q => sourceRepresentative q) (Icc c T ×ˢ Icc 0 1)
```

nor

```lean
ContinuousOn (fun q => secondDerivRepresentative q) (Icc c T ×ˢ Icc 0 1)
```

which are the facts needed for 2A-sup and 1A respectively.

## Q1. Does `hfluxC2` directly give the joint continuity needed for 1A?

No.

There are two separate gaps.

### Gap 1: order of differentiability

1A bounds

```lean
(hH2_per_slice s hs).secondDeriv x
```

where `hH2_per_slice s hs : IntervalWeakH2Neumann (...)`.  The structure `IntervalWeakH2Neumann` has a field

```lean
secondDeriv : ℝ → ℝ
```

and the constructor in `IntervalChemDivSpatialC2.lean` builds it from the cosine representative as follows:

```lean
set F := deriv (chemFluxFun p.β U_cos V_cos)
...
have hF_H2 : IntervalWeakH2Neumann F :=
  intervalWeakH2Neumann_of_contDiffOn hF_C2on ...
...
exact {
  secondDeriv := hF_H2.secondDeriv
  ...
}
```

Since `F = deriv (chemFluxFun ...)` is the chemDiv source, `secondDeriv` is essentially

```lean
deriv (deriv F)
```

so it is the second spatial derivative of the source, i.e. the third spatial derivative of the flux.

But `hfluxC2` only gives

```lean
ContDiffAt ℝ 2 (Function.uncurry (coupledChemDivFluxLift p u)) (s, x)
```

for the flux.  That is enough to speak about the flux's second derivative, not the source's second derivative.  For 1A, one needs a source-`C²`/flux-`C³` closed representative.  The fixed-time file `IntervalChemDivSpatialC2.lean` obtains that by asking for global `C⁴` representatives of `U_cos` and `V_cos`, then using

```lean
chemFluxDeriv_contDiff_two
chemDivSource_weakH2_of_cosineRep
```

So 1A needs the **joint-in-time version** of that fixed-time cosine-representative route, not merely `hfluxC2`.

### Gap 2: identifying the exact `secondDeriv` field

Even if one has a continuous function

```lean
G2 : ℝ × ℝ → ℝ
```

intended to be the second derivative of the source, Lean still needs an agreement theorem such as

```lean
∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
  (hH2_per_slice s hs).secondDeriv x = G2 (s, x)
```

or at least a bound transfer theorem.  This is not supplied by `hfluxC2`.

The recommended 1A bridge is therefore a new lemma with a shape like:

```lean
lemma level0_chemDiv_H2_secondDeriv_uniform_bound
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {c T M₀ : ℝ}
    (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    -- joint closed-slab cosine representatives for U, V and enough derivatives:
    (HG2 : ∃ G2 : ℝ × ℝ → ℝ,
      ContinuousOn G2 (Icc c T ×ˢ Icc (0 : ℝ) 1) ∧
      ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
        (hH2_per_slice s hs).secondDeriv x = G2 (s, x)) :
    ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
      ∀ x ∈ Icc (0 : ℝ) 1,
        |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  ... -- compactness only
```

The compactness part of this lemma is routine; building `G2` is the missing analytic bridge.

## Q2. Does `hfluxC2` give the interior uniform sup bound for 2A-sup?

It gives the **right kind of interior regularity**, but not a direct closed-slab compact bound.

For 2A-sup, the source is the first spatial derivative of the flux:

```lean
coupledChemDivSourceLift p u s x
```

On `x ∈ Ioo 0 1`, `hfluxC2` plus its spatial bridge can identify this with the spatial derivative of the flux representative.  Since `hfluxC2` has `ContDiffAt ℝ 2` of the flux, it is enough to obtain local interior continuity of the source.

But compactness requires a continuous function on a compact set.  The interior slab

```lean
Icc c T ×ˢ Ioo 0 1
```

is not compact.  The raw lift is not the desired continuous closed representative at `x = 0,1`.  The file has already proved endpoint values are zero via `hbdry_zero`, which removes the boundary obstruction for the **bound**, but Lean still needs a uniform interior bound.

The clean bridge is a closed representative for the source:

```lean
∃ Gsrc : ℝ × ℝ → ℝ,
  ContinuousOn Gsrc (Icc c T ×ˢ Icc (0 : ℝ) 1) ∧
  (∀ s ∈ Icc c T, ∀ x ∈ Ioo (0 : ℝ) 1,
    coupledChemDivSourceLift p u s x = Gsrc (s, x)) ∧
  (∀ s ∈ Icc c T, ∀ x ∈ ({0,1} : Set ℝ),
    coupledChemDivSourceLift p u s x = 0)
```

Then compactness bounds `Gsrc`; the interior bound transfers by agreement; endpoint bound is `0 ≤ C` using `hbdry_zero`.

This is analogous to the `ChemDivMixedTimeDerivClosedRepr` pattern, but for the source rather than the time-derivative field.

### Code skeleton for 2A-sup once `Gsrc` exists

```lean
-- K is compact.
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc

-- Suppose we have a closed-slab representative of the source.
rcases hGsrc with ⟨Gsrc, hGsrc_cont, hGsrc_int, hbdry_zero⟩

-- Bound `|Gsrc|` on K.
have hGabs_cont : ContinuousOn (fun q : ℝ × ℝ => |Gsrc q|) K :=
  hGsrc_cont.abs

obtain ⟨B, hB_upper⟩ := hKcompact.bddAbove_image hGabs_cont

have hB_nonneg : 0 ≤ B := by
  have hmem : (c, (0 : ℝ)) ∈ K :=
    ⟨left_mem_Icc.mpr hcT, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩
  exact le_trans (abs_nonneg (Gsrc (c, 0)))
    (hB_upper (Set.mem_image_of_mem _ hmem))

refine ⟨B, hB_nonneg, ?_⟩
intro s hs x hx
rcases eq_or_lt_of_le hx.1 with hx0 | hx0
· -- x = 0
  subst x
  rw [hbdry_zero s hs 0 (by simp)]
  exact hB_nonneg
rcases eq_or_lt_of_le hx.2 with hx1 | hx1
· -- x = 1
  subst x
  rw [hbdry_zero s hs 1 (by simp)]
  exact hB_nonneg
· -- interior
  have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  rw [hGsrc_int s hs x hxIoo]
  exact hB_upper (Set.mem_image_of_mem _ ⟨hs, hx⟩)
```

This is precisely the correct closure pattern for 2A-sup.  `hfluxC2` can help prove `hGsrc_int`, but it does not itself package `Gsrc`.

## Q3. Existing Mathlib compact-boundedness theorems

Yes.  The repo already uses two good patterns.

### Pattern A: `IsCompact.exists_isMaxOn`

This is used in `IntervalPicardIterateBddProducer.exists_datum_source_coeff_bound`:

```lean
have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
have habs_cont : ContinuousOn
    (fun x => |logisticSourceFun p.a p.b p.α (intervalDomainLift u₀) x|)
    (Set.Icc (0 : ℝ) 1) := hcontSrc.abs
obtain ⟨x₀, hx₀mem, hx₀⟩ := hcompact.exists_isMaxOn
  (Set.nonempty_Icc.mpr (by norm_num)) habs_cont
exact ⟨|logisticSourceFun p.a p.b p.α (intervalDomainLift u₀) x₀|,
  fun x hx => hx₀ hx⟩
```

For a product compact set:

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

### Pattern B: `IsCompact.bddAbove_image`

This is already used in `IntervalConjugateLevel0BFormSourceOn.lean`'s `hMdot` block:

```lean
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
have hFcont_norm : ContinuousOn (fun p => ‖Function.uncurry F p‖) K :=
  hjointcont.norm
obtain ⟨B_sup, hB_sup⟩ := hKcompact.bddAbove_image hFcont_norm
```

Then it extracts the pointwise bound by:

```lean
have hmem : (s, x) ∈ K := ⟨hs, hx⟩
have : ‖Function.uncurry F (s, x)‖ ≤ B_sup :=
  hB_sup (Set.mem_image_of_mem _ hmem)
```

and proves nonnegativity of `B_sup` by evaluating at `(c,0)`.

This exact pattern should be used for both 1A and 2A-sup once the right closed-slab representatives are available.

## Minimal missing lemmas

To close 1A and 2A-sup cleanly, I would add two representative/bound lemmas.

### 2A source representative

```lean
/-- Closed-slab continuous representative of the chemDiv source on a positive Level0 window. -/
structure ChemDivSourceClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c T : ℝ) : Prop where
  Gsrc : ℝ × ℝ → ℝ
  cont : ContinuousOn Gsrc (Icc c T ×ˢ Icc (0 : ℝ) 1)
  agree_int : ∀ s ∈ Icc c T, ∀ x ∈ Ioo (0 : ℝ) 1,
    coupledChemDivSourceLift p u s x = Gsrc (s, x)
  bdry_zero : ∀ s ∈ Icc c T, ∀ x ∈ ({0,1} : Set ℝ),
    coupledChemDivSourceLift p u s x = 0
```

Then 2A-sup is compactness-only.

### 1A second-derivative representative

```lean
/-- Closed-slab continuous representative of the weak-H² second derivative selected
by `chemDivSource_weakH2_of_cosineRep`. -/
structure ChemDivH2SecondClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (c T : ℝ)
    (hH2 : ∀ s, s ∈ Icc c T → IntervalWeakH2Neumann (coupledChemDivSourceLift p u s)) : Prop where
  G2 : ℝ × ℝ → ℝ
  cont : ContinuousOn G2 (Icc c T ×ˢ Icc (0 : ℝ) 1)
  agree : ∀ s (hs : s ∈ Icc c T), ∀ x ∈ Icc (0 : ℝ) 1,
    (hH2 s hs).secondDeriv x = G2 (s, x)
```

Then 1A is compactness-only:

```lean
rcases H2repr with ⟨G2, hG2cont, hG2agree⟩
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_Icc
have hAbsCont : ContinuousOn (fun q => |G2 q|) K := hG2cont.abs
obtain ⟨q₀, hq₀K, hmax⟩ := hKcompact.exists_isMaxOn
  (by refine ⟨(c,0), ?_⟩; exact ⟨left_mem_Icc.mpr hcT, left_mem_Icc.mpr (by norm_num)⟩)
  hAbsCont
refine ⟨|G2 q₀|, abs_nonneg _, ?_⟩
intro s hs x hx
rw [hG2agree s hs x hx]
exact hmax ⟨hs, hx⟩
```

## Final answers to the questions

### 1. Once `hfluxC2` is proved, does it directly give the joint continuity needed for 1A?

No.  It gives interior joint `C²` of the flux, but 1A needs a uniform bound on the weak-H² `secondDeriv` of the source.  That is essentially a second derivative of `chemDiv = ∂ₓ flux`, so it needs a higher-order closed representative and an agreement theorem with the specific `secondDeriv` field.  Existing fixed-time infrastructure (`chemDivSource_weakH2_of_cosineRep`, `chemFluxDeriv_contDiff_two`) is useful, but the joint-in-time closed-slab representative is not currently packaged.

### 2. For 2A-sup, does `hfluxC2` give the interior uniform sup bound?

It gives the right interior differentiability input, but not the finished uniform bound.  With `hbdry_zero`, the remaining bridge is a closed-slab continuous source representative `Gsrc` agreeing with `coupledChemDivSourceLift` on the interior.  Once `Gsrc` exists, compactness gives the bound immediately.  `hfluxC2` alone does not provide `Gsrc`, and its closed-slab continuity field is for `coupledChemDivTimeDerivativeLift`, not for the source.

### 3. Are there existing Mathlib theorems directly applicable?

Yes.  Use either:

```lean
IsCompact.exists_isMaxOn
```

or

```lean
IsCompact.bddAbove_image
```

The repo already uses both patterns.  The current `IntervalConjugateLevel0BFormSourceOn.lean` uses `isCompact_Icc.prod isCompact_Icc`, `ContinuousOn.norm`, and `hKcompact.bddAbove_image` in the `hMdot` block.  `IntervalPicardIterateBddProducer.lean` uses `hcompact.exists_isMaxOn` to bound a continuous function on `[0,1]`.

So the compactness machinery is present and directly usable.  The remaining work is analytic packaging of the correct closed representatives and agreement lemmas, not Mathlib boundedness.
