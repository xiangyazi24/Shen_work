# Q849 / cron1: compact maximum for `2A-sup`

Repo inspected: `xiangyazi24/Shen_work`

Source ref inspected: `main`

Branch written: `chatgpt-scratch`

## Verdict

Yes.  The pinned Mathlib has exactly:

```lean
IsCompact.exists_isMaxOn
```

in

```text
Mathlib/Topology/Order/Compact.lean
```

Its statement is:

```lean
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x
```

So for a real-valued continuous function on a compact box, this is the right theorem.

## Repo precedent

The repo already uses the exact pattern in:

```text
ShenWork/Wiener/EWA/ResolverSliceWindowBounds.lean
```

There, it sets a compact box

```lean
W ×ˢ Set.Icc (0 : ℝ) 1
```

proves compactness by

```lean
have hKcompact : IsCompact (W ×ˢ Set.Icc (0 : ℝ) 1) :=
  (isCompact_Icc).prod isCompact_Icc
```

proves nonemptiness, then obtains the max by:

```lean
obtain ⟨q₁, _, hq₁max⟩ := hKcompact.exists_isMaxOn hKne hFcont
```

and uses the `IsMaxOn` proof directly as:

```lean
exact hq₁max (Set.mem_prod.mpr ⟨hσ, hx⟩)
```

That is exactly the shape needed for `[c,T] × [0,1]`.

## Suggested `2A-sup` compact-bound skeleton

For the smooth representative, do this over the closed compact box:

```lean
set K : Set (ℝ × ℝ) := Set.Icc c T ×ˢ Set.Icc (0 : ℝ) 1
set G : ℝ × ℝ → ℝ := fun q => |smoothRep q.1 q.2|

have hKcompact : IsCompact K := by
  simpa [K] using (isCompact_Icc.prod isCompact_Icc)

have hKne : K.Nonempty := by
  refine ⟨(c, 0), ?_⟩
  exact Set.mem_prod.mpr ⟨Set.left_mem_Icc.mpr hcT, by norm_num⟩

have hGcont : ContinuousOn G K := by
  -- from joint continuity of `smoothRep`, composed with `abs`
  -- e.g. `exact hSmooth.continuousOn.abs` or a small `simpa [G]` variant
  ...

obtain ⟨qmax, hqmax_mem, hqmax⟩ := hKcompact.exists_isMaxOn hKne hGcont

refine ⟨G qmax, ?_, ?_⟩
· exact abs_nonneg _
· intro s hs x hx
  -- For the smooth representative itself:
  have hle_smooth : |smoothRep s x| ≤ G qmax := by
    simpa [G] using hqmax (Set.mem_prod.mpr ⟨hs, hx⟩)
  ...
```

For `2A-sup`, the last `...` splits on the spatial point:

```lean
by_cases hxIoo : x ∈ Set.Ioo (0 : ℝ) 1
```

* Interior: rewrite `coupledChemDivSourceLift ... s x` to `smoothRep s x`, using the interior agreement (`coupledChemDivSourceLift_eq_deriv_fluxLift_interior` plus the definition of the smooth representative).
* Boundary: from `x ∈ Icc 0 1` and `¬ x ∈ Ioo 0 1`, derive `x = 0 ∨ x = 1`; then use the endpoint fact that the zero-extension derivative/source value is `0`, so the absolute value is `0 ≤ G qmax`.

A useful boundary splitter is:

```lean
have hx_boundary : x = 0 ∨ x = 1 := by
  rcases hx with ⟨hx0, hx1⟩
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hxIoo
  rcases hxIoo with hxle0 | hxge1
  · exact Or.inl (le_antisymm hxle0 hx0)
  · exact Or.inr (le_antisymm hx1 hxge1)
```

## Important caveat

The compact maximum theorem gives a max for a **continuous** function on the **closed box**.  For this route, apply it to the smooth representative's absolute value:

```lean
G(s,x) = |smoothRep s x|
```

not to `|coupledChemDivSourceLift ... s x|`, because the latter is exactly the closed-boundary discontinuous object.

## Answer to the route

Your 5-step route is right, with this Lean-side wording:

1. Prove joint `ContinuousOn` of `smoothRep` on `Set.Icc c T ×ˢ Set.Icc 0 1`.
2. Apply `IsCompact.exists_isMaxOn` to `G q = |smoothRep q.1 q.2|` over that compact box.
3. Interior points: transfer by source/smooth-representative agreement on `Ioo 0 1`.
4. Boundary points: prove/consume the endpoint lemma that `coupledChemDivSourceLift ... s 0 = 0` and `... s 1 = 0`.
5. Use the max value `G qmax` as `Msup`.

This is also aligned with the current `hSup` comment in `IntervalConjugateLevel0BFormSourceOn.lean`: `2A-sup` is now a sup-bound problem, not a `ContinuousOn` problem for the actual source lift.
