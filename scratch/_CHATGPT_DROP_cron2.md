# Q851 (cron2) — extracting the heat resolver joint-C² datum

## Short answer

Yes, but extract the **resolver data lane**, not the whole `FluxJointC2Hyp` lane.
The right reusable object is a standalone heat-level lemma that produces the
`PhysicalResolverJointC2Data` used by `coupledChemical_jointContDiffAt_two`, and
then tiny wrappers for the two pointwise facts needed by `2A-sup`:

* resolver value joint C²:
  `coupledChemical_jointContDiffAt_two Hphys hx`
* resolver gradient joint C²:
  `coupledChemical_grad_jointContDiffAt_two Hphys hx`

This is exactly the same proof ingredient that sub-sorry 3C used inside the
`hfluxC2` construction, but without rebuilding the full factor-input record.

## Existing chain to reuse

The repo already has the generic physical chain:

```lean
FlooredSourceTimeData
  → PhysicalSourceTimeC2
  → PhysicalResolverJointC2Data
  → coupledChemical_jointContDiffAt_two
  → coupledChemical_grad_jointContDiffAt_two
```

The key existing producers are:

```lean
flooredSourceTimeData_of_iterate
physicalSourceTimeC2_of_floored
physicalResolverJointC2Data_of_floor
coupledChemical_jointContDiffAt_two
coupledChemical_grad_jointContDiffAt_two
```

So the heat-level extraction should not duplicate the bounded-weight series
assembler.  It should only package the heat-semigroup-specific construction of
the `FlooredSourceTimeData` / source envelopes that 3C already built inline.

## Recommended standalone theorem

Put this near `level0_chemDiv_timeDerivData`, or in a small helper imported by
`IntervalConjugateLevel0BFormSourceOn.lean`:

```lean
noncomputable theorem level0_physicalResolverJointC2Data
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M) :
    ∃ Bt : ℕ → ℕ → ℝ,
      PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0) Bt := by
  -- Extract the exact 3C construction here:
  --   1. construct the heat iterate time-C² source datum;
  --   2. form `Hfloor := flooredSourceTimeData_of_iterate Hiter`;
  --   3. set `Es := builtEs Hfloor`;
  --   4. prove the value/gradient bounded-weight summability majorants;
  --   5. set `Hsrc := physicalSourceTimeC2_of_floored Hfloor hval hgrad`;
  --   6. return `physicalResolverJointC2Data_of_floor Hsrc`.
```

If 3C already contains a direct `refine ⟨Bt, ...⟩` construction of
`PhysicalResolverJointC2Data`, copy that block into this theorem verbatim and
replace all local `τ`/ball assumptions by the positive-window facts derived from
`hc`, `hcT`, and `hpos`.

## Important caveat: global vs window-local data

Before committing the theorem shape above, check the quantifiers of the exact
3C proof you now have.

`PhysicalResolverJointC2Data` is a **global-in-time** structure: its coefficient
regularity and bounds are stated for all `t : ℝ`.  If the filled 3C proof really
built this exact structure for `u = conjugatePicardIter p u₀ 0`, then the theorem
above is the clean extraction.

If the filled 3C proof only established the data locally on a positive slab
around a fixed `τ`, do **not** force it into the global structure.  In that case,
extract the pointwise/window lemma instead:

```lean
theorem level0_coupledChemical_jointContDiffAt_two_on_window
    (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
    {c T M M₀ : ℝ} (hc : 0 < c) (hcT : c ≤ T)
    (hu₀_cont : Continuous u₀)
    (hu₀_bound : ∀ k, |heatCoeff u₀ k| ≤ M₀)
    (hpos : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x)
    (hub : ∀ σ ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      intervalDomainLift (conjugatePicardIter p u₀ 0 σ) x ≤ M)
    {s x : ℝ} (hs : s ∈ Icc c T) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s, x) := by
  -- same extracted proof, but only at `(s,x)` / on a positive local slab
```

and similarly:

```lean
theorem level0_coupledChemical_grad_jointContDiffAt_two_on_window ... :
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        deriv (intervalDomainLift
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1)) q.2)
      (s, x) := by
  ...
```

For `2A-sup`, the pointwise/window wrappers are actually enough and may be more
robust, because `2A-sup` only needs joint C² on the compact positive window
`[c,T] × [0,1]`, not a global time certificate.

## How to use it in `2A-sup`

Once the extracted lemma exists, the resolver part of the smooth representative
proof should become just:

```lean
have hv_c2 : ∀ s ∈ Icc c T, ∀ x ∈ Ioo (0 : ℝ) 1,
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ =>
        intervalDomainLift
          (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
      (s, x) := by
  intro s hs x hx
  exact level0_coupledChemical_jointContDiffAt_two_on_window
    p hc hcT hu₀_cont hu₀_bound hpos hub hs hx
```

Then use the corresponding gradient lemma for the flux derivative representative.
This is the missing resolver input for the compactness/sup-bound argument.

## Bottom line

The extraction is sound and is the right move.  The only design decision is:

* If 3C now constructs a genuine global `PhysicalResolverJointC2Data`, expose it
  as `level0_physicalResolverJointC2Data` and derive value/gradient C² wrappers
  from it.
* If 3C is only local to positive slabs, expose the window-local
  `level0_coupledChemical*_jointContDiffAt_two_on_window` lemmas instead.  That
  shape is sufficient for `2A-sup` and avoids over-strengthening the API.
