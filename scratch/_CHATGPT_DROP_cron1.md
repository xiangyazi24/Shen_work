# Q1335 / cron1 — wiring the remaining Level0 `IntervalConjugateLevel0BFormSourceOn` sorries

Repo: `xiangyazi24/Shen_work`

Branch written: `chatgpt-scratch`

Target file updated by this drop:

```text
scratch/_CHATGPT_DROP_cron1.md
```

## Executive answer

The four remaining Level0 gaps split into two different kinds of wiring.

* **SORRY 1A and 2A** are compactness-bound gaps.  The Lean API you want is the same pattern already used elsewhere in the repo:

  ```lean
  hK.exists_isMaxOn hK_nonempty hcont.abs
  ```

  where `hK : IsCompact K`, usually

  ```lean
  have hK : IsCompact (Icc c T ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  ```

  Then take the maximum of the absolute value on the compact set.  The crucial input is **not merely pointwise `ContDiffAt`**; it is a `ContinuousOn` representative of the actual quantity you want to bound on the whole closed slab.

* **SORRY 3C+3D+3F** is the local chain-rule/outer-commute gap.  The existing producer is:

  ```lean
  coupledChemDivFlux_timeBridge_of_physicalJointC2
  ```

  in `IntervalChemDivFACCommuteDischarge.lean`.  It expects a `PhysicalResolverJointC2Data`, not just the direct theorem `heatResolver_jointContDiffAt_two`.  If you only have the direct cutoff theorems, either package them into a direct analogue of the physical bridge or create `PhysicalResolverJointC2Data` first.  Also: value C² alone is not enough; the bridge needs resolver value **and gradient** C².

* **SORRY 3G** is the closed-slab continuity of `coupledChemDivTimeDerivativeLift`.  The existing producer is:

  ```lean
  chemDivMixedTimeDeriv_jointContinuousOn_closed
  ```

  in `IntervalChemDivTimeDerivClosed.lean`, but it consumes a closed-slab spectral representative:

  ```lean
  ChemDivMixedTimeDerivClosedRepr p u τ δ
  ```

  For heat Level0, the intended constructor is already sketched in:

  ```text
  ShenWork/Paper2/IntervalLevel0HeatMixedRepr.lean
  ```

  namely:

  ```lean
  chemDivMixedTimeDerivClosedRepr_level0
  ```

  That theorem still has its own representative-continuity/agreement sorries, but it is the exact path to 3G.

## Imports to add to `IntervalConjugateLevel0BFormSourceOn.lean`

At minimum, for the wiring discussed here:

```lean
import ShenWork.Paper2.IntervalHeatResolverJointC2
import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
import ShenWork.PDE.IntervalChemDivTimeDerivClosed
import ShenWork.Paper2.IntervalLevel0HeatMixedRepr
```

The file currently imports `IntervalChemDivTimeDerivative`, but not the later FAC commute discharge or closed mixed-time representative files.

## 1. SORRY 1A: uniform pointwise bound for `secondDeriv`

Target shape at line ~756:

```lean
have hunif_ptwise : ∃ C, 0 ≤ C ∧ ∀ s (hs : s ∈ Icc c T),
    ∀ x ∈ Icc (0 : ℝ) 1, |(hH2_per_slice s hs).secondDeriv x| ≤ C := by
  sorry
```

### Compactness API

Use:

```lean
isCompact_Icc.prod isCompact_Icc
```

and:

```lean
IsCompact.exists_isMaxOn
```

The repo already uses this exact pattern in `IntervalPicardIterateBddProducer.lean`:

```lean
have hcompact : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
have habs_cont : ContinuousOn (fun x => |logisticSourceFun ... x|) (Set.Icc (0 : ℝ) 1) := ...
obtain ⟨x₀, hx₀mem, hx₀⟩ := hcompact.exists_isMaxOn
  (Set.nonempty_Icc.mpr (by norm_num)) habs_cont
exact ⟨|logisticSourceFun ... x₀|, fun x hx => hx₀ hx⟩
```

For the product slab, the skeleton is:

```lean
-- K = [c,T] × [0,1]
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hK : IsCompact K := by
  simpa [K] using (isCompact_Icc.prod isCompact_Icc)

have hK_nonempty : K.Nonempty := by
  refine ⟨(c, 0), ?_⟩
  simp [K]
  constructor
  · exact ⟨le_rfl, hcT⟩       -- `hcT : c ≤ T` is already in this theorem branch
  · exact ⟨le_rfl, by norm_num⟩

-- This is the *real* missing input: continuous representative of the second derivative.
-- Fdd must be definitionally or propositionally equal to `(hH2_per_slice s hs).secondDeriv x`.
have hFdd_cont : ContinuousOn Fdd K := by
  -- from joint source-C² / representative construction
  sorry

obtain ⟨q₀, hq₀, hmax⟩ := hK.exists_isMaxOn hK_nonempty hFdd_cont.abs

refine ⟨|Fdd q₀|, abs_nonneg _, ?_⟩
intro s hs x hx
have hqx : (s, x) ∈ K := by
  simp [K, hs, hx]
calc
  |(hH2_per_slice s hs).secondDeriv x|
      = |Fdd (s, x)| := by
          -- bridge from the `IntervalWeakH2Neumann` secondDeriv to the smooth rep
          sorry
  _ ≤ |Fdd q₀| := hmax hqx
```

### Important refactor note

Do not try to get this directly from the abstract `hH2_per_slice : IntervalWeakH2Neumann ...` unless that structure still exposes enough definitional equality for `secondDeriv`.  The compactness proof needs a concrete jointly continuous representative:

```lean
Fdd : ℝ × ℝ → ℝ
```

with an agreement lemma:

```lean
∀ s hs x hx, (hH2_per_slice s hs).secondDeriv x = Fdd (s, x)
```

If that equality is not available, refactor `hH2_per_slice` to return it alongside the H² package.

## 2. SORRY 2A: uniform sup bound for `coupledChemDivSourceLift`

Target shape at line ~894:

```lean
have hsup_bound : ∃ (Msup : ℝ), 0 ≤ Msup ∧
    ∀ s ∈ Icc c T, ∀ x ∈ Icc (0 : ℝ) 1,
      |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x| ≤ Msup := by
  sorry
```

Yes, this is the same compactness pattern as 1A, but with the **source value** representative instead of the second derivative representative.

Use a jointly continuous representative:

```lean
Fsrc : ℝ × ℝ → ℝ
```

such that:

```lean
∀ s ∈ Icc c T, ∀ x ∈ Ioo (0 : ℝ) 1,
  coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x = Fsrc (s, x)
```

and handle endpoints with the already-proved `hbdry_zero` block in the file.

Skeleton:

```lean
set K : Set (ℝ × ℝ) := Icc c T ×ˢ Icc (0 : ℝ) 1
have hK : IsCompact K := by
  simpa [K] using (isCompact_Icc.prod isCompact_Icc)
have hK_nonempty : K.Nonempty := by
  refine ⟨(c, 0), ?_⟩
  simp [K]
  exact ⟨⟨le_rfl, hcT⟩, ⟨le_rfl, by norm_num⟩⟩

have hFsrc_cont : ContinuousOn Fsrc K := by
  -- from joint C² of heat/resolver + flux composition
  sorry

obtain ⟨q₀, hq₀, hmax⟩ := hK.exists_isMaxOn hK_nonempty hFsrc_cont.abs

refine ⟨|Fsrc q₀|, abs_nonneg _, ?_⟩
intro s hs x hx
rcases lt_trichotomy x 0 with hxlt | hxeq0 | hxgt0
-- easier: split by `x = 0`, `x = 1`, otherwise interior using `hx`
```

A cleaner split under `hx : x ∈ Icc 0 1`:

```lean
by_cases hx0 : x = 0
· subst hx0
  have hz := hbdry_zero s 0 (by simp)
  rw [hz]
  exact abs_nonneg _ |> le_trans ?_ -- or `simpa [abs_zero] using abs_nonneg (Fsrc q₀)`
by_cases hx1 : x = 1
· subst hx1
  have hz := hbdry_zero s 1 (by simp)
  rw [hz]
  exact by simpa using abs_nonneg (Fsrc q₀)
· have hxIoo : x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  calc
    |coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) s x|
        = |Fsrc (s, x)| := by rw [hFsrc_agree s hs x hxIoo]
    _ ≤ |Fsrc q₀| := hmax (by simp [K, hs, hx])
```

Again, the core API is `exists_isMaxOn`; the real analytic input is the jointly continuous representative and its agreement.  Boundary discontinuity of the raw lift is not a blocker because `hbdry_zero` handles `{0,1}`.

## 3. SORRY 3C+3D+3F: chain-rule `HasDerivAt`

The target at line ~1547 is inside the `exists_local_slab` field for the local chain rule:

```lean
∀ x ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Metric.ball τ δ,
  HasDerivAt
    (fun r => coupledChemDivSourceLift p (conjugatePicardIter p u₀ 0) r x)
    (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0) s x) s
```

There are two viable wiring paths.

### Path A: use the existing physical FAC producer

Existing theorem:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivFlux_timeBridge_of_physicalJointC2
```

Signature, abbreviated:

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

But note: this theorem expects:

```lean
H : PhysicalResolverJointC2Data p u Bt
```

not just

```lean
heatResolver_jointContDiffAt_two ...
```

So if you want to use it verbatim, first obtain a physical resolver package from source-side physical data:

```lean
have Hsrc : PhysicalSourceTimeC2 p (conjugatePicardIter p u₀ 0) Es := ...
have Hres : PhysicalResolverJointC2Data p (conjugatePicardIter p u₀ 0)
    (fun i k => intervalNeumannResolverWeight p k * Es i k) :=
  ShenWork.IntervalPhysicalResolverDataConcrete.physicalResolverJointC2Data_of_floor Hsrc
```

Then:

```lean
have hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
    ContDiffAt ℝ 2
      (fun q : ℝ × ℝ => intervalDomainLift (conjugatePicardIter p u₀ 0 q.1) q.2)
      (s, x) := by
  intro x hx s
  -- use heat semigroup joint regularity and the already-present bridge in the file
  -- from the heat cosine series to `intervalDomainLift (conjugatePicardIter ... 0)`.
  sorry

have hbase_all : ∀ s : ℝ, ∀ x : ℝ,
    0 < 1 + intervalDomainLift
      (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) s) x := by
  -- globalize the hbase proof already present at the point, or use
  -- `coupledChemical_floor_pos_of_nonneg_continuous` if you can supply `u` continuity/nonnegativity.
  sorry

have hflux_time_bridge :=
  ShenWork.IntervalCoupledRegularityBootstrap
    .coupledChemDivFlux_timeBridge_of_physicalJointC2
      (p := p) (u := conjugatePicardIter p u₀ 0)
      Hres hu_c2 hbase_all (s := s) (x := x) hx
```

Then combine with the outer-commute bridge already present in `IntervalChemDivOuterCommute.lean`:

```lean
coupledChemDivSourceLift_eq_deriv_fluxLift_interior
coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative
```

The full path is:

```text
PhysicalResolverJointC2Data
  → coupledChemical_jointContDiffAt_two
  → coupledChemical_grad_jointContDiffAt_two
  → coupledChemical_innerCommute_of_physicalJointC2
  → coupledChemDivFlux_timeBridge_of_physicalJointC2
  → coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
  → real_twoVar_clairaut_hasDerivAt_of_fderiv_partials
  → coupledChemDivOuterCommuteAtoms_of_fluxJointC2
  → coupledChemDivLocalChainRule_of_outerCommuteAtoms
```

The shortest way to use that stack is to build a `CoupledChemDivFluxJointC2Hyp` and then call:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.coupledChemDivLocalChainRule_of_fluxJointC2
```

because that returns the exact `CoupledChemDivLocalChainRule` package whose `exists_local_slab` field has the HasDerivAt you need.

### Path B: direct-cutoff analogue, avoiding `PhysicalResolverJointC2Data`

If the premise is specifically “once `heatResolver_jointContDiffAt_two` is proved”, and you do not have `PhysicalResolverJointC2Data`, write a direct analogue of `coupledChemical_innerCommute_of_physicalJointC2` and `coupledChemDivFlux_timeBridge_of_physicalJointC2` where the inputs are:

```lean
hv_c2 : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
  ContDiffAt ℝ 2
    (fun q : ℝ × ℝ => intervalDomainLift
      (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1) q.2)
    (s, y)

hgradv_c2 : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
  ContDiffAt ℝ 2
    (fun q : ℝ × ℝ => deriv (intervalDomainLift
      (coupledChemicalConcentration p (conjugatePicardIter p u₀ 0) q.1)) q.2)
    (s, y)
```

For `hv_c2`, use:

```lean
ShenWork.Paper2.HeatResolverJointC2Direct.heatResolver_jointContDiffAt_two
```

For `hgradv_c2`, you also need:

```lean
ShenWork.Paper2.HeatResolverJointC2Direct.heatResolver_grad_jointContDiffAt_two
```

The value theorem alone does not supply 3D.  Once both direct cutoff theorems are present, the direct wrapper is just the body of `coupledChemical_innerCommute_of_physicalJointC2` with the two calls replaced by `hv_c2`/`hgradv_c2`, and then the body of `coupledChemDivFlux_timeBridge_of_physicalJointC2` with the eventuallies built from direct hypotheses.

Skeleton:

```lean
theorem coupledChemical_innerCommute_of_directJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hv_c2 : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => intervalDomainLift
          (coupledChemicalConcentration p u q.1) q.2) (s, y))
    {s y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun r => deriv (intervalDomainLift (coupledChemicalConcentration p u r)) y)
      (deriv (coupledChemicalTimeDerivativeLift p u s) y) s := by
  -- copy `coupledChemical_innerCommute_of_physicalJointC2`, replacing
  -- `coupledChemical_jointContDiffAt_two H hy` by `hv_c2 hy ...`.
  sorry
```

Then:

```lean
theorem coupledChemDivFlux_timeBridge_of_directJointC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    (hv_c2 : ...)
    (hgradv_c2 : ...)
    (hu_c2 : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ,
      ContDiffAt ℝ 2 (fun q => intervalDomainLift (u q.1) q.2) (s, x))
    (hbase : ∀ s x, 0 < 1 + intervalDomainLift (coupledChemicalConcentration p u s) x)
    {s x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (fun y => coupledChemDivFluxTimeDerivativeLift p u s y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (Function.uncurry (coupledChemDivFluxLift p u)) (s, y) (1, 0)) := by
  have hopen : Ioo (0 : ℝ) 1 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  refine coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
    (hu := ?_) (hv := ?_) (hgradv := ?_) (hbase := ?_) (hgv := ?_)
  · filter_upwards [hopen] with y hy using hu_c2 y hy s
  · filter_upwards [hopen] with y hy using hv_c2 y hy s
  · filter_upwards [hopen] with y hy using hgradv_c2 y hy s
  · filter_upwards [hopen] with y _ using hbase s y
  · filter_upwards [hopen] with y hy using
      coupledChemical_innerCommute_of_directJointC2 hv_c2 hy
```

Then feed this into `CoupledChemDivFluxJointC2Hyp` / `coupledChemDivLocalChainRule_of_fluxJointC2`, or use it directly to prove the local source HasDerivAt through `coupledChemDivSourceLift_eq_deriv_fluxLift_interior` and `coupledChemDivTimeDerivativeLift_eq_deriv_fluxTimeDerivative`.

## 4. SORRY 3G: time-derivative joint continuity

Target line ~1556:

```lean
ContinuousOn
  (Function.uncurry (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
  (Icc (τ - δ) (τ + δ) ×ˢ Icc (0 : ℝ) 1)
```

Existing producer:

```lean
ShenWork.IntervalCoupledRegularityBootstrap.chemDivMixedTimeDeriv_jointContinuousOn_closed
```

It consumes:

```lean
ChemDivMixedTimeDerivClosedRepr p u τ δ
```

Definition:

```lean
def ChemDivMixedTimeDerivClosedRepr
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (τ δ : ℝ) : Prop :=
  ∃ Gmix : ℝ × ℝ → ℝ, Continuous Gmix ∧
    ∀ t ∈ Icc (τ - δ) (τ + δ), ∀ x ∈ Icc (0 : ℝ) 1,
      coupledChemDivTimeDerivativeLift p u t x = Gmix (t, x)
```

For heat Level0, the intended constructor is:

```lean
ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0
```

Signature:

```lean
theorem chemDivMixedTimeDerivClosedRepr_level0
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ} {M₀ τ : ℝ}
    (hτ : 0 < τ)
    (hu₀_bound : ∀ k, |cosineCoeffs (intervalDomainLift u₀) k| ≤ M₀)
    (hu₀_cont : Continuous u₀) :
    ChemDivMixedTimeDerivClosedRepr
      p (conjugatePicardIter p u₀ 0) τ (min (1 : ℝ) (τ / 2))
```

Then 3G becomes:

```lean
have hrepr : ChemDivMixedTimeDerivClosedRepr
    p (conjugatePicardIter p u₀ 0) s (min (1 : ℝ) (s / 2)) :=
  ShenWork.Paper2.Level0HeatMixedRepr.chemDivMixedTimeDerivClosedRepr_level0
    (p := p) (u₀ := u₀) (M₀ := M₀) hs_pos _hu₀_bound _hu₀_cont

have htime_cont : ContinuousOn
    (Function.uncurry (coupledChemDivTimeDerivativeLift p (conjugatePicardIter p u₀ 0)))
    (Icc (s - min (1 : ℝ) (s / 2)) (s + min (1 : ℝ) (s / 2)) ×ˢ Icc (0 : ℝ) 1) :=
  ShenWork.IntervalCoupledRegularityBootstrap.chemDivMixedTimeDeriv_jointContinuousOn_closed hrepr
```

If your local slab chose

```lean
δ := min 1 (s / 2)
```

this plugs in exactly.  If your local slab uses another `δ`, either choose this canonical `δ` in `hlocal_slab` or use a restriction lemma: continuity on the canonical slab restricts to any smaller closed slab.

## Recommended exact filling order

1. **Add imports**:

   ```lean
   import ShenWork.Paper2.IntervalHeatResolverJointC2
   import ShenWork.PDE.IntervalChemDivFACCommuteDischarge
   import ShenWork.PDE.IntervalChemDivTimeDerivClosed
   import ShenWork.Paper2.IntervalLevel0HeatMixedRepr
   ```

2. **Fill 3G first** using:

   ```lean
   chemDivMixedTimeDerivClosedRepr_level0
   chemDivMixedTimeDeriv_jointContinuousOn_closed
   ```

   This gives the `ContinuousOn` field that `CoupledChemDivLocalChainRule` needs.

3. **Fill 3C+3D+3F next** either by:

   * physical lane:

     ```lean
     PhysicalSourceTimeC2
       → physicalResolverJointC2Data_of_floor
       → coupledChemDivFlux_timeBridge_of_physicalJointC2
       → coupledChemDivLocalChainRule_of_fluxJointC2
     ```

   * or direct lane:

     ```lean
     heatResolver_jointContDiffAt_two
     heatResolver_grad_jointContDiffAt_two
       → direct clone of coupledChemical_innerCommute_of_physicalJointC2
       → direct clone of coupledChemDivFlux_timeBridge_of_physicalJointC2
       → coupledChemDivFlux_timeBridge_of_innerTimeHasDerivAt
       → coupledChemDivLocalChainRule_of_outerCommuteAtoms / fluxJointC2
     ```

4. **Fill 2A and 1A after representatives are available**, using compact maxima:

   ```lean
   isCompact_Icc.prod isCompact_Icc
   hK.exists_isMaxOn hK_nonempty hcont.abs
   ```

   For 2A, the representative is the source value `Fsrc`.  For 1A, it is the second-derivative representative `Fdd` of the `IntervalWeakH2Neumann.secondDeriv` field.

## Minimal caution

`heatResolver_jointContDiffAt_two` alone only gives resolver **value** C².  The chain-rule route also needs resolver gradient C²:

```lean
heatResolver_grad_jointContDiffAt_two
```

or a `PhysicalResolverJointC2Data` package from which both value and gradient C² are produced.  Without the gradient theorem/package, SORRY 3D remains open.

No local `lake build` was run; this drop was produced through the GitHub connector only.
