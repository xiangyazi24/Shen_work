# Assembly Spec: realSlice_reducedCore_wired_v5_auto

## Goal

Write `SourceReducedCoreWireV5Auto.lean` that produces
`CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)` from
ONLY the Picard framework data + PPID datum cosine data + heat floor.
ALL spectral chain hypotheses (groups D-H of the v4 audit) are derived
internally.

## What this unblocks

```
realSlice_reducedCore_auto  (this file)
  → ChiNegDatumUniformConstructionStrong p  (wire in SourceChiNegUncondFix)
    → chiNeg_theorem_1_1_of_strong           (IntervalDomainTheorem11StrongPath)
      → Theorem_1_1 intervalDomain p          UNCONDITIONAL
```

## Theorem signature (target)

```lean
theorem realSlice_reducedCore_auto (p : CM2Params)
    (u_star : EWA T 1) (u₀ : intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    -- Heat floor data
    {u₀E : WA 1} {δ ρ : ℝ} (hδρ : 0 < δ - ρ)
    (hheat : UniformFloor (heatEWA (T := T) u₀E) δ)
    (hu_ball : u_star ∈ Metric.closedBall (heatEWA (T := T) u₀E) ρ)
    -- Initial datum cosine data
    (hsumc : Summable (fun k => |u₀cos k|))
    (hmem : MemW 1 (ofCosineCoeffs u₀cos))
    {Mu0 : ℝ} (hu0bd : ∀ n, |u₀cos n| ≤ Mu0)
    (hrecon : ∀ x : intervalDomainPoint,
      u₀ x = ∑' n, u₀cos n * cosineMode n x.1)
    -- Picard framework
    (hT0 : (0 : ℝ) ≤ T) (hT : (0 : ℝ) < T) {L_Q L_G : ℝ}
    (hfix : u_star = picardEWA p p.μ p.ν p.γ p.hμ hT0
      (⟨ofCosineCoeffs u₀cos, hmem⟩ : WA 1) u_star)
    (hρ : 0 ≤ ρ)
    (hself : MapsTo ...)
    (hLipQ : ∀ a ∈ ..., ∀ b ∈ ..., ...)
    (hLipG : ∀ a ∈ ..., ∀ b ∈ ..., ...)
    (hKnn : (0 : ℝ) ≤ ...)
    (hK : ... < 1)
    (hmem_star : u_star ∈ Metric.closedBall ...)
    -- Parameter conditions
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1) (hνnn : 0 ≤ p.ν)
    -- Floor on u_star
    (hfloor : UniformFloor u_star T) :
    CoupledDuhamelReducedClassicalCore p T u₀ (realSlice u_star)
```

## Proof structure (step-by-step)

### Step 0: EvenRealEWA
```lean
have hER : EvenRealEWA u_star :=
  picardEWA_evenReal_fixedPoint p p.hμ hT0 u₀cos hmem hρ hself hLipQ hLipG hKnn hK
    u_star hmem_star hfix
```

### Step 1: Source family (from SourceResolverSummabilityDischarge)
```lean
have hsumR := fun σ => resolverSourceSummable_of_evenReal p u_star hER hTpos hfloor σ
have hgrad := fun τ => resolverGradSummable_of_evenReal p u_star hER hTpos hfloor τ
-- set f as the standard source function (see realizes_evalST_auto:663)
have hf_cont := fun σ => sourceFn_continuous p u_star hTpos hfloor σ
have hf_nonneg := fun σ y => sourceFn_nonneg p u_star hνnn hTpos hfloor σ y
have hf_coeff : ... := ...
have hf2 : ... := ...
```

### Step 2: L1ContOn (from SourceResolverSummabilityDischarge)
```lean
have hlog_l1 := logisticSourceL1ContOn_auto p u_star hTpos hER hfloor hαnn hT0
have hchem_l1 := chemDivSourceL1ContOn_auto p u_star hTpos hER hT hfloor hβpos hνnn hμle1
```

### Step 3: hsumE (from SourceResolverSummabilityDischarge)
```lean
have hsumE := fun t ht htT => hsumE_of_L1ContOn p (realSlice u_star) u₀cos hu0bd hchem_l1 hlog_l1 ht htT
```

### Step 4: Flux/log regularity
```lean
have h_flux_diff := fun τ x hx => chemFluxLifted_differentiableAt_of_EWA p u_star hER hTpos hfloor hνnn τ hx
have h_src_cont_log := fun τ => wLog_continuous_of_floor p u_star hTpos hfloor τ
```

### Step 5: Slab evaluation (realizes)
Uses `realizes_evalST_auto` to get `hrealizes`.

### Step 6: Endpoint nonvanishing
```lean
have huNE0 := realSlice_lift_endpoint0_ne_zero hδρ hheat hu_ball
have huNE1 := realSlice_lift_endpoint1_ne_zero hδρ hheat hu_ball
```

### Step 7: hdefect
```lean
-- From cosineCoeff_summable_of_eigenvalue_summable:
--   Summable (|fullSourceCoeff ...|) follows from hsumE
-- Then |defect_n| ≤ |fullSourceCoeff n| + |u₀cos n|, both summable
have hdefect : ... := fun t ht =>
  let hsumE_t := hsumE t ht ht.2.le
  let ⟨_, habs⟩ := cosineCoeff_summable_of_eigenvalue_summable hsumE_t
  (habs.add hsumc).of_nonneg_of_le (fun n => abs_nonneg _)
    (fun n => abs_sub_le_abs_add ...)  -- triangle inequality
```

### Step 8: htrace
```lean
-- Two parts going to 0:
-- (a) ∑ |e^{-tλ_n} - 1| |u₀cos n| → 0 by DCT over 2|u₀cos|
-- (b) ∑ (Duhamel terms) ≤ t · ∑ envelope → 0
-- This needs Mathlib's dominated convergence for series.
```

This is the hardest step — may need a dedicated helper theorem.

### Step 9: Feed into v4
```lean
exact realSlice_reducedCore_wired_v4 p u_star u₀ u₀cos hu0bd hδρ hheat hu_ball
  hsumc hmem hT0 rfl rfl hfix hρ hself hLipQ hLipG hKnn hK hmem_star
  hβpos hαnn hμle1 rfl hfloor hsumR hgrad f hf_cont hf_nonneg hf_coeff hf2
  h_flux_diff h_src_cont_log hchem_l1 hlog_l1 hsumE hT hu0cos hrecon hdefect htrace
```

## Imports needed

```lean
import ShenWork.Wiener.EWA.SourceReducedCoreWireV2
import ShenWork.Wiener.EWA.SourceResolverSummabilityDischarge
import ShenWork.PDE.IntervalDuhamelClosedC2  -- for cosineCoeff_summable_of_eigenvalue_summable
```

## Estimated size

~200-300 lines (most is wiring; the novel content is hdefect/htrace derivation).

## Verification

1. `lake env lean ShenWork/Wiener/EWA/SourceReducedCoreWireV5Auto.lean`
2. `#print axioms realSlice_reducedCore_auto` → expect `[propext, Classical.choice, Quot.sound]`

## After this file

The remaining step to make `Theorem_1_1` UNCONDITIONAL is to wire
`realSlice_reducedCore_auto` into `ChiNegDatumUniformConstructionStrong`:

```lean
theorem chiNegDatumUniformConstructionStrong_unconditional (p : CM2Params)
    (hchi : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b) (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ChiNegDatumUniformConstructionStrong p := by
  intro M hM
  -- obtain lifespan from EWA tower
  obtain ⟨T, hT, ...⟩ := exists_uniform_EWA_lifespan p M hM
  refine ⟨T, hT, fun {u0} hu0 hbd => ?_⟩
  -- lift u0 to continuous, get cosine data
  -- build Picard fixed point
  -- call realSlice_reducedCore_auto
  sorry  -- this wiring is the next piece
```

This requires:
1. `exists_uniform_EWA_lifespan` — may already exist
2. Datum lifting: PPID → continuous lift → cosine coefficients
3. Heat floor: PPID floor → heat EWA floor (via chiNegStrong_heatFloor_of_paperDatum)
4. Picard construction: chiNegStrong_EWA_fixedPoint_of_floor
