# Codex Spec: v2 Faithful Frontier Capstone

## Goal

Create ONE new file `ShenWork/Wiener/EWA/ChiNegFaithfulFrontierDirect.lean`
that proves `ChiNegFaithfulRealizationFrontier p` DIRECTLY using the v2
L1ContOn machinery, WITHOUT constructing `hfp`.

## The theorem to prove

```lean
theorem chiNeg_faithfulFrontier_direct (p : CM2Params)
    (hchi : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    ChiNegFaithfulRealizationFrontier p
```

Where `ChiNegFaithfulRealizationFrontier p` is (from ChiNegFrontierAssembly.lean:83):
```lean
def ChiNegFaithfulRealizationFrontier (p : CM2Params) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∀ {u0 : intervalDomain.Point → ℝ},
      PositiveInitialDatum intervalDomain u0 →
      (∀ x, |u0 x| ≤ M) →
        ∃ u_star : EWA δ 1,
          CoupledDuhamelReducedClassicalCore p δ u0 (realSlice u_star)
```

## Proof strategy

For each M > 0, δ > 0, and positive datum u₀ bounded by M:

### Step 1: Build contraction-tower parameters
Use `chiNegStrong_heatFloor_of_paperDatum` (SourceChiNegUncondFix.lean:136)
to get the heat floor, and then use `chiNegStrong_EWA_fixedPoint_of_floor`
(SourceChiNegUncondFix.lean:166) or `picardEWA_uncond_fixedPoint`
(SourceUncondFixedPoint.lean:38) to get the fixed point.

NOTE: This step requires choosing ρ, Md, Mdv, R, L_Q, L_G, δv satisfying
the contraction conditions. The existing `exists_uniform_EWA_lifespan`
(ChiNegUniformLifespan.lean) does this for the datum-uniform lifespan.
But here we have a GIVEN δ, not one we choose. So the approach may differ.

IMPORTANT: Read `SourceChiNegUncondFix.lean` and `ChiNegUniformLifespan.lean`
carefully to understand how the contraction parameters are chosen.

### Step 2: Get L1ContOn packages
Use `chemDivSourceL1ContOn_of_EWA` and `logisticSourceL1ContOn_of_EWA`
from SourceL1ContOnBridge.lean.

### Step 3: Get hsumE, hrealizes, htimeDeriv, hdiffU
These come from the fixed point's contraction data. Look at how
`realSlice_reducedCore_wired` (SourceReducedCoreWire.lean) and
`realSlice_reducedCore_wired_v2` (SourceReducedCoreWireV2.lean) get them.

### Step 4: Get Hv (HasResolverDirectSpectralData)
Use `realSlice_Hv_closed_of_L1ContOn` from SourcePerSliceCloseL1.lean.

### Step 5: Get classical regularity
Use `realSlice_classicalRegularity_of_L1ContOn` from SourceReducedCoreWireV2.lean.

### Step 6: Feed everything to realSlice_reducedCore_wired_v2
This produces `CoupledDuhamelReducedClassicalCore p δ u₀ (realSlice u_star)`.

## Key files to read (in order)

1. `ShenWork/Wiener/EWA/ChiNegFrontierAssembly.lean` — defines the target
2. `ShenWork/Wiener/EWA/SourceChiNegUncondFix.lean` — fixed point construction
3. `ShenWork/Wiener/EWA/SourceReducedCoreWireV2.lean` — v2 reduced core wired
4. `ShenWork/Wiener/EWA/SourceReducedCoreWire.lean` — v1 pattern to follow
5. `ShenWork/Wiener/EWA/SourceL1ContOnBridge.lean` — L1ContOn packages
6. `ShenWork/Wiener/EWA/SourcePerSliceCloseL1.lean` — Hv production
7. `ShenWork/Wiener/EWA/ChiNegUniformLifespan.lean` — contraction parameters
8. `ShenWork/Wiener/EWA/SourceUncondFixedPoint.lean` — uncond fixed point

## Once proven, the full unconditional headline follows

With `chiNeg_faithfulFrontier_direct`, the FULLY unconditional theorem is:

```lean
theorem chiNeg_theorem_1_1_fully_unconditional (p : CM2Params)
    (hchi : p.χ₀ < 0) (ha : 0 < p.a) (hb : 0 < p.b)
    (hα : 1 ≤ p.α) (hγ : 1 ≤ p.γ) :
    Theorem_1_1 intervalDomain p :=
  chiNeg_theorem_1_1_unconditional_faithful p hchi ha hb hα hγ
    (chiNeg_faithfulFrontier_direct p hchi ha hb hα hγ)
```

This is the FINAL goal. Include this theorem in the file too.

## Verification

```bash
cd ~/repos/Shen_work
lake build ShenWork.Wiener.EWA.ChiNegFaithfulFrontierDirect 2>&1 | tail -10
```

Must compile with `#print axioms` showing ONLY [propext, Classical.choice, Quot.sound].

## CRITICAL constraints

- NO sorry, NO axiom, NO native_decide, NO admit
- Line length ≤ 100 characters
- Do NOT modify any existing files
- This is the CAPSTONE — it must compile clean
- The theorem `chiNeg_faithfulFrontier_direct` is the KEY output
- If you cannot complete the full proof, at MINIMUM identify which
  hypotheses of `realSlice_reducedCore_wired_v2` you cannot produce
  and report them precisely in a stall report

## What to be careful about

The main difficulty is producing ALL the hypotheses that
`realSlice_reducedCore_wired_v2` requires. There are ~40 of them.
Many come from the contraction tower (ρ, Md, etc.) which are
existentially quantified from `picardEWA_uncond_fixedPoint`.

The v1 `realSlice_reducedCore_wired` (SourceReducedCoreWire.lean:459)
takes similar parameters. Study how its callers (if any) produce them.

The key insight: `picardEWA_uncond_fixedPoint` produces `u_star` AND
the fixed-point identity `hfix`. Many other hypotheses (like `hsumE`,
`hrealizes`, endpoint nonvanish, etc.) are derived from `hfix` by
other intermediate theorems. Read the code to find these derivations.
