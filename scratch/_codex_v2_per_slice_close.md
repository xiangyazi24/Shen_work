# Codex Spec: v2 SourcePerSliceClose (L1ContOn)

## Goal

Create ONE new file `ShenWork/Wiener/EWA/SourcePerSliceCloseL1.lean`
that retypes the three theorems in `SourcePerSliceClose.lean` against
`DuhamelSourceL1ContOn` instead of `DuhamelSourceTimeC1`.

## What to retype

### 1. `gPow_continuousOn_window_of_L1ContOn`

v2 of `gPow_continuousOn_window` (line 96 of SourcePerSliceClose.lean).

Replace:
```lean
(hchem : DuhamelSourceTimeC1
  (coupledChemDivSourceCoeffs p (realSlice u_star)))
(hlog : DuhamelSourceTimeC1
  (coupledLogisticSourceCoeffs p (realSlice u_star)))
```
with:
```lean
(hchem : DuhamelSourceL1ContOn
  (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
(hlog : DuhamelSourceL1ContOn
  (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
```

Proof changes:
- Line 118: `fullSourceCoeff_jointSolutionClosed p ... hchem hlog (T := T)`
  → `fullSourceCoeff_jointSolutionClosed_of_L1ContOn p ... hchem hlog`
- Line 143: `fullSourceCoeffDot_jointTimeDerivClosed p ... hchem hlog (T := T)`
  → `fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn p ... hchem hlog`

Everything else is identical.

### 2. `hK1_assembled_of_L1ContOn`

v2 of `hK1_assembled` (line 187 of SourcePerSliceClose.lean).

Same TimeC1 → L1ContOn substitution.

Additional change in the proof body:
- Line 238: `realSlice_hasDerivAt_time p ... hchem hlog hrealizes hsIoo ...`
  → Need a v2 call. Use `synthesis_hasDerivAt_of_L1ContOn` from
  SourceSynthesisL1.lean, composed with hrealizes.

The proof at line 230-245 does:
```lean
have hd := realSlice_hasDerivAt_time p (realSlice u_star) u₀cos
    hu0bd hchem hlog hrealizes hsIoo ⟨x, hxIcc⟩
```

Replace with the L1ContOn version. The L1ContOn equivalent is
`synthesis_hasDerivAt_of_L1ContOn` which gives:
```lean
HasDerivAt (fun s => ∑' n, fullSourceCoeff ... s n * cosineMode n x)
    (∑' n, fullSourceCoeffDot ... s n * cosineMode n x) s
```

Then compose with hrealizes to get:
```lean
HasDerivAt (fun r => intervalDomainLift (realSlice u_star r) x)
    (vdotLslice p u_star u₀cos s x) s
```

This is the same logic as `slice_hasDerivAt_of_l1` in
SourceReducedCoreWireV2.lean lines 72-90, but for the lift instead
of the subtype. The relevant identity:
```lean
intervalDomainLift (realSlice u_star r) x = realSlice u_star r ⟨x, hxIcc⟩
```
which holds by `intervalDomainLift` and `dif_pos hxIcc`.

The complete replacement:
```lean
-- from synthesis_hasDerivAt_of_L1ContOn:
have hsynth := synthesis_hasDerivAt_of_L1ContOn p
    (realSlice u_star) u₀cos hu0bd hchem hlog hsIoo x
-- compose with hrealizes (eventuallyEq from Ioo membership):
have hagree : (fun r => intervalDomainLift (realSlice u_star r) x)
    =ᶠ[𝓝 s] (fun r => ∑' n,
      fullSourceCoeff p (realSlice u_star) u₀cos r n
        * cosineMode n x) :=
  Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hsIoo)
    (fun r hr => hrealizes r hr x hxIcc)
have hfun : (fun r => intervalDomainLift (realSlice u_star r) x)
    = (fun r => realSlice u_star r ⟨x, hxIcc⟩) := by
  funext r; rw [intervalDomainLift, dif_pos hxIcc]
rw [hfun]
have hd := hsynth.congr_of_eventuallyEq (by
  rw [← hfun]; exact hagree.symm)
simpa only [vdotLslice] using hd
```

- Line 257-258: `gPow_continuousOn_window p ... hchem hlog ...`
  → `gPow_continuousOn_window_of_L1ContOn p ... hchem hlog ...`

### 3. `realSlice_Hv_closed_of_L1ContOn`

v2 of `realSlice_Hv_closed` (line 282 of SourcePerSliceClose.lean).

Same TimeC1 → L1ContOn substitution.

In the proof body, the only change is the call to `hK1_assembled`:
`hK1_assembled p ... hchem hlog ...`
→ `hK1_assembled_of_L1ContOn p ... hchem hlog ...`

## Imports

```lean
import ShenWork.Wiener.EWA.SourcePerSliceClose
import ShenWork.Wiener.EWA.SourceSynthesisL1
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
```

## Available v2 theorems (from SourceSynthesisL1.lean)

```lean
theorem synthesis_hasDerivAt_of_L1ContOn ...
theorem fullSourceCoeff_jointSolutionClosed_of_L1ContOn ...
theorem fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn ...
```

## Available structures

```lean
structure DuhamelSourceL1ContOn (a : ℝ → ℕ → ℝ) (T : ℝ) where
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |a s n| ≤ envelope n
  hcont : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 T)
```

## Verification

```bash
cd ~/repos/Shen_work
lake env lean ShenWork/Wiener/EWA/SourcePerSliceCloseL1.lean
```

Must exit 0 with `#print axioms` showing ONLY [propext, Classical.choice, Quot.sound].

## CRITICAL constraints

- NO sorry, NO axiom, NO native_decide, NO admit
- Line length ≤ 100 characters
- Do NOT modify any existing files
- Read the FULL template file `SourcePerSliceClose.lean` (282+ lines) to understand all the proofs
- The theorem `realSlice_Hv_closed_of_L1ContOn` is the most important output

## What NOT to do

- Do NOT redefine `vdotLslice`, `lift_eq_valueField`, `powerSource_continuousOn_Icc`, or `gPow`
- These are already defined in `SourcePerSliceClose.lean` and accessible via import
- Also DO NOT redefine `realSlice_pos` — it's from `SourcePositivity.lean`
