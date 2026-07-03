# Codex Spec: v2 Classical Regularity + v2 Reduced Core Wire

## Goal

Create **ONE** new file that:
1. Retypes `realSlice_classicalRegularity` against `DuhamelSourceL1ContOn` (instead of `DuhamelSourceTimeC1`)
2. Retypes `realSlice_reducedCore_wired` against `DuhamelSourceL1ContOn` (instead of `DuhamelSourceTimeC1On`)
3. Includes helper retypes for `htime_of_on`, `hsum_chem_of_on`, `hsum_log_of_on`

File: `ShenWork/Wiener/EWA/SourceReducedCoreWireV2.lean`

## How this fits

The v2 files replace the `DuhamelSourceTimeC1(On)` dependency (which requires `derivBound`) with `DuhamelSourceL1ContOn` (which only requires continuity + envelope). The key new theorems that make this possible:

From `ShenWork/Wiener/EWA/SourceSynthesisL1.lean` (already built, clean3):
- `synthesis_hasDerivAt_of_L1ContOn` — HasDerivAt for the synthesis, replacing `synthesis_hasDerivAt_on`
- `fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn` — joint time-derivative continuity on Ioo×Icc
- `fullSourceCoeffDot_jointTimeDerivInterior_of_L1ContOn` — joint time-derivative continuity on Ioo×Ioo
- `fullSourceCoeff_jointSolutionClosed_of_L1ContOn` — joint solution-field continuity on Ioo×Icc

## Part 1: Helper retypes

### `hsum_chem_of_l1`

EXACT same proof as `hsum_chem_of_on` (SourceReducedCoreWire.lean:114-124) but takes:
```lean
(src : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T)
```
instead of `DuhamelSourceTimeC1On`. The proof body is identical — it only uses
`src.henv_summable` and `src.envelope` with `src.henv_bound`. The field names
in `DuhamelSourceL1ContOn` are:
- `src.henv_summable : Summable src.envelope`
- `src.henv_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |a s n| ≤ src.envelope n`

Note: `henv_bound` takes `(s : ℝ) (hs0 : 0 ≤ s) (hsT : s ≤ T)` as separate args,
not `s ∈ Set.Icc 0 T`.

### `hsum_log_of_l1`

Same retype for the logistic source.

### `slice_hasDerivAt_of_l1`

EXACT same proof as `slice_hasDerivAt_on` (SourceReducedCoreWire.lean:~420-455) but calls
`synthesis_hasDerivAt_of_L1ContOn` instead of `synthesis_hasDerivAt_on`.

### `htime_of_l1`

EXACT same proof as `htime_of_on` (SourceReducedCoreWire.lean:443-455) but calls
`slice_hasDerivAt_of_l1` instead of `slice_hasDerivAt_on`.

## Part 2: v2 Classical Regularity

Retype of `realSlice_classicalRegularity` (SourceClassicalRegularity.lean:120-241).

### Signature change

Replace:
```lean
(hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p (realSlice u_star)))
(hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p (realSlice u_star)))
```

with:
```lean
(hchem : DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
(hlog : DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
```

### Proof changes

There are exactly 4 call sites that use `hchem`/`hlog`:

1. **Conjunct (2), line ~169:**
   ```lean
   -- OLD:
   have hjoint := fullSourceCoeffDot_jointTimeDerivClosed p u u₀cos hu0bd hchem hlog (T := T)
   -- NEW:
   have hjoint := fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn p u u₀cos hu0bd hchem hlog
   ```

2. **Conjunct (3), line ~183:**
   ```lean
   -- OLD:
   have hjoint := fullSourceCoeffDot_jointTimeDerivInterior p u u₀cos hu0bd hchem hlog (T := T)
   -- NEW:
   have hjoint := fullSourceCoeffDot_jointTimeDerivInterior_of_L1ContOn p u u₀cos hu0bd hchem hlog
   ```

3. **Conjunct (6), line ~227:**
   ```lean
   -- OLD:
   have hjoint := fullSourceCoeffDot_jointTimeDerivClosed p u u₀cos hu0bd hchem hlog (T := T)
   -- NEW:
   have hjoint := fullSourceCoeffDot_jointTimeDerivClosed_of_L1ContOn p u u₀cos hu0bd hchem hlog
   ```

4. **Conjunct (7), line ~235:**
   ```lean
   -- OLD:
   have hjoint := fullSourceCoeff_jointSolutionClosed p u u₀cos hu0bd hchem hlog (T := T)
   -- NEW:
   have hjoint := fullSourceCoeff_jointSolutionClosed_of_L1ContOn p u u₀cos hu0bd hchem hlog
   ```

EVERYTHING ELSE in the proof stays EXACTLY the same. Read the original file
(`SourceClassicalRegularity.lean`) to get the full proof, make the 4 substitutions above.

## Part 3: v2 Reduced Core Wiring

Retype of `realSlice_reducedCore_wired` (SourceReducedCoreWire.lean:459-569).

### Signature change

Replace:
```lean
(hchem_on : DuhamelSourceTimeC1On
  (coupledChemDivSourceCoeffs p (realSlice u_star)) 0 T)
(hlog_on : DuhamelSourceTimeC1On
  (coupledLogisticSourceCoeffs p (realSlice u_star)) 0 T)
```

with:
```lean
(hchem_l1 : DuhamelSourceL1ContOn
  (coupledChemDivSourceCoeffs p (realSlice u_star)) T)
(hlog_l1 : DuhamelSourceL1ContOn
  (coupledLogisticSourceCoeffs p (realSlice u_star)) T)
```

Also replace:
```lean
(hclassReg : intervalDomainClassicalRegularity T (realSlice u_star)
  (mildChemicalConcentration p (realSlice u_star)))
```

with producing `hclassReg` INTERNALLY using `realSlice_classicalRegularity_of_L1ContOn` (the v2 classical regularity from Part 2). This requires the v2 reduced core to also take:
```lean
(hdecay : ∀ t ∈ Ioo T, SourceCoeffQuadraticDecay p (realSlice u_star t))
(Hvpos : ∀ t ∈ Ioo T, ∀ x, 0 < mildChemicalConcentration ... t x)
```

### Proof body changes

Replace:
```lean
-- Line 558:
have htime := htime_of_on p (realSlice u_star) u₀cos hu0bd hchem_on hlog_on hrealizes
-- → 
have htime := htime_of_l1 p (realSlice u_star) u₀cos hu0bd hchem_l1 hlog_l1 hrealizes

-- Line 561:
have hsc := hsum_chem_of_on p (realSlice u_star) hchem_on (T := T)
-- →
have hsc := hsum_chem_of_l1 p (realSlice u_star) hchem_l1

-- Line 562:
have hsl := hsum_log_of_on p (realSlice u_star) hlog_on (T := T)
-- →
have hsl := hsum_log_of_l1 p (realSlice u_star) hlog_l1
```

For `hclassReg`, produce it internally:
```lean
have hdiffU : ∀ t ∈ Ioo T, ∀ x : intervalDomainPoint,
    DifferentiableAt ℝ (fun s => realSlice u_star s x) t :=
  fun t ht x => (slice_hasDerivAt_of_l1 ... ht x).differentiableAt
have htimeDeriv : ... := htime
have hclassReg := realSlice_classicalRegularity_of_L1ContOn p u_star u₀cos hu0bd
    hchem_l1 hlog_l1 hsumE hrealizes htimeDeriv hdiffU huNE0 huNE1 hdecay Hv Hvpos
```

## Imports

```lean
import ShenWork.Wiener.EWA.SourceReducedCoreWire
import ShenWork.Wiener.EWA.SourceClassicalRegularity
import ShenWork.Wiener.EWA.SourceSynthesisL1
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
```

## File structure

```lean
import ...

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
...

variable {T : ℝ}

-- Part 1: Helpers
private theorem hsum_chem_of_l1 ...
private theorem hsum_log_of_l1 ...
private theorem slice_hasDerivAt_of_l1 ...
private theorem htime_of_l1 ...

-- Part 2: v2 Classical Regularity
theorem realSlice_classicalRegularity_of_L1ContOn ...

-- Part 3: v2 Reduced Core Wire
theorem realSlice_reducedCore_wired_v2 ...

end ShenWork.EWA

#print axioms ShenWork.EWA.realSlice_reducedCore_wired_v2
```

## KEY: How to build

The original files (`SourceClassicalRegularity.lean` ~241 lines, `SourceReducedCoreWire.lean` ~571 lines) contain the TEMPLATE. The v2 file retypes them. The process is:

1. **Copy** the original theorem proofs from the two files
2. **Substitute** the 4 joint-continuity calls (see Part 2 above)
3. **Substitute** the 3 source-package uses (see Part 3 above)
4. **Produce** `hclassReg` internally from the v2 classical regularity

Everything that doesn't involve `DuhamelSourceTimeC1(On)` or `hclassReg` stays EXACTLY the same.

## Verification

```bash
cd ~/repos/Shen_work
lake env lean ShenWork/Wiener/EWA/SourceReducedCoreWireV2.lean
```

Must exit 0 with no `sorry`, no `sorryAx` in axiom print.

## Reference files (READ these to understand the retypes)

1. `ShenWork/Wiener/EWA/SourceClassicalRegularity.lean` (TEMPLATE for Part 2)
2. `ShenWork/Wiener/EWA/SourceReducedCoreWire.lean` (TEMPLATE for Part 3)
3. `ShenWork/Wiener/EWA/SourceSynthesisL1.lean` (provides the v2 theorems)
4. `ShenWork/Paper2/IntervalPicardLimitRestartWeak.lean:127` (DuhamelSourceL1ContOn structure)

## What NOT to do

- Do NOT modify any existing files
- Do NOT introduce sorry, axiom, native_decide, or admit
- Keep line length ≤ 100 chars
- Do NOT import `ShenWork.Wiener.EWA.SourceL1ContOnBridge` — that file is not needed here
