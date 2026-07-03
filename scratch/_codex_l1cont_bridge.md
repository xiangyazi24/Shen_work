# Codex Spec: EWA → DuhamelSourceL1ContOn Bridge

## Goal

Create file `ShenWork/Wiener/EWA/SourceL1ContOnBridge.lean` that produces
`DuhamelSourceL1ContOn` (the weak source package) from EWA fixed-point data,
for both the chemotaxis-divergence source and the logistic source.

This file is the bridge between the EWA spectral algebra and the Duhamel
spectral pipeline. After it, the v2 synthesis chain can produce the reduced
core without any `derivBound` hypothesis.

## Key types

```
-- From ShenWork/Paper2/IntervalPicardLimitRestartWeak.lean:127
structure DuhamelSourceL1ContOn (a : ℝ → ℕ → ℝ) (T : ℝ) where
  envelope : ℕ → ℝ
  henv_summable : Summable envelope
  henv_bound : ∀ s, 0 ≤ s → s ≤ T → ∀ n, |a s n| ≤ envelope n
  hcont : ∀ n, ContinuousOn (fun s : ℝ => a s n) (Set.Icc 0 T)
```

## Required theorems (4 total)

### Theorem 1: `ewaCosCoeffAt_continuousOn`

```lean
theorem ewaCosCoeffAt_continuousOn (F : EWA T 0) (n : ℕ) :
    ContinuousOn (fun s => ewaCosCoeffAt F ⟨s, ‹_›⟩ n) (Set.Icc 0 T)
```

**Actually**, because `ewaCosCoeffAt` takes a `TimeDom T` (which is `↥(Set.Icc 0 T)`),
the clean way is to define a helper and prove continuity:

```lean
noncomputable def ewaCosCoeffAtReal (F : EWA T 0) (hT : 0 ≤ T)
    (s : ℝ) (n : ℕ) : ℝ :=
  if hs : s ∈ Set.Icc (0 : ℝ) T then ewaCosCoeffAt F ⟨s, hs⟩ n
  else 0

theorem ewaCosCoeffAtReal_continuousOn (F : EWA T 0) (hT : 0 ≤ T) (n : ℕ) :
    ContinuousOn (fun s => ewaCosCoeffAtReal F hT s n) (Set.Icc 0 T)
```

**Proof idea:** On `Icc 0 T`, `ewaCosCoeffAtReal` agrees with the composition:
- `s ↦ ⟨s, hs⟩` (continuous embedding into `TimeDom T`)
- `τ ↦ ewaCosCoeffAt F τ n` (continuous because built from `ContinuousMap` evaluations)

`ewaCosCoeffAt F τ n` is defined as:
- If n = 0: `((F.toFun 0) τ).re`
- If n ≠ 0: `(((F.toFun (n:ℤ)) τ + (F.toFun (-(n:ℤ))) τ).re)`

Since `F.toFun k : ContinuousMap (TimeDom T) ℂ`, evaluation at `τ` is continuous.
`.re` is continuous. Sum of continuous is continuous.

So the whole thing is ContinuousOn `(Icc 0 T)` as a composition of continuous maps.

Use `ContinuousOn.congr` to show `ewaCosCoeffAtReal` equals the continuous composition
on `Icc 0 T`.

### Theorem 2: `logistic_coeff_bound_of_EWA`

This is an EXACT RETYPE of `chemDiv_coeff_bound_of_EWA` (in HCoeffDischarge.lean:56-85)
with these substitutions:
- `chemDivEWA μ ν γ hμ p U` → `GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U)`
- `coupledChemDivSourceCoeffs` → `coupledLogisticSourceCoeffs`
- `coupledChemDivSourceLift` → `coupledLogisticSourceLift`
- `chemDivEWA_evenReal` → `(growthEWA_evenReal ... hU).incl (by omega)`

```lean
theorem logistic_coeff_bound_of_EWA
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
          = ((coupledLogisticSourceLift p u τ.1 x : ℝ) : ℂ))
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) (n : ℕ) :
    |coupledLogisticSourceCoeffs p u s n|
      ≤ sourceEnvelope
          (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) n
```

**Proof:** Copy the proof of `chemDiv_coeff_bound_of_EWA` line by line with the
substitutions listed above. The four steps are:
1. `growthEWA_evenReal` + `.incl` for even-real closure
2. Pick time slice `τ := ⟨s, hs⟩`
3. `ewaCosCoeffAt_eq_cosineCoeffs_of_even_real` for the coeff bridge
4. `ewaCosCoeffAt_abs_le_envelope` for the envelope bound

### Theorem 3: `chemDivSourceL1ContOn_of_EWA`

```lean
theorem chemDivSourceL1ContOn_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hT : 0 ≤ T)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
          = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ))
    (hcoeff_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
      coupledChemDivSourceCoeffs p u s n
        = ewaCosCoeffAtReal (chemDivEWA μ ν γ hμ p U) hT s n) :
    DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T where
  envelope := sourceEnvelope (chemDivEWA μ ν γ hμ p U)
  henv_summable := sourceEnvelope_summable (chemDivEWA μ ν γ hμ p U)
  henv_bound := fun s hs0 hsT n =>
    chemDiv_coeff_bound_of_EWA hμ p u U hU h_eval s ⟨hs0, hsT⟩ n
  hcont := fun n => by
    apply ContinuousOn.congr (ewaCosCoeffAtReal_continuousOn _ hT n)
    intro s hs
    exact (hcoeff_eq s hs n).symm
```

**Note:** The `hcoeff_eq` hypothesis states that on `Icc 0 T`, the source
coefficient equals the `ewaCosCoeffAtReal` extractor. This follows from the
coeff bridge (`ewaCosCoeffAt_eq_cosineCoeffs_of_even_real`), but packaging it
as a hypothesis keeps this theorem clean. The caller produces `hcoeff_eq` from
the coeff bridge.

**Alternative (simpler, PREFERRED):** Avoid `hcoeff_eq` entirely by:
- Using `chemDiv_coeff_bound_of_EWA` for the bound
- Using the coeff bridge INTERNALLY to prove continuity

```lean
theorem chemDivSourceL1ContOn_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hT : 0 ≤ T)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
          = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ)) :
    DuhamelSourceL1ContOn (coupledChemDivSourceCoeffs p u) T where
  envelope := sourceEnvelope (chemDivEWA μ ν γ hμ p U)
  henv_summable := sourceEnvelope_summable _
  henv_bound := fun s hs0 hsT n =>
    chemDiv_coeff_bound_of_EWA hμ p u U hU h_eval s ⟨hs0, hsT⟩ n
  hcont := fun n => by
    -- On Icc 0 T, source coeff = ewaCosCoeffAt (from coeff bridge)
    -- ewaCosCoeffAt is continuous (from EWA mode continuity)
    -- So source coeff is continuous
    have hdiv : EvenRealEWA (chemDivEWA μ ν γ hμ p U) :=
      chemDivEWA_evenReal FnegEWA_evenReal_Hyp_proved hμ p hU
    apply ContinuousOn.congr
    · exact ewaCosCoeffAtReal_continuousOn (chemDivEWA μ ν γ hμ p U) hT n
    · intro s hs
      rw [ewaCosCoeffAtReal, dif_pos hs]
      exact (ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
        (F := chemDivEWA μ ν γ hμ p U)
        (f := coupledChemDivSourceLift p u s) ⟨s, hs⟩
        (fun m => hdiv.even ⟨s, hs⟩ m)
        (fun m => hdiv.real ⟨s, hs⟩ m)
        (fun x hx => h_eval ⟨s, hs⟩ x hx) n).symm
```

USE THIS SIMPLER VERSION.

### Theorem 4: `logisticSourceL1ContOn_of_EWA`

Same pattern as Theorem 3 but for the logistic source:

```lean
theorem logisticSourceL1ContOn_of_EWA
    (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (hT : 0 ≤ T)
    (hU : EvenRealEWA U)
    (h_eval : ∀ (τ : TimeDom T) (x : ℝ), x ∈ Set.Ioo (0 : ℝ) 1 →
        evalST τ (x : WA.Circ)
          (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
          = ((coupledLogisticSourceLift p u τ.1 x : ℝ) : ℂ)) :
    DuhamelSourceL1ContOn (coupledLogisticSourceCoeffs p u) T where
  envelope := sourceEnvelope (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
  henv_summable := sourceEnvelope_summable _
  henv_bound := fun s hs0 hsT n =>
    logistic_coeff_bound_of_EWA p u U hU h_eval s ⟨hs0, hsT⟩ n
  hcont := fun n => by
    have hgr : EvenRealEWA (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U)) :=
      (growthEWA_evenReal FnegEWA_evenReal_Hyp_proved hU).incl (by omega)
    apply ContinuousOn.congr
    · exact ewaCosCoeffAtReal_continuousOn _ hT n
    · intro s hs
      rw [ewaCosCoeffAtReal, dif_pos hs]
      exact (ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
        (F := GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U))
        (f := coupledLogisticSourceLift p u s) ⟨s, hs⟩
        (fun m => hgr.even ⟨s, hs⟩ m)
        (fun m => hgr.real ⟨s, hs⟩ m)
        (fun x hx => h_eval ⟨s, hs⟩ x hx) n).symm
```

## Imports

```lean
import ShenWork.Wiener.EWA.SourceEnvelope
import ShenWork.Wiener.EWA.HCoeffDischarge
import ShenWork.Wiener.EWA.NonCircularCoeffBridge
import ShenWork.Wiener.EWA.GrowthEvenReal
import ShenWork.Wiener.EWA.GrowthEvalBridge
import ShenWork.Wiener.EWA.EvenRealClosure
import ShenWork.Paper2.IntervalPicardLimitRestartWeak
import ShenWork.PDE.IntervalCoupledSourceTimeC1
```

## File structure

```lean
import ...

noncomputable section

namespace ShenWork.EWA

open Set Filter Topology
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalPicardLimitRestartWeak (DuhamelSourceL1ContOn)

variable {T : ℝ}

-- 1. ewaCosCoeffAtReal definition
-- 2. ewaCosCoeffAtReal_continuousOn
-- 3. logistic_coeff_bound_of_EWA
-- 4. chemDivSourceL1ContOn_of_EWA
-- 5. logisticSourceL1ContOn_of_EWA

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDivSourceL1ContOn_of_EWA
#print axioms ShenWork.EWA.logisticSourceL1ContOn_of_EWA
```

## Verification

```bash
cd ~/repos/Shen_work
lake env lean ShenWork/Wiener/EWA/SourceL1ContOnBridge.lean
```

Must exit 0 with no sorry, no axiom, no native_decide.

## Key references (read these files)

1. `ShenWork/Wiener/EWA/HCoeffDischarge.lean` — the chemDiv coeff bound (TEMPLATE)
2. `ShenWork/Wiener/EWA/SourceEnvelope.lean` — sourceEnvelope definition + bounds
3. `ShenWork/Wiener/EWA/NonCircularCoeffBridge.lean:121` — ewaCosCoeffAt_eq_cosineCoeffs_of_even_real
4. `ShenWork/Wiener/EWA/CoeffBridge.lean:151` — ewaCosCoeffAt definition
5. `ShenWork/Wiener/EWA/GrowthEvenReal.lean:27` — growthEWA_evenReal
6. `ShenWork/Wiener/EWA/EvenRealClosure.lean:104` — EvenRealEWA.incl
7. `ShenWork/Paper2/IntervalPicardLimitRestartWeak.lean:127` — DuhamelSourceL1ContOn structure
8. `ShenWork/PDE/IntervalCoupledSourceTimeC1.lean:29-37` — coupledLogisticSourceLift/Coeffs definitions

## What NOT to do

- Do NOT modify any existing files
- Do NOT introduce sorry, axiom, native_decide, or admit
- Do NOT import anything from SourceSynthesisL1 (that file doesn't exist yet)
- Keep line length ≤ 100 chars
