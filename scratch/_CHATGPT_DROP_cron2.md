# Q404 (cron2): Barrier C / `BFormBankedInputs.hchemCont`

## Executive verdict

I traced `BFormBankedInputs.hchemCont` through `IntervalBFormDirectClassical.lean`, `IntervalBFormPIDUnconditional.lean`, the old global provider, the windowed `On` provider, and `IntervalBankChemSliceFix.lean`.

The short answer:

* **Do not just delete `hchemCont` in the current code path.** It is not dead at present. `BFormBankedInputs.hpde_u` passes it to `intervalConjugateMildSolution_pde_u_PID_unconditional`; that theorem uses it to build `ChemDivCosineFourierData` through the hard-wired `chemDivCosineFourierData_constExtend` provider.

* **Changing it to `ContinuousOn ... (Ioo 0 1)` is also not enough** for the current consumers. The old consumer wants a `ChemDivCosineFourierData`, whose `representative` is globally continuous and agrees with `chemDivLift` on `Icc 0 1`. The landed fix introduces `ChemDivCosineFourierDataIoo`, not merely a local `ContinuousOn` field.

* The right fix is to **replace the false field by an endpoint-insensitive representative package**, e.g.

  ```lean
  hchemDataIoo : ∀ t, 0 < t → t < DB.T →
    ShenWork.Paper2.BankChemSliceFix.ChemDivCosineFourierDataIoo p
      ((conjugatePicardLimit p u₀ DB.T) t)
      (coupledChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t)
  ```

  or equivalently explicit fields `ψ`, `Continuous ψ`, `EqOn ψ chemDivLift (Ioo 0 1)`, and Fourier summability for `reflCircle ψ`.

* The endpoint values really do not matter for the PDE identity: the Fourier-convergence consumers evaluate only at `hx : x.1 ∈ Ioo 0 1`. But the **current type** forces endpoint continuity/agreement through `ChemDivCosineFourierData` and `chemDivCosineFourierData_constExtend`, so the code still asks for a false endpoint statement.

* The **windowed `On` PDE identity** does **not inherently need `hchemCont`**. It still currently takes `hchemData : ChemDivCosineFourierData ...`, so in the current signature it still indirectly needs a chem-div Fourier package. But if the `On` theorem is rewired to take `ChemDivCosineFourierDataIoo` and use the `_Ioo` consumers from `IntervalBankChemSliceFix.lean`, then `hchemCont` disappears. The windowed `On` route is the right place to do this because it directly proves the interior PDE and does not pack the old global `HasBFormSpectralPdeAgreement` existential.

Bottom line:

```text
Current global path:
  hchemCont is used and false.

Endpoint-insensitive fixed path:
  remove hchemCont only after replacing old ChemDivCosineFourierData
  by ChemDivCosineFourierDataIoo / smooth-surrogate data.

Changing hchemCont to ContinuousOn Ioo alone:
  insufficient; the consumer needs a globally continuous representative
  plus Fourier summability, not just local continuity.

Windowed On path:
  can avoid hchemCont once its hchemData argument is changed to the Ioo package
  and its two chemDiv consumer calls are switched to the _Ioo lemmas.
```

## Lean probes used

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugateDuhamelMap
  (IntervalConjugateMildSolution intervalConjugateDuhamelMap)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugateMildSolutionData_of_data conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalDuhamelClosedC2 (DuhamelSourceTimeC1)
open ShenWork.IntervalBFormSpectral
  (bFormSourceCoeffs bFormSource_duhamelSourceTimeC1
   bFormSource_duhamelSourceTimeC1On)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration coupledChemDivSourceCoeffs
   coupledLogisticSourceCoeffs)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2

namespace ShenWork.Paper2.BFormDirectClassical

#check BFormBankedInputs
#check BFormBankedInputs.hpde_u
#check BFormBankedInputs.hsrcB
#check BFormBankedInputs.hsrcB_on

end ShenWork.Paper2.BFormDirectClassical
```

```lean
import ShenWork.Paper2.IntervalBFormPIDUnconditional

open Filter Topology Set

namespace ShenWork.IntervalBFormSpectral

#check ChemDivCosineFourierData
#check chemDivCosineFourierData_constExtend
#check chemDiv_cosineSeries_summable
#check chemDiv_cosineFourier_convergence

end ShenWork.IntervalBFormSpectral

namespace ShenWork.IntervalConjugatePicard

#check hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional
#check intervalConjugateMildSolution_pde_u_PID_unconditional

end ShenWork.IntervalConjugatePicard
```

```lean
import ShenWork.Paper2.IntervalBFormSpectralProviderDischargeOn

open Filter Topology Set

namespace ShenWork.IntervalConjugatePicard

#check pde_u_of_localized_data_with_hpost_on
#check pde_u_PID_global_restart_on
#check intervalConjugateMildSolution_pde_u_PID_global_restart_on

end ShenWork.IntervalConjugatePicard
```

```lean
import ShenWork.Paper2.IntervalBankChemSliceFix

open Set Filter Topology

namespace ShenWork.Paper2.BankChemSliceFix

#check chemDivLift_continuousOn_Ioo
#check ChemDivCosineFourierDataIoo
#check chemDiv_cosineSeries_summable_Ioo
#check chemDiv_cosineFourier_convergence_Ioo
#check coupledChemDiv_cosineSeries_summable_Ioo
#check coupledChemDiv_cosineFourier_convergence_Ioo
#check chemDivCosineFourierDataIoo_of_repr
#check hchemFourier_of_chemDiv_C2Neumann_reexport

end ShenWork.Paper2.BankChemSliceFix
```

## 1. Exact `BFormBankedInputs.hchemCont` field

In `ShenWork/Paper2/IntervalBFormDirectClassical.lean`, `BFormBankedInputs` currently contains:

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open Filter Topology Set

open ShenWork.IntervalDomain
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData ConjugatePicardInfThresholdData
   conjugatePicardLimit paperPositiveFloor)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemicalConcentration)
open ShenWork.HeatKernelGradientEstimates
  (heatGradientLinftyLinftyConstant)
open ShenWork.IntervalNeumannFullKernel
  (cosineCoeffs)
open ShenWork.Paper2

namespace ShenWork.Paper2.BFormDirectClassical

-- Relevant excerpt, as read:
--
-- structure BFormBankedInputs
--     (p : CM2Params) {u₀ : intervalDomainPoint → ℝ}
--     (DB : ConjugateMildExistenceData p u₀) where
--   ...
--   hchemCont : ∀ t, 0 < t → t < DB.T →
--     Continuous
--       (intervalDomainConstExtend
--         (fun x : intervalDomainPoint =>
--           intervalDomainChemotaxisDiv p
--             ((conjugatePicardLimit p u₀ DB.T) t)
--             (coupledChemicalConcentration p
--               (conjugatePicardLimit p u₀ DB.T) t) x))
--   hchemFourier : ∀ t, 0 < t → t < DB.T →
--     Summable (fun n : ℤ =>
--       fourierCoeff
--         (ShenWork.IntervalCosineInversion.reflCircle
--           (intervalDomainConstExtend
--             (fun x : intervalDomainPoint =>
--               intervalDomainChemotaxisDiv p
--                 ((conjugatePicardLimit p u₀ DB.T) t)
--                 (coupledChemicalConcentration p
--                   (conjugatePicardLimit p u₀ DB.T) t) x))) n)
#check BFormBankedInputs

end ShenWork.Paper2.BFormDirectClassical
```

This is exactly the false endpoint-continuity statement documented by `IntervalBankSourceSliceLeaves.lean` and `IntervalBankChemSliceFix.lean`: the representative is the constant extension of `intervalDomainChemotaxisDiv`, but the endpoint values forced by the zero-extension derivative convention do not match the interior one-sided limit in general.

## 2. Is `hchemCont` actually used by `intervalConjugateMildSolution_pde_u_PID_unconditional`?

Yes. It is not dead in the current direct-classical path.

`BFormBankedInputs.hpde_u` in `IntervalBFormDirectClassical.lean` passes the bank fields to `intervalConjugateMildSolution_pde_u_PID_unconditional`:

```lean
import ShenWork.Paper2.IntervalBFormDirectClassical

open Filter Topology Set

namespace ShenWork.Paper2.BFormDirectClassical

-- Current shape, relevant tail:
--
-- theorem BFormBankedInputs.hpde_u ... (B : BFormBankedInputs p DB) : ... :=
--   ShenWork.IntervalConjugatePicard.intervalConjugateMildSolution_pde_u_PID_unconditional
--       DB B.huPaper B.Hinf B.hsmall
--       (cosineCoeffs (intervalDomainLift u₀)) B.haInit
--       B.hlogSrc B.hchemSrc B.hB_global
--       B.hlogCont B.hlogFourier B.hchemCont B.hchemFourier
#check BFormBankedInputs.hpde_u

end ShenWork.Paper2.BFormDirectClassical
```

Inside `IntervalBFormPIDUnconditional.lean`, `intervalConjugateMildSolution_pde_u_PID_unconditional` first builds a `HasBFormSpectralPdeAgreement` by calling `hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional`:

```lean
import ShenWork.Paper2.IntervalBFormPIDUnconditional

open Filter Topology Set

namespace ShenWork.IntervalConjugatePicard

-- theorem intervalConjugateMildSolution_pde_u_PID_unconditional ...
--   have Hpde : HasBFormSpectralPdeAgreement p D.T
--       (conjugatePicardLimit p u₀ D.T) :=
--     hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional
--       D hu₀ Hinf hsmall aInit haInit hlogSrc hchemSrc hB_global
--       hlogCont hlogFourier hchemCont hchemFourier
--   exact intervalConjugateMildSolution_pde_u_from_picard_data_and_spectral D Hpde
#check intervalConjugateMildSolution_pde_u_PID_unconditional

end ShenWork.IntervalConjugatePicard
```

Then `hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional` uses `hchemCont` to build the chem-div Fourier package by the old const-extension provider:

```lean
import ShenWork.Paper2.IntervalBFormPIDUnconditional

open Filter Topology Set

namespace ShenWork.IntervalConjugatePicard

-- Current use, excerpt:
--
-- have hchemData : ∀ t, 0 < t → t < D.T →
--     ChemDivCosineFourierData p (u t)
--       (coupledChemicalConcentration p u t) := by
--   intro t ht htT
--   exact chemDivCosineFourierData_constExtend p (u t)
--     (coupledChemicalConcentration p u t)
--     (by simpa [u] using hchemCont t ht htT)
--     (by simpa [u] using hchemFourier t ht htT)
#check hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional

end ShenWork.IntervalConjugatePicard
```

So current consumption is real: `hchemCont` supplies `ChemDivCosineFourierData.continuous_representative` for the representative hard-wired to `intervalDomainConstExtend (chemDiv)`.

## 3. What does the old chem-div consumer actually need?

The old package is in `IntervalBFormSpectralHchem.lean`:

```lean
import ShenWork.Paper2.IntervalBFormPIDUnconditional

open Set

namespace ShenWork.IntervalBFormSpectral

-- structure ChemDivCosineFourierData
--     (p : CM2Params) (u v : intervalDomainPoint → ℝ) where
--   representative : ℝ → ℝ
--   continuous_representative : Continuous representative
--   representative_eq_chemDiv :
--     Set.EqOn representative (chemDivLift p u v) (Set.Icc (0 : ℝ) 1)
--   fourier_summable :
--     Summable (fun n : ℤ => fourierCoeff (reflCircle representative) n)
#check ChemDivCosineFourierData

-- The old constExtend builder demands global continuity of the false representative:
#check chemDivCosineFourierData_constExtend

-- The two downstream consumers only evaluate at interior points:
#check chemDiv_cosineSeries_summable
#check chemDiv_cosineFourier_convergence

end ShenWork.IntervalBFormSpectral
```

The important asymmetry:

* The **type** requires global `Continuous representative` and `EqOn ... (Icc 0 1)`.
* The **actual convergence/summability consumers** require `hx : x.1 ∈ Ioo 0 1` and only evaluate at interior points.

That matches the audit: endpoint values do not matter for the PDE identity, but the current representative package has an endpoint-sensitive shape.

## 4. Why `ContinuousOn ... (Ioo 0 1)` alone is not enough

A field like

```lean
hchemContIoo : ∀ t, 0 < t → t < DB.T →
  ContinuousOn
    (intervalDomainConstExtend
      (fun x : intervalDomainPoint => intervalDomainChemotaxisDiv p ... x))
    (Set.Ioo (0 : ℝ) 1)
```

or even

```lean
ContinuousOn (chemDivLift p u v) (Set.Ioo (0 : ℝ) 1)
```

is too weak for the current inversion machinery. The inversion theorem `intervalCosine_hasSum_pointwise` is used on a globally continuous representative and a Fourier-summable reflected representative. The landed replacement in `IntervalBankChemSliceFix.lean` therefore does not just switch `Continuous` to `ContinuousOn`; it introduces a new package:

```lean
import ShenWork.Paper2.IntervalBankChemSliceFix

open Set Filter Topology

namespace ShenWork.Paper2.BankChemSliceFix

-- structure ChemDivCosineFourierDataIoo
--     (p : CM2Params) (u v : intervalDomainPoint → ℝ) where
--   representative : ℝ → ℝ
--   continuous_representative : Continuous representative
--   representative_eq_chemDiv :
--     Set.EqOn representative (chemDivLift p u v) (Set.Ioo (0 : ℝ) 1)
--   fourier_summable :
--     Summable (fun n : ℤ => fourierCoeff (reflCircle representative) n)
#check ChemDivCosineFourierDataIoo

#check chemDivCosineFourierDataIoo_of_repr
#check chemDiv_cosineSeries_summable_Ioo
#check chemDiv_cosineFourier_convergence_Ioo
#check coupledChemDiv_cosineSeries_summable_Ioo
#check coupledChemDiv_cosineFourier_convergence_Ioo

end ShenWork.Paper2.BankChemSliceFix
```

This is the correct payload: a globally continuous surrogate `ψ` that agrees with the physical chem-div lift on the open interval, plus Fourier summability for `reflCircle ψ`.

Thus a useful bank replacement is not `hchemCont : ContinuousOn ... Ioo`; it is either direct `hchemDataIoo` or explicit surrogate fields:

```lean
-- Preferred direct package field:
hchemDataIoo : ∀ t, 0 < t → t < DB.T →
  ShenWork.Paper2.BankChemSliceFix.ChemDivCosineFourierDataIoo p
    ((conjugatePicardLimit p u₀ DB.T) t)
    (coupledChemicalConcentration p
      (conjugatePicardLimit p u₀ DB.T) t)
```

or:

```lean
-- Equivalent expanded shape:
hchemRep : ∀ t, 0 < t → t < DB.T → ℝ → ℝ
hchemRep_cont : ∀ t ht htT, Continuous (hchemRep t ht htT)
hchemRep_eq : ∀ t ht htT,
  Set.EqOn (hchemRep t ht htT)
    (ShenWork.IntervalBFormSpectral.chemDivLift p
      ((conjugatePicardLimit p u₀ DB.T) t)
      (coupledChemicalConcentration p
        (conjugatePicardLimit p u₀ DB.T) t))
    (Set.Ioo (0 : ℝ) 1)
hchemRep_fourier : ∀ t ht htT,
  Summable (fun n : ℤ =>
    fourierCoeff (ShenWork.IntervalCosineInversion.reflCircle
      (hchemRep t ht htT)) n)
```

## 5. Can `hchemCont` be removed entirely?

Only after changing the consumer interface.

### Not safe in the current path

Current path:

```text
BFormBankedInputs.hpde_u
  → intervalConjugateMildSolution_pde_u_PID_unconditional
  → hasBFormSpectralPdeAgreement_conjugatePicardLimit_of_PID_unconditional
  → chemDivCosineFourierData_constExtend
  → ChemDivCosineFourierData.continuous_representative
```

In this path, deleting `hchemCont` breaks the call to `chemDivCosineFourierData_constExtend`.

### Safe after replacing the consumer with Ioo package

If the bank carries `hchemDataIoo` and the PDE theorem uses the `_Ioo` consumers, then there is no need for `hchemCont`.

Suggested shape:

```lean
import ShenWork.Paper2.IntervalBankChemSliceFix

open Set Filter Topology

-- In the bank, replace false hchemCont (+ maybe the old hchemFourier shape)
-- by a direct endpoint-insensitive package:
--
-- hchemDataIoo : ∀ t, 0 < t → t < DB.T →
--   ShenWork.Paper2.BankChemSliceFix.ChemDivCosineFourierDataIoo p
--     ((conjugatePicardLimit p u₀ DB.T) t)
--     (coupledChemicalConcentration p
--       (conjugatePicardLimit p u₀ DB.T) t)
```

Then in the PDE proof, replace old calls:

```lean
-- old:
-- ShenWork.IntervalBFormSpectral.coupledChemDiv_cosineFourier_convergence
--   p u t₀ (hchemData t₀ ht₀ ht₀T) hx
--
-- ShenWork.IntervalBFormSpectral.coupledChemDiv_cosineSeries_summable
--   p u t₀ (hchemData t₀ ht₀ ht₀T) hx
```

with:

```lean
-- new:
-- ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineFourier_convergence_Ioo
--   p u t₀ (hchemDataIoo t₀ ht₀ ht₀T) hx
--
-- ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineSeries_summable_Ioo
--   p u t₀ (hchemDataIoo t₀ ht₀ ht₀T) hx
```

Because the PDE conclusion has `x ∈ intervalDomain.inside`, these calls already have exactly the required `hx : x.1 ∈ Ioo 0 1`.

## 6. Does the windowed `On` PDE identity still need `hchemCont`?

### Current `On` theorem: still needs a chem-div data package, but not necessarily `hchemCont`

The windowed theorem currently has this argument:

```lean
import ShenWork.Paper2.IntervalBFormSpectralProviderDischargeOn

open Filter Topology Set

namespace ShenWork.IntervalConjugatePicard

-- theorem pde_u_of_localized_data_with_hpost_on ...
--   (hchemData : ∀ t, 0 < t → t < D.T →
--     ChemDivCosineFourierData p
--       ((conjugatePicardLimit p u₀ D.T) t)
--       (coupledChemicalConcentration p
--         (conjugatePicardLimit p u₀ D.T) t)) :
--   ∀ t x, 0 < t → t < D.T → x ∈ intervalDomain.inside → ...
#check pde_u_of_localized_data_with_hpost_on
#check intervalConjugateMildSolution_pde_u_PID_global_restart_on

end ShenWork.IntervalConjugatePicard
```

Inside it, the chem-div data is consumed only through interior calls:

```lean
-- Current body excerpt:
--
-- have hchem :
--     (∑' n, coupledChemDivSourceCoeffs p u t₀ n * cosineMode n x.1)
--       = intervalDomain.chemotaxisDiv p (u t₀)
--           (ShenWork.IntervalMildToClassical.mildChemicalConcentration p u t₀) x :=
--   ShenWork.IntervalBFormSpectral.coupledChemDiv_cosineFourier_convergence
--     p u t₀ (hchemData t₀ ht₀ ht₀T) hx
--
-- have hsum_chem := ShenWork.IntervalBFormSpectral.coupledChemDiv_cosineSeries_summable
--   p u t₀ (hchemData t₀ ht₀ ht₀T) hx
```

So the windowed `On` theorem does **not** need the false `hchemCont` statement as such. It only needs enough chem-div Fourier data to perform interior convergence and summability. The present signature still names the old `ChemDivCosineFourierData`, so if one insists on constructing that old package via `chemDivCosineFourierData_constExtend`, one is back to the false `hchemCont`. But the theorem body is already compatible with the Ioo replacement.

### Correct `On`-fixed shape

A fixed theorem should take:

```lean
hchemDataIoo : ∀ t, 0 < t → t < D.T →
  ShenWork.Paper2.BankChemSliceFix.ChemDivCosineFourierDataIoo p
    ((conjugatePicardLimit p u₀ D.T) t)
    (coupledChemicalConcentration p
      (conjugatePicardLimit p u₀ D.T) t)
```

and use:

```lean
ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineFourier_convergence_Ioo
ShenWork.Paper2.BankChemSliceFix.coupledChemDiv_cosineSeries_summable_Ioo
```

Then `hchemCont` is gone. The source time-C¹ windowing (`DuhamelSourceTimeC1On`) solves a separate problem: it avoids needing a global `DuhamelSourceTimeC1` witness inside `HasBFormSpectralPdeAgreement`. It does not, by itself, solve the endpoint-continuity problem unless the chem-div Fourier package is also changed to the Ioo/surrogate version.

## 7. Concrete recommendation

Do **not** replace

```lean
hchemCont : Continuous (intervalDomainConstExtend chemDiv)
```

by

```lean
hchemCont : ContinuousOn (intervalDomainConstExtend chemDiv) (Set.Ioo 0 1)
```

because that still does not provide the globally continuous Fourier-inversion representative.

Instead, change the bank and consumers to one of these two designs:

### Option A — best: carry the finished Ioo package

```lean
import ShenWork.Paper2.IntervalBankChemSliceFix

open Set Filter Topology

-- Replace hchemCont/hchemFourier with one endpoint-insensitive package:
--
-- hchemDataIoo : ∀ t, 0 < t → t < DB.T →
--   ShenWork.Paper2.BankChemSliceFix.ChemDivCosineFourierDataIoo p
--     ((conjugatePicardLimit p u₀ DB.T) t)
--     (coupledChemicalConcentration p
--       (conjugatePicardLimit p u₀ DB.T) t)
```

This is the cleanest for consumers: they no longer know about the false `constExtend(chemDiv)` representative.

### Option B — carry surrogate pieces

```lean
import ShenWork.Paper2.IntervalBankChemSliceFix

open Set Filter Topology

-- Carry a smooth/global representative explicitly:
--
-- hchemRep : ∀ t, 0 < t → t < DB.T → ℝ → ℝ
-- hchemRep_cont : ∀ t ht htT, Continuous (hchemRep t ht htT)
-- hchemRep_eq : ∀ t ht htT,
--   Set.EqOn (hchemRep t ht htT)
--     (ShenWork.IntervalBFormSpectral.chemDivLift p
--       ((conjugatePicardLimit p u₀ DB.T) t)
--       (coupledChemicalConcentration p
--         (conjugatePicardLimit p u₀ DB.T) t))
--     (Set.Ioo (0 : ℝ) 1)
-- hchemRep_fourier : ∀ t ht htT,
--   Summable (fun n : ℤ =>
--     fourierCoeff (ShenWork.IntervalCosineInversion.reflCircle
--       (hchemRep t ht htT)) n)
--
-- Then build:
--
-- ShenWork.Paper2.BankChemSliceFix.chemDivCosineFourierDataIoo_of_repr
```

Option A is simpler and less error-prone.

## Final answer to the user’s specific questions

### “Can I just REMOVE the field entirely?”

Not in the current direct-classical path. It is used to build `ChemDivCosineFourierData` via `chemDivCosineFourierData_constExtend`.

You can remove it only after replacing the old chem-div Fourier-data API with `ChemDivCosineFourierDataIoo` or direct surrogate data. In that reworked path, the field should disappear because endpoint continuity is irrelevant.

### “Or change it to `ContinuousOn ... (Ioo 0 1)`?”

Not by itself. `ContinuousOn` on the interior is true/satisfiable, but it is not enough for the old Fourier inversion package. The consumer needs a globally continuous representative plus Fourier summability. Use the `ChemDivCosineFourierDataIoo` package instead.

### “Is it actually used by `intervalConjugateMildSolution_pde_u_PID_unconditional`, or passed through?”

It is actually used, but only to construct `hchemData : ChemDivCosineFourierData ...`. After that, the endpoint values are not used by the PDE identity; the Fourier convergence is evaluated only at interior points.

### “If the windowed On PDE identity replaces the global PDE identity, does it still need hchemCont?”

Conceptually no. The current `On` theorem still takes old `ChemDivCosineFourierData`, so as written it still needs some old-style chem-div data. But it does not need the false `hchemCont` once rewired to take `ChemDivCosineFourierDataIoo` and call the `_Ioo` consumers. The `On` path removes the global source-time-C¹ obstruction; the Ioo package removes Barrier C.
