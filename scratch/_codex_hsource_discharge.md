# Codex Spec: Discharge `hsource` (ResolverSourceSummable) from EWA structure

## Goal

Create ONE new file `ShenWork/Wiener/EWA/SourceResolverSummabilityDischarge.lean`
containing TWO theorems:

1. `resolverSourceSummable_of_heat` — constructs `ResolverSourceSummable` from heat datum
2. `vdEWA_center_floor_heat_discharged` — strengthened center floor WITHOUT `hsource` hypothesis

## Why this matters

`hsource` (`ResolverSourceSummable`) is the single most fundamental "secondary atom" —
it feeds into `vdEWA_center_floor_heat`, which feeds into the entire contraction tower,
which feeds into `Theorem_1_1`. Currently it is CARRIED as a hypothesis. This file
DISCHARGES it from the EWA algebra.

## The breakthrough insight (already verified)

The existing infrastructure provides:
- `slice_smul_realPow_eq_source` (FluxRealizeEmbed.lean:95) produces `hWslice`
  WITHOUT needing `hsource`
- `summable_abs_of_slice_eq` (ParityFoundations.lean:99) turns `hWslice` INTO
  `ResolverSourceSummable`

So: build `hWslice` (lines 96-143 of SourceCenterFloorHeat.lean, which do NOT
use `hsource`), then apply `summable_abs_of_slice_eq`.

## Theorem 1: `resolverSourceSummable_of_heat`

```lean
theorem resolverSourceSummable_of_heat (p : CM2Params) (u₀ : ℝ → ℝ)
    (hu₀ : Continuous u₀)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : ∀ y, δ ≤ u₀ y)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀)))
    (uR : ℝ → intervalDomainPoint → ℝ)
    (huR : uR = fun t pt =>
      unitIntervalCosineHeatValue t (cosineCoeffs u₀) pt.1)
    (τ : TimeDom T) :
    ResolverSourceSummable p (uR τ.1) := by
```

### Proof (copy lines 92-143 of SourceCenterFloorHeat.lean, add punchline)

The proof is EXACTLY the first half of `vdEWA_center_floor_heat`'s proof,
up to and including `hWslice`, plus one final line:

```lean
  set c₀ : ℕ → ℝ := cosineCoeffs u₀ with hc₀
  set u₀E : WA 1 := ⟨ofCosineCoeffs c₀, hmem⟩ with hu₀E
  -- Step 1: even-real parity (NO hsource needed)
  have hheatER : EvenRealEWA (heatEWA (T := T) u₀E) :=
    heatEWA_evenReal c₀ hmem
  have hER : EvenRealEWA (GWA.incl (by omega : (0 : ℕ) ≤ 1)
      ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ)) :=
    ((realPowEWA_evenReal FnegEWA_evenReal_Hyp_proved
      hheatER p.γ).smul_real p.ν).incl (by omega)
  -- Step 2: heat floor (NO hsource needed)
  have hheatFloor : UniformFloor (heatEWA (T := T) u₀E) δ :=
    heatEWA_uniformFloor hu₀ hfloor hsumc hmem
  -- Step 3: reality of heat evaluation (NO hsource needed)
  have hheatReal : ∀ (τ' : TimeDom T) (x : WA.Circ),
      (evalST τ' x (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        (heatEWA (T := T) u₀E))).im = 0 := by
    intro τ' x
    induction x using QuotientAddGroup.induction_on with
    | _ x =>
      rw [heatEWA_evalST_eq_cosineHeatValue c₀ hsumc hmem τ' x,
        Complex.ofReal_im]
  -- Step 4: lift identity (NO hsource needed)
  have hlift : ∀ (t : ℝ) (y : ℝ),
      y ∈ Set.Icc (0 : ℝ) 1 →
      intervalDomainLift (uR t) y =
        unitIntervalCosineHeatValue t c₀ y := by
    intro t y hy
    rw [intervalDomainLift, dif_pos hy, huR]
  -- Step 5: hRealize (NO hsource needed)
  have hRealize : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (x : WA.Circ) (GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA (heatEWA (T := T) u₀E) p.γ))
        = ((p.ν * intervalDomainLift (uR τ.1) x ^ p.γ : ℝ)
            : ℂ) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx.1.le, hx.2.le⟩
    have hincl_smul :
        GWA.incl (by omega : (0 : ℕ) ≤ 1)
          ((p.ν : ℂ) • realPowEWA
            (heatEWA (T := T) u₀E) p.γ)
        = (p.ν : ℂ) • GWA.incl (by omega : (0 : ℕ) ≤ 1)
            (realPowEWA (heatEWA (T := T) u₀E) p.γ) := by
      rw [← GWA.gIncl_apply, map_smul, GWA.gIncl_apply]
    rw [hincl_smul, evalST_smul]
    rw [realPowEWA_eval p.hγ.le hδpos hheatFloor
      hheatReal τ (x : WA.Circ)]
    rw [heatEWA_evalST_eq_cosineHeatValue c₀ hsumc hmem τ x,
      Complex.ofReal_re]
    rw [hlift (τ : ℝ) x hxIcc]
    push_cast
    ring
  -- Step 6: hWslice (NO hsource needed — this IS the crux)
  have hWslice : (sliceWA τ (GWA.incl (by omega : (0 : ℕ) ≤ 1)
        ((p.ν : ℂ) • realPowEWA
          (heatEWA (T := T) u₀E) p.γ))).toFun
      = ofCosineCoeffs (resolverSourceReCoeff p (uR τ.1)) :=
    slice_smul_realPow_eq_source p uR
      (heatEWA (T := T) u₀E) τ hER hRealize
  -- PUNCHLINE: EWA membership gives intrinsic ℓ¹ summability
  exact summable_abs_of_slice_eq hWslice
```

NOTE: The `hRealize` in the original `vdEWA_center_floor_heat` is quantified
over ALL `τ`, but `slice_smul_realPow_eq_source` takes `hRealize` for a
SPECIFIC `τ`. In the original, it uses `hRealize τ`. Here, we build
`hRealize` for the specific `τ` from the theorem's parameter directly.

## Theorem 2: `vdEWA_center_floor_heat_discharged`

```lean
theorem vdEWA_center_floor_heat_discharged
    (p : CM2Params) (u₀ : ℝ → ℝ) (hu₀ : Continuous u₀)
    {δ : ℝ} (hδpos : 0 < δ) (hfloor : ∀ y, δ ≤ u₀ y)
    (hνpos : 0 ≤ p.ν)
    (hsumc : Summable (fun k => |cosineCoeffs u₀ k|))
    (hmem : MemW 1 (ofCosineCoeffs (cosineCoeffs u₀))) :
    UniformFloor (1 + vdEWA p.μ p.ν p.γ p.hμ
      (heatEWA (T := T) (⟨ofCosineCoeffs (cosineCoeffs u₀),
        hmem⟩ : WA 1))) 1 := by
  set uR : ℝ → intervalDomainPoint → ℝ :=
    fun t pt => unitIntervalCosineHeatValue t
      (cosineCoeffs u₀) pt.1
  have hsource : ∀ τ : TimeDom T,
      ResolverSourceSummable p (uR τ.1) :=
    resolverSourceSummable_of_heat p u₀ hu₀
      hδpos hfloor hsumc hmem uR rfl
  exact vdEWA_center_floor_heat p u₀ hu₀ hδpos hfloor
    hνpos hsumc hmem uR rfl hsource
```

## Imports

```lean
import ShenWork.Wiener.EWA.SourceCenterFloorHeat
import ShenWork.Wiener.EWA.ParityFoundations
```

These imports transitively bring in everything needed:
- `SourceCenterFloorHeat` brings `vdEWA_center_floor_heat`, `heatEWA_evenReal`,
  `heatEWA_uniformFloor`, `heatEWA_evalST_eq_cosineHeatValue`, `cosineHeatValue_continuous`,
  `cosineHeatValue_ge_floor_all`, `intervalDomainLift`
- `SourceCenterFloorHeat` imports `FluxRealizeEmbed` which has `slice_smul_realPow_eq_source`
- `ParityFoundations` has `summable_abs_of_slice_eq`

Actually, `SourceCenterFloorHeat` already imports `FluxRealizeEmbed`, and `ParityFoundations`
may already be transitively imported. Check with `lake build` — if `ParityFoundations` is
already available, the explicit import is harmless.

## Opens

Copy the opens from `SourceCenterFloorHeat.lean` (lines 39-44):
```lean
open scoped BigOperators
open Set
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (cosineCoeffs_congr_on_Icc)
```

## File structure

```lean
import ShenWork.Wiener.EWA.SourceCenterFloorHeat
import ShenWork.Wiener.EWA.ParityFoundations

/-!
# Discharge `hsource` (ResolverSourceSummable) from EWA structure

`resolverSourceSummable_of_heat` proves that for heat initial data
with floor `δ > 0` and ℓ¹ cosine coefficients, the resolver source
coefficients `resolverSourceReCoeff p (uR τ.1)` are automatically
ℓ¹-summable — derived from the EWA structure, NOT carried as an
external hypothesis.

The chain: even-real parity → hRealize → hWslice →
`summable_abs_of_slice_eq` → ResolverSourceSummable.

`vdEWA_center_floor_heat_discharged` is the strengthened center
floor theorem that drops the `hsource` hypothesis entirely.
-/

open scoped BigOperators
open Set
open ShenWork.GWA ShenWork.Wiener ShenWork.CosineSpectrum
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverSourceCoeff)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

-- Theorem 1 here
-- Theorem 2 here
-- #print axioms for both

end ShenWork.EWA
```

## Verification

```bash
cd ~/repos/Shen_work
lake build ShenWork.Wiener.EWA.SourceResolverSummabilityDischarge 2>&1 | tail -20
```

Must compile with `#print axioms` showing ONLY `[propext, Classical.choice, Quot.sound]`.

## CRITICAL constraints

- NO sorry, NO axiom, NO native_decide, NO admit
- Line length ≤ 100 characters
- Do NOT modify any existing files
- The proof of theorem 1 is essentially lines 92-143 of
  `SourceCenterFloorHeat.lean` with the punchline `summable_abs_of_slice_eq`
- If any step fails to elaborate, check:
  (a) Universe annotations on `T`
  (b) Coercion `(τ : ℝ)` vs `τ.1` for `TimeDom` subtypes
  (c) `WA.Circ` coercion from `ℝ` to `QuotientAddGroup`
  (d) Whether `FnegEWA_evenReal_Hyp_proved` needs explicit import

## If stuck

Report EXACTLY which step fails with the elaboration error. The most
likely failure points are:
- `realPowEWA_eval` argument order or implicit variable mismatch
- `heatEWA_evalST_eq_cosineHeatValue` needing explicit `(T := T)`
- `slice_smul_realPow_eq_source` needing the quantifier over `τ`
  adjusted (the original has `∀ τ, hRealize τ` but we build for a
  specific `τ`)
