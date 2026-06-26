# Q929 (cron3): chemotaxis boundary facts

## Verdict

1. **Aggregate Neumann is available, but not as a theorem literally named for `NeumannBoundarySlice Dw`.** The intrinsic Wiener/Paper2 theorem is the full-source cosine-synthesis theorem `ShenWork.EWA.SourceStrongSolutionData.isClassicalSpatialSlice`, with atom lemmas `ShenWork.EWA.fullSourceCoeff_neumann_left` and `ShenWork.EWA.fullSourceCoeff_neumann_right`. These prove endpoint Neumann for the **full aggregate mild slice**

   `x ↦ ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x`.

   They do not prove boundary vanishing for any individual mild leg.

2. **Do not assume per-leg Neumann for the chemotaxis leg (`chemDeriv`).** I found no Lean theorem of that shape. The only `chemDeriv` occurrence I found is descriptive text in `ShenWork/Wiener/EWA/SourceTimeRegularityMajorant.lean`, where it is the spectral time-derivative coefficient leg

   `aₙ(t) - λₙ * duhamelSpectralCoeff a t n`.

   The C1eta assembly explicitly says the Neumann fact is a PDE no-flux invariant of the full solution, not a termwise property of the chemotaxis leg. The source-slice C²-Neumann file also records the chem-source C²-Neumann data as a residual requiring stronger regularity (`u ∈ C³`, `v ∈ C⁴`), so it is not banked/discharged.

3. **Keep `NeumannBoundarySlice` aggregate-only.** It is already the right residual shape. Discharge it by a bridge from the aggregate full-source slice, or by the lift-extension endpoint lemmas when the global function is literally the zero-extension lift and the required endpoint nonzero facts are available. Do not add boundary fields for `initLeg`, `chemLeg`, or `reactLeg`.

## Exact Lean names/signatures

```lean
import ShenWork.Paper2.ChemMildC1etaAssembly
import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.PDE.IntervalCosineSliceRegularity
import ShenWork.PDE.IntervalLiftEndpointDeriv

open scoped BigOperators
open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)
```

### Current residual shape

From `ShenWork/Paper2/ChemMildC1etaAssembly.lean`:

```lean
namespace ShenWork.Paper2

#check NeumannBoundarySlice
-- NeumannBoundarySlice : (ℝ → ℝ) → Prop

-- Exact structure:
-- structure NeumannBoundarySlice (Dw : ℝ → ℝ) : Prop where
--   deriv_zero : Dw 0 = 0
--   deriv_one  : Dw 1 = 0

#check chemMild_positiveTime_C1eta_slice
#check chemMild_positiveTime_wiener_l1

end ShenWork.Paper2
```

The important consumer shape is:

```lean
-- chemMild_positiveTime_C1eta_slice consumes:
--   (D : DifferentiatedMildSlice χ₀ η w Dw initLeg chemLeg reactLeg Ainit Achem Areact)
--   (N : NeumannBoundarySlice Dw)
-- and produces:
--   Differentiable ℝ w ∧ (deriv w 0 = 0 ∧ deriv w 1 = 0) ∧ ...
```

### Intrinsic aggregate theorem

From `ShenWork/Wiener/EWA/SourceStrongSolution.lean`:

```lean
namespace ShenWork.EWA

#check fullSourceCoeff_neumann_left
-- fullSourceCoeff_neumann_left (p : CM2Params)
--   (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {t : ℝ}
--   (hsum : Summable (fun n => unitIntervalCosineEigenvalue n *
--     |fullSourceCoeff p u u₀cos t n|)) :
--   deriv (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) 0 = 0

#check fullSourceCoeff_neumann_right
-- fullSourceCoeff_neumann_right (p : CM2Params)
--   (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) {t : ℝ}
--   (hsum : Summable (fun n => unitIntervalCosineEigenvalue n *
--     |fullSourceCoeff p u u₀cos t n|)) :
--   deriv (fun x => ∑' n, fullSourceCoeff p u u₀cos t n * cosineMode n x) 1 = 0

#check SourceStrongSolutionData.isClassicalSpatialSlice
-- SourceStrongSolutionData.isClassicalSpatialSlice
--   (D : SourceStrongSolutionData T (μ := μ) (ν := ν) (γ := γ) hμ p) :
--   ContDiff ℝ 2
--       (fun x => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x)
--     ∧ deriv
--         (fun x => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x) 0 = 0
--     ∧ deriv
--         (fun x => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x) 1 = 0
--     ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
--         intervalDomainLift (D.u D.t) x =
--           ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n x

end ShenWork.EWA
```

So the intrinsic theorem is aggregate/full-slice, not per-leg and not directly the `NeumannBoundarySlice Dw` wrapper.

## Why chem per-leg Neumann should not be added

From `ShenWork/Paper2/ChemMildC1etaAssembly.lean`, the chem leg is only the differentiated mild chem contribution:

```lean
namespace ShenWork.Paper2

#check chemDuhamelLeg
-- chemDuhamelLeg (t₀ : ℝ) (Q : ℝ → ℝ → ℝ) : ℝ → ℝ
-- def body:
--   fun x => ∫ s in (0:ℝ)..t₀,
--     unitIntervalCosineHeatSecondValue (t₀ - s) (cosineCoeffs (Q s)) (clamp01 x)

#check differentiatedMildSlice_of_brick4_chem
-- This constructor proves the chem_holder field for chemDuhamelLeg.
-- It does not take or prove endpoint-Neumann fields for the chem leg.

end ShenWork.Paper2
```

From `ShenWork/Wiener/EWA/SourceTimeRegularity.lean`, the term informally called `CHEMderiv` is a coefficient-time-derivative leg, not a spatial boundary fact:

```lean
namespace ShenWork.EWA

#check fullSourceCoeffDot
-- fullSourceCoeffDot p u u₀cos t n =
--   heat derivative leg
--   + (-p.χ₀) * (coupledChemDivSourceCoeffs p u t n
--       - unitIntervalCosineEigenvalue n
--         * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
--   + logistic derivative leg

end ShenWork.EWA
```

From `ShenWork/Wiener/EWA/SourceSliceC2Neumann.lean`, the chem-source C²-Neumann facts are still residual. The file says the banked regularity gives only C², while the chem source C²-Neumann route needs `lift u ∈ C³` and `lift v ∈ C⁴`. The residual theorem still carries `hC2`, `htend0`, `htend1`, `hbc0`, and `hbc1` as hypotheses:

```lean
namespace ShenWork.EWA

#check realSlice_hchemInv_C2Neumann_residual
-- realSlice_hchemInv_C2Neumann_residual
--   ...
--   (hC2 : ∀ t ∈ Set.Ioo (0 : ℝ) T, ContDiffOn ℝ 2 ...)
--   (htend0 : ∀ t ∈ Set.Ioo (0 : ℝ) T, Tendsto ... (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
--   (htend1 : ∀ t ∈ Set.Ioo (0 : ℝ) T, Tendsto ... (nhdsWithin 1 (Set.Iio 1)) (nhds 0))
--   (hbc0 : ∀ t ∈ Set.Ioo (0 : ℝ) T, deriv ... 0 = 0)
--   (hbc1 : ∀ t ∈ Set.Ioo (0 : ℝ) T, deriv ... 1 = 0) :
--   ...

end ShenWork.EWA
```

Therefore the safe rule is: no `chemLeg_neumann0`, no `chemLeg_neumann1`, no `chemDeriv_boundary`. Boundary should be aggregate-only.

## Recommended bridge encoding

Do **not** change `DifferentiatedMildSlice` to carry per-leg endpoint facts. Keep:

```lean
structure NeumannBoundarySlice (Dw : ℝ → ℝ) : Prop where
  deriv_zero : Dw 0 = 0
  deriv_one  : Dw 1 = 0
```

Then add a bridge that converts the aggregate full-source theorem into that residual. This should live **after** both worlds are available, preferably in a small bridge file such as:

`ShenWork/Wiener/EWA/SourceStrongNeumannBoundarySlice.lean`

or, if layering permits, immediately after `SourceStrongSolutionData.isClassicalSpatialSlice` in `ShenWork/Wiener/EWA/SourceStrongSolution.lean`. Avoid placing it inside `differentiatedMildSlice_of_brick4_chem`; that constructor is correctly only about the chem Hölder estimate.

```lean
import ShenWork.Paper2.ChemMildC1etaAssembly
import ShenWork.Wiener.EWA.SourceStrongSolution

open scoped BigOperators
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.CosineSpectrum (cosineMode)

namespace ShenWork.EWA

/-- Aggregate full-source Neumann, packaged in the `ChemMildC1etaAssembly` residual shape. -/
theorem SourceStrongSolutionData.neumannBoundarySlice_fullCoeff
    {T μ ν γ : ℝ} {hμ : 0 < μ} {p : CM2Params}
    (D : SourceStrongSolutionData T (μ := μ) (ν := ν) (γ := γ) hμ p) :
    ShenWork.Paper2.NeumannBoundarySlice
      (fun x => deriv
        (fun y => ∑' n,
          fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n y) x) := by
  obtain ⟨_hC2, hN0, hN1, _hrealizes⟩ := D.isClassicalSpatialSlice
  exact ⟨hN0, hN1⟩

end ShenWork.EWA
```

At the C1eta/Wiener call site, instantiate

```lean
Dw := fun x => deriv (fun y => ∑' n, fullSourceCoeff p D.u D.u₀cos D.t n * cosineMode n y) x
```

or use your existing `Dw` plus an equality/`HasDerivAt` bridge, and pass `Dstrong.neumannBoundarySlice_fullCoeff` as `N`.

If the assembly’s global `w` is literally the zero-extension lift `intervalDomainLift slice`, there is a separate endpoint-junk bridge available. This is not a per-leg chem fact; it is a global lift-extension fact.

```lean
import ShenWork.Paper2.ChemMildC1etaAssembly
import ShenWork.PDE.IntervalCosineSliceRegularity

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalCosineSliceRegularity
  (intervalDomainLift_deriv_left_endpoint_zero_of_ne
   intervalDomainLift_deriv_right_endpoint_zero_of_ne)

namespace ShenWork.Paper2

/-- Package zero-extension endpoint derivative facts as the aggregate residual. -/
theorem neumannBoundarySlice_of_lift_endpoint_nonzero
    {w : intervalDomainPoint → ℝ}
    (hne0 : intervalDomainLift w 0 ≠ 0)
    (hne1 : intervalDomainLift w 1 ≠ 0) :
    NeumannBoundarySlice (fun x => deriv (intervalDomainLift w) x) := by
  exact
    ⟨intervalDomainLift_deriv_left_endpoint_zero_of_ne hne0,
     intervalDomainLift_deriv_right_endpoint_zero_of_ne hne1⟩

/-- Same bridge when the carried derivative field `Dw` is supplied by `HasDerivAt`. -/
theorem neumannBoundarySlice_of_hasDeriv_lift_endpoint_nonzero
    {w : intervalDomainPoint → ℝ} {Dw : ℝ → ℝ}
    (hD : ∀ x : ℝ, HasDerivAt (intervalDomainLift w) (Dw x) x)
    (hne0 : intervalDomainLift w 0 ≠ 0)
    (hne1 : intervalDomainLift w 1 ≠ 0) :
    NeumannBoundarySlice Dw := by
  refine ⟨?_, ?_⟩
  · rw [← (hD 0).deriv]
    exact intervalDomainLift_deriv_left_endpoint_zero_of_ne hne0
  · rw [← (hD 1).deriv]
    exact intervalDomainLift_deriv_right_endpoint_zero_of_ne hne1

end ShenWork.Paper2
```

## Exact lift-extension lemmas to use

For endpoint point derivatives of the zero-extension lift:

```lean
import ShenWork.PDE.IntervalCosineSliceRegularity

open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)

#check ShenWork.IntervalCosineSliceRegularity.intervalDomainLift_deriv_left_endpoint_zero_of_ne
-- {w : intervalDomainPoint → ℝ} →
--   intervalDomainLift w 0 ≠ 0 →
--   deriv (intervalDomainLift w) 0 = 0

#check ShenWork.IntervalCosineSliceRegularity.intervalDomainLift_deriv_right_endpoint_zero_of_ne
-- {w : intervalDomainPoint → ℝ} →
--   intervalDomainLift w 1 ≠ 0 →
--   deriv (intervalDomainLift w) 1 = 0
```

For the aggregate cosine-slice closed-domain bridge and genuine one-sided Neumann limits:

```lean
import ShenWork.PDE.IntervalCosineSliceRegularity

#check ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_conjunct7
#check ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_neumann_limit_left
#check ShenWork.IntervalCosineSliceRegularity.intervalDomainCosineSlice_neumann_limit_right
```

For off-domain first-derivative zero and endpoint second-derivative residuals of the lift:

```lean
import ShenWork.PDE.IntervalLiftEndpointDeriv

#check ShenWork.IntervalLiftEndpointDeriv.lift_deriv_eq_zero_of_neg
-- (f : intervalDomainPoint → ℝ) → {x : ℝ} → x < 0 →
--   deriv (intervalDomainLift f) x = 0

#check ShenWork.IntervalLiftEndpointDeriv.lift_deriv_eq_zero_of_gt_one
-- (f : intervalDomainPoint → ℝ) → {x : ℝ} → 1 < x →
--   deriv (intervalDomainLift f) x = 0

#check ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_eq_zero_at_zero
-- (f : intervalDomainPoint → ℝ) →
--   deriv (deriv (intervalDomainLift f)) 0 = 0

#check ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_eq_zero_at_one
-- (f : intervalDomainPoint → ℝ) →
--   deriv (deriv (intervalDomainLift f)) 1 = 0

#check ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_abs_le_at_zero
#check ShenWork.IntervalLiftEndpointDeriv.lift_deriv2_abs_le_at_one
```

## Placement summary

- Keep `NeumannBoundarySlice` in `ChemMildC1etaAssembly.lean` as the aggregate residual.
- Place the aggregate discharge bridge after `SourceStrongSolutionData.isClassicalSpatialSlice` or in a new bridge file importing both `ChemMildC1etaAssembly` and `SourceStrongSolution`.
- Pass the resulting `NeumannBoundarySlice Dw` only at the final `chemMild_positiveTime_C1eta_slice` / `chemMild_positiveTime_wiener_l1` assembly call.
- Do not place endpoint fields in `differentiatedMildSlice_of_brick4_chem`.
- Do not assert chem-leg or chem-source per-leg endpoint Neumann unless a separate theorem proves exactly that; current files point the other way.
