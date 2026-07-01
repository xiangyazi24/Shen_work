# Q2762 (shen1) — safest next non-Zinan Moser edit

Repo: `xiangyazi24/Shen_work`  
Delivery branch: `chatgpt-scratch`  
Scope: non-Zinan files only.

I treated the two Zinan-owned producer files named in the prompt as off-limits. I did not inspect them, rely on them, or propose edits to them.

I inspected the non-Zinan interfaces that matter for this decision:

- `ShenWork/PDE/P3MoserIntegratedClosure.lean`
- `ShenWork/PDE/IntervalDomainMoserLadderAtoms.lean`
- `ShenWork/PDE/P3MoserRegularityProducer.lean`

## Recommendation

Choose **A** now: add small closure-only gradient-energy nonnegativity utilities in

```text
ShenWork/PDE/P3MoserIntegratedClosure.lean
```

Do **not** choose B yet. A downstream package in `IntervalDomainMoserLadderAtoms.lean` that imports or consumes a theorem from the moving Zinan-owned threshold producer would reduce residuals on paper, but it is not the safest edit while that file may still change.

The proposed A-edit is safe because `P3MoserIntegratedClosure.lean` already defines the relevant generic quantities:

```lean
integratedMoserEnergy
integratedMoserGradientEnergy
IntegratedMoserEnergyNonnegativity
intervalDomain_integral_nonneg
intervalDomain_integratedMoserEnergyNonnegativity_of_classical
integratedMoserFirstCrossingStep_of_windowFrontier
integratedMoserFirstCrossingStep_of_lowerUpperFrontiers
integratedMoserFirstCrossingStep_of_lowerAverageUpperDataGapData
```

It currently has concrete nonnegativity for the power energy, but not the analogous packaged nonnegativity for the Moser gradient energy. Adding that package is low-conflict and useful for any later abstract-data first-crossing route.

## Suggested Lean edit

Place this near the existing `IntegratedMoserEnergyNonnegativity` and `intervalDomain_integral_nonneg` lemmas in `ShenWork/PDE/P3MoserIntegratedClosure.lean`.

If pasted directly into that file, omit the self-import shown here.

```lean
import ShenWork.PDE.P3MoserIntegratedClosure

open MeasureTheory
open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalDomainMoserClosure
open ShenWork.IntervalDomainExistence.P3MoserDissipationShape
open scoped Interval

noncomputable section

namespace ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure

/-- Abstract nonnegativity of Moser gradient energies at interior times.

This is separate from `IntegratedMoserEnergyNonnegativity` because abstract
`BoundedDomainData.integral` does not by itself preserve nonnegative functions.
For `intervalDomain`, it follows from the concrete interval integral and
`sq_nonneg`. -/
def IntegratedMoserGradientEnergyNonnegativity
    (D : BoundedDomainData) (u : ℝ → D.Point → ℝ)
    (T p0 : ℝ) : Prop :=
  ∀ p, p0 ≤ p → 0 ≤ p → ∀ t, 0 < t → t < T →
    0 ≤ integratedMoserGradientEnergy D u p t

/-- The concrete interval-domain Moser gradient energy is nonnegative. -/
theorem intervalDomain_integratedMoserGradientEnergy_nonneg
    {u : ℝ → intervalDomain.Point → ℝ} {p t : ℝ} :
    0 ≤ integratedMoserGradientEnergy intervalDomain u p t := by
  unfold integratedMoserGradientEnergy
  exact intervalDomain_integral_nonneg _
    (fun x => sq_nonneg _)

/-- The interval domain supplies the abstract gradient-energy nonnegativity
package. -/
theorem intervalDomain_integratedMoserGradientEnergyNonnegativity
    {u : ℝ → intervalDomain.Point → ℝ} {T p0 : ℝ} :
    IntegratedMoserGradientEnergyNonnegativity intervalDomain u T p0 := by
  intro p _hp _hp_nonneg t _ht0 _htT
  exact intervalDomain_integratedMoserGradientEnergy_nonneg
    (u := u) (p := p) (t := t)

/-- Integrating a nonnegative Moser gradient energy over a non-reversed interval
preserves nonnegativity. -/
theorem integratedMoserGradientEnergy_intervalIntegral_nonneg_of_nonneg_on
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {p a b : ℝ}
    (hab : a ≤ b)
    (hgrad_nonneg :
      ∀ t ∈ Set.Icc a b,
        0 ≤ integratedMoserGradientEnergy D u p t) :
    0 ≤ ∫ t in a..b, integratedMoserGradientEnergy D u p t := by
  exact intervalIntegral.integral_nonneg hab hgrad_nonneg

/-- Package-level version of gradient-energy interval-integral nonnegativity on
an interior time window. -/
theorem integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package
    {D : BoundedDomainData} {u : ℝ → D.Point → ℝ}
    {T p0 p a b : ℝ}
    (hgrad : IntegratedMoserGradientEnergyNonnegativity D u T p0)
    (hp : p0 ≤ p) (hp_nonneg : 0 ≤ p)
    (hab : a ≤ b) (ha_pos : 0 < a) (hb_lt : b < T) :
    0 ≤ ∫ t in a..b, integratedMoserGradientEnergy D u p t := by
  refine integratedMoserGradientEnergy_intervalIntegral_nonneg_of_nonneg_on
    (D := D) (u := u) (p := p) hab ?_
  intro t ht
  exact hgrad p hp hp_nonneg t
    (lt_of_lt_of_le ha_pos ht.1)
    (lt_of_le_of_lt ht.2 hb_lt)

#print axioms intervalDomain_integratedMoserGradientEnergy_nonneg
#print axioms intervalDomain_integratedMoserGradientEnergyNonnegativity
#print axioms integratedMoserGradientEnergy_intervalIntegral_nonneg_of_nonneg_on
#print axioms integratedMoserGradientEnergy_intervalIntegral_nonneg_of_package

end ShenWork.IntervalDomainExistence.P3MoserIntegratedClosure
```

## Why this is the safest edit

This edit uses only local non-Zinan definitions and the already-proved concrete interval integral nonnegativity lemma. The key proof is just:

```lean
unfold integratedMoserGradientEnergy
exact intervalDomain_integral_nonneg _ (fun x => sq_nonneg _)
```

So it has no analytic risk, no import-cycle risk, and no dependency on a moving Zinan-owned API.

## Why not add the downstream wrapper now

A wrapper in `IntervalDomainMoserLadderAtoms.lean` that consumes the currently reported threshold-producer theorem would be attractive, but it creates a dependency on a file that Zinan owns and may continue changing. That makes it the wrong next move for Codex.

Recommended sequencing:

1. Add the closure-only gradient nonnegativity utilities above.
2. Let Zinan stabilize the abstract first-crossing theorem in her producer file.
3. After that theorem is stable, add a thin downstream wrapper that applies it using:
   - existing classical energy nonnegativity from `P3MoserIntegratedClosure.lean`;
   - the new gradient-energy nonnegativity package above;
   - the existing regularity, dissipation, relative interpolation, and endpoint fields.

## Final option call

- **A: yes, do this now.**
- **B: no, wait until the Zinan-owned theorem is stable.**
- **C: only if it is a tiny closure-local utility like the one above; do not add another residual wrapper yet.**
