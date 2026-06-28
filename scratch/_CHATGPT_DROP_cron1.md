# Q1652 (cron1) -- cron2 derivative/cancellation issue

Repository: `xiangyazi24/Shen_work`  
Committed branch: `chatgpt-scratch`  
Target report file: `scratch/_CHATGPT_DROP_cron1.md`

## Scope and caveat

The prompt was:

```text
Q1652 (cron1): cron2 /tmp/q_cron2_deriv.txt
```

The local file `/tmp/q_cron2_deriv.txt` is not accessible through the GitHub connector. I therefore inferred the target from the cron2 files currently in the repository. The relevant files are:

```text
ShenWork/Paper2/IntervalBFormNegativePartCron2.lean
ShenWork/Paper2/IntervalBFormCron2NegativePartEnergy.lean
ShenWork/Paper2/IntervalBFormCron2RegularNegativePartEnergy.lean
```

The derivative issue is the treatment of:

```lean
deriv (negativePartTest u t) x
```

where:

```lean
def negativePartTest (u : ℝ → intervalDomainPoint → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun x => -negativePartLift (u t) x
```

and the energy proof needs the chemotaxis cancellation against this derivative.

I used the GitHub connector only. I did **not** use Python, the sandbox, `/mnt/data`, or a sandbox download link. I did not run Lean locally.

## Short answer

The cron2 derivative/cancellation route is already set up correctly. The key point is:

```text
You do not need differentiability of negativePart at u = 0.
```

The cancellation is split by support:

* on `{0 < u}`, continuity makes `u_-` locally constant zero, so its classical derivative vanishes;
* on `{u ≤ 0}`, the truncated chemotactic power/flux is zero because the positive part of `u` is zero.

For the weak energy proof, the project intentionally does **not** try to derive this from the weak PDE automatically. It packages the required Sobolev/a.e. chain-rule fact as a field:

```lean
neg_deriv_zero_on_pos :
  ∀ t, 0 < t → t ≤ T →
    ∀ᵐ x ∂ intervalMeasure 1,
      0 < intervalDomainLift (u t) x →
        deriv (negativePartLift (u t)) x = 0
```

Then the actual flux cancellation is already proved from that field.

## The pointwise scalar derivative lemma

`IntervalBFormCron2NegativePartEnergy.lean` has the local positive-set derivative lemma:

```lean
/-- At a point where the slice is strictly positive, the negative part is
locally constant zero, hence its classical derivative vanishes. -/
lemma deriv_negativePartLift_eq_zero_of_pos
    {u : ℝ → ℝ} {x : ℝ} (hu : ContinuousAt u x) (hpos : 0 < u x) :
    deriv (fun y : ℝ => negativePart (u y)) x = 0 := by
  have hmem : u x ∈ Set.Ioi (0 : ℝ) := hpos
  have hnhds : Set.Ioi (0 : ℝ) ∈ 𝓝 (u x) :=
    isOpen_Ioi.mem_nhds hmem
  have hev_pos : ∀ᶠ y in 𝓝 x, u y ∈ Set.Ioi (0 : ℝ) :=
    hu hnhds
  have hev :
      (fun y : ℝ => negativePart (u y)) =ᶠ[𝓝 x] (fun _ : ℝ => 0) :=
    hev_pos.mono (fun y hy => negativePart_eq_zero_of_nonneg hy.le)
  rw [hev.deriv_eq]
  simp
```

This is the right proof. It avoids the nondifferentiability point of `negativePart` at `0`: when `0 < u x`, continuity gives a whole neighborhood where `u y > 0`, so `negativePart (u y) = 0` locally. When `u x ≤ 0`, the flux factor vanishes instead.

The corresponding pointwise product cancellation is:

```lean
lemma truncatedChemotacticPower_mul_deriv_negativePartLift_eq_zero_of_continuousAt
    (p : CM2Params) {u : ℝ → ℝ} {x : ℝ}
    (hu : ContinuousAt u x) :
    truncatedChemotacticPower p (u x)
        * deriv (fun y : ℝ => negativePart (u y)) x = 0 := by
  by_cases hpos : 0 < u x
  · have hderiv := deriv_negativePartLift_eq_zero_of_pos hu hpos
    simp [hderiv]
  · have hflux :
        truncatedChemotacticPower p (u x) = 0 :=
      truncatedChemotacticPower_eq_zero_of_nonpos p (le_of_not_gt hpos)
    simp [hflux]
```

This is also the right proof: no derivative of `positivePart` or `negativePart` at the free boundary is needed.

## The a.e. weak/Sobolev cancellation layer

The weak energy proof does not use the pointwise classical derivative lemma directly. Instead it uses a more flexible a.e. lemma:

```lean
lemma truncatedChemFluxLifted_mul_negDeriv_eq_zero_ae
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {duNeg : ℝ → ℝ}
    (hdu_zero_on_pos :
      ∀ᵐ x ∂ intervalMeasure 1,
        0 < intervalDomainLift w x → duNeg x = 0) :
    (fun x => truncatedChemFluxLifted p w x * duNeg x)
      =ᵐ[intervalMeasure 1] fun _ => 0 := by
  filter_upwards [hdu_zero_on_pos] with x hx
  by_cases hpos : 0 < intervalDomainLift w x
  · simp [hx hpos]
  · have hpp :
        positivePart (intervalDomainLift w x) = 0 :=
      positivePart_eq_zero_of_nonpos (le_of_not_gt hpos)
    simp [truncatedChemFluxLifted, hpp]
```

and the integral version:

```lean
theorem truncatedChemFluxLifted_mul_negDeriv_integral_eq_zero
    (p : CM2Params) {w : intervalDomainPoint → ℝ} {duNeg : ℝ → ℝ}
    (hdu_zero_on_pos :
      ∀ᵐ x ∂ intervalMeasure 1,
        0 < intervalDomainLift w x → duNeg x = 0) :
    (∫ x, truncatedChemFluxLifted p w x * duNeg x
        ∂ intervalMeasure 1) = 0 := by
  rw [MeasureTheory.integral_congr_ae
    (truncatedChemFluxLifted_mul_negDeriv_eq_zero_ae
      (p := p) (w := w) hdu_zero_on_pos)]
  simp
```

This is the correct abstraction: `duNeg` can be either the classical derivative of `u_-` or the weak derivative representative. The lemma only needs `duNeg = 0` a.e. on `{u > 0}`.

## The `deriv (negativePartTest u t)` sign issue

In both `negativePart_half_energy_deriv_le` and its regular version, the chemotaxis term is:

```lean
(∫ x,
  truncatedChemFluxLifted p (u t) x
    * deriv (negativePartTest u t) x
  ∂ intervalMeasure 1)
```

but the energy data field gives zero for:

```lean
deriv (negativePartLift (u t)) x
```

The bridge is exactly:

```lean
change deriv (-negativePartLift (u t)) x = 0
rw [deriv.neg]
simp [hx hpos]
```

This is correct because `negativePartTest u t` is definitionally `fun x => -negativePartLift (u t) x`. The theorem `deriv.neg` rewrites:

```lean
deriv (fun x => -f x) a = - deriv f a
```

Then `hx hpos : deriv (negativePartLift (u t)) x = 0`, so the derivative of the negative test is `-0 = 0`.

The current code in `negativePart_half_energy_deriv_le` is:

```lean
  have hchem_neg :
      (∫ x,
        truncatedChemFluxLifted p (u t) x
          * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1) = 0 := by
    refine truncatedChemFluxLifted_mul_negDeriv_integral_eq_zero
      (p := p) (w := u t)
      (duNeg := fun x => deriv (negativePartTest u t) x) ?_
    filter_upwards [H.neg_deriv_zero_on_pos t ht htT] with x hx hpos
    change deriv (-negativePartLift (u t)) x = 0
    rw [deriv.neg]
    simp [hx hpos]
```

and the regular version has the same block:

```lean
  have hchem_neg :
      (∫ x,
        truncatedChemFluxLifted p (u t) x
          * deriv (negativePartTest u t) x
        ∂ intervalMeasure 1) = 0 := by
    refine truncatedChemFluxLifted_mul_negDeriv_integral_eq_zero
      (p := p) (w := u t)
      (duNeg := fun x => deriv (negativePartTest u t) x) ?_
    filter_upwards [H.neg_deriv_zero_on_pos t ht htT] with x hx hpos
    change deriv (-negativePartLift (u t)) x = 0
    rw [deriv.neg]
    simp [hx hpos]
```

This is the exact Lean pattern to use.

## More robust replacement if `simp [hx hpos]` is brittle

If the last two lines ever become brittle because `simp` does not use `hx hpos` in the desired direction, replace them with this more explicit version:

```lean
    filter_upwards [H.neg_deriv_zero_on_pos t ht htT] with x hx hpos
    have hx0 : deriv (negativePartLift (u t)) x = 0 := hx hpos
    change deriv (-negativePartLift (u t)) x = 0
    rw [deriv.neg, hx0, neg_zero]
```

or, if Lean wants the function written as a lambda:

```lean
    filter_upwards [H.neg_deriv_zero_on_pos t ht htT] with x hx hpos
    have hx0 : deriv (negativePartLift (u t)) x = 0 := hx hpos
    change deriv (fun y : ℝ => -negativePartLift (u t) y) x = 0
    rw [deriv.neg, hx0, neg_zero]
```

This does exactly the same proof but avoids relying on `simp` to infer the instantiated hypothesis.

## What not to try

Do **not** try to prove the full weak field

```lean
neg_deriv_zero_on_pos :
  ∀ t, 0 < t → t ≤ T →
    ∀ᵐ x ∂ intervalMeasure 1,
      0 < intervalDomainLift (u t) x →
        deriv (negativePartLift (u t)) x = 0
```

from mere continuity of the slice in the weak energy core. In the weak/Sobolev route this is a chain-rule/support theorem for the negative-part representative, and the project correctly leaves it as explicit data in:

```lean
NegativePartEnergyEstimateData
NegativePartEnergyEstimateRegularData
```

The pointwise classical lemma is useful when you have classical slices and actual classical derivatives. The energy core is deliberately more general and therefore requires the a.e. support condition as a field.

## Minimal import/check snippet

For a separate scratch Lean file, the relevant imports/checks are:

```lean
import ShenWork.Paper2.IntervalBFormCron2NegativePartEnergy
import ShenWork.Paper2.IntervalBFormCron2RegularNegativePartEnergy

open Filter Topology Set MeasureTheory
open scoped Topology

open ShenWork.IntervalDomain
  (intervalDomain intervalDomainLift intervalDomainPoint intervalMeasure)
open ShenWork.IntervalConjugatePicard
  (ConjugateMildExistenceData conjugatePicardLimit)

noncomputable section

namespace ShenWork.Paper2.BFormPositiveDatumNegPart

#check deriv_negativePartLift_eq_zero_of_pos
#check truncatedChemotacticPower_mul_deriv_negativePartLift_eq_zero_of_continuousAt
#check truncatedChemFluxLifted_mul_negDeriv_eq_zero_ae
#check truncatedChemFluxLifted_mul_negDeriv_integral_eq_zero
#check negativePart_half_energy_deriv_le
#check negativePart_half_energy_deriv_le_regular

end ShenWork.Paper2.BFormPositiveDatumNegPart
```

## Bottom line

The derivative step should be handled at the support-cancellation level:

```text
positive set: derivative of u_- is zero;
nonpositive set: truncated flux is zero;
test derivative: deriv(-u_-) = -deriv(u_-), so zero remains zero.
```

The current code already implements this correctly. If a local proof involving `deriv (negativePartTest u t)` is failing, use the explicit `hx0` replacement above around `rw [deriv.neg, hx0, neg_zero]`.
