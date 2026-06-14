import Mathlib
import ShenWork.Wiener.EWA.ResolverEvalBridge
import ShenWork.Wiener.WeightedL1EvalDeriv
import ShenWork.PDE.IntervalResolverGradientBridge
import ShenWork.Paper2.IntervalDomainL2StaticVDifference

/-!
# EWA brick — the resolver GRADIENT eval bridge (Phase C source eval-bridge)

This file proves the **EVAL bridge for the resolver gradient**: the Wiener
synthesis (`WA.evalC`) of the EWA Fourier derivative `gDeriv` of the resolver
field equals (cast to `ℂ`) the committed real-space resolver gradient
`resolverGradReal p u x` (`= ∂ₓ` of the Neumann resolver), pointwise on the
**open** interval `(0,1)`.

## Structure

1. `sliceWA_gDeriv` (coefficient algebra): slicing the EWA Fourier derivative
   `gDeriv F` at a time `τ` agrees with the WA Fourier derivative `wD` of the
   slice `sliceWA τ F`.  Both sides read `iπn · (sliceWA τ F).toFun n`:
   * LHS via `scalarMultiplier_toFun` (the `gDeriv` symbol `iπn`) followed by
     `coeff_sliceWA` (slicing reads the time-coefficient at `τ`), with the
     `smul` on `CT T = C(TimeDom T, ℂ)` evaluated pointwise at `τ`;
   * RHS via `wDeriv`'s symbol `iπn` and `coeff_sliceWA` again.

2. `evalC_gDeriv_vField_eq_resolverGradReal` (the gradient eval bridge):
   compose `sliceWA_gDeriv`, the committed eval/derivative commutation
   `evalC_wD_eq_deriv`, the open-set derivative congruence
   (`HasDerivAt.congr_of_eventuallyEq` on `Ioo 0 1 ∈ 𝓝 x`), the committed
   termwise differentiation `resolverR_hasDerivAt_grad`, and the ℝ→ℂ lift
   `HasDerivAt.ofReal_comp`.

The realization hypothesis `hreal` (that `vField` realizes the resolver value)
and the gradient majorant `hgrad` are **upstream obligations**, supplied as
hypotheses here.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators

noncomputable section

namespace ShenWork.EWA

open ShenWork.Wiener ShenWork.Wiener.WA ShenWork.GWA ShenWork.GWA.GWA
open ShenWork.PDE ShenWork.IntervalDomain ShenWork.Paper2
open ShenWork.IntervalResolverGradientBridge

variable {T : ℝ}

/-! ### 1. Slicing commutes with the EWA Fourier derivative -/

/-- **Coefficient-level commutation `sliceWA ∘ gDeriv = wD ∘ sliceWA`.**

Slicing the EWA Fourier derivative `gDeriv F` at time `τ` equals the WA Fourier
derivative `wD` of the slice `sliceWA τ F`, coefficientwise.  Both sides are
`iπn · (sliceWA τ F).toFun n`. -/
theorem sliceWA_gDeriv_toFun {r : ℕ} (F : EWA T (r + 1)) (τ : TimeDom T) (n : ℤ) :
    (sliceWA τ (GWA.gDeriv F)).toFun n = (WA.wD (sliceWA τ F)).toFun n := by
  -- RHS: `(wD (sliceWA τ F)).toFun n = iπn · (sliceWA τ F).toFun n = iπn · (F.toFun n) τ`.
  rw [WA.wD_toFun, wDeriv, coeff_sliceWA]
  -- LHS: `(gDeriv F).toFun n` read at `τ`.
  rw [coeff_sliceWA]
  -- `gDeriv = scalarMultiplier (iπn)`, so its coefficient is `(iπn) • F.toFun n` in `CT T`.
  rw [GWA.gDeriv, scalarMultiplier_toFun]
  -- Evaluate the pointwise `smul` on continuous functions at `τ`.
  rw [ContinuousMap.smul_apply, smul_eq_mul]

/-- The bundled form `sliceWA τ (gDeriv F) = wD (sliceWA τ F)`. -/
theorem sliceWA_gDeriv {r : ℕ} (F : EWA T (r + 1)) (τ : TimeDom T) :
    sliceWA τ (GWA.gDeriv F) = WA.wD (sliceWA τ F) :=
  WA.ext (funext (fun n => sliceWA_gDeriv_toFun F τ n))

/-! ### 2. The gradient eval bridge -/

/-- **The resolver-gradient eval bridge.**

For a resolver field `vField : EWA T (r+1)` whose slices realize the real-space
Neumann resolver `intervalNeumannResolverR` (hypothesis `hreal`), and under the
gradient `ℓ¹` majorant `hgrad` (the obligation of `resolverR_hasDerivAt_grad`),
the Wiener synthesis of the EWA Fourier derivative `gDeriv vField`, sliced at any
time `τ`, equals (cast to `ℂ`) the committed real-space resolver gradient
`resolverGradReal p u x`, for every interior point `x ∈ (0,1)`.

* `hreal` is the value realization (upstream `EWARealizesOn` discharge).
* `hgrad` is the gradient-series absolute summability (b1 ⇒ b2 input).

PROOF (compose):
1. `sliceWA_gDeriv` ⟹ `sliceWA τ (gDeriv vField) = wD (sliceWA τ vField)`.
2. `evalC_wD_eq_deriv` ⟹ the LHS is `deriv (fun y => evalC (toZero (sliceWA τ
   vField)) ↑y) x`.
3. On the open set `Ioo 0 1 ∈ 𝓝 x`, `hreal` + `resolverR_apply_eq` give that the
   inner function agrees with the ℂ-lift of the real cosine series differentiated
   by `resolverR_hasDerivAt_grad`; `HasDerivAt.congr_of_eventuallyEq` transports
   the derivative.
4. `resolverR_hasDerivAt_grad` ⟹ `deriv = (intervalNeumannResolverRGrad …).ofReal`,
   then `resolverGradReal_eq` casts to `resolverGradReal p u x`. -/
theorem evalC_gDeriv_vField_eq_resolverGradReal
    {r : ℕ} (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (vField : EWA T (r + 1)) (τ : TimeDom T)
    (hreal : ∀ (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1),
      (WA.evalC (WA.toZero (sliceWA τ vField)) (y : WA.Circ) : ℂ)
        = ((intervalNeumannResolverR p u ⟨y, hy⟩ : ℝ) : ℂ))
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi))
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (WA.evalC (WA.toZero (sliceWA τ (GWA.gDeriv vField))) (x : WA.Circ) : ℂ)
      = ((resolverGradReal p u x : ℝ) : ℂ) := by
  -- The interior point lies in the closed interval, and `Ioo 0 1 ∈ 𝓝 x`.
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  -- Step 1: slice commutes with gDeriv.
  rw [sliceWA_gDeriv vField τ]
  -- Step 2: eval/derivative commutation.
  rw [WA.evalC_wD_eq_deriv (sliceWA τ vField) x]
  -- The committed real cosine series whose derivative is the resolver gradient.
  set g : ℝ → ℝ := fun z : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hg_def
  -- Step 4 input: `g` has derivative `intervalNeumannResolverRGrad p u ⟨x,_⟩` at `x`.
  have hgrad_at : HasDerivAt g (intervalNeumannResolverRGrad p u ⟨x, hxIcc⟩) x :=
    resolverR_hasDerivAt_grad (p := p) (u := u) hgrad x hxIcc
  -- Its ℝ→ℂ lift.
  have hgrad_atC : HasDerivAt (fun z : ℝ => ((g z : ℝ) : ℂ))
      ((intervalNeumannResolverRGrad p u ⟨x, hxIcc⟩ : ℝ) : ℂ) x :=
    hgrad_at.ofReal_comp
  -- Step 3: the eval-lift agrees with the ℂ-lift of `g` on the open nbhd `Ioo 0 1`.
  have hee : (fun y : ℝ => (WA.evalC (WA.toZero (sliceWA τ vField)) (y : WA.Circ) : ℂ))
      =ᶠ[nhds x] (fun z : ℝ => ((g z : ℝ) : ℂ)) := by
    refine Filter.eventuallyEq_of_mem hnhds (fun y hy => ?_)
    have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 :=
      Set.mem_Icc.2 ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    -- `evalC … ↑y = (intervalNeumannResolverR p u ⟨y,_⟩ : ℂ)`, then unfold to the series.
    rw [hreal y hyIcc]
    -- `intervalNeumannResolverR p u ⟨y,_⟩ = g y` (cosine-series unfolding).
    have hval : intervalNeumannResolverR p u ⟨y, hyIcc⟩ = g y := by
      rw [hg_def, resolverR_apply_eq]
    rw [hval]
  -- Transport the derivative across the eventual equality (Step 3 ⟹ Step 4).
  have hderiv_eq :
      deriv (fun y : ℝ => (WA.evalC (WA.toZero (sliceWA τ vField)) (y : WA.Circ) : ℂ)) x
        = ((intervalNeumannResolverRGrad p u ⟨x, hxIcc⟩ : ℝ) : ℂ) :=
    (hgrad_atC.congr_of_eventuallyEq hee).deriv
  rw [hderiv_eq]
  -- `intervalNeumannResolverRGrad p u ⟨x,_⟩ = resolverGradReal p u x`.
  rw [← resolverGradReal_eq p u ⟨x, hxIcc⟩]

end ShenWork.EWA

#print axioms ShenWork.EWA.evalC_gDeriv_vField_eq_resolverGradReal
