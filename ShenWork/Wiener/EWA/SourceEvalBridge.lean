import ShenWork.Wiener.EWA.FluxEvalBridge
import ShenWork.Wiener.EWA.GrowthEvalBridge
import ShenWork.Wiener.EWA.ResolverGradEvalBridge

/-!
# EWA brick — the chemotaxis-growth SOURCE eval bridge (Phase C source assembly)

This file assembles the **eval bridge for the committed real-space coupled
source** `intervalCoupledSource p u R x = −χ₀·chemDiv + logisticSource`: the
Wiener synthesis (`evalST`) of the EWA source

  `sourceEWA p U = (−χ₀) • gDeriv (chemFluxEWA … U) + incl (growthEWA … U)`

equals (cast to `ℂ`) the committed `intervalCoupledSource p u (R u) x`, pointwise
on the interior `(0,1)`.

## Structure

`evalST` is a `RingHom`, so linearity (`map_add` + `evalST_smul`) splits

  `evalST (sourceEWA) = (−χ₀)·evalST (gDeriv chemFluxEWA U) + evalST (incl growthEWA U)`.

* **growth leg.**  `evalST (incl growthEWA U) = logisticLifted p u x =
  intervalLogisticSource p u ⟨x,_⟩` directly from the committed
  `evalST_growthEWA_eq_logisticLifted` + the `dif_pos` unfold of `logisticLifted`.

* **divergence leg.**  `evalST (gDeriv chemFluxEWA U)` is routed through
  `evalST = evalC ∘ toZero ∘ sliceWA` (`evalST_apply`/`evalAt_apply`),
  `sliceWA_gDeriv` (slice ↔ Fourier derivative), and the committed
  `evalC_wD_eq_deriv` (eval/∂ₓ commutation) to
  `deriv (fun y => evalST τ y (incl chemFluxEWA U)) x`.  The flux value-nbhd
  hypothesis `h_flux_nbhd` (agreement on the OPEN `Ioo 0 1 ∈ 𝓝 x`) lets a
  deriv-congruence (`HasDerivAt.congr_of_eventuallyEq`) replace the integrand by
  the ℂ-cast of `chemFluxLifted p u`, giving `(deriv (chemFluxLifted p u) x : ℂ)`.

  The hard reconciliation `deriv (chemFluxLifted p u) x =
  intervalDomainChemotaxisDiv p u (R u) x` is built here (NO committed lemma
  relating `chemotaxisDiv` to `deriv chemFluxLifted` exists): the two
  differentiated integrands agree on `Ioo 0 1` once
  `deriv (intervalDomainLift (R u)) y = resolverGradReal p u y` there — which is
  itself a deriv-congruence built from `resolverR_hasDerivAt_grad` (gradient ℓ¹
  majorant `hgrad`) and the cosine-series unfold of the lifted resolver.  A
  second `Filter.EventuallyEq.deriv_eq` then matches the two `deriv`s.

All factor realizations (`h_flux_nbhd`, `h_growth`) and the gradient majorant
`hgrad` are upstream (B5e) obligations supplied here as **hypotheses** (NOT
discharged).

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open MeasureTheory
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverRGrad
  intervalNeumannResolverCoeff)
open ShenWork.IntervalResolverGradientBridge (resolverR_apply_eq resolverR_hasDerivAt_grad)
open ShenWork.IntervalDomainExistence (intervalLogisticSource intervalCoupledSource)
open ShenWork.Paper2 (resolverGradReal resolverGradReal_eq)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted logisticLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The EWA coupled chemotaxis-growth source** `sourceEWA p U =
`(−χ₀)·∂ₓB(U) + G(U)`, the EWA realization of `intervalCoupledSource`.
`gDeriv (chemFluxEWA … U) : EWA T 0` (the flux is `EWA T 1 = EWA T (0+1)`) and the
growth term is down-included from `EWA T 1` to weight `0`. -/
def sourceEWA (μ ν γ : ℝ) (hμ : 0 < μ) (p : CM2Params) (U : EWA T 1) : EWA T 0 :=
  (-p.χ₀ : ℂ) • GWA.gDeriv (chemFluxEWA μ ν p.β γ hμ U)
    + GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b U)

/-- `evalST τ y (incl (chemFluxEWA …)) = evalC (toZero (sliceWA τ chemFluxEWA)) ↑y`:
the `evalST = evalC ∘ toZero ∘ sliceWA` link, specialized to the flux.  Routes
through `evalST_apply` (slice then point-eval), `sliceWA_incl` (slice of the
inclusion is `incl10` of the slice), and the `incl10 = toZero` equality on `WA`. -/
theorem evalST_incl_chemFlux_eq_evalC (μ ν γ : ℝ) (hμ : 0 < μ) (p : CM2Params)
    (U : EWA T 1) (τ : TimeDom T) (y : ℝ) :
    evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ U))
      = (WA.evalC (WA.toZero (sliceWA τ (chemFluxEWA μ ν p.β γ hμ U)))
          (y : WA.Circ) : ℂ) := by
  rw [evalST_apply, sliceWA_incl]
  have htz : WA.incl10 (sliceWA τ (chemFluxEWA μ ν p.β γ hμ U))
      = WA.toZero (sliceWA τ (chemFluxEWA μ ν p.β γ hμ U)) := by
    apply WA.ext; funext n; rw [WA.incl10_toFun, WA.toZero_toFun]
  rw [htz, WA.evalAt_apply, WA.evalC_apply]

/-- The divergence leg, value form: `evalST τ x (gDeriv chemFluxEWA U)` equals
`deriv (fun y => evalST τ y (incl chemFluxEWA U)) x`, via `sliceWA_gDeriv` +
`evalC_wD_eq_deriv` + the `evalST = evalC∘toZero∘sliceWA` link. -/
theorem evalST_gDeriv_chemFlux_eq_deriv (μ ν γ : ℝ) (hμ : 0 < μ) (p : CM2Params)
    (U : EWA T 1) (τ : TimeDom T) (x : ℝ) :
    evalST τ (x : WA.Circ) (GWA.gDeriv (chemFluxEWA μ ν p.β γ hμ U))
      = deriv (fun y : ℝ => evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
          (chemFluxEWA μ ν p.β γ hμ U))) x := by
  -- `evalST (gDeriv F) = evalC (toZero (sliceWA τ (gDeriv F))) ↑x`.
  have hev : evalST τ (x : WA.Circ) (GWA.gDeriv (chemFluxEWA μ ν p.β γ hμ U))
      = (WA.evalC (WA.toZero (sliceWA τ (GWA.gDeriv (chemFluxEWA μ ν p.β γ hμ U))))
          (x : WA.Circ) : ℂ) := by
    rw [evalST_apply, WA.evalAt_apply, WA.evalC_apply]
    congr 1
  rw [hev]
  -- `sliceWA (gDeriv F) = wD (sliceWA F)`, then eval/∂ₓ commutation.
  rw [sliceWA_gDeriv (chemFluxEWA μ ν p.β γ hμ U) τ,
    WA.evalC_wD_eq_deriv (sliceWA τ (chemFluxEWA μ ν p.β γ hμ U)) x]
  -- match the differentiated integrands.
  refine Filter.EventuallyEq.deriv_eq (Filter.Eventually.of_forall (fun y => ?_))
  simp only [evalST_incl_chemFlux_eq_evalC μ ν γ hμ p U τ y]

/-- **The lifted resolver agrees with the cosine series near interior points.**
`intervalDomainLift (R u) y = ∑' k, (v̂_k).re·cos(kπy)` on `[0,1]` (the lift is
the resolver value there, and the resolver is the cosine reconstruction). -/
theorem liftResolver_eq_cos (p : CM2Params) (u : intervalDomainPoint → ℝ)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    intervalDomainLift (intervalNeumannResolverR p u) y
      = ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
          Real.cos ((k : ℝ) * Real.pi * y) := by
  rw [intervalDomainLift, dif_pos hy, resolverR_apply_eq]

/-- **`deriv (lift R) = resolverGradReal` on the interior.**  Built by a
deriv-congruence: the lifted resolver agrees with the cosine series `g` on the
open `Ioo 0 1 ∈ 𝓝 x`, and `resolverR_hasDerivAt_grad` (gradient ℓ¹ majorant
`hgrad`) gives `HasDerivAt g (resolverGradReal p u x) x`; transport the derivative
across the eventual equality. -/
theorem deriv_liftResolver_eq_grad (p : CM2Params) (u : intervalDomainPoint → ℝ)
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (intervalDomainLift (intervalNeumannResolverR p u)) x
      = resolverGradReal p u x := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  set g : ℝ → ℝ := fun z : ℝ =>
    ∑' k : ℕ, (intervalNeumannResolverCoeff p u k).re *
      Real.cos ((k : ℝ) * Real.pi * z) with hg_def
  -- `g` has derivative `intervalNeumannResolverRGrad p u ⟨x,_⟩ = resolverGradReal p u x`.
  have hgrad_at : HasDerivAt g (intervalNeumannResolverRGrad p u ⟨x, hxIcc⟩) x :=
    resolverR_hasDerivAt_grad (p := p) (u := u) hgrad x hxIcc
  rw [← resolverGradReal_eq p u ⟨x, hxIcc⟩] at hgrad_at
  -- lift agrees with `g` on the open nbhd.
  have hee : intervalDomainLift (intervalNeumannResolverR p u) =ᶠ[nhds x] g := by
    refine Filter.eventuallyEq_of_mem hnhds (fun z hz => ?_)
    have hzIcc : z ∈ Set.Icc (0 : ℝ) 1 := Set.mem_Icc.2 ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    rw [liftResolver_eq_cos p u hzIcc, hg_def]
  exact (hgrad_at.congr_of_eventuallyEq hee).deriv

/-- **The integrands of `deriv chemFluxLifted` and `chemDiv` agree on `Ioo 0 1`.**
On the interior, `resolverGradReal p u y = deriv (lift R) y` (committed-built),
so the C⁰ flux `chemFluxLifted` equals the integrand of `intervalDomainChemotaxisDiv`. -/
theorem chemFluxLifted_eq_chemDivIntegrand (p : CM2Params)
    (u : intervalDomainPoint → ℝ)
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi))
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    chemFluxLifted p u y
      = intervalDomainLift u y *
          deriv (intervalDomainLift (intervalNeumannResolverR p u)) y /
        (1 + intervalDomainLift (intervalNeumannResolverR p u) y) ^ p.β := by
  rw [chemFluxLifted, deriv_liftResolver_eq_grad p u hgrad hy]

/-- **The chemotaxisDiv ↔ deriv chemFluxLifted reconciliation.**
`deriv (chemFluxLifted p u) x = intervalDomainChemotaxisDiv p u (R u) x`, by a
deriv-congruence on `Ioo 0 1` (the integrands agree there by
`chemFluxLifted_eq_chemDivIntegrand`). -/
theorem deriv_chemFluxLifted_eq_chemDiv (p : CM2Params)
    (u : intervalDomainPoint → ℝ)
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi))
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1) :
    deriv (chemFluxLifted p u) x
      = intervalDomainChemotaxisDiv p u (intervalNeumannResolverR p u) ⟨x, hxIcc⟩ := by
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  rw [intervalDomainChemotaxisDiv]
  refine Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem hnhds (fun y hy => ?_))
  exact chemFluxLifted_eq_chemDivIntegrand p u hgrad hy

/-- **The chemotaxis-growth source eval bridge.**

The Wiener synthesis of the EWA coupled source `sourceEWA μ ν γ hμ p U` equals the
committed real-space `intervalCoupledSource p u (R u) ⟨x,_⟩`, cast to `ℂ`, at every
interior spatial point `x ∈ (0,1)`.

The two factor realizations (`h_flux_nbhd`, `h_growth`) and the gradient ℓ¹
majorant `hgrad` are upstream (B5e) obligations supplied here as hypotheses; the
assembly performs the linearity split, the growth-leg unfold, the divergence-leg
deriv-congruence, and the `chemotaxisDiv ↔ deriv chemFluxLifted` reconciliation. -/
theorem evalST_sourceEWA_eq_intervalCoupledSource
    (μ ν γ : ℝ) (hμ : 0 < μ) (p : CM2Params)
    (u : intervalDomainPoint → ℝ) (U : EWA T 1)
    (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p u k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ U)) = ((chemFluxLifted p u y : ℝ) : ℂ))
    (h_growth : evalST τ (x : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (growthEWA p.α p.a p.b U)) = ((logisticLifted p u x : ℝ) : ℂ))
    (h_flux_diff : DifferentiableAt ℝ (chemFluxLifted p u) x) :
    evalST τ (x : WA.Circ) (sourceEWA μ ν γ hμ p U)
      = ((intervalCoupledSource p u (intervalNeumannResolverR p u)
          ⟨x, hxIcc⟩ : ℝ) : ℂ) := by
  -- Step 1 — linearity of `evalST` splits the source.
  rw [sourceEWA, (evalST τ (x : WA.Circ)).map_add, evalST_smul]
  -- Step 2 — growth leg.
  rw [h_growth]
  have hlift_src : logisticLifted p u x
      = intervalLogisticSource p u ⟨x, hxIcc⟩ := by
    rw [logisticLifted, intervalDomainLift, dif_pos hxIcc]
  rw [hlift_src]
  -- Step 3 — divergence leg: route to `deriv (· evalST (incl chemFlux))`.
  rw [evalST_gDeriv_chemFlux_eq_deriv μ ν γ hμ p U τ x]
  -- deriv-congruence: replace the integrand by `(chemFluxLifted p u y : ℂ)`.
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  have hee : (fun y : ℝ => evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ U)))
      =ᶠ[nhds x] (fun y : ℝ => ((chemFluxLifted p u y : ℝ) : ℂ)) :=
    Filter.eventuallyEq_of_mem hnhds (fun y hy => h_flux_nbhd y hy)
  rw [Filter.EventuallyEq.deriv_eq hee]
  -- The ℝ-flux has derivative `chemDiv` at `x` (real differentiability + the
  -- committed `chemFluxLifted ↔ chemDiv` reconciliation), hence its ℂ-cast too.
  have hderivR : HasDerivAt (chemFluxLifted p u)
      (intervalDomainChemotaxisDiv p u (intervalNeumannResolverR p u) ⟨x, hxIcc⟩) x := by
    have h := h_flux_diff.hasDerivAt
    rwa [deriv_chemFluxLifted_eq_chemDiv p u hgrad hx hxIcc] at h
  have hderivC : deriv (fun y : ℝ => ((chemFluxLifted p u y : ℝ) : ℂ)) x
      = ((intervalDomainChemotaxisDiv p u (intervalNeumannResolverR p u)
          ⟨x, hxIcc⟩ : ℝ) : ℂ) := hderivR.ofReal_comp.deriv
  rw [hderivC]
  -- Step 4 — combine into `intervalCoupledSource`.
  rw [intervalCoupledSource, intervalLogisticSource]
  push_cast
  ring

end ShenWork.EWA

#print axioms ShenWork.EWA.evalST_sourceEWA_eq_intervalCoupledSource
