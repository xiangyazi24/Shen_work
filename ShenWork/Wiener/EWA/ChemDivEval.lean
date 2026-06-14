import ShenWork.Wiener.EWA.SourceEvalBridge
import ShenWork.Wiener.EWA.ChemDivSourceAssembly

/-!
# EWA brick — the chemDiv EVAL sublemma (Phase C, `h_eval` of `h_coeff`)

This file **factors out** the chemotaxis-DIVERGENCE eval realization from the
committed full-source eval bridge `evalST_sourceEWA_eq_intervalCoupledSource`
(`SourceEvalBridge.lean`).  The full bridge proves

  `evalST τ x (sourceEWA p U) = intervalCoupledSource p u (R u) x`   on `Ioo 0 1`,

with `sourceEWA = (−χ₀)·gDeriv(chemFluxEWA) + growth`.  Here we isolate the pure
divergence summand `chemDivEWA = gDeriv (chemFluxEWA …)` and prove that its Wiener
synthesis equals the committed `coupledChemDivSourceLift p u s` at the time slice
`s = τ.1` (the iterate `u τ.1`).

## The chain
`chemDivEWA = gDeriv (chemFluxEWA …)` (def), then the two committed INTERNAL
lemmas of `SourceEvalBridge` (both public `theorem`s, re-usable):

* `evalST_gDeriv_chemFlux_eq_deriv` :
  `evalST τ x (gDeriv chemFluxEWA) = deriv (fun y => evalST τ y (incl chemFluxEWA)) x`;
* `deriv_chemFluxLifted_eq_chemDiv` :
  `deriv (chemFluxLifted p w) x = intervalDomainChemotaxisDiv p w (R w) ⟨x,_⟩`.

Between them a `deriv`-congruence (over the OPEN `Ioo 0 1 ∈ 𝓝 x`) replaces the
synthesized integrand by the ℂ-cast of `chemFluxLifted p (u τ.1)` — supplied by the
factor hypothesis `h_flux_nbhd` — and the real differentiability `h_flux_diff`
plus the ℓ¹ gradient majorant `hgrad` discharge the cast `deriv`.

## The resolver match (def, NOT a hypothesis)
`coupledChemDivSourceLift p u s x` unfolds (`intervalDomainLift`, `dif_pos hxIcc`)
to `intervalDomainChemotaxisDiv p (u s) (coupledChemicalConcentration p u s) ⟨x,_⟩`,
and `coupledChemicalConcentration p u s = intervalNeumannResolverR p (u s)` holds
**definitionally** (`IntervalCoupledRegularityBootstrap.coupledChemicalConcentration`).
So the resolver match is `rfl` — no `h_resolver_match` hypothesis is needed.

The factor realizations (`h_flux_nbhd`, `hgrad`, `h_flux_diff`) are upstream (B5e)
obligations carried as hypotheses, to be discharged later by the Q2 construction.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint intervalDomainChemotaxisDiv)
open ShenWork.PDE (intervalNeumannResolverR intervalNeumannResolverCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap (coupledChemDivSourceLift
  coupledChemicalConcentration)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The chemDiv eval sublemma.**

The Wiener synthesis (`evalST`) of the chemotaxis-divergence EWA source
`chemDivEWA μ ν γ hμ p U = gDeriv (chemFluxEWA …)` equals (cast to `ℂ`) the
committed real-space `coupledChemDivSourceLift p u τ.1 x`, at every interior
spatial point `x ∈ (0,1)` and time slice `τ.1`.

This is the divergence leg of the full-source eval bridge in isolation: it is the
`h_eval` obligation behind the `h_coeff` discharge of
`coupledChemDivSource_timeC1On_of_EWA`.

The factor realizations are carried as hypotheses (discharged later by Q2):
* `h_flux_nbhd` — the flux value agreement on the OPEN `Ioo 0 1 ∈ 𝓝 x`
  (for the slice `u τ.1`);
* `hgrad` — the gradient ℓ¹ majorant for the resolver of the slice `u τ.1`;
* `h_flux_diff` — real differentiability of `chemFluxLifted p (u τ.1)` at `x`.

The resolver match `coupledChemicalConcentration = intervalNeumannResolverR` is
**definitional** (`rfl`), so no resolver-match hypothesis is required. -/
theorem evalST_chemDivEWA_eq_coupledChemDivSourceLift
    {μ ν γ : ℝ} (hμ : 0 < μ) (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (τ : TimeDom T) (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    (hgrad : Summable fun k : ℕ =>
      |(intervalNeumannResolverCoeff p (u τ.1) k).re| * ((k : ℝ) * Real.pi))
    (h_flux_nbhd : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ U)) = ((chemFluxLifted p (u τ.1) y : ℝ) : ℂ))
    (h_flux_diff : DifferentiableAt ℝ (chemFluxLifted p (u τ.1)) x) :
    evalST τ (x : WA.Circ) (chemDivEWA μ ν γ hμ p U)
      = ((coupledChemDivSourceLift p u τ.1 x : ℝ) : ℂ) := by
  -- Step 0 — unfold `chemDivEWA = gDeriv (chemFluxEWA …)`.
  rw [chemDivEWA]
  -- Step 1 — route the divergence leg to `deriv (· evalST (incl chemFlux))`.
  rw [evalST_gDeriv_chemFlux_eq_deriv μ ν γ hμ p U τ x]
  -- Step 2 — `deriv`-congruence on `Ioo 0 1 ∈ 𝓝 x`: replace the synthesized
  -- integrand by the ℂ-cast of `chemFluxLifted p (u τ.1)`.
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds x := IsOpen.mem_nhds isOpen_Ioo hx
  have hee : (fun y : ℝ => evalST τ (y : WA.Circ) (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (chemFluxEWA μ ν p.β γ hμ U)))
      =ᶠ[nhds x] (fun y : ℝ => ((chemFluxLifted p (u τ.1) y : ℝ) : ℂ)) :=
    Filter.eventuallyEq_of_mem hnhds (fun y hy => h_flux_nbhd y hy)
  rw [Filter.EventuallyEq.deriv_eq hee]
  -- Step 3 — the ℝ-flux has derivative `chemDiv` at `x` (real differentiability +
  -- the committed `chemFluxLifted ↔ chemDiv` reconciliation), hence its ℂ-cast.
  have hderivR : HasDerivAt (chemFluxLifted p (u τ.1))
      (intervalDomainChemotaxisDiv p (u τ.1) (intervalNeumannResolverR p (u τ.1))
        ⟨x, hxIcc⟩) x := by
    have h := h_flux_diff.hasDerivAt
    rwa [deriv_chemFluxLifted_eq_chemDiv p (u τ.1) hgrad hx hxIcc] at h
  have hderivC : deriv (fun y : ℝ => ((chemFluxLifted p (u τ.1) y : ℝ) : ℂ)) x
      = ((intervalDomainChemotaxisDiv p (u τ.1) (intervalNeumannResolverR p (u τ.1))
          ⟨x, hxIcc⟩ : ℝ) : ℂ) := hderivR.ofReal_comp.deriv
  rw [hderivC]
  -- Step 4 — def-match: `coupledChemDivSourceLift p u τ.1 x` unfolds to the same
  -- `chemotaxisDiv`, with the resolver match `coupledChemicalConcentration =
  -- intervalNeumannResolverR` definitional (`rfl`).
  rw [coupledChemDivSourceLift, intervalDomainLift, dif_pos hxIcc]
  rfl

end ShenWork.EWA

#print axioms ShenWork.EWA.evalST_chemDivEWA_eq_coupledChemDivSourceLift
