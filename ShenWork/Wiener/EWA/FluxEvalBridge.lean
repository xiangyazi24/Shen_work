import ShenWork.Wiener.EWA.Flux
import ShenWork.Paper2.IntervalGradientDuhamelMap

/-!
# EWA brick — the chemotaxis FLUX eval bridge (Phase C central assembly)

This file assembles the **eval bridge for the chemotaxis flux**: the Wiener
synthesis (`evalST`) of the EWA chemotaxis flux `chemFluxEWA μ ν β γ hμ u`
equals (cast to `ℂ`) the committed real-space lifted flux `chemFluxLifted p u x`,
pointwise on the interior `(0,1)`.

## Structure

The committed product-factoring `chemFluxEWA_eval` splits
`evalST (incl (chemFluxEWA … u))` into the three factor evaluations

* `u`            — realized by `h_u`   as `(intervalDomainLift u x : ℂ)`;
* `gDeriv vField`— realized by `h_vx`  as `(resolverGradReal p u x : ℂ)`;
* `qFactor β v`  — evaluated by the committed `qFactor_eval` to
  `((evalST (1+v)).re ^ (-β) : ℂ)`, then `h_v` (the value realization of `v`)
  identifies `evalST (1+v) = 1 + (intervalNeumannResolverR p u ⟨x,hx⟩ : ℂ)`,
  whose real part is `1 + intervalNeumannResolverR p u ⟨x,hx⟩` (the resolver is
  real).

The three factor realizations (`h_u`, `h_v`, `h_vx`) are upstream B5e
obligations and are supplied here as **hypotheses** (NOT discharged).  The
`qFactor_eval` floor/reality preconditions (`hqfloor`, `hqreal`) on `1+v` are
likewise the upstream floor discharge, supplied as hypotheses.

The final real-arithmetic match converts the EWA `(1+R)^(-β)` (a `Real.rpow`
from `qFactor`) to `chemFluxLifted`'s division by `(1+lift R)^β` via
`Real.rpow_neg` + `div_eq_mul_inv`, needing the positivity `h_floor : 0 < 1+R`.

## The `evalST ↔ evalC` link

`evalST τ x a = WA.evalAt x (sliceWA τ a)` (committed `evalST_apply`,
`ShenWork/Wiener/EWA/Decisive.lean:41`) and `WA.evalAt x b = WA.evalC b x`
(`WeightedL1Eval.lean:395`,`:366`).  The resolver/grad bridges export their
value at the `evalC (toZero (sliceWA τ ·)) ↑x` level; here those values arrive
already packaged at the `evalST` level as the realization hypotheses, so this
assembly does not re-derive the `evalST = evalC∘sliceWA` link — it consumes the
hypotheses directly.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.PDE (intervalNeumannResolverR)
open ShenWork.Paper2 (resolverGradReal)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The chemotaxis flux eval bridge.**

The Wiener synthesis of the EWA chemotaxis flux `chemFluxEWA μ ν p.β γ hμ u`
equals the committed real-space lifted flux `chemFluxLifted p u x`, cast to `ℂ`,
at every interior spatial point `x ∈ (0,1)`.

The three factor realizations and the `qFactor` floor/reality preconditions are
upstream (B5e) obligations supplied here as hypotheses; the assembly routes them
through the committed `chemFluxEWA_eval` (product factoring) and `qFactor_eval`
(negative-power evaluation), then matches the `Real.rpow` power against
`chemFluxLifted`'s division. -/
theorem evalST_chemFluxEWA_eq_chemFluxLifted
    (μ ν γ : ℝ) (hμ : 0 < μ) (p : CM2Params)
    (u : EWA T 1) (uR : intervalDomainPoint → ℝ)
    (τ : TimeDom T) (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    (h_u : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) u)
      = (intervalDomainLift uR x : ℂ))
    (h_vx : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (GWA.incl (by omega : (1:ℕ) ≤ 2) (GWA.gDeriv (vFieldEWA μ ν γ hμ u))))
      = (resolverGradReal p uR x : ℂ))
    (h_v : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u)))
      = (intervalNeumannResolverR p uR ⟨x, hxIcc⟩ : ℂ))
    (hqfloor : UniformFloor (1 + GWA.incl (by omega : (1:ℕ) ≤ 3)
        (vFieldEWA μ ν γ hμ u)) μ)
    (hqreal : ∀ (σ : TimeDom T) (y : WA.Circ),
      (evalST σ y (GWA.incl (by omega : (0:ℕ) ≤ 1)
        (1 + GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u)))).im = 0)
    (hβpos : 0 < p.β)
    (h_floor : 0 < 1 + intervalNeumannResolverR p uR ⟨x, hxIcc⟩) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (chemFluxEWA μ ν p.β γ hμ u))
      = ((chemFluxLifted p uR x : ℝ) : ℂ) := by
  -- Abbreviations for the included resolver field and `1 + v`.
  set v : EWA T 1 := GWA.incl (by omega : (1:ℕ) ≤ 3) (vFieldEWA μ ν γ hμ u) with hv_def
  -- Step 1 — committed product factoring of the flux into three evalST factors.
  rw [chemFluxEWA_eval μ ν p.β γ hμ u τ x]
  -- Step 2a — the `u` factor (value realization).
  rw [h_u]
  -- Step 2b — the `gDeriv vField` factor (gradient realization).
  rw [h_vx]
  -- Step 2c — the `qFactor` factor via the committed `qFactor_eval`.
  rw [qFactor_eval (β := p.β) (δ := μ) (v := v) hβpos hμ hqfloor hqreal τ x]
  -- Identify `evalST (incl (1+v))` with `1 + (R : ℂ)` via the ring-hom structure
  -- of `evalST ∘ incl` and the value realization `h_v`.
  have hincl_one : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1) = 1 := by
    rw [← GWA.gIncl_apply, map_one]
  have hincl_add : GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + v)
      = GWA.incl (by omega : (0:ℕ) ≤ 1) (1 : EWA T 1)
        + GWA.incl (by omega : (0:ℕ) ≤ 1) v := by
    rw [← GWA.gIncl_apply, map_add, GWA.gIncl_apply, GWA.gIncl_apply]
  have hev1v : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (1 + v))
      = ((1 + intervalNeumannResolverR p uR ⟨x, hxIcc⟩ : ℝ) : ℂ) := by
    rw [hincl_add, (evalST τ x).map_add, hincl_one, (evalST τ x).map_one, h_v]
    push_cast; ring
  rw [hev1v, Complex.ofReal_re]
  -- The flux value is real; reduce to a real equality cast to `ℂ`.
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  -- Match the EWA negative power `(1+R)^(-β)` to `chemFluxLifted`'s `/(1+R)^β`.
  congr 1
  rw [chemFluxLifted]
  -- `intervalDomainLift (intervalNeumannResolverR p uR) x = R p uR ⟨x,_⟩`.
  have hliftR : intervalDomainLift (intervalNeumannResolverR p uR) x
      = intervalNeumannResolverR p uR ⟨x, hxIcc⟩ := by
    rw [intervalDomainLift, dif_pos hxIcc]
  rw [hliftR]
  -- `a * b * (1+R)^(-β) = a * b / (1+R)^β`.
  rw [Real.rpow_neg h_floor.le, div_eq_mul_inv, mul_assoc]

end ShenWork.EWA

#print axioms ShenWork.EWA.evalST_chemFluxEWA_eq_chemFluxLifted
