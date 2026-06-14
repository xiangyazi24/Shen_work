import ShenWork.Wiener.EWA.Flux
import ShenWork.Paper2.IntervalGradientDuhamelMap

/-!
# EWA brick — the logistic growth/source eval bridge (Phase C source assembly)

This file assembles the **eval bridge for the logistic growth source**: the
Wiener synthesis (`evalST`) of the EWA growth term `growthEWA p.α p.a p.b u`
equals (cast to `ℂ`) the committed real-space lifted source `logisticLifted p uR x`,
pointwise on the closed interval `[0,1]`.  Sibling of `FluxEvalBridge`.

## Structure

The committed factoring `growthEWA_eval` splits `evalST (incl (growthEWA … u))`
into

* the `u` factor, realized by `h_u` as `(intervalDomainLift uR x : ℂ)`;
* the `realPowEWA u p.α` factor, realized by `h_uα` as
  `(((intervalDomainLift uR x : ℝ)) ^ p.α : ℂ)`  (this is the `realPowEWA_eval`
  value packaged at the `evalST` level — see `Flux.realPowEWA_eval`).

Both realizations are upstream (B5e) obligations supplied here as **hypotheses**
(NOT discharged).

The final match unfolds the committed
`logisticLifted p uR = intervalDomainLift (intervalLogisticSource p uR)` with
`intervalLogisticSource p uR x = uR x * (p.a − p.b · (uR x)^p.α)`.  Since
`intervalDomainLift f x = if x ∈ Icc 0 1 then f ⟨x,_⟩ else 0`, on `x ∈ [0,1]` the
lift of the product/power equals the product/power of the lifts (`dif_pos`), so
the two sides agree after pushing the real arithmetic through `Complex.ofReal_*`.

No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalDomainExistence (intervalLogisticSource)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **The logistic growth source eval bridge.**

The Wiener synthesis of the EWA growth term `growthEWA p.α p.a p.b u` equals the
committed real-space lifted source `logisticLifted p uR x`, cast to `ℂ`, at every
spatial point `x ∈ [0,1]`.

The two factor realizations (`h_u`, `h_uα`) are upstream (B5e) obligations
supplied here as hypotheses; the assembly routes them through the committed
`growthEWA_eval` factoring, then unfolds `logisticLifted` / `intervalLogisticSource`
and pushes the real arithmetic through `Complex.ofReal_*` via the `dif_pos`
distribution of `intervalDomainLift` on `[0,1]`. -/
theorem evalST_growthEWA_eq_logisticLifted
    (p : CM2Params) (u : EWA T 1) (uR : intervalDomainPoint → ℝ)
    (τ : TimeDom T) (x : ℝ) (hxIcc : x ∈ Set.Icc (0 : ℝ) 1)
    (h_u : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) u)
      = (intervalDomainLift uR x : ℂ))
    (h_uα : evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (realPowEWA u p.α))
      = ((intervalDomainLift uR x ^ p.α : ℝ) : ℂ)) :
    evalST τ x (GWA.incl (by omega : (0:ℕ) ≤ 1) (growthEWA p.α p.a p.b u))
      = ((logisticLifted p uR x : ℝ) : ℂ) := by
  -- Step 1 — committed factoring of the source through the product and the
  -- ℂ-linear combination (`growthEWA_eval`).
  rw [growthEWA_eval p.α p.a p.b u τ x]
  -- Step 2 — the two factor realizations.
  rw [h_u, h_uα]
  -- Step 3 — push `intervalDomainLift` through `dif_pos` on `[0,1]`, on both the
  -- LHS factor `lift uR x` and the RHS lifted source `logisticLifted p uR x`.
  -- `intervalDomainLift uR x = uR ⟨x,_⟩` (LHS), and
  -- `logisticLifted p uR x = intervalLogisticSource p uR ⟨x,_⟩`
  --   = uR ⟨x,_⟩ * (p.a - p.b * (uR ⟨x,_⟩)^p.α)` (RHS).
  have hlift_u : intervalDomainLift uR x = uR ⟨x, hxIcc⟩ := by
    rw [intervalDomainLift, dif_pos hxIcc]
  have hlift_src : logisticLifted p uR x
      = uR ⟨x, hxIcc⟩ * (p.a - p.b * (uR ⟨x, hxIcc⟩) ^ p.α) := by
    rw [logisticLifted, intervalDomainLift, dif_pos hxIcc, intervalLogisticSource]
  rw [hlift_u, hlift_src]
  -- Step 4 — both sides are `ℂ`-casts of the same real expression.
  push_cast
  ring

end ShenWork.EWA

#print axioms ShenWork.EWA.evalST_growthEWA_eq_logisticLifted
