import ShenWork.Wiener.EWA.SourceEnvelope
import ShenWork.Wiener.EWA.Flux
import ShenWork.PDE.IntervalCoupledSourceTimeC1
import ShenWork.PDE.IntervalDuhamelSourceTimeC1On

/-!
# EWA assembly — the chemotaxis-divergence source `DuhamelSourceTimeC1On` from the EWA envelope

This file is the **assembly** node: it chains the committed EWA bricks into the
committed window-local `DuhamelSourceTimeC1On` package for the chemotaxis-divergence
source coefficient family `coupledChemDivSourceCoeffs p u`.

The single load-bearing wiring is the `envelope`/`henv_summable` pair: they come
from the committed Wiener-algebra `SourceEnvelope` of an EWA source element
`chemDivEWA μ ν γ hμ p U = gDeriv (chemFluxEWA …)`.  That is the ℓ¹ gap-filler.

The genuinely-remaining pieces are taken as EXPLICIT HYPOTHESES, to be discharged
later by the eval/coeff bridge (`h_coeff`) and the chemDiv time-derivative chain
(`adot`, `h_deriv`, `h_adotcont`, `Mdot`, `h_Mdot`).

No `sorry`, no `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.IntervalDuhamelSourceTimeC1On
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- The chemotaxis-divergence EWA source element: the spatial derivative of the
chemotactic flux, as a genuine `EWA T 0` element. -/
noncomputable def chemDivEWA (μ ν γ : ℝ) (hμ : 0 < μ) (p : CM2Params) (U : EWA T 1) :
    EWA T 0 :=
  GWA.gDeriv (chemFluxEWA μ ν p.β γ hμ U)

/-- **The assembled theorem.**  Build the committed window-local
`DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T` for the
chemotaxis-divergence source FROM the EWA `SourceEnvelope` of `chemDivEWA`.

The `envelope`/`henv_summable` fields are supplied by the committed EWA
`SourceEnvelope` brick — the Wiener-algebra ℓ¹ gap-filler, now wired in.

The remaining fields are explicit hypotheses to discharge later:
* `h_coeff` — the value-envelope domination leg (eval/coeff bridge);
* `adot`, `h_deriv`, `h_adotcont`, `Mdot`, `h_Mdot` — the time-derivative leg. -/
noncomputable def coupledChemDivSource_timeC1On_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ)
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    (h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p u s n|
          ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n)
    (adot : ℝ → ℕ → ℝ)
    (h_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (adot s n) (Set.Icc 0 T) s)
    (h_adotcont : ∀ n, ContinuousOn (fun s => adot s n) (Set.Icc 0 T))
    (Mdot : ℝ) (h_Mdot : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |adot s n| ≤ Mdot) :
    DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T where
  adot := adot
  hderiv := h_deriv
  hadotcont := h_adotcont
  envelope := sourceEnvelope (chemDivEWA μ ν γ hμ p U)
  henv_summable := sourceEnvelope_summable _
  henv_bound := h_coeff
  derivBound := Mdot
  hderivBound := h_Mdot

end ShenWork.EWA

#print axioms ShenWork.EWA.coupledChemDivSource_timeC1On_of_EWA
