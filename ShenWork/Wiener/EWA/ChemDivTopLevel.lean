import ShenWork.Wiener.EWA.ChemDivSourceAssembly

/-!
# EWA chemotaxis-divergence top-level chaining

This file assembles a concrete **top-level conditional theorem** that genuinely
routes the EWA Wiener-algebra `DuhamelSourceTimeC1On` package (built from the ℓ¹
`SourceEnvelope` of the chemotaxis-divergence flux element `chemDivEWA`) into a
committed PDE conclusion.

The proof has two genuine steps:

1.  Apply `ShenWork.EWA.coupledChemDivSource_timeC1On_of_EWA` (the committed
    assembly node) to manufacture
    `DuhamelSourceTimeC1On (coupledChemDivSourceCoeffs p u) 0 T`
    from the EWA envelope `sourceEnvelope (chemDivEWA μ ν γ hμ p U)` plus the
    coefficient-domination and time-derivative hypotheses.
2.  Feed that package to the committed windowed consumer
    `ShenWork.IntervalDuhamelSourceTimeC1On.duhamelSpectralCoeff_eigenvalue_summable_on`,
    which yields the **windowed eigenvalue-weighted ℓ¹ summability** of the
    Duhamel spectral coefficients at any interior evaluation time `t ∈ (0, T]`.

The genuinely-remaining inputs are taken as EXPLICIT, NAMED hypotheses
(`h_coeff`, `adot`, `h_deriv`, `h_adotcont`, `Mdot`, `h_Mdot`), exactly the
fields of the assembly node still awaiting their eval/coeff and time-derivative
discharges.

The richer closed-`C²`/Neumann target is reached through a *different* committed
interface (`GradientMildSolutionData` / `HasRestartCosineRepresentations`) that
is keyed on the mild-solution datum rather than directly on a
`DuhamelSourceTimeC1On` of the chemDiv coefficients; that wiring is mapped in the
report, not forced here.

No `sorry`, no `axiom`, no `native_decide`.
-/

open scoped BigOperators
open ShenWork.GWA ShenWork.Wiener
open ShenWork.EWA
open ShenWork.IntervalDuhamelSourceTimeC1On
open ShenWork.IntervalCoupledRegularityBootstrap
open ShenWork.IntervalDomain (intervalDomainPoint)

noncomputable section

namespace ShenWork.EWA

variable {T : ℝ}

/-- **Top-level conditional theorem.**

From the EWA `SourceEnvelope` of the chemotaxis-divergence flux element
`chemDivEWA μ ν γ hμ p U` (the Wiener-algebra ℓ¹ gap-filler), together with the
remaining coefficient-domination and time-derivative inputs as explicit
hypotheses, the eigenvalue-weighted Duhamel spectral coefficients of the
chemotaxis-divergence source are summable on the window at every interior
evaluation time `t ∈ (0, T]`.

The proof genuinely chains:
`coupledChemDivSource_timeC1On_of_EWA` ⟶
`duhamelSpectralCoeff_eigenvalue_summable_on`. -/
theorem chemDiv_eigenvalueSummableOn_of_EWA
    {μ ν γ : ℝ} (hμ : 0 < μ)
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ) (U : EWA T 1)
    {t : ℝ} (htlo : 0 < t) (hthi : t ≤ T)
    (h_coeff : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        |coupledChemDivSourceCoeffs p u s n|
          ≤ sourceEnvelope (chemDivEWA μ ν γ hμ p U) n)
    (adot : ℝ → ℕ → ℝ)
    (h_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n,
        HasDerivWithinAt (fun r => coupledChemDivSourceCoeffs p u r n)
          (adot s n) (Set.Icc 0 T) s)
    (h_adotcont : ∀ n, ContinuousOn (fun s => adot s n) (Set.Icc 0 T))
    (Mdot : ℝ)
    (h_Mdot : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n, |adot s n| ≤ Mdot) :
    Summable (fun n => unitIntervalCosineEigenvalue n *
      |∫ s in (0 : ℝ)..t,
        Real.exp (-(t - s) * unitIntervalCosineEigenvalue n)
          * coupledChemDivSourceCoeffs p u s n|) :=
  duhamelSpectralCoeff_eigenvalue_summable_on
    (coupledChemDivSource_timeC1On_of_EWA hμ p u U
      h_coeff adot h_deriv h_adotcont Mdot h_Mdot)
    htlo hthi

end ShenWork.EWA

#print axioms ShenWork.EWA.chemDiv_eigenvalueSummableOn_of_EWA
