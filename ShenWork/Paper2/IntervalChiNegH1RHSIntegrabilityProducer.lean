import ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability

/-!
# H¹ RHS integrability producer

This file packages the explicit H¹ identity RHS integrability assumption from
continuity data.  It does not prove the component continuity hypotheses; those
remain upstream regularity frontiers.
-/

open MeasureTheory Set
open scoped BigOperators Topology Interval

open ShenWork.IntervalDomain
open ShenWork.Paper2
open ShenWork.Paper2.IntervalChiNegH1Energy
open ShenWork.Paper2.IntervalChiNegH1DerivativeIntegrability

noncomputable section

namespace ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer

/-- Closed-window continuity of the explicit H¹ identity RHS gives the
`H1IdentityRHSIntegrableBefore` package. -/
theorem H1IdentityRHSIntegrableBefore_of_continuousOn_Icc
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hRHSCont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn
        (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.Icc a b)) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  { identity := hId
    rhs_intervalIntegrable :=
      H1IdentityRHS_intervalIntegrable_of_continuousOn_Icc hRHSCont }

/-- Unordered closed-window continuity of the explicit H¹ identity RHS also
gives the `H1IdentityRHSIntegrableBefore` package. -/
theorem H1IdentityRHSIntegrableBefore_of_continuousOn_uIcc
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hRHSCont : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn
        (H1IdentityRHSValue p u taxisX uvxx reactX) (Set.uIcc a b)) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX :=
  { identity := hId
    rhs_intervalIntegrable :=
      H1IdentityRHS_intervalIntegrable_of_continuousOn_uIcc hRHSCont }

/-- Component continuity on a closed time window gives continuity of the
assembled explicit H¹ identity RHS on that window. -/
theorem H1IdentityRHS_continuousOn_Icc_of_components
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ} {a b : ℝ}
    (hLap : ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hTaxis : ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ContinuousOn uvxx (Set.Icc a b))
    (hReact : ContinuousOn reactX (Set.Icc a b)) :
    ContinuousOn (H1IdentityRHSValue p u taxisX uvxx reactX)
      (Set.Icc a b) := by
  have hLapNeg : ContinuousOn (fun τ => -(lapL2sq u τ)) (Set.Icc a b) :=
    hLap.neg
  have hTaxisScaled :
      ContinuousOn (fun τ => (-p.χ₀) * taxisX τ) (Set.Icc a b) :=
    hTaxis.const_mul (-p.χ₀)
  have hUvxxScaled :
      ContinuousOn (fun τ => (-p.χ₀) * uvxx τ) (Set.Icc a b) :=
    hUvxx.const_mul (-p.χ₀)
  have hsum :
      ContinuousOn
        (fun τ =>
          ((-(lapL2sq u τ) + (-p.χ₀) * taxisX τ) +
            (-p.χ₀) * uvxx τ) + reactX τ)
        (Set.Icc a b) :=
    ((hLapNeg.add hTaxisScaled).add hUvxxScaled).add hReact
  change ContinuousOn
    (fun τ =>
      -(lapL2sq u τ) + (-p.χ₀) * taxisX τ + (-p.χ₀) * uvxx τ +
        reactX τ)
    (Set.Icc a b)
  simpa [neg_mul, add_assoc] using hsum

/-- Component continuity on every pre-horizon closed window gives the
`H1IdentityRHSIntegrableBefore` package. -/
theorem H1IdentityRHSIntegrableBefore_of_component_continuousOn_Icc
    {p : CM2Params} {T : ℝ}
    {u : ℝ → intervalDomainPoint → ℝ}
    {taxisX uvxx reactX : ℝ → ℝ}
    (hId : ∀ τ, τ ∈ Set.Ioo (0 : ℝ) T →
      H1EnergyIdentity p u τ (taxisX τ) (uvxx τ) (reactX τ))
    (hLap : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn (fun τ => lapL2sq u τ) (Set.Icc a b))
    (hTaxis : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn taxisX (Set.Icc a b))
    (hUvxx : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn uvxx (Set.Icc a b))
    (hReact : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b < T →
      ContinuousOn reactX (Set.Icc a b)) :
    H1IdentityRHSIntegrableBefore p u T taxisX uvxx reactX := by
  refine H1IdentityRHSIntegrableBefore_of_continuousOn_Icc hId ?_
  intro a b ha hab hbT
  exact H1IdentityRHS_continuousOn_Icc_of_components
    (hLap ha hab hbT) (hTaxis ha hab hbT) (hUvxx ha hab hbT)
    (hReact ha hab hbT)

#print axioms H1IdentityRHSIntegrableBefore_of_continuousOn_Icc
#print axioms H1IdentityRHSIntegrableBefore_of_continuousOn_uIcc
#print axioms H1IdentityRHS_continuousOn_Icc_of_components
#print axioms H1IdentityRHSIntegrableBefore_of_component_continuousOn_Icc

end ShenWork.Paper2.IntervalChiNegH1RHSIntegrabilityProducer
