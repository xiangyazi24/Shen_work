/-
  ShenWork/Wiener/EWA/SourceChiNegUniformBridgeC3.lean

  A narrowed, C3/Neumann datum-side residual for the strict chi-negative
  uniform core route.

  The current clean fixed-point estimates need two uniform controls over each
  bounded datum class: a positive common floor and a Wiener norm bound.  This
  file packages those controls for certified `C3NeumannDatum` representatives,
  then reuses the existing `DatumWienerData -> ChiNegDatumUniformCore` bridge.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegUniformBridge

open ShenWork.Wiener (WA ofCosineCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomain)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.EWA

/-- Wiener norm of the certified lifting associated to a C3/Neumann datum. -/
def c3DatumWienerNorm {u0p : intervalDomainPoint → ℝ}
    (hpaper : PaperPositiveInitialDatum intervalDomain u0p)
    (C : C3NeumannDatum u0p) : ℝ :=
  ‖(⟨ofCosineCoeffs (cosineCoeffs (datumWienerLifting_of_C3_neumann hpaper C).u₀),
      (datumWienerLifting_of_C3_neumann hpaper C).hmem⟩ : WA 1)‖

/-- A narrowed datum-side residual for the strict-negative uniform core.

For each sup-bound class `M`, it carries exactly the uniform controls consumed
by the current clean fixed-point estimates: a positive common floor `fm`, a
Wiener norm bound `WM`, and a certified C3/Neumann representative for each
paper-positive datum in the class. -/
structure UniformFlooredC3NeumannData (p : CM2Params) where
  liftM : ∀ M : ℝ, 0 < M →
    ∃ (fm : ℝ) (_ : 0 < fm) (WM : ℝ) (_ : 0 ≤ WM),
      ∀ {u0p : intervalDomainPoint → ℝ},
        (hpaper : PaperPositiveInitialDatum intervalDomain u0p) →
        (∀ x, |u0p x| ≤ M) →
        ∃ C : C3NeumannDatum u0p,
          fm ≤ C.floor ∧
          c3DatumWienerNorm hpaper C ≤ WM

/-- The C3/Neumann narrowed residual supplies the monolithic
`DatumWienerData` interface used by the existing strict-negative bridge. -/
def datumWienerData_of_uniformFlooredC3NeumannData
    (p : CM2Params) (hD : UniformFlooredC3NeumannData p) :
    DatumWienerData p where
  liftM := by
    intro M hM
    obtain ⟨fm, hfm, WM, hWM, hbody⟩ := hD.liftM M hM
    refine ⟨fm, hfm, WM, hWM, ?_⟩
    intro u0p hpaper hbd
    obtain ⟨C, hfloor, hnorm⟩ := hbody hpaper hbd
    let W := datumWienerLifting_of_C3_neumann hpaper C
    exact ⟨W, hfloor, hnorm⟩

/-- Direct composition to the EWA-free uniform core. -/
theorem uniformCore_of_uniformFlooredC3NeumannData
    (p : CM2Params)
    (hβpos : 0 < p.β) (hαnn : 0 ≤ p.α) (hμle1 : p.μ ≤ 1)
    (hD : UniformFlooredC3NeumannData p) :
    ChiNegDatumUniformCore p :=
  uniformCore_of_datumWienerData p hβpos hαnn hμle1
    (datumWienerData_of_uniformFlooredC3NeumannData p hD)

end ShenWork.EWA

#print axioms ShenWork.EWA.datumWienerData_of_uniformFlooredC3NeumannData
#print axioms ShenWork.EWA.uniformCore_of_uniformFlooredC3NeumannData
