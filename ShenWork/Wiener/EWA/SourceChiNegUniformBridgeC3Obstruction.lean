/-
  ShenWork/Wiener/EWA/SourceChiNegUniformBridgeC3Obstruction.lean

  The C3/floored residual over the full bounded PPID class implies a common
  lower floor for bounded PPID data.  The constant-datum obstruction from
  `IntervalDomainPPIDNoUniformFloor` therefore makes that all-PPID residual
  uninhabitable.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceChiNegUniformBridgeC3
import ShenWork.Paper2.IntervalDomainPPIDNoUniformFloor

open ShenWork.IntervalDomain (intervalDomain intervalDomainPoint)
open ShenWork.Paper2 (PaperPositiveInitialDatum)

noncomputable section

namespace ShenWork.EWA

/-- A full-PPID `UniformFlooredC3NeumannData` package would give a common
positive closed-domain floor for all interval PPID data with `|u₀| ≤ 1`. -/
theorem commonPPIDFloor_of_uniformFlooredC3NeumannData
    {p : CM2Params} (hD : UniformFlooredC3NeumannData p) :
    ∃ fm : ℝ, 0 < fm ∧
      ∀ {u0p : intervalDomainPoint → ℝ},
        PaperPositiveInitialDatum intervalDomain u0p →
        (∀ x, |u0p x| ≤ (1 : ℝ)) →
        ∀ x, fm ≤ u0p x := by
  obtain ⟨fm, hfm, _WM, _hWM, hbody⟩ := hD.liftM 1 zero_lt_one
  refine ⟨fm, hfm, ?_⟩
  intro u0p hpaper hbd x
  obtain ⟨C, hfloor, _hnorm⟩ := hbody hpaper hbd
  calc
    fm ≤ C.floor := hfloor
    _ ≤ C.u₀ x.1 := C.hfloor x.1
    _ = u0p x := C.hagree x

/-- Consequently the all-PPID C3/floored residual is not satisfiable on the
interval domain. -/
theorem not_uniformFlooredC3NeumannData (p : CM2Params) :
    ¬ UniformFlooredC3NeumannData p := by
  intro hD
  exact ShenWork.Paper2.intervalDomain_paperPositive_bounded_one_no_uniform_floor
    (commonPPIDFloor_of_uniformFlooredC3NeumannData hD)

end ShenWork.EWA

#print axioms ShenWork.EWA.not_uniformFlooredC3NeumannData
