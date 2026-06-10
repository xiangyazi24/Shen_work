/-
  ShenWork/Paper2/IntervalDomainHresWiring.lean

  **Final wiring, step 4 — narrowing the capstone's `Hres` surface.**

  The χ₀ = 0 capstone (`IntervalDomainThm11ChiZeroCoreProvider`) currently takes a
  universal provider

      Hres : ∀ u₀, PID u₀ → ∀ D, D.u = picardLimit p u₀ D.T →
               PicardIterateResidualData p u₀ D

  of the FULL iterate-side residual bundle (four substantive legs: `hFacts`,
  `hLcont_iter`/`hLcont_lim`, `Wdata`, `hsliceTC`).  Two of those legs are
  derivable for EVERY canonical-Picard-limit datum `D` from `D` + `hDu` alone:

    * **`hsliceTC`** — the patched-slice sup-norm time continuity — is exactly
      `IntervalPicardLimitSliceTimeContinuity.hsliceTC_of_mild_restart`, consuming
      only `(hχ0, Continuous u₀, D, hDu)`;
    * **`hLcont_lim`** — `[0,1]`-continuity of the limit's logistic source —
      follows from `D.hcont` + `hDu` (discharged inside
      `HresProducer.picardIterateResidualData_of_cone`).

  This file isolates the GENUINELY cone-specific residual core

      PicardIterateResidualCore p u₀ D
        := { hFacts, hFacts_T, hcont_iter, Wdata }

  (the iterate ball/geometric facts package, the iterate slice-continuity bundle,
  and the per-window K2 data — all properties of the Picard iteration AT the
  horizon `D.T`, not recoverable from a bare `D`), and provides

      picardIterateResidualData_of_core :
        (hχ0) → (Continuous u₀) → (hDu) → PicardIterateResidualCore … →
          PicardIterateResidualData p u₀ D

  which combines the core with the two universally-derived legs.  The capstone is
  then rewired to take the NARROWER core provider, discharging `hsliceTC` and
  `hLcont_lim` once and for all.

  HONESTY: the `Wdata`/`hFacts`/`hcont_iter` legs of the core remain genuine,
  satisfiable residuals — they bottom out in the `UniformWiring` analytic stack
  (whose gate is now discharged by `IntervalPicardGateSolve.exists_gate_solution`
  and `coneGradientMildSolutionData_exists_with_gate_data`) and the cone's
  internal ball/geometric/slice-continuity iterate data.  Wiring them fully is the
  remaining open analytic work; this pass removes the two legs that are NOT open.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.  New file only.
-/
import ShenWork.Paper2.IntervalDomainHresProducer
import ShenWork.Paper2.IntervalPicardLimitSliceTimeContinuity

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalMildPicard
  (GradientMildSolutionData HasContinuousSlices picardIter picardLimit)
open ShenWork.IntervalPicardWeightedC2Bootstrap (IterateWindowC2Data)
open ShenWork.IntervalPicardLimitCoeffConv (PicardConvFacts)

noncomputable section

namespace ShenWork.Paper2.HresWiring

/-- **The genuinely cone-specific iterate-side residual core.**

For a canonical-Picard-limit datum `D` (`D.u = picardLimit p u₀ D.T`), this bundles
exactly the three legs of `PicardIterateResidualData` that are properties of the
Picard iteration AT the horizon `D.T` (and hence NOT derivable from a bare `D`):
the ball/geometric facts package, the iterate slice-continuity bundle, and the
per-window K2 data.  The remaining legs (`hLcont_lim`, `hsliceTC`) are discharged
universally by `picardIterateResidualData_of_core`. -/
structure PicardIterateResidualCore
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  /-- The standalone ball/geometric-tail facts package (horizon `= D.T`). -/
  hFacts : PicardConvFacts p u₀
  hFacts_T : hFacts.T = D.T
  /-- The cone construction's internal iterate slice-continuity bundle. -/
  hcont_iter : ∀ n : ℕ, HasContinuousSlices D.T (picardIter p u₀ n)
  /-- The per-window uniform K2 data for the Picard iterates. -/
  Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T

/-- **Combine the cone-specific core with the universally-derived legs.**

`hsliceTC` is `hsliceTC_of_mild_restart` (needs only `hχ0`, `Continuous u₀`, `D`,
`hDu`); `hLcont_lim`/`hLcont_iter` are discharged inside
`HresProducer.picardIterateResidualData_of_cone`.  The result is the full
`PicardIterateResidualData` bundle the capstone consumes. -/
def picardIterateResidualData_of_core
    {p : CM2Params} (hχ0 : p.χ₀ = 0) {u₀ : intervalDomainPoint → ℝ}
    (hu₀cont : Continuous u₀)
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (C : PicardIterateResidualCore p u₀ D) :
    Thm11ChiZeroResidual.PicardIterateResidualData p u₀ D :=
  HresProducer.picardIterateResidualData_of_cone hDu C.hcont_iter C.hFacts C.hFacts_T
    C.Wdata
    (ShenWork.IntervalPicardLimitSliceTimeContinuity.hsliceTC_of_mild_restart
      hχ0 hu₀cont D hDu)

end ShenWork.Paper2.HresWiring
