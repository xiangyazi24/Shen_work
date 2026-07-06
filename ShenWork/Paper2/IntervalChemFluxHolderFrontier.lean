/-
  ShenWork/Paper2/IntervalChemFluxHolderFrontier.lean

  Source-side frontier for the chemotaxis differentiated leg.

  The full-kernel second-derivative Duhamel zero-time API consumes a uniform
  spatial `C^θ` modulus for the source family

    `Q(s) = chemFluxLifted p (u s)`.

  This file deliberately packages that source regularity as a frontier assumption.
  It does not prove the nonlinear flux is Hölder and does not mention the downstream
  patched zero-face/headline targets.

-/
import ShenWork.Paper2.IntervalGradientDuhamelMap
import ShenWork.PDE.IntervalFullKernelSecondDerivCtheta

open MeasureTheory
open ShenWork.IntervalDomain (intervalDomainPoint intervalMeasure)
open ShenWork.IntervalGradientDuhamelMap (chemFluxLifted)

namespace ShenWork.Paper2

noncomputable section

/-- Source-side frontier: uniform small-time `C^θ` data for the chemotaxis flux
`Q(s) = chemFluxLifted p (u s)`.  This is only a source-regularity package; it does
not assert any downstream zero-face trace or patched derivative convergence. -/
structure ChemFluxCthetaSourceOn
    (p : CM2Params) (u : ℝ → intervalDomainPoint → ℝ)
    (T θ CQ HQ : ℝ) : Prop where
  theta_pos : 0 < θ
  theta_lt_one : θ < 1
  CQ_nonneg : 0 ≤ CQ
  HQ_nonneg : 0 ≤ HQ
  flux_meas : Measurable (Function.uncurry (fun s => chemFluxLifted p (u s)))
  flux_int : ∀ s : ℝ, Integrable (chemFluxLifted p (u s)) (intervalMeasure 1)
  flux_bound : ∀ s : ℝ, 0 < s → s ≤ T → ∀ y : ℝ,
    |chemFluxLifted p (u s) y| ≤ CQ
  flux_cont : ∀ s : ℝ, 0 < s → s ≤ T → Continuous (chemFluxLifted p (u s))
  flux_holder : ∀ s : ℝ, 0 < s → s ≤ T →
    ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      |chemFluxLifted p (u s) a - chemFluxLifted p (u s) b| ≤
        HQ * |a - b| ^ θ

/-- A `ChemFluxCthetaSourceOn` package supplies exactly the per-slice hypotheses
needed by the full-kernel cancellative Hessian estimate. -/
theorem chemFlux_secondDeriv_slice_bound_of_CthetaSourceOn
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ}
    {T θ CQ HQ : ℝ}
    (H : ChemFluxCthetaSourceOn p u T θ CQ HQ)
    {s σ x : ℝ} (hs0 : 0 < s) (hsT : s ≤ T)
    (hσ : 0 < σ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |deriv (fun z : ℝ => deriv
        (fun w : ℝ =>
          ShenWork.IntervalNeumannFullKernel.intervalFullSemigroupOperator σ
            (chemFluxLifted p (u s)) w) z) x| ≤
      ShenWork.IntervalNeumannFullKernel.weightedHeatHessConst θ *
        σ ^ (-1 + θ / 2 : ℝ) * HQ :=
  ShenWork.IntervalNeumannFullKernel.neumannHeatSecondDeriv_Ctheta_to_Linfty
    hσ H.theta_pos H.theta_lt_one
    (H.flux_int s).aestronglyMeasurable
    (H.flux_bound s hs0 hsT)
    H.HQ_nonneg
    (H.flux_holder s hs0 hsT)
    hx

end

end ShenWork.Paper2
