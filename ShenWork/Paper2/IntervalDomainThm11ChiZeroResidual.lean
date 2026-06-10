/-
  ShenWork/Paper2/IntervalDomainThm11ChiZeroResidual.lean

  **The precisely-named iterate-side residual bundle for the χ₀ = 0 Provider.**

  After the `hDu : D.u = picardLimit p u₀ D.T` threading pass, the three remaining
  open obligations of `reducedLimitRegularityInputs_of_picard`
  (`IntervalDomainThm11ChiZeroCoreProvider`) are ALL iterate-side analytic facts
  about the *canonical* Picard limit — none of them is extractable from a bare
  `GradientMildSolutionData` (which carries only spatial slice continuity
  `HasContinuousSlices`, not the iterate ball/geometric data nor joint time
  continuity).  This file bundles them as one honest record
  `PicardIterateResidualData p u₀ D`, and turns each of the Provider's former
  `sorry`s into a clean *implication* from that bundle:

  * **`hconv`** (R-src0F-3) — pointwise coefficient convergence of the iterates to
    the limit slice.  PROVED here from the bundle's `MildExistenceData` (matching
    `D.T`, supplying the ball/geometric facts) + iterate/limit `[0,1]`-continuity,
    via `IntervalPicardLimitCoeffConv.picardIter_logisticCoeff_tendsto_limit`,
    after rewriting the limit slice through `hDu`.  Nothing is re-asserted: the
    convergence is genuinely derived from the contraction tail.

  * **`hCwin_ex`** (R-src0F-2) — the n-uniform window source envelope.  PROVED here
    from the bundle's per-window `IterateWindowC2Data` via
    `IntervalPicardWeightedC2Bootstrap.source_coeff_window_uniform`.

  * **`hsliceTC`** (R-src0F-4 input) — sup-norm time continuity of the patched
    slice profile on `[0,T]`.  This is the single genuinely-open analytic field
    (interior mild-slice time continuity + the `s = 0⁺` initial approach
    `gradientMildSolutionData_initialApproach`); the scaffolding consuming it is
    already proved in `IntervalPicardLimitBddHcontP.patchedSource_continuousOn_Icc`.
    Carried verbatim as a bundle field.

  The bundle is the honest residual boundary: every field is a TRUE statement about
  the canonical Picard limit, satisfiable from the cone construction's internal
  iterate data; the Provider threads — does not assert — them.

  No `sorry`, no `admit`, no custom `axiom`, no `native_decide`.
-/
import ShenWork.Paper2.IntervalPicardLimitBddHcontP
import ShenWork.Paper2.IntervalPicardWeightedC2Bootstrap
import ShenWork.Paper2.IntervalPicardLimitCoeffConv

open MeasureTheory Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainLift intervalDomainPoint)
open ShenWork.IntervalNeumannFullKernel (cosineCoeffs)
open ShenWork.IntervalGradientDuhamelMap (logisticLifted)
open ShenWork.IntervalMildPicard (GradientMildSolutionData MildExistenceData picardIter picardLimit)
open ShenWork.IntervalPicardLimitBddProducer (windowEnv)
open ShenWork.IntervalPicardWeightedC2Bootstrap (IterateWindowC2Data source_coeff_window_uniform)

noncomputable section

namespace ShenWork.Paper2.Thm11ChiZeroResidual

/-- **The iterate-side residual bundle for the canonical Picard-limit datum.**

For a packaged mild solution `D` whose trajectory IS the canonical Picard limit
(`D.u = picardLimit p u₀ D.T`), this records exactly the iterate-side analytic
data the χ₀ = 0 Provider cannot recover from `D` alone. -/
structure PicardIterateResidualData
    (p : CM2Params) (u₀ : intervalDomainPoint → ℝ)
    (D : GradientMildSolutionData p u₀) where
  /-- The `MildExistenceData` whose Picard iterates underlie `D`'s trajectory.
  Its horizon matches `D.T`; it supplies the ball / geometric-tail data that
  `picardIter_logisticCoeff_tendsto_limit` consumes.  Satisfiable: the cone
  construction (`coneGradientMildSolutionData_exists`) builds `D` from exactly
  such iterate data. -/
  hME : MildExistenceData p u₀
  hME_T : hME.T = D.T
  /-- `[0,1]`-continuity of each iterate's logistic source (genuinely C² slices). -/
  hLcont_iter : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ D.T →
    ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1)
  /-- `[0,1]`-continuity of the limit's logistic source. -/
  hLcont_lim : ∀ (σ : ℝ), 0 < σ → σ ≤ D.T →
    ContinuousOn (logisticLifted p (picardLimit p u₀ D.T σ)) (Set.Icc (0 : ℝ) 1)
  /-- Per-window uniform K2 data for the Picard iterates (R-src0F-2 input). -/
  Wdata : ∀ a', 0 < a' → IterateWindowC2Data p u₀ a' D.T
  /-- Sup-norm time continuity of the patched slice profile on `[0,T]`
  (R-src0F-4 input): the single genuinely-open analytic residual. -/
  hsliceTC : ∀ s₀ ∈ Set.Icc (0 : ℝ) D.T, ∀ ε > 0, ∃ δ > 0,
    ∀ s ∈ Set.Icc (0 : ℝ) D.T, |s - s₀| < δ →
      ∀ y, |ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s y
            - ShenWork.IntervalPicardLimitBddHcontP.patchedSlice u₀ D.u s₀ y| < ε

/-- **R-src0F-3 (hconv), proved from the bundle.**  Rewriting the limit slice
through `hDu` reduces the convergence to the canonical Picard-limit statement,
discharged by `picardIter_logisticCoeff_tendsto_limit` with the bundle's
`MildExistenceData` and `[0,1]`-continuity data. -/
theorem hconv_of_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hDu : D.u = picardLimit p u₀ D.T)
    (R : PicardIterateResidualData p u₀ D) :
    ∀ s, 0 < s → s ≤ D.T → ∀ k,
      Tendsto (fun n => cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k)
        atTop (nhds (cosineCoeffs (logisticLifted p (D.u s)) k)) := by
  intro s hs hsT k
  -- rewrite the limit slice `D.u s = picardLimit p u₀ D.T s`
  have hslice : D.u s = picardLimit p u₀ D.T s := by rw [hDu]
  rw [hslice]
  -- transport the `MildExistenceData`'s horizon to `D.T`
  have hLcont_iter' : ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ R.hME.T →
      ContinuousOn (logisticLifted p (picardIter p u₀ n σ)) (Set.Icc (0 : ℝ) 1) := by
    rw [R.hME_T]; exact R.hLcont_iter
  have hLcont_lim' : ∀ (σ : ℝ), 0 < σ → σ ≤ R.hME.T →
      ContinuousOn (logisticLifted p (picardLimit p u₀ R.hME.T σ)) (Set.Icc (0 : ℝ) 1) := by
    rw [R.hME_T]; exact R.hLcont_lim
  have hsT' : s ≤ R.hME.T := by rw [R.hME_T]; exact hsT
  have h := ShenWork.IntervalPicardLimitCoeffConv.picardIter_logisticCoeff_tendsto_limit
    R.hME hLcont_iter' hLcont_lim' hs hsT' k
  -- the limit slice's horizon is `R.hME.T = D.T`
  rw [R.hME_T] at h
  exact h

/-- **R-src0F-2 (hCwin_ex), proved from the bundle.**  The per-window
`IterateWindowC2Data` feeds `source_coeff_window_uniform` to produce the n-uniform
window source envelope existence statement. -/
theorem hCwin_ex_of_residual
    {p : CM2Params} {u₀ : intervalDomainPoint → ℝ}
    {D : GradientMildSolutionData p u₀}
    (hα : 1 ≤ p.α)
    (R : PicardIterateResidualData p u₀ D) :
    ∃ Cwin : ℝ → ℝ, (∀ a', 0 ≤ Cwin a') ∧
      (∀ a', 0 < a' → ∀ s, a' ≤ s → s ≤ D.T → ∀ (n : ℕ) (k : ℕ),
        |cosineCoeffs (logisticLifted p (picardIter p u₀ n s)) k|
          ≤ windowEnv (Cwin a') k) :=
  source_coeff_window_uniform p u₀ hα R.Wdata

end ShenWork.Paper2.Thm11ChiZeroResidual
