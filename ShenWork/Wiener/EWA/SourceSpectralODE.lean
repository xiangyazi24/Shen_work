/-
  ShenWork/Wiener/EWA/SourceSpectralODE.lean

  **χ₀<0 coefficient-level spectral ODE — foundational lemma.**

  The full-source coefficient `fullSourceCoeff p u u₀cos t n`
  (SourceStrongSolution.lean:109) satisfies the per-mode spectral ODE

    `d/dt b̂ₙ(t) = −λₙ · b̂ₙ(t) + ((−χ₀)·âₙ^chem(t) + âₙ^log(t))`

  i.e. its committed time-derivative `fullSourceCoeffDot`
  (SourceTimeRegularity.lean:41) equals `−λₙ` times the coefficient plus the two
  physical source coefficients.  This is pure algebra: the heat leg's
  `−λₙ·e^{−tλₙ}·u₀cos n` and each Duhamel leg's `−λₙ·bₙ(t)` are exactly `−λₙ`
  times the corresponding pieces of `fullSourceCoeff`, and the `aₙ(t)` terms of
  the Duhamel ODE RHS are the source coefficients.

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceTimeRegularity

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)

/-- **Coefficient-level spectral ODE for the full source coefficient.**  The
committed time-derivative `fullSourceCoeffDot` is `−λₙ` times the coefficient
`fullSourceCoeff` plus the two physical source coefficients `(−χ₀)·` chemDiv `+`
logistic.  The Duhamel `λₙ·bₙ` terms in `fullSourceCoeffDot` cancel against `−λₙ`
times the `bₙ` carried in `fullSourceCoeff`, leaving the source coeffs. -/
theorem fullSourceCoeff_spectral_ode (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ)
    (u₀cos : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    fullSourceCoeffDot p u u₀cos t n
      = -(unitIntervalCosineEigenvalue n) * fullSourceCoeff p u u₀cos t n
        + ((-p.χ₀) * coupledChemDivSourceCoeffs p u t n
            + coupledLogisticSourceCoeffs p u t n) := by
  unfold fullSourceCoeffDot fullSourceCoeff; ring

end ShenWork.EWA
