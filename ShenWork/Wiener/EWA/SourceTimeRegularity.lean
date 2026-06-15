/-
  ShenWork/Wiener/EWA/SourceTimeRegularity.lean

  **χ₀<0 u_t (time-regularity) construction — BRICK 1.**

  Per-mode time-derivative of `fullSourceCoeff` (SourceStrongSolution.lean:109).

  `fullSourceCoeff p u u₀cos t n` is the heat datum leg
  `e^{−tλₙ}·u₀cos n` plus `(−χ₀)·` the chemDiv spectral Duhamel coefficient
  plus the logistic spectral Duhamel coefficient.  Each leg is a clean
  `HasDerivAt`:

  * heat leg: `d/dt e^{−tλₙ}·u₀cos n = −λₙ·e^{−tλₙ}·u₀cos n`;
  * each Duhamel leg: the **spectral Duhamel ODE**
    `duhamelSpectralCoeff_hasDerivAt` (IntervalSourceCoefficientTimeC1.lean:200),
    `d/dt bₙ(t) = aₙ(t) − λₙ·bₙ(t)`, scaled by `(−χ₀)` resp. `1`.

  The two `DuhamelSourceTimeC1` packages are carried as hypotheses (the logistic
  one is the committed `logSrc`; the chemDiv one is constructible via
  `coupledChemDivSource_timeC1_of_fields`).

  No `sorry`, `admit`, `native_decide`, or custom `axiom`.
-/
import ShenWork.Wiener.EWA.SourceStrongSolution
import ShenWork.PDE.IntervalSourceCoefficientTimeC1

noncomputable section

namespace ShenWork.EWA

open ShenWork.IntervalDuhamelClosedC2 (duhamelSpectralCoeff DuhamelSourceTimeC1)
open ShenWork.IntervalCoupledRegularityBootstrap
  (coupledChemDivSourceCoeffs coupledLogisticSourceCoeffs)
open ShenWork.IntervalDomain (intervalDomainPoint)
open ShenWork.IntervalSourceCoefficientTimeC1 (duhamelSpectralCoeff_hasDerivAt)

/-- **The full-source coefficient time-derivative.**  The per-mode `d/dt` of
`fullSourceCoeff p u u₀cos t n`: heat leg `−λₙ·e^{−tλₙ}·u₀cos n`, plus `(−χ₀)·`
the chemDiv spectral Duhamel ODE RHS `aₙ(t) − λₙ·bₙ(t)`, plus the logistic
spectral Duhamel ODE RHS. -/
noncomputable def fullSourceCoeffDot (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  -(unitIntervalCosineEigenvalue n)
      * Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n
  + (-p.χ₀) * (coupledChemDivSourceCoeffs p u t n
      - unitIntervalCosineEigenvalue n
        * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)
  + (coupledLogisticSourceCoeffs p u t n
      - unitIntervalCosineEigenvalue n
        * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n)

/-- **Per-mode time-derivative of `fullSourceCoeff`.**  The `n`-th Neumann cosine
coefficient of the source-form mild solution has time-derivative
`fullSourceCoeffDot`, assembled from the heat-leg derivative and the two
spectral Duhamel ODEs (one per carried `DuhamelSourceTimeC1` package). -/
theorem fullSourceCoeff_term_hasDerivAt_time (p : CM2Params)
    (u : ℝ → intervalDomainPoint → ℝ) (u₀cos : ℕ → ℝ)
    (hchem : DuhamelSourceTimeC1 (coupledChemDivSourceCoeffs p u))
    (hlog : DuhamelSourceTimeC1 (coupledLogisticSourceCoeffs p u))
    (t : ℝ) (n : ℕ) :
    HasDerivAt (fun t => fullSourceCoeff p u u₀cos t n)
      (fullSourceCoeffDot p u u₀cos t n) t := by
  -- heat leg: d/dt e^{−tλₙ}·u₀cos n = −λₙ·e^{−tλₙ}·u₀cos n.
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-r * unitIntervalCosineEigenvalue n))
      (-unitIntervalCosineEigenvalue n
        * Real.exp (-t * unitIntervalCosineEigenvalue n)) t := by
    have h1 : HasDerivAt (fun r : ℝ => -r * unitIntervalCosineEigenvalue n)
        (-1 * unitIntervalCosineEigenvalue n) t :=
      (hasDerivAt_id t).neg.mul_const (unitIntervalCosineEigenvalue n)
    have h2 := h1.exp
    simp only [neg_mul, one_mul] at h2 ⊢
    convert h2 using 1; ring
  have hheat : HasDerivAt
      (fun r : ℝ => Real.exp (-r * unitIntervalCosineEigenvalue n) * u₀cos n)
      (-unitIntervalCosineEigenvalue n
        * Real.exp (-t * unitIntervalCosineEigenvalue n) * u₀cos n) t :=
    hexp.mul_const (u₀cos n)
  -- chemDiv leg: (−χ₀)· spectral Duhamel ODE.
  have hchemleg : HasDerivAt
      (fun r => (-p.χ₀)
        * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) r n)
      ((-p.χ₀) * (coupledChemDivSourceCoeffs p u t n
        - unitIntervalCosineEigenvalue n
          * duhamelSpectralCoeff (coupledChemDivSourceCoeffs p u) t n)) t :=
    (duhamelSpectralCoeff_hasDerivAt hchem t n).const_mul (-p.χ₀)
  -- logistic leg: spectral Duhamel ODE.
  have hlogleg : HasDerivAt
      (fun r => duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) r n)
      (coupledLogisticSourceCoeffs p u t n
        - unitIntervalCosineEigenvalue n
          * duhamelSpectralCoeff (coupledLogisticSourceCoeffs p u) t n) t :=
    duhamelSpectralCoeff_hasDerivAt hlog t n
  exact (hheat.add hchemleg).add hlogleg

end ShenWork.EWA
