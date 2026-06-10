/-
  ShenWork/PDE/IntervalSpectralSubtypeAdapter.lean

  **The single surgical point of the constant-extension reroute.**

  The closed-interval spectral identity
  (`IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`)
  takes `Continuous f` GLOBALLY on ℝ.  Throughout the Picard chain it is
  invoked with `f = intervalDomainLift g` (zero extension), whose global
  continuity is FALSE for positive boundary data.

  This file provides the paper-faithful form: `Continuous g` on the SUBTYPE
  (g ∈ C(Ω̄), paper Def 1.1) suffices.  Route: the constant extension
  `intervalDomainConstExtend g` IS globally continuous, the semigroup operator
  and the cosine coefficients cannot distinguish it from the lift (both only
  see [0,1], where they agree), so the spectral identity transfers verbatim.

  Downstream (`IntervalPicardLimitRestartWeak.limit_lift_eq_cosineSeries_of_subtypeCont`)
  this replaces BOTH call sites of the Icc identity — the homogeneous term
  `S(t)(lift u₀)` and the Duhamel integrand `S(t−s)(logisticLifted …)` — with
  no other change to the chain.

  Inputs (proved in `IntervalDomainContinuousExtension`):
  * `constExtend_continuous`
  * `cosineCoeffs_constExtend_eq_lift`
  * `semigroupOperator_constExtend_eq_lift`

  No `sorry`, no `admit`, no custom `axiom`.
-/
import ShenWork.PDE.IntervalDomainContinuousExtension
import ShenWork.PDE.IntervalFullKernelSpectralClean

open ShenWork.IntervalDomain
open ShenWork.IntervalNeumannFullKernel (intervalFullSemigroupOperator cosineCoeffs)

noncomputable section

namespace ShenWork.IntervalSpectralSubtypeAdapter

/-- **Closed-interval spectral identity from subtype continuity.**
Same conclusion as
`intervalFullSemigroupOperator_eq_cosineHeatValue_Icc`, with the (false for
positive data) hypothesis `Continuous (intervalDomainLift f)` replaced by the
paper-faithful `Continuous f` on the subtype.  Routed through the constant
extension, which agrees with the lift on `[0,1]` — the only region the
semigroup operator and the cosine coefficients see. -/
theorem intervalFullSemigroupOperator_eq_cosineHeatValue_Icc_of_subtypeCont
    {t : ℝ} (ht : 0 < t) {f : intervalDomainPoint → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ n, |cosineCoeffs (intervalDomainLift f) n| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    intervalFullSemigroupOperator t (intervalDomainLift f) x =
      unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x := by
  have hcoef : cosineCoeffs (intervalDomainConstExtend f)
      = cosineCoeffs (intervalDomainLift f) :=
    funext (cosineCoeffs_constExtend_eq_lift f)
  have hM' : ∀ n, |cosineCoeffs (intervalDomainConstExtend f) n| ≤ M := by
    intro n
    rw [cosineCoeffs_constExtend_eq_lift f n]
    exact hM n
  calc intervalFullSemigroupOperator t (intervalDomainLift f) x
      = intervalFullSemigroupOperator t (intervalDomainConstExtend f) x :=
        semigroupOperator_constExtend_eq_lift.symm
    _ = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainConstExtend f)) x :=
        ShenWork.IntervalFullKernelSpectralClean.intervalFullSemigroupOperator_eq_cosineHeatValue_Icc
          ht (constExtend_continuous hf) hM' hx
    _ = unitIntervalCosineHeatValue t (cosineCoeffs (intervalDomainLift f)) x := by
        rw [hcoef]

end ShenWork.IntervalSpectralSubtypeAdapter
