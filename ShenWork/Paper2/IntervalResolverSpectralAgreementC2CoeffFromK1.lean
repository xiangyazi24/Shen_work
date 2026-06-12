import ShenWork.Paper2.IntervalPicardLimitK1C2Coeff
import ShenWork.PDE.IntervalDuhamelDirectC2Coeff

/-!
# C2-coefficient spectral agreement from K1 local restarts

This file only packages source-side `SourceC2CoeffFields` into the strengthened
resolver spectral-agreement record.  The Duhamel branch C2 estimates are proved
in `IntervalDuhamelDirectC2Coeff`; the remaining input here is exactly the
source λ² coefficient envelope.
-/

open Filter Topology Set
open ShenWork.IntervalDomain (intervalDomainPoint intervalDomainLift)
open ShenWork.IntervalResolverJointC2 (ResolverHasSpectralAgreementC2Coeff)
open ShenWork.IntervalResolverTimeRegularity (ResolverHasSpectralAgreement)
open ShenWork.IntervalSourceCoefficientTimeC1 (localRestartCoeff)
open ShenWork.CosineSpectrum (cosineMode)
open ShenWork.Paper2.PicardLimitK1 (LocalRestart)
open ShenWork.Paper2.PicardLimitK1C2Coeff
  (LocalRestartC2 SourceC2CoeffFields)

noncomputable section

namespace ShenWork.Paper2.ResolverSpectralAgreementC2CoeffFromK1

/-- Package already-upgraded K1 local restarts into
`ResolverHasSpectralAgreementC2Coeff`. -/
theorem resolverHasSpectralAgreementC2Coeff_of_localRestartC2
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestartC2 p u T σ) :
    ResolverHasSpectralAgreementC2Coeff T u := by
  refine ⟨H, ?_⟩
  intro t₀ ht₀ hT
  let L : LocalRestartC2 p u T t₀ := mkL t₀ ht₀ hT
  refine ⟨L.base.a₀, L.base.M, L.base.hM_nonneg, L.base.ha₀,
    L.base.aC, L.srcC2, L.base.τ, ?_, ?_⟩
  · have := L.base.hστ
    linarith
  · refine eventually_of_mem (isOpen_Ioo.mem_nhds L.base.hσ_mem) ?_
    intro s hs x
    simpa [intervalDomainLift, x.2] using L.base.hrep s hs x.1 x.2

/-- Package K1 local restarts plus source-side C2 coefficient fields into the
strengthened resolver spectral-agreement record.

The hypothesis `fields` is the honest residual: it is the source λ² coefficient
envelope for the clamped local source, not a Duhamel or resolver C2 assumption. -/
theorem resolverHasSpectralAgreementC2Coeff_of_sourceFields
    {p : CM2Params} {u : ℝ → intervalDomainPoint → ℝ} {T : ℝ}
    (H : ResolverHasSpectralAgreement T u)
    (mkL : ∀ σ, 0 < σ → σ < T → LocalRestart p u T σ)
    (fields : ∀ σ (hσ0 : 0 < σ) (hσT : σ < T),
      SourceC2CoeffFields (mkL σ hσ0 hσT).srcC) :
    ResolverHasSpectralAgreementC2Coeff T u :=
  resolverHasSpectralAgreementC2Coeff_of_localRestartC2 H
    (fun σ hσ0 hσT =>
      LocalRestartC2.ofSourceFields
        (mkL σ hσ0 hσT) (fields σ hσ0 hσT))

end ShenWork.Paper2.ResolverSpectralAgreementC2CoeffFromK1
